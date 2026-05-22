import io
#!/usr/bin/env python3
"""
Enrichissement GPX avec POIs eau/restaurants/épiceries via OpenStreetMap (Overpass API)
Usage: python enrichir_gpx.py *.gpx
Dépendances: pip install requests
"""

import sys
import math
import time
import os
import xml.etree.ElementTree as ET
import requests
from reportlab.pdfgen import canvas
from reportlab.lib.units import mm, cm

# ─── Configuration ───────────────────────────────────────────────────────────

MAX_DIST_WATER = 300   # mètres max du tracé pour eau potable
MAX_DIST_FOOD  = 400   # mètres max pour restaurants/cafés
MAX_DIST_SHOP  = 500   # mètres max pour épiceries/supermarchés
MAX_DIST_COL        = 50    # mètres max pour cols de montagne (marge OSM uniquement)
MAX_DIST_COL_NAME   = 1000  # mètres max pour chercher un nom OSM autour d'un sommet sans nom
MANUAL_NAMES_FILE   = "noms_cols.csv"  # fichier CSV optionnel: lat,lon,nom (pour nommer les cols sans nom OSM)
SPRINTS_FILE        = "sprints.csv"    # fichier CSV optionnel: nom,km (sprints intermédiaires à ajouter au tracé)

# ─── Détection des sommets sur le profil GPX ─────────────────────────────────
# Ces paramètres pilotent detect_track_peaks(), qui repère les côtes que
# OpenStreetMap ne connaît pas (la plupart des « côtes » nommées ne sont pas
# des nœuds OSM). Ils sont volontairement adaptables au relief :
#
#   • Haute montagne (Alpes, Vosges, Pyrénées) : on peut remonter la
#     proéminence (~80-100 m) et fixer un plancher d'altitude pour ignorer les
#     bosses de vallée.
#   • Moyenne montagne / plaine (Ardennes, Flandres) : proéminence basse
#     (~40-50 m) et AUCUN plancher d'altitude, sinon toutes les côtes — dont
#     le sommet est souvent sous 500 m — sont rejetées.
#
# La détection est désormais pilotée par la SIGNIFICATIVITÉ de la montée
# (proéminence + dénivelé via classify_col), et non plus par l'altitude
# absolue : une côte de 150 m à 8 % est un col, qu'elle culmine à 300 m ou
# à 1500 m.
PEAK_MIN_PROMINENCE = 50      # proéminence minimale d'un sommet (m) : hauteur
                              #   dont il dépasse le creux le plus haut de part
                              #   et d'autre. Filtre le bruit GPS et les faux
                              #   plats. Baisser pour la moyenne montagne.
PEAK_MIN_ELEVATION  = None    # plancher d'altitude absolu (m) ou None.
                              #   None = aucun plancher (recommandé hors haute
                              #   montagne). Mettre p.ex. 800 pour ne garder
                              #   que les vrais sommets en haute montagne.
PEAK_ISOLATION_KM   = 1.0     # un sommet doit être le point le plus haut dans
                              #   ce rayon (km) ; deux sommets plus proches que
                              #   cette distance sont fusionnés (on garde le
                              #   plus haut). Indépendant de la densité de points.
PEAK_PROM_SEARCH_KM = 5.0     # distance (km) explorée de chaque côté pour
                              #   mesurer la proéminence.
PEAK_SMOOTH_WINDOW  = 15      # demi-fenêtre de lissage du profil altimétrique
                              #   (points), pour filtrer le bruit des altitudes.

# ─── Nommage des cols / côtes détectés ───────────────────────────────────────
# Mots-clés qui, présents dans le nom OSM d'une voie ou d'un lieu, indiquent
# qu'il s'agit déjà d'un nom de côte/montée : ce nom est alors repris tel quel.
# (« thier » et « tienne » = mot wallon désignant une route en forte pente.)
CLIMB_KEYWORDS = ('côte', 'cote', 'col ', 'mur ', 'montée', 'montee', 'rampe',
                  'thier', 'tienne', 'helling', 'berg', 'pas de', 'raidillon')

# Types de voie retirés en tête d'un nom de rue pour en extraire le nom propre
# (« Rue de la Redoute » -> « La Redoute »).
ROAD_TYPE_PREFIXES = ('rue', 'route', 'chemin', 'avenue', 'voie', 'allée',
                      'allee', 'impasse', 'ruelle', 'sentier', 'clos', 'drève',
                      'dreve', 'quai', 'boulevard', 'venelle', 'passage',
                      'tige', 'cour')

# Noms trop génériques pour servir de nom de côte (rejetés pour éviter les
# faux positifs : « Rue de l'Église » ne donne pas une côte « L'Église »).
GENERIC_NAME_TOKENS = ('église', 'eglise', 'gare', 'village', 'école', 'ecole',
                       'mairie', 'cimetière', 'cimetiere', 'stade', 'centre',
                       'pont', 'fontaine', 'chapelle', 'calvaire', 'commune',
                       'hameau', 'parking', 'industrie', 'usine')

# Nommage par la route gravie : un point de la montée est considéré « sur » une
# route si sa géométrie passe à moins de ROAD_COVER_M mètres ; une route doit
# « couvrir » au moins ROAD_MIN_COVERAGE de la montée pour être retenue comme
# celle que l'on gravit. C'est cette couverture — et non la proximité du seul
# sommet — qui départage les routes : une petite rue de crête traversée sur
# 50 m ne l'emporte pas sur la route gravie pendant 2 km.
ROAD_COVER_M      = 30
ROAD_MIN_COVERAGE = 0.20

# Longueur (km) de montée analysée avant le sommet pour chercher un nom.
NAMING_APPROACH_KM = 2.5

CATEGORIES = {
    "water": True,   # Eau potable (fontaines, sources, robinets)
    "food":  True,   # Restaurants, cafés, fast-food
    "shop":  True,   # Épiceries, supermarchés
    "col":   True,   # Cols et passages de montagne
}

OVERPASS_URL = "https://overpass-api.de/api/interpreter"

# ─── Fonctions utilitaires ───────────────────────────────────────────────────

def haversine(lat1, lon1, lat2, lon2):
    R = 6371000
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlam = math.radians(lon2 - lon1)
    a = math.sin(dphi/2)**2 + math.cos(phi1)*math.cos(phi2)*math.sin(dlam/2)**2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))

def min_dist_to_track(lat, lon, track_pts, step=10):
    """Distance minimale d'un point au tracé (échantillonné tous les `step` points)."""
    return min(haversine(lat, lon, tlat, tlon) for tlat, tlon in track_pts[::step])

def smooth_eles(arr, w=8):
    """Lissage par moyenne glissante pour filtrer le bruit GPS."""
    return [sum(arr[max(0,i-w):i+w+1]) / len(arr[max(0,i-w):i+w+1]) for i in range(len(arr))]


def classify_col(summit_lat, summit_lon, summit_ele, track_pts_with_ele, start_limit_idx=0):
    """
    Calcule les stats de la montée menant au col.
    Le pied ne peut pas remonter avant start_limit_idx (sommet du col précédent).
    Remonte depuis le sommet en cherchant le minimum, s'arrête sur une bosse > DROP_M.
    """
    if not summit_ele or not track_pts_with_ele:
        return None, None, None, None, None, None, None

    DROP_M   = 30   # tolérance pour les petites bosses dans la montée (m)
    MIN_CLIMB = 30  # dénivelé minimum pour une vraie montée (m)

    # Trouver le point le plus proche du col sur le tracé
    best_idx = min(range(len(track_pts_with_ele)),
                   key=lambda i: haversine(summit_lat, summit_lon,
                                           track_pts_with_ele[i][0], track_pts_with_ele[i][1]))

    # Fenêtre de recherche : de start_limit_idx jusqu'au sommet
    start = max(start_limit_idx, max(0, best_idx - 1200))
    seg = [track_pts_with_ele[i][2] for i in range(start, best_idx + 1)]
    if len(seg) < 3:
        return None, None, None, None, None, None, None

    sm = smooth_eles(seg)
    n = len(sm) - 1
    min_val    = sm[n]
    foot_local = n

    for j in range(n - 1, -1, -1):
        if sm[j] < min_val:
            min_val    = sm[j]
            foot_local = j
        elif sm[j] > min_val + DROP_M:
            break

    foot_idx = start + foot_local
    foot_lat, foot_lon = track_pts_with_ele[foot_idx][0], track_pts_with_ele[foot_idx][1]

    foot_ele = track_pts_with_ele[foot_idx][2]
    denivele = summit_ele - foot_ele
    if denivele < MIN_CLIMB:
        # Col en descente ou trop petit — ignorer
        return None, None, None, None, None, None, None

    dist_m = sum(
        haversine(track_pts_with_ele[i][0], track_pts_with_ele[i][1],
                  track_pts_with_ele[i+1][0], track_pts_with_ele[i+1][1])
        for i in range(foot_idx, best_idx)
        if i + 1 < len(track_pts_with_ele)
    )
    if dist_m < 100:
        return None, None, None, None, None, None, None

    pente_moy   = (denivele / dist_m) * 100
    coefficient = round((pente_moy ** 2) * (dist_m / 1000), 1)

    if coefficient >= 600:   cat = 'HC'
    elif coefficient >= 250: cat = '1'
    elif coefficient >= 180: cat = '2'
    elif coefficient >= 80:  cat = '3'
    elif coefficient > 34:   cat = '4'
    else:                    cat = None

    return cat, round(denivele), round(dist_m / 1000, 1), round(pente_moy, 1), round(coefficient), foot_lat, foot_lon


def parse_gpx(filepath):
    """Extrait les points du tracé GPX, avec altitude si disponible.
    Retourne aussi un dict des noms de waypoints existants {(lat4,lon4): name}."""
    tree = ET.parse(filepath)
    root = tree.getroot()
    ns = {'gpx': 'http://www.topografix.com/GPX/1/1'}
    pts = root.findall('.//gpx:trkpt', ns) or root.findall('.//gpx:rtept', ns)
    track_pts = [(float(p.get('lat')), float(p.get('lon'))) for p in pts]
    track_pts_ele = []
    for p in pts:
        ele_el = p.find('gpx:ele', ns)
        ele = float(ele_el.text) if ele_el is not None else None
        track_pts_ele.append((float(p.get('lat')), float(p.get('lon')), ele))
    has_ele = any(e[2] is not None for e in track_pts_ele)
    # Lire les noms des waypoints existants (enrichissements précédents)
    existing_names = {}
    for wpt in root.findall('gpx:wpt', ns):
        wname = wpt.findtext('gpx:name', '', ns) or ''
        # Nettoyer les préfixes ajoutés par le script
        for prefix in ('[COL] ', '[EAU] ', '[RESTO] ', '[EPICERIE] '):
            wname = wname.replace(prefix, '')
        # Nettoyer les suffixes score/catégorie ajoutés par le script
        if ' | Score:' in wname:
            wname = wname[:wname.index(' | Score:')]
        if ' | Cat.' in wname:
            wname = wname[:wname.index(' | Cat.')]
        if ' | HC' in wname:
            wname = wname[:wname.index(' | HC')]
        if wname:
            key = (round(float(wpt.get('lat')), 4), round(float(wpt.get('lon')), 4))
            existing_names[key] = wname.strip()
    return track_pts, track_pts_ele if has_ele else None, tree, root, existing_names

# ─── Requête Overpass ────────────────────────────────────────────────────────

def build_query(bbox, incl_water, incl_food, incl_shop, incl_col):
    s, w, n, e = bbox
    buf = 0.005
    b = f"{s-buf:.4f},{w-buf:.4f},{n+buf:.4f},{e+buf:.4f}"
    parts = []
    if incl_water:
        parts += [
            f'node["amenity"="drinking_water"]({b});',
            f'node["natural"="spring"]["drinking_water"="yes"]({b});',
            f'node["man_made"="water_tap"]({b});',
            f'node["amenity"="fountain"]["drinking_water"="yes"]({b});',
        ]
    if incl_food:
        parts += [
            f'node["amenity"="restaurant"]({b});',
            f'node["amenity"="cafe"]({b});',
            f'node["amenity"="fast_food"]({b});',
            f'node["amenity"="bar"]({b});',
        ]
    if incl_shop:
        parts += [
            f'node["shop"="supermarket"]({b});',
            f'node["shop"="convenience"]({b});',
            f'node["shop"="grocery"]({b});',
            f'node["amenity"="supermarket"]({b});',
        ]
    if incl_col:
        parts += [
            f'node["mountain_pass"="yes"]({b});',
            f'node["natural"="saddle"]({b});',
            f'node["natural"="peak"]["ele"]({b});',
        ]
        return f"[out:json][timeout:30];\n(\n{''.join(parts)}\n);\nout body;"

def query_overpass(bbox):
    query = build_query(bbox, CATEGORIES["water"], CATEGORIES["food"], CATEGORIES["shop"], CATEGORIES["col"])
    print(f"  Requête Overpass...", end=" ", flush=True)
    headers = {
        "User-Agent": "GPX-POI-Enricher/1.0 (personal use)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept": "application/json",
    }
    mirrors = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    ]
    last_err = None
    for url in mirrors:
        try:
            resp = requests.post(url, data={"data": query}, headers=headers, timeout=45)
            resp.raise_for_status()
            data = resp.json()
            print(f"{len(data.get('elements', []))} éléments trouvés")
            return data
        except Exception as e:
            last_err = e
            print(f"\n  Mirror {url} échoué ({e}), essai suivant...", end=" ", flush=True)
    raise Exception(f"Tous les mirrors Overpass ont échoué. Dernière erreur: {last_err}")

# ─── Catégorisation des POIs ─────────────────────────────────────────────────

def categorize(el):
    t = el.get('tags', {})
    if t.get('access') == 'private':
        return None
    amenity = t.get('amenity', '')
    shop    = t.get('shop', '')
    natural = t.get('natural', '')
    dw      = t.get('drinking_water', '')

    if amenity in ('drinking_water', 'water_point') \
       or (amenity == 'fountain' and dw == 'yes') \
       or (natural == 'spring' and dw == 'yes') \
       or t.get('man_made') == 'water_tap':
        return 'water'

    if amenity in ('restaurant', 'cafe', 'fast_food', 'bar'):
        return 'food'

    if shop in ('supermarket', 'convenience', 'grocery') or amenity == 'supermarket':
        if t.get('vending') == 'fuel' and not t.get('name'):
            return None
        return 'shop'

    if t.get('mountain_pass') == 'yes' or natural in ('saddle', 'peak'):
        return 'col'

    return None

def get_name(tags, cat):
    for key in ('name', 'name:fr', 'alt_name', 'official_name', 'loc_name'):
        if tags.get(key):
            return tags[key]
    defaults = {'water': 'Eau potable', 'food': 'Restaurant', 'shop': 'Épicerie', 'col': 'Col'}
    return defaults.get(cat, 'POI')

def get_prefix(cat):
    return {'water': '[EAU]', 'food': '[RESTO]', 'shop': '[EPICERIE]', 'col': '[COL]'}[cat]

def get_symbol(tags, cat, col_cat=None):
    """Retourne le code icône OpenRunner selon la catégorie."""
    if cat == 'water':
        return '104'
    if cat == 'food':
        return '49'
    if cat == 'shop':
        return '50'
    if cat == 'col':
        return {'HC': '66', '1': '62', '2': '63', '3': '64', '4': '65'}.get(col_cat, '105')
    if cat == 'sprint':
        return '19'        # sprint intermédiaire
    if cat == 'climb_foot':
        return '17'        # « Meilleur Grimpeur » : pied d'une ascension
    return '1'



def get_description(tags, cat):
    parts = []
    if tags.get('opening_hours'):
        parts.append(f"Horaires: {tags['opening_hours']}")
    if tags.get('phone'):
        parts.append(f"Tel: {tags['phone']}")
    if tags.get('cuisine'):
        parts.append(f"Cuisine: {tags['cuisine']}")
    if tags.get('website'):
        parts.append(f"Web: {tags['website']}")
    if cat == 'water' and tags.get('drinking_water') == 'yes':
        parts.append("Eau potable confirmée")
    if cat == 'col':
        if tags.get('ele'):
            parts.insert(0, f"Alt: {tags['ele']}m")
        if tags.get('wikipedia'):
            parts.append(f"Wikipedia: {tags['wikipedia']}")
    return ' | '.join(parts)

def get_col_description(tags, col_cat, denivele, col_dist, pente, score=None):
    """Description enrichie pour un col avec sa catégorie Tour de France."""
    parts = []
    if tags.get('ele'):
        parts.append(f"Alt: {tags['ele']}m")
    if col_cat:
        label = 'HC' if col_cat == 'HC' else f"Cat. {col_cat}"
        parts.append(f"Categorie: {label}")
    if score:
        parts.append(f"Score: {score}")
    if denivele and col_dist:
        parts.append(f"Montee: {col_dist}km / {denivele}m")
    if pente:
        parts.append(f"Pente moy: {pente}%")
    if tags.get('wikipedia'):
        parts.append(f"Wikipedia: {tags['wikipedia']}")
    return ' | '.join(parts)

# ─── Injection dans le GPX ───────────────────────────────────────────────────

def inject_waypoints(root, pois):
    ns = 'http://www.topografix.com/GPX/1/1'
    ET.register_namespace('', ns)

    for poi in sorted(pois, key=lambda x: x['dist']):
        wpt = ET.SubElement(root, f'{{{ns}}}wpt')
        wpt.set('lat', str(poi['lat']))
        wpt.set('lon', str(poi['lon']))

        ele_el = ET.SubElement(wpt, f'{{{ns}}}ele')
        ele_el.text = poi['tags'].get('ele', '0')

        # Nom : pour les cols, inclure nom + score + catégorie
        name_el = ET.SubElement(wpt, f'{{{ns}}}name')
        if poi['cat'] == 'col':
            col_cat = poi.get('col_cat')
            col_score = poi.get('col_score')
            label = 'HC' if col_cat == 'HC' else (f'Cat. {col_cat}' if col_cat else None)
            if label and col_score:
                name_el.text = f"{poi['name']} | Score: {col_score} | {label}"
            elif label:
                name_el.text = f"{poi['name']} | {label}"
            else:
                name_el.text = poi['name']
        else:
            name_el.text = poi['name']

        desc_el = ET.SubElement(wpt, f'{{{ns}}}desc')
        if poi['cat'] == 'col':
            desc_el.text = get_col_description(
                poi['tags'], poi.get('col_cat'), poi.get('col_denivele'),
                poi.get('col_dist'), poi.get('col_pente'), poi.get('col_score'))
        elif 'desc' in poi:
            desc_el.text = poi['desc']        # sprints, repères grimpeur : desc vide
        else:
            desc_el.text = get_description(poi['tags'], poi['cat'])

        sym_el = ET.SubElement(wpt, f'{{{ns}}}sym')
        sym_el.text = get_symbol(poi['tags'], poi['cat'], poi.get('col_cat'))

# ─── Génération PDF roadbook ─────────────────────────────────────────────────

def compute_cumulative_distances(track_pts):
    """Calcule la distance cumulée en km à chaque point du tracé."""
    dists = [0.0]
    for i in range(1, len(track_pts)):
        d = haversine(track_pts[i-1][0], track_pts[i-1][1],
                      track_pts[i][0],   track_pts[i][1])
        dists.append(dists[-1] + d)
    return [d / 1000 for d in dists]

def find_km_at_point(lat, lon, track_pts, cum_dists):
    """Retourne la distance cumulée (km) au point du tracé le plus proche."""
    best_i = min(range(len(track_pts)), key=lambda i: haversine(lat, lon, track_pts[i][0], track_pts[i][1]))
    return cum_dists[best_i]

def _draw_sprint_icon(c, x, y, s):
    """
    Dessine un petit cycliste en danseuse (sprint) dans un carré s×s, dont le
    coin inférieur gauche est en (x, y). Utilisé comme pictogramme de sprint
    intermédiaire dans le roadbook.
    """
    c.saveState()
    c.setStrokeColorRGB(0.10, 0.10, 0.10)
    c.setFillColorRGB(0.10, 0.10, 0.10)
    c.setLineWidth(max(0.4, s * 0.05))
    c.setLineCap(1)
    r = s * 0.20
    yb = y + r                                   # axe des roues
    xrear, xfront = x + r, x + s - r
    c.circle(xrear, yb, r, stroke=1, fill=0)
    c.circle(xfront, yb, r, stroke=1, fill=0)
    bb = (x + s * 0.46, yb)                      # boîtier de pédalier
    seat = (x + s * 0.40, yb + s * 0.42)         # selle
    bar = (xfront - s * 0.02, yb + s * 0.40)     # cintre
    p = c.beginPath()
    p.moveTo(*bb); p.lineTo(xrear, yb)
    p.moveTo(*bb); p.lineTo(*seat)
    p.moveTo(*seat); p.lineTo(*bar)
    p.moveTo(*bb); p.lineTo(*bar)
    p.moveTo(*bar); p.lineTo(xfront, yb)
    c.drawPath(p, stroke=1, fill=0)
    hip = (seat[0], seat[1] + s * 0.03)
    shoulder = (x + s * 0.62, yb + s * 0.72)
    head = (x + s * 0.75, yb + s * 0.82)
    q = c.beginPath()
    q.moveTo(*hip); q.lineTo(*shoulder)          # dos penché
    q.moveTo(*shoulder); q.lineTo(*bar)          # bras vers le cintre
    q.moveTo(*hip); q.lineTo(*bb)                # jambe vers le pédalier
    c.drawPath(q, stroke=1, fill=0)
    c.circle(head[0], head[1], s * 0.11, stroke=1, fill=1)
    c.restoreState()


def generate_roadbook_pdf(col_pois, track_pts, track_pts_ele, gpx_name, out_path,
                          logo_path=None, title=None, sprint_pois=None):
    """Génère un PDF 3.6x20cm avec la liste des cols et sprints pour le cadre."""
    PAGE_W = 3.6 * cm
    PAGE_H = 20 * cm
    MARGIN = 3 * mm

    cum_dists = compute_cumulative_distances(track_pts)
    total_km = cum_dists[-1]

    # Enrichir chaque col avec km sommet et km pied
    # Les cols ont déjà _s_idx calculé dans process_gpx
    cols_with_km = []
    for poi in col_pois:
        s_idx    = poi.get('_s_idx')
        if s_idx is None:
            s_idx = min(range(len(track_pts)),
                        key=lambda i: haversine(poi['lat'], poi['lon'],
                                                track_pts[i][0], track_pts[i][1]))
        km_summit = round(cum_dists[s_idx], 1)
        col_dist  = poi.get('col_dist')
        km_foot   = round(max(0.0, km_summit - col_dist), 1) if col_dist is not None else None
        cols_with_km.append({**poi, 'km_summit': km_summit, 'km_foot': km_foot, '_s_idx': s_idx})
    cols_with_km.sort(key=lambda x: x['km_summit'])

    # Supprimer les cols englobés par un suivant.
    # Un col A est englobé par B si :
    #   - B commence avant A (km_foot_B <= km_foot_A)
    #   - B se termine après A (km_summit_B > km_summit_A)
    #   - Il n'y a PAS de descente >= 20m entre le sommet de A et le pied de B
    #     (une vraie descente prouve qu'ils sont distincts)
    DESCENT_THRESHOLD = 20  # m

    # Déterminer les sommets intermédiaires :
    # Col A est intermédiaire si un col B ultérieur a un pied <= pied de A
    # ET qu'il n'y a pas de descente >= 15% du d+ de A entre les deux sommets.
    DISTINCT_RATIO = 0.15

    for col in cols_with_km:
        col['intermediate'] = False

    for i, col_a in enumerate(cols_with_km):
        foot_a   = col_a.get('km_foot') if col_a.get('km_foot') is not None else col_a['km_summit']
        deniv_a  = col_a.get('col_denivele') or 0
        min_desc = max(20, deniv_a * DISTINCT_RATIO)
        s_idx_a  = col_a['_s_idx']
        # Altitude sommet A
        try:    ele_a = float(col_a['tags'].get('ele') or 0) or track_pts_ele[s_idx_a][2]
        except: ele_a = track_pts_ele[s_idx_a][2]

        for col_b in cols_with_km[i+1:]:
            foot_b  = col_b.get('km_foot') if col_b.get('km_foot') is not None else col_b['km_summit']
            s_idx_b = col_b['_s_idx']
            if foot_b <= foot_a:
                # B démarre avant ou au même endroit → vérifier descente entre sommets
                eles_between = [track_pts_ele[k][2] for k in range(s_idx_a, s_idx_b+1)
                                if k < len(track_pts_ele)]
                descent = ele_a - min(eles_between) if eles_between else 0
                if descent < min_desc:
                    col_a['intermediate'] = True
                    break

    c = canvas.Canvas(out_path, pagesize=(PAGE_W, PAGE_H))

    y = PAGE_H - MARGIN

    # Logo optionnel
    if logo_path and os.path.isfile(logo_path):
        try:
            from reportlab.lib.utils import ImageReader
            img = ImageReader(logo_path)
            iw, ih = img.getSize()
            max_w = PAGE_W - 2 * MARGIN
            max_h = 12 * mm
            ratio = min(max_w / iw, max_h / ih)
            draw_w = iw * ratio
            draw_h = ih * ratio
            x_logo = (PAGE_W - draw_w) / 2
            c.drawImage(logo_path, x_logo, y - draw_h, width=draw_w, height=draw_h, mask='auto')
            y -= draw_h + 2 * mm
        except Exception as e:
            print(f"  Avertissement logo: {e}")

    # Titre
    c.setFont("Helvetica-Bold", 7)
    c.setFillColorRGB(0.15, 0.15, 0.15)
    route_name = title if title else os.path.basename(gpx_name).replace('.gpx', '').replace('_', ' ')
    # Tronquer si trop long
    while c.stringWidth(route_name, "Helvetica-Bold", 7) > PAGE_W - 2*MARGIN and len(route_name) > 4:
        route_name = route_name[:-1]
    if route_name[-1] not in ('.', '!', '?') and c.stringWidth(
            title if title else os.path.basename(gpx_name).replace('.gpx','').replace('_',' '),
            "Helvetica-Bold", 7) > PAGE_W - 2*MARGIN:
        route_name = route_name[:-1] + '.'
    c.drawCentredString(PAGE_W / 2, y - 4, route_name)
    y -= 5 * mm

    # Sous-titre total km
    n_sprints = len(sprint_pois or [])
    c.setFont("Helvetica", 5.5)
    c.setFillColorRGB(0.5, 0.5, 0.5)
    sub = f"{total_km:.0f} km — {len(cols_with_km)} col(s)"
    if n_sprints:
        sub += f" — {n_sprints} sprint(s)"
    c.drawCentredString(PAGE_W / 2, y - 2, sub)
    y -= 5 * mm

    # Séparateur
    c.setStrokeColorRGB(0.6, 0.6, 0.6)
    c.setLineWidth(0.4)
    c.line(MARGIN, y, PAGE_W - MARGIN, y)
    y -= 4 * mm

    cat_colors = {
        'HC':     (0.6, 0.0, 0.0),
        'Cat. 1': (0.8, 0.2, 0.0),
        'Cat. 2': (0.9, 0.5, 0.0),
        'Cat. 3': (0.2, 0.5, 0.8),
        'Cat. 4': (0.3, 0.6, 0.3),
    }

    # Fusionner cols et sprints en une seule liste ordonnée par kilométrage,
    # pour que le roadbook les présente dans l'ordre de la course.
    render_items = [{'kind': 'col', 'km': col['km_summit'], 'data': col}
                    for col in cols_with_km]
    for sp in (sprint_pois or []):
        s_idx = min(range(len(track_pts)),
                    key=lambda i: haversine(sp['lat'], sp['lon'],
                                            track_pts[i][0], track_pts[i][1]))
        render_items.append({'kind': 'sprint', 'km': round(cum_dists[s_idx], 1),
                              'data': sp})
    render_items.sort(key=lambda it: it['km'])

    for item in render_items:
        # ─── Bloc « sprint intermédiaire » ──────────────────────────────────
        if item['kind'] == 'sprint':
            sp = item['data']
            icon_s = 5.5 * mm
            _draw_sprint_icon(c, MARGIN, y - icon_s, icon_s)
            text_x = MARGIN + icon_s + 1.5 * mm
            c.setFillColorRGB(0.0, 0.6, 0.2)            # vert (maillot vert)
            c.setFont("Helvetica-Bold", 5.5)
            c.drawString(text_x, y - 2.3 * mm, "SPRINT")
            c.drawString(text_x, y - 4.7 * mm, "INTERMÉDIAIRE")
            c.setFillColorRGB(0.2, 0.2, 0.2)
            c.setFont("Helvetica-Bold", 6.5)
            c.drawRightString(PAGE_W - MARGIN, y - 2.3 * mm, f"{item['km']:.1f} km")
            # Nom du sprint sur sa propre ligne, pleine largeur
            c.setFillColorRGB(0.05, 0.05, 0.05)
            c.setFont("Helvetica-Bold", 7)
            sname = sp['name']
            while c.stringWidth(sname, "Helvetica-Bold", 7) > PAGE_W - 2 * MARGIN \
                    and len(sname) > 4:
                sname = sname[:-1]
            if sname != sp['name']:
                sname = sname[:-1] + '.'
            c.drawString(MARGIN, y - icon_s - 3 * mm, sname)
            y -= icon_s + 6 * mm
            c.setStrokeColorRGB(0.88, 0.88, 0.88)
            c.setLineWidth(0.3)
            c.line(MARGIN, y, PAGE_W - MARGIN, y)
            y -= 3.5 * mm
            if y < MARGIN + 15 * mm:
                c.showPage()
                y = PAGE_H - MARGIN
            continue

        # ─── Bloc col (inchangé) ────────────────────────────────────────────
        col = item['data']
        is_intermediate = col.get('intermediate', False)
        col_cat = col.get('col_cat')
        label = 'HC' if col_cat == 'HC' else (f"Cat. {col_cat}" if col_cat else None)
        indent = 4 * mm if is_intermediate else 0

        if is_intermediate:
            # Sommet intermédiaire : ligne compacte avec tiret et altitude
            c.setFillColorRGB(0.55, 0.55, 0.55)
            c.setFont("Helvetica", 6)
            name = col['name']
            ele_str = f"  {col['tags'].get('ele', '')}m" if col['tags'].get('ele') else ''
            km_summit = col.get('km_summit')
            km_str = f"{km_summit:.1f}km" if km_summit is not None else ''
            inter_text = f"↳ {name}{ele_str}"
            # Tronquer si trop long
            max_w = PAGE_W - 2*MARGIN - indent - c.stringWidth(km_str, "Helvetica", 6) - 2*mm
            while c.stringWidth(inter_text, "Helvetica", 6) > max_w and len(inter_text) > 5:
                inter_text = inter_text[:-1]
            if inter_text != f"↳ {name}{ele_str}":
                inter_text = inter_text[:-1] + '.'
            c.drawString(MARGIN + indent, y, inter_text)
            c.drawRightString(PAGE_W - MARGIN, y, km_str)
            y -= 4 * mm

            # Séparateur pointillé léger
            c.setStrokeColorRGB(0.88, 0.88, 0.88)
            c.setLineWidth(0.2)
            c.setDash(2, 3)
            c.line(MARGIN + indent, y, PAGE_W - MARGIN, y)
            c.setDash()
            y -= 3 * mm

        else:
            color = cat_colors.get(label, (0.55, 0.55, 0.55))

            # Badge catégorie
            badge_w = 9 * mm
            badge_h = 3.5 * mm
            c.setFillColorRGB(*color)
            c.roundRect(MARGIN, y - badge_h + 0.5*mm, badge_w, badge_h, 1*mm, fill=1, stroke=0)
            c.setFillColorRGB(1, 1, 1)
            c.setFont("Helvetica-Bold", 5.5)
            badge_text = label if label else 'Col'
            c.drawCentredString(MARGIN + badge_w/2, y - badge_h + 1.6*mm, badge_text)

            # km pied → sommet (droite)
            c.setFillColorRGB(0.2, 0.2, 0.2)
            c.setFont("Helvetica-Bold", 6.5)
            km_summit = col.get('km_summit')
            km_foot   = col.get('km_foot')
            if km_foot is not None and km_summit is not None:
                km_str = f"{km_foot:.1f}→{km_summit:.1f}km"
            elif km_summit is not None:
                km_str = f"{km_summit:.1f} km"
            else:
                km_str = ""
            c.drawRightString(PAGE_W - MARGIN, y - 1*mm, km_str)

            y -= 5 * mm

            # Nom du col + altitude
            c.setFillColorRGB(0.05, 0.05, 0.05)
            c.setFont("Helvetica-Bold", 7)
            ele_tag = col['tags'].get('ele', '')
            ele_str = f" ({ele_tag}m)" if ele_tag else ''
            name = col['name'] + ele_str
            while c.stringWidth(name, "Helvetica-Bold", 7) > PAGE_W - 2*MARGIN and len(name) > 4:
                name = name[:-1]
            if name != col['name'] + ele_str:
                name = name[:-1] + '.'
            c.drawString(MARGIN, y, name)
            y -= 4 * mm

            # Détails: longueur / d+ / pente
            c.setFillColorRGB(0.45, 0.45, 0.45)
            c.setFont("Helvetica", 5.5)
            dist_km  = col.get('col_dist')
            denivele = col.get('col_denivele')
            pente    = col.get('col_pente')
            score    = col.get('col_score')
            if dist_km is not None and denivele is not None and pente is not None:
                details = f"{dist_km} km  |  +{denivele} m  |  {pente}%"
                if score:
                    details += f"  |  score: {score}"
                c.drawString(MARGIN, y, details)
            y -= 2.5 * mm

            # Séparateur fin
            c.setStrokeColorRGB(0.88, 0.88, 0.88)
            c.setLineWidth(0.3)
            c.line(MARGIN, y, PAGE_W - MARGIN, y)
            y -= 3.5 * mm

        # Débordement : nouvelle page si nécessaire
        if y < MARGIN + 15 * mm:
            c.showPage()
            y = PAGE_H - MARGIN

    c.save()
    print(f"  PDF roadbook: {out_path}")


# ─── Détection automatique des sommets sur le tracé ─────────────────────────

def _km_window(cum_km, center, half_km):
    """
    Indices (lo, hi) du tracé couvrant une fenêtre de ±half_km autour du point
    `center`. Permet des fenêtres exprimées en distance (km) plutôt qu'en
    nombre de points : la détection devient indépendante de la densité GPS.
    """
    n = len(cum_km)
    lo = center
    while lo > 0 and cum_km[center] - cum_km[lo] < half_km:
        lo -= 1
    hi = center
    while hi < n - 1 and cum_km[hi] - cum_km[center] < half_km:
        hi += 1
    return lo, hi


def detect_track_peaks(track_pts_ele, cum_km):
    """
    Détecte les sommets significatifs sur le profil altimétrique du tracé.
    Retourne une liste de POIs synthétiques au format col.

    Un point est retenu comme sommet si :
      1. (optionnel) son altitude dépasse PEAK_MIN_ELEVATION ;
      2. c'est le point le plus haut dans un rayon de ±PEAK_ISOLATION_KM ;
      3. sa proéminence (hauteur au-dessus du creux le plus haut de part et
         d'autre, mesurée sur ±PEAK_PROM_SEARCH_KM) atteint PEAK_MIN_PROMINENCE.

    Contrairement à la version précédente, la détection ne dépend plus d'un
    plancher d'altitude codé en dur : elle fonctionne donc aussi bien dans les
    Ardennes (côtes culminant sous 500 m) qu'en haute montagne. La catégorie
    (HC/1/2/3/4) reste ensuite déterminée par classify_col.
    """
    eles = [p[2] for p in track_pts_ele]
    n = len(eles)
    if n < 5:
        return []

    sm = smooth_eles(eles, PEAK_SMOOTH_WINDOW)

    peaks = []
    seen_km = []
    for i in range(1, n - 1):
        # 1. Plancher d'altitude absolu (optionnel — None = désactivé)
        if PEAK_MIN_ELEVATION is not None and sm[i] < PEAK_MIN_ELEVATION:
            continue

        # 2. Doit être le point le plus haut dans ±PEAK_ISOLATION_KM
        lo, hi = _km_window(cum_km, i, PEAK_ISOLATION_KM)
        if sm[i] < max(sm[lo:hi + 1]) - 1e-6:
            continue

        # 3. Proéminence : descente requise de part et d'autre du sommet
        plo, phi = _km_window(cum_km, i, PEAK_PROM_SEARCH_KM)
        left_min  = min(sm[plo:i + 1])
        right_min = min(sm[i:phi + 1])
        prominence = sm[i] - max(left_min, right_min)
        if prominence < PEAK_MIN_PROMINENCE:
            continue

        # Dédoublonnage : ignorer si un sommet déjà retenu est trop proche
        km = cum_km[i]
        if any(abs(km - k) < PEAK_ISOLATION_KM for k in seen_km):
            continue
        seen_km.append(km)

        lat, lon, ele = track_pts_ele[i]
        peaks.append({
            'lat': lat, 'lon': lon, 'cat': 'col',
            'name': f'Sommet ({ele:.0f}m)',
            'dist': 0,
            'tags': {'ele': str(round(ele)), 'source': 'gpx_peak'},
            'col_cat': None, 'col_denivele': None, 'col_dist': None,
            'col_pente': None, 'col_score': None,
            'foot_lat': None, 'foot_lon': None,
            '_s_idx': i,
        })
    return peaks


# ─── Recherche de nom pour les sommets sans nom ──────────────────────────────

def _has_climb_keyword(name):
    """Vrai si le nom contient déjà un mot-clé de côte (Côte, Mur, Thier...)."""
    low = ' ' + name.lower() + ' '
    return any(k in low for k in CLIMB_KEYWORDS)


def _point_seg_dist(plat, plon, alat, alon, blat, blon):
    """Distance (m) d'un point au segment [A,B] (projection locale plane)."""
    latref = math.radians((alat + blat) / 2)
    sx = 111320.0 * math.cos(latref)
    sy = 110540.0
    px, py = plon * sx, plat * sy
    ax, ay = alon * sx, alat * sy
    bx, by = blon * sx, blat * sy
    dx, dy = bx - ax, by - ay
    seg2 = dx * dx + dy * dy
    if seg2 == 0:
        return math.hypot(px - ax, py - ay)
    t = max(0.0, min(1.0, ((px - ax) * dx + (py - ay) * dy) / seg2))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


def _polyline_dist(lat, lon, geom):
    """Distance (m) minimale d'un point à une polyligne [(lat,lon), ...]."""
    if not geom:
        return float('inf')
    if len(geom) == 1:
        return haversine(lat, lon, geom[0][0], geom[0][1])
    return min(_point_seg_dist(lat, lon, geom[i][0], geom[i][1],
                               geom[i + 1][0], geom[i + 1][1])
               for i in range(len(geom) - 1))


def _lower_leading_article(name):
    """Met l'article de tête en minuscule : « La Redoute » -> « la Redoute »."""
    low = name.lower()
    for art in ('les ', 'la ', 'le '):
        if low.startswith(art):
            return art + name[len(art):]
    if low.startswith("l'") or low.startswith('l’'):
        return name[:2].lower() + name[2:]
    return name


def place_to_cote_name(name):
    """
    Transforme le nom d'un hameau/village en nom de côte.
      « Niaster »              -> « Côte de Niaster »
      « La Roche aux Faucons » -> « Côte de la Roche aux Faucons »
      « Aywaille »             -> « Côte d'Aywaille »  (élision devant voyelle)
    Si le nom contient déjà un mot-clé de côte, il est repris tel quel.
    """
    n = name.strip()
    if _has_climb_keyword(n):
        return n
    low = n.lower()
    if low.startswith(('la ', 'le ', 'les ')) or low.startswith(("l'", 'l’')):
        return 'Côte de ' + _lower_leading_article(n)
    if low[:1] in 'aàâeéèêiîïoôuûyh':   # élision : « Côte d'Aywaille »
        return "Côte d'" + n
    return 'Côte de ' + n


def road_to_cote_name(name):
    """
    Transforme un nom de rue en nom de côte, ou None si non exploitable.

      « Rue de la Redoute »            -> « Côte de la Redoute »
      « Chemin de la Roche aux Faucons » -> « Côte de la Roche aux Faucons »
      « Thier de Coo »                 -> « Thier de Coo »  (déjà un nom de côte)
      « Rue Toussaint Gerkens »        -> None  (rue sans connecteur :
                                                 nom de personne, pas de lieu)
      « Rue du Calvaire »              -> None  (lieu générique)

    Principe : une rue nommée d'après un LIEU s'écrit « Rue DE [LA/L'/DU...] X »
    (avec connecteur), tandis qu'une rue nommée d'après une personne s'écrit
    « Rue X » (sans connecteur). On n'exploite que la première forme, ce qui
    évite de baptiser une côte du nom d'un échevin local.
    """
    if not name:
        return None
    n = name.strip()
    if _has_climb_keyword(n):
        return n  # la rue est déjà nommée « Côte/Thier/Mur... »
    parts = n.split(None, 1)
    if len(parts) < 2:
        return None
    first = parts[0].lower().strip("'’-")
    rest = parts[1].strip()
    if first not in ROAD_TYPE_PREFIXES:
        return None
    rl = rest.lower()
    for conn in ('de la ', "de l'", 'de l’', 'du ', 'des ', "d'", 'd’', 'de '):
        if rl.startswith(conn):
            tail = rest.lower().replace("'", ' ').replace('’', ' ').split()
            if tail and tail[-1] in GENERIC_NAME_TOKENS:
                return None
            return 'Côte ' + rest
    return None  # rue sans connecteur -> nom de personne, on ne devine pas


# Rang de préférence des types de lieu (un village prime un simple lieu-dit).
PLACE_RANK = {'village': 0, 'hamlet': 1, 'isolated_dwelling': 2, 'locality': 3}


def _climb_approach(track_pts, cum_km, summit_idx, back_km=None):
    """
    Renvoie les points de tracé des derniers `back_km` kilomètres avant le
    sommet (la montée elle-même). Sert à chercher un nom le long de la côte,
    et non au seul point du sommet — c'est ce qui permet de retrouver la route
    gravie pendant toute l'ascension même si la crête porte un autre nom.
    """
    if back_km is None:
        back_km = NAMING_APPROACH_KM
    target = cum_km[summit_idx] - back_km
    i = summit_idx
    while i > 0 and cum_km[i] > target:
        i -= 1
    return track_pts[i:summit_idx + 1] or [track_pts[summit_idx]]


def _pick_col_name(climb_pts, elements, max_dist):
    """
    Choisit le meilleur nom pour une côte parmi des éléments OSM, en suivant
    strictement la convention demandée (priorité par catégorie, pas par
    distance brute) :

      1. un col / sommet / point de vue NOMMÉ près du sommet (nœud OSM
         mountain_pass, saddle, peak, hill ou viewpoint) ;
      2. à défaut, le hameau ou village le plus proche de la MONTÉE
         -> « Côte de <lieu> » ;
      3. à défaut, la route effectivement gravie : celle dont la géométrie
         recouvre la plus grande part de la montée -> « Côte de <rue> ».

    `climb_pts` est la liste ordonnée des points (lat, lon) de la montée, le
    dernier étant le sommet. Une route n'est retenue (étape 3) que si elle
    « couvre » réellement la montée : une rue de crête seulement effleurée ne
    peut donc plus l'emporter sur la route gravie pendant des kilomètres.
    Séparé de la requête réseau pour pouvoir être testé hors-ligne.
    """
    if not climb_pts:
        return None
    slat, slon = climb_pts[-1]
    # Moitié supérieure de la montée : une côte est nommée d'après son sommet.
    upper = climb_pts[len(climb_pts) // 2:] or climb_pts

    cols, places, roads = [], [], []

    for el in elements:
        tags = el.get('tags', {})
        name = tags.get('name') or tags.get('name:fr')
        if not name:
            continue
        etype = el.get('type')

        if etype == 'node' and 'lat' in el:
            nlat, nlon = el['lat'], el['lon']
            d_summit = haversine(nlat, nlon, slat, slon)
            d_climb = min(haversine(nlat, nlon, p[0], p[1]) for p in climb_pts)
            if (tags.get('mountain_pass') == 'yes'
                    or tags.get('natural') in ('saddle', 'peak', 'hill')
                    or tags.get('tourism') == 'viewpoint'):
                if d_summit <= max_dist:
                    cols.append((d_summit, name))
            elif tags.get('place') in PLACE_RANK:
                if d_climb <= max_dist:
                    places.append((PLACE_RANK[tags['place']], d_climb, name))

        elif etype == 'way' and tags.get('highway') and el.get('geometry'):
            geom = [(g['lat'], g['lon']) for g in el['geometry']]
            near = sum(1 for p in upper
                       if _polyline_dist(p[0], p[1], geom) <= ROAD_COVER_M)
            coverage = near / len(upper)
            if coverage >= ROAD_MIN_COVERAGE:
                roads.append((coverage, name))

    # 1. Col / sommet / point de vue nommé : le plus proche du sommet
    if cols:
        cols.sort(key=lambda x: x[0])
        return cols[0][1]

    # 2. Hameau / village : type le plus « habité » d'abord, puis proximité
    if places:
        places.sort(key=lambda x: (x[0], x[1]))
        return place_to_cote_name(places[0][2])

    # 3. Route gravie : la mieux « couverte » par la montée
    if roads:
        roads.sort(key=lambda x: -x[0])
        for _cov, road_name in roads:
            cote = road_to_cote_name(road_name)
            if cote:
                return cote

    return None


def lookup_col_name(climb_pts, max_dist=MAX_DIST_COL_NAME):
    """
    Cherche dans OSM un nom pour une côte, à partir des points de la montée.

    `climb_pts` est la liste (lat, lon) de la montée (dernier point = sommet).
    Pour un simple point, passer [(lat, lon)]. Interroge les cols/sommets/
    points de vue nommés, les hameaux et villages, et les routes nommées sur la
    boîte englobant toute la montée, puis applique _pick_col_name.
    Renvoie None si rien d'exploitable n'est trouvé.
    """
    if not climb_pts:
        return None
    buf = max_dist / 111000  # degrés approximatifs
    lats = [p[0] for p in climb_pts]
    lons = [p[1] for p in climb_pts]
    b = (f"{min(lats)-buf:.5f},{min(lons)-buf:.5f},"
         f"{max(lats)+buf:.5f},{max(lons)+buf:.5f}")
    query = (
        f"[out:json][timeout:25];\n(\n"
        f'  node["mountain_pass"="yes"]["name"]({b});\n'
        f'  node["natural"~"^(peak|saddle|hill)$"]["name"]({b});\n'
        f'  node["tourism"="viewpoint"]["name"]({b});\n'
        f'  node["place"~"^(village|hamlet|isolated_dwelling|locality)$"]["name"]({b});\n'
        f'  way["highway"]["name"]({b});\n'
        f");\nout tags geom;"
    )
    mirrors = [
        "https://overpass-api.de/api/interpreter",
        "https://overpass.kumi.systems/api/interpreter",
        "https://maps.mail.ru/osm/tools/overpass/api/interpreter",
    ]
    headers = {
        "User-Agent": "GPX-POI-Enricher/1.0",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept": "application/json",
    }
    for url in mirrors:
        try:
            resp = requests.post(url, data={"data": query}, headers=headers, timeout=25)
            resp.raise_for_status()
            return _pick_col_name(climb_pts, resp.json().get("elements", []), max_dist)
        except Exception:
            continue
    return None


# ─── Noms manuels ────────────────────────────────────────────────────────────

def load_manual_names(csv_path=None):
    """
    Charge un CSV optionnel de noms manuels pour les cols (prioritaire sur OSM).

    Deux formats de ligne sont acceptés (sans entête, séparateur virgule) :

      • par coordonnées :        lat,lon,Nom
            47.9763118,6.7561008,Col de la Burotte

      • par point kilométrique : km,VALEUR,Nom
            km,89.6,Côte de la Redoute

    Le format « km » est le plus simple à renseigner : lancez le script une
    fois, relevez le kilométrage affiché pour chaque « Sommet (...) » non nommé,
    puis ajoutez une ligne par côte. Il est ainsi trivial de corriger un nom
    qu'OSM ne fournit pas (surnoms type « Mur de Durbuy »).

    Renvoie un dict {'coord': [(lat, lon, nom)], 'km': [(km, nom)]}.
    """
    import csv
    path = csv_path or MANUAL_NAMES_FILE
    result = {'coord': [], 'km': []}
    if not os.path.isfile(path):
        return result
    try:
        with open(path, newline='', encoding='utf-8') as f:
            for row in csv.reader(f):
                if len(row) < 3:
                    continue
                try:
                    if row[0].strip().lower() == 'km':
                        result['km'].append((float(row[1].strip()),
                                             row[2].strip()))
                    else:
                        result['coord'].append((float(row[0].strip()),
                                                float(row[1].strip()),
                                                row[2].strip()))
                except ValueError:
                    continue  # ligne malformée ou entête -> ignorée
        total = len(result['coord']) + len(result['km'])
        print(f"  {total} nom(s) manuel(s) chargé(s) depuis {path}")
    except Exception as e:
        print(f"  Avertissement noms manuels: {e}")
    return result


def find_manual_name(lat, lon, manual_names, km=None,
                     max_dist=MAX_DIST_COL_NAME, max_km=0.6):
    """
    Nom manuel correspondant à un col, ou None.

    Cherche d'abord par point kilométrique (si `km` est fourni et qu'une entrée
    « km » du CSV se trouve à moins de `max_km` km), puis par coordonnées
    géographiques. `manual_names` est le dict renvoyé par load_manual_names()
    (les anciennes listes de tuples restent acceptées par rétro-compatibilité).
    """
    if isinstance(manual_names, list):  # ancien format : liste (lat,lon,nom)
        manual_names = {'coord': manual_names, 'km': []}

    if km is not None and manual_names.get('km'):
        best_name, best = None, max_km
        for mkm, mname in manual_names['km']:
            if abs(mkm - km) < best:
                best, best_name = abs(mkm - km), mname
        if best_name:
            return best_name

    best_name, best = None, max_dist
    for mlat, mlon, mname in manual_names.get('coord', []):
        d = haversine(lat, lon, mlat, mlon)
        if d < best:
            best, best_name = d, mname
    return best_name


# ─── Sprints intermédiaires ──────────────────────────────────────────────────

def load_sprints_csv(path):
    """
    Charge un CSV optionnel de sprints intermédiaires.

    Format d'une ligne (sans entête, séparateur virgule) :  nom,km
        Sprint de Gérardmer,34.2

    `km` est la distance depuis le départ ; le sprint est positionné sur le
    point du tracé correspondant. Renvoie [(nom, km), ...] ; liste vide si le
    fichier est absent.
    """
    import csv
    sprints = []
    if not path or not os.path.isfile(path):
        return sprints
    try:
        with open(path, newline='', encoding='utf-8') as f:
            for row in csv.reader(f):
                if len(row) < 2:
                    continue
                try:
                    sprints.append((row[0].strip(), float(row[1].strip())))
                except ValueError:
                    continue  # entête ou ligne malformée -> ignorée
        if sprints:
            print(f"  {len(sprints)} sprint(s) chargé(s) depuis {path}")
    except Exception as e:
        print(f"  Avertissement sprints CSV: {e}")
    return sprints


def extract_gpx_sprints(root):
    """
    Repère les waypoints de sprint déjà présents dans le GPX source (symbole
    19), les retire du document — ils seront réinjectés au format homogène —
    et renvoie leurs données : [{'lat', 'lon', 'name'}].
    """
    ns = {'gpx': 'http://www.topografix.com/GPX/1/1'}
    found = []
    for wpt in list(root.findall('gpx:wpt', ns)):
        sym = (wpt.findtext('gpx:sym', '', ns) or '').strip()
        if sym != '19':
            continue
        name = (wpt.findtext('gpx:name', '', ns) or '').strip()
        found.append({'lat': float(wpt.get('lat')),
                       'lon': float(wpt.get('lon')),
                       'name': name or 'Sprint'})
        root.remove(wpt)
    return found


def point_at_km(km, track_pts, cum_dists):
    """Coordonnées (lat, lon) du point du tracé situé à `km` du départ."""
    if not cum_dists:
        return None
    km = max(0.0, min(km, cum_dists[-1]))
    idx = min(range(len(cum_dists)), key=lambda i: abs(cum_dists[i] - km))
    return track_pts[idx]


def build_sprint_pois(gpx_sprints, csv_sprints, track_pts, cum_dists):
    """
    Construit les POIs « sprint » à partir des deux sources :
      - gpx_sprints : sprints déjà présents dans le GPX source (positionnés) ;
      - csv_sprints : sprints du CSV (nom, km), positionnés sur le tracé.
    Un sprint du CSV à moins de 200 m d'un sprint du GPX est ignoré (doublon).
    """
    pois = []

    def _add(lat, lon, name):
        pois.append({
            'lat': lat, 'lon': lon, 'cat': 'sprint',
            'name': name or 'Sprint', 'desc': '',
            'dist': min_dist_to_track(lat, lon, track_pts, step=5),
            'tags': {}, 'col_cat': None, 'col_denivele': None,
            'col_dist': None, 'col_pente': None, 'col_score': None,
            'foot_lat': None, 'foot_lon': None,
        })

    for s in gpx_sprints:
        _add(s['lat'], s['lon'], s['name'])
    for name, km in csv_sprints:
        pt = point_at_km(km, track_pts, cum_dists)
        if pt is None:
            continue
        if any(haversine(pt[0], pt[1], p['lat'], p['lon']) < 200 for p in pois):
            continue  # doublon avec un sprint déjà présent dans le GPX
        _add(pt[0], pt[1], name)
    return pois


# ─── PDF impression A4 paysage (8 roadbooks côte à côte) ────────────────────

def generate_roadbook_print_sheet(single_pdf_path, out_path):
    """
    Génère une version A4 paysage contenant 8 exemplaires du roadbook
    côte à côte avec lignes de coupe. Pure Python, sans dépendance système.
    Utilise pypdf pour placer le PDF directement (pas de rasterisation).
    """
    from reportlab.lib.pagesizes import landscape, A4
    from reportlab.lib.units import mm, cm
    from reportlab.pdfgen import canvas as rl_canvas

    try:
        from pypdf import PdfReader, PdfWriter, Transformation
    except ImportError:
        print("  ⚠️  pypdf non disponible — installer avec: pip install pypdf")
        return

    PAGE_W, PAGE_H = landscape(A4)
    RB_W = 3.6 * cm   # 3.6cm × 8 = 28.8cm, marge ~4.5mm chaque côté
    RB_H = 20 * cm
    N_COLS = 8
    N_ROWS = 1
    CUT_EXTRA = 3 * mm

    total_w = N_COLS * RB_W
    total_h = N_ROWS * RB_H
    margin_x = (PAGE_W - total_w) / 2
    margin_y = (PAGE_H - total_h) / 2

    reader = PdfReader(single_pdf_path)
    writer = PdfWriter()

    for page_idx in range(len(reader.pages)):
        src_page = reader.pages[page_idx]
        src_w = float(src_page.mediabox.width)
        src_h = float(src_page.mediabox.height)
        sx = RB_W / src_w
        sy = RB_H / src_h

        # Créer la page de base A4 paysage avec les lignes de coupe via ReportLab
        rl_buf = io.BytesIO()
        c = rl_canvas.Canvas(rl_buf, pagesize=landscape(A4))

        # Lignes de coupe pointillées
        c.setStrokeColorRGB(0.5, 0.5, 0.5)
        c.setLineWidth(0.3)
        c.setDash(2, 3)
        for col in range(N_COLS + 1):
            x = margin_x + col * RB_W
            c.line(x, margin_y - CUT_EXTRA, x, margin_y + total_h + CUT_EXTRA)
        for row in range(N_ROWS + 1):
            y = PAGE_H - margin_y - row * RB_H
            c.line(margin_x - CUT_EXTRA, y, margin_x + total_w + CUT_EXTRA, y)

        # Croix de repérage aux intersections
        c.setDash()
        c.setLineWidth(0.5)
        cross = 2 * mm
        for col in range(N_COLS + 1):
            for row in range(N_ROWS + 1):
                x = margin_x + col * RB_W
                y = PAGE_H - margin_y - row * RB_H
                c.line(x - cross, y, x + cross, y)
                c.line(x, y - cross, x, y + cross)
        c.save()
        rl_buf.seek(0)

        # Lire la page de base et y fusionner 8 copies du roadbook
        base_page = PdfReader(rl_buf).pages[0]
        for col in range(N_COLS):
            x0 = margin_x + col * RB_W
            y0 = margin_y
            t = Transformation().scale(sx, sy).translate(x0 / sx, y0 / sy)
            base_page.merge_transformed_page(src_page, t, over=False)

        writer.add_page(base_page)

    with open(out_path, 'wb') as f:
        writer.write(f)
    print(f"  PDF impression A4: {out_path}")

# ─── Traitement principal ────────────────────────────────────────────────────

def process_gpx(filepath, logo_path=None, title=None, sprints_csv=None):
    print(f"\n{'='*60}")
    print(f"Fichier: {filepath}")

    track_pts, track_pts_ele, tree, root, existing_names = parse_gpx(filepath)
    manual_names = load_manual_names()
    if not track_pts:
        print("  Aucun point trouvé, fichier ignoré.")
        return
    # Sprints déjà présents dans le GPX source (symbole 19) : retirés ici,
    # ils seront réinjectés au format homogène avec ceux du CSV.
    gpx_sprints = extract_gpx_sprints(root)

    lats = [p[0] for p in track_pts]
    lons = [p[1] for p in track_pts]
    bbox = (min(lats), min(lons), max(lats), max(lons))
    print(f"  {len(track_pts)} points | bbox {tuple(f'{x:.3f}' for x in bbox)}")

    try:
        data = query_overpass(bbox)
    except Exception as e:
        print(f"  Erreur Overpass: {e}")
        return

    max_dists = {'water': MAX_DIST_WATER, 'food': MAX_DIST_FOOD, 'shop': MAX_DIST_SHOP, 'col': MAX_DIST_COL}
    pois = []
    skipped = {'private': 0, 'far': 0, 'uncategorized': 0}

    for el in data.get('elements', []):
        lat, lon = el.get('lat'), el.get('lon')
        if lat is None:
            continue
        tags = el.get('tags', {})
        if tags.get('access') == 'private':
            skipped['private'] += 1
            continue
        cat = categorize(el)
        if cat is None:
            skipped['uncategorized'] += 1
            continue
        step = 1 if cat == 'col' else 10
        dist = min_dist_to_track(lat, lon, track_pts, step=step)
        if dist > max_dists[cat]:
            skipped['far'] += 1
            continue
        osm_name = get_name(tags, cat)
        if osm_name in ('Col', 'Eau potable', 'Restaurant', 'Épicerie'):
            # Nom générique : chercher d'abord dans les waypoints existants du GPX
            key = (round(lat, 4), round(lon, 4))
            osm_name = existing_names.get(key, osm_name)
        # Si toujours générique et c'est un col, chercher dans les noms manuels puis OSM
        if osm_name == 'Col' and cat == 'col':
            manual = find_manual_name(lat, lon, manual_names)
            if manual:
                osm_name = manual
            else:
                nearby_name = lookup_col_name([(lat, lon)], MAX_DIST_COL_NAME)
                if nearby_name:
                    osm_name = nearby_name
        poi = {'lat': lat, 'lon': lon, 'cat': cat,
                'name': osm_name, 'dist': dist, 'tags': tags,
                'col_cat': None, 'col_denivele': None, 'col_dist': None, 'col_pente': None, 'col_score': None,
                'foot_lat': None, 'foot_lon': None}
        pois.append(poi)

    # Calculer les stats des cols dans l'ordre d'apparition sur le tracé
    # Le pied de chaque col ne peut pas remonter avant le sommet du précédent
    col_pois_unsorted = [p for p in pois if p['cat'] == 'col']

    # Ajouter les sommets détectés sur le tracé (non couverts par OSM)
    if track_pts_ele:
        cum_km_list = compute_cumulative_distances(track_pts)
        gpx_peaks = detect_track_peaks(track_pts_ele, cum_km_list)
        for peak in gpx_peaks:
            peak_km = cum_km_list[peak['_s_idx']]
            # Points de la montée vers ce sommet (pour chercher un nom le long
            # de la côte, pas seulement au point culminant).
            approach = _climb_approach(track_pts, cum_km_list, peak['_s_idx'])
            # Chercher le POI OSM le plus proche dans les 500m
            covering_poi = None
            best_cover_dist = 500
            for p in col_pois_unsorted:
                d = haversine(peak['lat'], peak['lon'], p['lat'], p['lon'])
                if d < best_cover_dist:
                    best_cover_dist = d
                    covering_poi = p

            if covering_poi is not None:
                # Pic couvert par un POI OSM : ignorer le pic GPX,
                # mais s'assurer que le POI OSM a un bon nom
                if covering_poi['name'] in ('Col', 'Sommet'):
                    manual = find_manual_name(covering_poi['lat'], covering_poi['lon'],
                                              manual_names, km=peak_km)
                    if manual:
                        covering_poi['name'] = manual
                    else:
                        nearby = lookup_col_name(approach, MAX_DIST_COL_NAME)
                        if nearby:
                            covering_poi['name'] = nearby
            else:
                # Pic GPX non couvert : chercher un nom et l'ajouter
                osm_name = find_manual_name(peak['lat'], peak['lon'],
                                            manual_names, km=peak_km)
                if not osm_name:
                    osm_name = lookup_col_name(approach, MAX_DIST_COL_NAME)
                if osm_name:
                    peak['name'] = osm_name
                    peak['tags']['name'] = osm_name
                pois.append(peak)
                col_pois_unsorted.append(peak)
                print(f"  Sommet GPX détecté: {peak['name']} @ {peak_km:.1f}km")

    if col_pois_unsorted and track_pts_ele:
        # Assigner _s_idx à tous
        for p in col_pois_unsorted:
            if '_s_idx' not in p:
                p['_s_idx'] = min(range(len(track_pts_ele)),
                    key=lambda i: haversine(p['lat'], p['lon'], track_pts_ele[i][0], track_pts_ele[i][1]))

        # Séparer cols OSM et pics GPX — traiter les OSM en premier
        # pour que leur start_limit_idx ne soit pas pollué par les pics GPX
        osm_cols  = [p for p in col_pois_unsorted if p.get('tags', {}).get('source') != 'gpx_peak']
        gpx_peaks_cl = [p for p in col_pois_unsorted if p.get('tags', {}).get('source') == 'gpx_peak']

        osm_cols.sort(key=lambda p: p['_s_idx'])
        prev_summit_idx = 0
        for p in osm_cols:
            ele = track_pts_ele[p['_s_idx']][2]
            col_cat, denivele, col_dist_km, pente, score, foot_lat, foot_lon = \
                classify_col(p['lat'], p['lon'], ele, track_pts_ele,
                             start_limit_idx=prev_summit_idx)
            if col_dist_km is None:
                p['cat'] = 'col_invalid'
            else:
                p.update({'col_cat': col_cat, 'col_denivele': denivele,
                          'col_dist': col_dist_km, 'col_pente': pente, 'col_score': score,
                          'foot_lat': foot_lat, 'foot_lon': foot_lon})
            prev_summit_idx = p['_s_idx']

        # Traiter les pics GPX : leur start_limit_idx est le dernier col OSM valide avant eux
        for p in gpx_peaks_cl:
            prev_osm_idx = 0
            for osm in osm_cols:
                if osm['_s_idx'] < p['_s_idx'] and osm.get('cat') != 'col_invalid':
                    prev_osm_idx = osm['_s_idx']
            ele = track_pts_ele[p['_s_idx']][2]
            col_cat, denivele, col_dist_km, pente, score, foot_lat, foot_lon = \
                classify_col(p['lat'], p['lon'], ele, track_pts_ele,
                             start_limit_idx=prev_osm_idx)
            if col_dist_km is None:
                p['cat'] = 'col_invalid'
            else:
                p.update({'col_cat': col_cat, 'col_denivele': denivele,
                          'col_dist': col_dist_km, 'col_pente': pente, 'col_score': score,
                          'foot_lat': foot_lat, 'foot_lon': foot_lon})

    # ─── Sprints : repris du GPX source (symbole 19) + ajoutés depuis le CSV ─
    cum_dists_full = compute_cumulative_distances(track_pts)
    csv_sprints = load_sprints_csv(sprints_csv or SPRINTS_FILE)
    sprint_pois = build_sprint_pois(gpx_sprints, csv_sprints, track_pts, cum_dists_full)
    pois.extend(sprint_pois)
    for sp in sprint_pois:
        skm = find_km_at_point(sp['lat'], sp['lon'], track_pts, cum_dists_full)
        print(f"  Sprint: {sp['name']} @ {skm:.1f}km")

    # ─── Repère « Meilleur Grimpeur » au pied de chaque ascension classée ────
    # (point de départ pris en compte pour la durée d'ascension du col)
    foot_pois = []
    for p in pois:
        if p['cat'] == 'col' and p.get('foot_lat') is not None:
            foot_pois.append({
                'lat': p['foot_lat'], 'lon': p['foot_lon'], 'cat': 'climb_foot',
                'name': 'Meilleur Grimpeur', 'desc': '', 'dist': 0.0, 'tags': {},
                'col_cat': None, 'col_denivele': None, 'col_dist': None,
                'col_pente': None, 'col_score': None,
                'foot_lat': None, 'foot_lon': None,
            })
    pois.extend(foot_pois)

    counts = {c: sum(1 for p in pois if p['cat'] == c)
              for c in ('water', 'food', 'shop', 'col', 'sprint')}  # col_invalid not counted
    print(f"  POIs retenus: {len(pois)} total "
          f"(eau: {counts['water']}, resto: {counts['food']}, épicerie: {counts['shop']}, "
          f"cols: {counts['col']}, sprints: {counts['sprint']})")
    for p in [x for x in pois if x['cat'] == 'col']:
        if p.get('col_cat'):
            label = 'HC' if p['col_cat'] == 'HC' else f"Cat. {p['col_cat']}"
            print(f"    {label} — {p['name']} ({p['tags'].get('ele','?')}m) "
                  f"{p.get('col_dist','?')}km / {p.get('col_denivele','?')}m / {p.get('col_pente','?')}%")
        else:
            print(f"    (non catégorisé) — {p['name']} ({p['tags'].get('ele','?')}m)")
    print(f"  Ignorés — privé: {skipped['private']}, trop loin: {skipped['far']}")

    inject_waypoints(root, pois)

    out_path = filepath.replace('.gpx', '_enrichi.gpx')
    tree.write(out_path, encoding='utf-8', xml_declaration=True)
    print(f"  Sauvegardé: {out_path}")

    # Générer le PDF roadbook si des cols ou des sprints ont été trouvés
    col_pois = [p for p in pois if p['cat'] == 'col']  # col_invalid already excluded
    if col_pois or sprint_pois:
        pdf_path = filepath.replace('.gpx', '_roadbook.pdf')
        generate_roadbook_pdf(col_pois, track_pts, track_pts_ele, filepath, pdf_path,
                              logo_path=logo_path, title=title, sprint_pois=sprint_pois)
        print_path = filepath.replace('.gpx', '_roadbook_impression.pdf')
        generate_roadbook_print_sheet(pdf_path, print_path)
    else:
        print("  Aucun col ni sprint trouvé, pas de PDF roadbook généré.")

    return len(pois)

# ─── Point d'entrée ──────────────────────────────────────────────────────────

if __name__ == '__main__':
    import glob
    import argparse

    parser = argparse.ArgumentParser(
        prog='enrichir_gpx.py',
        description=(
            "Enrichit des fichiers GPX avec des POIs OpenStreetMap (eau potable, restaurants,\n"
            "épiceries, cols), des sprints intermédiaires et des repères de pied d'ascension,\n"
            "puis génère trois fichiers par GPX :\n"
            "  • <nom>_enrichi.gpx      — fichier GPX avec waypoints POI\n"
            "  • <nom>_roadbook.pdf     — carton 3.6×20cm à coller sur le cadre (cols + sprints)\n"
            "  • <nom>_roadbook_impression.pdf — A4 paysage, 8 roadbooks côte à côte avec lignes de coupe"
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Exemples :\n"
            "  python enrichir_gpx.py mon_trajet.gpx\n"
            "  python enrichir_gpx.py *.gpx --titre \"Étape 1 — Col Attitude\"\n"
            "  python enrichir_gpx.py tour.gpx --logo logo.png --titre \"Groupetto 2025\"\n"
            "  python enrichir_gpx.py etape.gpx --sprints sprints.csv\n"
            "  # Moyenne montagne (Ardennes) — détecter les côtes basses :\n"
            "  python enrichir_gpx.py lbl.gpx --col-prominence 40 --col-isolation 0.8\n"
            "\n"
            "Dépendances :\n"
            "  pip install requests reportlab pypdf\n"
            "\n"
            "Fichier de noms manuels (optionnel, prioritaire sur OSM) :\n"
            "  Créer noms_cols.csv dans le même dossier. Deux formats de ligne :\n"
            "    • par coordonnées :  47.9763118,6.7561008,Col de la Burotte\n"
            "    • par kilométrage :  km,89.6,Côte de la Redoute\n"
            "  Le format « km » est le plus simple : relevez le kilométrage\n"
            "  affiché pour chaque « Sommet (...) » détecté, puis ajoutez une ligne.\n"
            "\n"
            "Sprints intermédiaires (optionnel) :\n"
            "  • Les waypoints du GPX source portant le symbole 19 sont repris.\n"
            "  • Un CSV « nom,km » (option --sprints, ou sprints.csv par défaut)\n"
            "    ajoute des sprints positionnés sur le tracé.\n"
            "  Les sprints sont écrits dans le GPX (symbole 19) et figurent dans\n"
            "  le roadbook. Chaque pied d'ascension reçoit en plus un repère\n"
            "  « Meilleur Grimpeur » (symbole 17)."
        )
    )
    parser.add_argument(
        'files', nargs='*',
        help="Fichiers GPX à traiter. Si omis, traite tous les *.gpx du dossier courant."
    )
    parser.add_argument(
        '--titre', metavar='TITRE',
        help="Titre affiché en haut du roadbook PDF (défaut : nom du fichier GPX)."
    )
    parser.add_argument(
        '--logo', metavar='IMAGE',
        help="Chemin vers un logo PNG ou JPG à afficher en haut du roadbook PDF."
    )
    parser.add_argument(
        '--col-prominence', type=float, metavar='M',
        help=("Proéminence minimale (m) d'un sommet détecté sur le profil "
              f"(défaut : {PEAK_MIN_PROMINENCE:.0f}). Baisser en moyenne "
              "montagne (Ardennes : ~40), monter en haute montagne (~80-100).")
    )
    parser.add_argument(
        '--col-altitude-min', type=float, metavar='M',
        help=("Plancher d'altitude (m) sous lequel les sommets sont ignorés. "
              "Par défaut aucun : indispensable pour détecter les côtes de "
              "moyenne montagne. À fixer (p.ex. 800) en haute montagne.")
    )
    parser.add_argument(
        '--col-isolation', type=float, metavar='KM',
        help=("Distance minimale (km) entre deux sommets détectés "
              f"(défaut : {PEAK_ISOLATION_KM:.1f}). Baisser quand les côtes "
              "s'enchaînent (Ardennes), monter pour les regrouper.")
    )
    parser.add_argument(
        '--sprints', metavar='CSV',
        help=("Fichier CSV de sprints intermédiaires à ajouter (format : "
              f"nom,km). Par défaut, « {SPRINTS_FILE} » est lu s'il existe. "
              "Les sprints déjà présents dans le GPX source (symbole 19) sont "
              "de toute façon repris.")
    )
    args = parser.parse_args()

    # Surcharge éventuelle des paramètres de détection des cols par la ligne
    # de commande (sinon on garde les valeurs de la section Configuration).
    if args.col_prominence is not None:
        PEAK_MIN_PROMINENCE = args.col_prominence
    if args.col_altitude_min is not None:
        PEAK_MIN_ELEVATION = args.col_altitude_min
    if args.col_isolation is not None:
        PEAK_ISOLATION_KM = args.col_isolation

    files = args.files if args.files else glob.glob('*.gpx')
    if not files:
        parser.print_help()
        sys.exit(1)

    # Exclure les fichiers déjà enrichis
    files = [f for f in files if '_enrichi' not in f]

    logo_path = args.logo
    custom_title = args.titre if hasattr(args, "titre") else None
    if logo_path and not os.path.isfile(logo_path):
        print(f"Avertissement: logo introuvable: {logo_path}")
        logo_path = None

    print(f"Traitement de {len(files)} fichier(s) GPX...")
    if logo_path:
        print(f"Logo: {logo_path}")

    total = 0
    for i, f in enumerate(files):
        total += process_gpx(f, logo_path=logo_path, title=custom_title,
                              sprints_csv=args.sprints) or 0
        if i < len(files) - 1:
            time.sleep(1)  # pause entre requêtes Overpass

    print(f"\nTerminé ! {total} POIs ajoutés au total.")
    print("Les fichiers enrichis ont le suffixe '_enrichi.gpx'")
    print("Les roadbooks PDF ont le suffixe '_roadbook.pdf'")
