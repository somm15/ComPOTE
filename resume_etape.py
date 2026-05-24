#!/usr/bin/env python3
"""
Résumé d'étape GPX — génère un PDF A4 portrait contenant :
  • Page 1 : carte OSM du parcours + profil altimétrique global + stats
  • Page N : fiche détaillée de chaque col (profil + stats)

Usage:
  python resume_etape.py mon_trajet.gpx
  python resume_etape.py mon_trajet.gpx --titre "Étape 1 — Col Attitude"
  python resume_etape.py mon_trajet.gpx --logo logo.png

Dépendances: pip install requests matplotlib pillow reportlab
"""

import sys
import os
import math
import argparse
import io
import time
import xml.etree.ElementTree as ET

import requests
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.patches import FancyBboxPatch
import matplotlib.patheffects as pe
from PIL import Image

from reportlab.lib.pagesizes import A4
from reportlab.lib.units import mm, cm
from reportlab.pdfgen import canvas as rl_canvas
from reportlab.lib.utils import ImageReader

# ─── Configuration ───────────────────────────────────────────────────────────

OSM_TILE_URL    = "https://tile.openstreetmap.org/{z}/{x}/{y}.png"
OSM_HEADERS     = {"User-Agent": "GPX-Stage-Summary/1.0 (personal use)"}
TILE_CACHE      = {}          # cache mémoire des tuiles
MAX_TILES       = 9 * 9      # limite raisonnable

# Seuils catégories : (pente_moy%)^2 * distance(km)
def compute_cat(pente_pct, dist_km):
    """Calcule la catégorie TdF depuis la pente et la distance."""
    score = round((pente_pct ** 2) * dist_km, 1)
    if score >= 600:   return 'HC', score
    elif score >= 250: return '1',  score
    elif score >= 180: return '2',  score
    elif score >= 80:  return '3',  score
    elif score >  34:  return '4',  score
    else:              return None, score
CAT_COLORS = {
    'HC':  '#8B0000',
    '1':   '#CC3300',
    '2':   '#E07800',
    '3':   '#2255BB',
    '4':   '#339933',
    None:  '#888888',
}

PAGE_W, PAGE_H = A4   # 595 x 842 pt
MARGIN = 15 * mm

# ─── Utilitaires géographiques ───────────────────────────────────────────────

def haversine(lat1, lon1, lat2, lon2):
    R = 6371000
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    a = math.sin(math.radians(lat2-lat1)/2)**2 + \
        math.cos(phi1)*math.cos(phi2)*math.sin(math.radians(lon2-lon1)/2)**2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1-a))

def smooth(arr, w=8):
    return [sum(arr[max(0,i-w):i+w+1])/len(arr[max(0,i-w):i+w+1]) for i in range(len(arr))]

# ─── Lecture GPX ─────────────────────────────────────────────────────────────

def parse_gpx(filepath):
    tree = ET.parse(filepath)
    root = tree.getroot()
    ns = {'gpx': 'http://www.topografix.com/GPX/1/1'}
    pts = root.findall('.//gpx:trkpt', ns) or root.findall('.//gpx:rtept', ns)
    track = []
    for p in pts:
        ele_el = p.find('gpx:ele', ns)
        ele = float(ele_el.text) if ele_el is not None else None
        track.append((float(p.get('lat')), float(p.get('lon')), ele))

    # Distances cumulées en km
    cum_km = [0.0]
    for i in range(1, len(track)):
        d = haversine(track[i-1][0], track[i-1][1], track[i][0], track[i][1])
        cum_km.append(cum_km[-1] + d/1000)

    # Stats globales
    eles = [p[2] for p in track if p[2] is not None]
    d_plus  = sum(max(0, track[i][2]-track[i-1][2])
                  for i in range(1, len(track))
                  if track[i][2] and track[i-1][2])
    d_minus = sum(max(0, track[i-1][2]-track[i][2])
                  for i in range(1, len(track))
                  if track[i][2] and track[i-1][2])

    # Lire les cols depuis les waypoints enrichis
    cols = []
    for wpt in root.findall('gpx:wpt', ns):
        sym = wpt.findtext('gpx:sym', '', ns)
        if sym in ('62','63','64','65','66','105'):
            name = wpt.findtext('gpx:name', '', ns)
            desc = wpt.findtext('gpx:desc', '', ns) or ''
            lat, lon = float(wpt.get('lat')), float(wpt.get('lon'))
            # Parser la description
            col = {'name': name, 'lat': lat, 'lon': lon, 'sym': sym,
                   'ele': None, 'cat': None, 'dist_km': None,
                   'deniv': None, 'pente': None, 'score': None}
            for part in desc.split('|'):
                part = part.strip()
                if part.startswith('Alt:'):
                    try: col['ele'] = float(part.split(':')[1].strip().replace('m',''))
                    except: pass
                elif part.startswith('Categorie:'):
                    raw = part.split(':')[1].strip()
                    # Normaliser : 'Cat. 4' → '4', 'HC' → 'HC'
                    col['cat'] = raw.replace('Cat. ', '').strip()
                elif part.startswith('Score:'):
                    try: col['score'] = float(part.split(':')[1].strip())
                    except: pass
                elif part.startswith('Montee:'):
                    try:
                        vals = part.split(':')[1].strip().split('/')
                        col['dist_km'] = float(vals[0].strip().replace('km',''))
                        col['deniv']   = float(vals[1].strip().replace('m',''))
                    except: pass
                elif part.startswith('Pente moy:'):
                    try: col['pente'] = float(part.split(':')[1].strip().replace('%',''))
                    except: pass
            # Trouver le km du sommet sur le tracé
            best_i = min(range(len(track)), key=lambda i: haversine(lat, lon, track[i][0], track[i][1]))
            col['km_summit'] = round(cum_km[best_i], 1)
            col['km_foot']   = round(max(0, col['km_summit'] - (col['dist_km'] or 0)), 1)
            # Toujours recalculer cat et score depuis la formule (pente²×dist)
            # pour garantir la cohérence indépendamment de la version du script d'enrichissement
            if col['pente'] and col['dist_km']:
                cat_calc, score_calc = compute_cat(col['pente'], col['dist_km'])
                col['cat']   = cat_calc
                col['score'] = score_calc
            else:
                # Fallback : dériver cat depuis le sym
                sym_to_cat = {'62': '1', '63': '2', '64': '3', '65': '4', '66': 'HC', '105': None}
                if col['cat'] is None:
                    col['cat'] = sym_to_cat.get(col.get('sym'))
            col['s_idx']     = best_i
            cols.append(col)

    cols.sort(key=lambda c: c['km_summit'])

    stats = {
        'total_km':  round(cum_km[-1], 1),
        'd_plus':    round(d_plus),
        'd_minus':   round(d_minus),
        'alt_min':   round(min(eles)) if eles else 0,
        'alt_max':   round(max(eles)) if eles else 0,
        'n_cols':    len(cols),
    }
    return track, cum_km, cols, stats

# ─── Tuiles OSM ──────────────────────────────────────────────────────────────

def deg2tile(lat, lon, zoom):
    n = 2 ** zoom
    x = int((lon + 180) / 360 * n)
    y = int((1 - math.log(math.tan(math.radians(lat)) + 1/math.cos(math.radians(lat))) / math.pi) / 2 * n)
    return x, y

def tile2deg(x, y, zoom):
    n = 2 ** zoom
    lon = x / n * 360 - 180
    lat = math.degrees(math.atan(math.sinh(math.pi * (1 - 2*y/n))))
    return lat, lon

def fetch_tile(z, x, y):
    key = (z, x, y)
    if key in TILE_CACHE:
        return TILE_CACHE[key]
    url = OSM_TILE_URL.format(z=z, x=x, y=y)
    try:
        resp = requests.get(url, headers=OSM_HEADERS, timeout=10)
        if resp.status_code == 200:
            img = Image.open(io.BytesIO(resp.content)).convert('RGB')
            TILE_CACHE[key] = img
            time.sleep(0.05)
            return img
    except Exception:
        pass
    return None

def build_map_image(track, width_px=1200, height_px=900):
    """Assemble les tuiles OSM et dessine le tracé."""
    lats = [p[0] for p in track]
    lons = [p[1] for p in track]
    lat_min, lat_max = min(lats), max(lats)
    lon_min, lon_max = min(lons), max(lons)

    # Marge
    dlat = (lat_max - lat_min) * 0.15 or 0.005
    dlon = (lon_max - lon_min) * 0.15 or 0.005
    lat_min -= dlat; lat_max += dlat
    lon_min -= dlon; lon_max += dlon

    # Choisir le zoom
    for zoom in range(15, 7, -1):
        x0, y0 = deg2tile(lat_max, lon_min, zoom)
        x1, y1 = deg2tile(lat_min, lon_max, zoom)
        nx = x1 - x0 + 1
        ny = y1 - y0 + 1
        if nx * ny <= MAX_TILES:
            break

    # Télécharger et assembler les tuiles
    tile_size = 256
    mosaic_w = nx * tile_size
    mosaic_h = ny * tile_size
    mosaic = Image.new('RGB', (mosaic_w, mosaic_h), (240, 240, 240))

    print(f"  Téléchargement {nx*ny} tuiles OSM (zoom={zoom})...", end='', flush=True)
    for tx in range(x0, x0+nx):
        for ty in range(y0, y0+ny):
            tile = fetch_tile(zoom, tx, ty)
            if tile:
                px = (tx - x0) * tile_size
                py = (ty - y0) * tile_size
                mosaic.paste(tile, (px, py))
    print(" OK")

    # Coordonnées de la mosaïque
    top_lat, left_lon = tile2deg(x0, y0, zoom)
    bot_lat, right_lon = tile2deg(x0+nx, y0+ny, zoom)

    def geo2px(lat, lon):
        px = int((lon - left_lon) / (right_lon - left_lon) * mosaic_w)
        py = int((lat - top_lat) / (bot_lat - top_lat) * mosaic_h)
        return px, py

    # Dessiner sur matplotlib pour avoir un rendu propre
    fig, ax = plt.subplots(figsize=(width_px/100, height_px/100), dpi=100)
    ax.imshow(mosaic, extent=[0, mosaic_w, mosaic_h, 0])
    ax.set_xlim(0, mosaic_w); ax.set_ylim(mosaic_h, 0)
    ax.axis('off')

    # Tracé GPX
    pxs = [geo2px(p[0], p[1]) for p in track[::3]]
    xs  = [p[0] for p in pxs]
    ys  = [p[1] for p in pxs]
    ax.plot(xs, ys, color='#E62020', linewidth=2.5, solid_capstyle='round', zorder=3)

    # Départ / Arrivée
    sx, sy = geo2px(track[0][0], track[0][1])
    ex, ey = geo2px(track[-1][0], track[-1][1])
    ax.plot(sx, sy, 'o', color='#22AA22', ms=10, zorder=5)
    ax.plot(ex, ey, 's', color='#E62020', ms=10, zorder=5)

    fig.tight_layout(pad=0)
    buf = io.BytesIO()
    fig.savefig(buf, format='png', dpi=100, bbox_inches='tight', pad_inches=0)
    plt.close(fig)
    buf.seek(0)
    return Image.open(buf)

# ─── Profil altimétrique global ───────────────────────────────────────────────

def build_profile_image(track, cum_km, cols, width_px=1200, height_px=430):
    """Profil altimétrique avec cols marqués + badges catégorie/score."""
    eles = [p[2] if p[2] is not None else 0 for p in track]
    sm   = smooth(eles, 5)

    fig, ax = plt.subplots(figsize=(width_px/100, height_px/100), dpi=100)

    # Gradient sous le profil
    ax.fill_between(cum_km, sm, alpha=0.25, color='#4477AA', zorder=1)
    ax.plot(cum_km, sm, color='#1A4A7A', linewidth=1.8, zorder=2)

    cat_labels = {'HC':'HC', '1':'Cat.1', '2':'Cat.2', '3':'Cat.3', '4':'Cat.4'}
    ele_range  = max(sm) - min(sm) if sm else 1

    # Marquer chaque col
    for col in cols:
        km    = col['km_summit']
        ele   = col['ele'] or (track[col['s_idx']][2] if track[col['s_idx']][2] else 0)
        cat   = col.get('cat')
        score = col.get('score')
        color = CAT_COLORS.get(cat, '#888888')

        ax.axvline(x=km, color=color, linewidth=1.2, linestyle='--', alpha=0.6, zorder=3)
        ax.plot(km, ele, 'v', color=color, ms=8, zorder=4)

        # Nom tronqué
        name = col['name'].split('|')[0].strip()
        if len(name) > 20: name = name[:19] + '.'

        cat_label = cat_labels.get(cat, 'NC')

        # Badge catégorie coloré juste au-dessus du sommet
        bbox_props = dict(boxstyle='round,pad=0.3', facecolor=color,
                          edgecolor='none', alpha=0.92)
        ax.annotate(cat_label,
                    xy=(km, ele),
                    xytext=(km, ele + ele_range * 0.03),
                    textcoords='data',
                    ha='center', va='bottom',
                    fontsize=7, color='white', fontweight='bold',
                    bbox=bbox_props, zorder=7)

        # Nom du col incliné juste au-dessus du badge
        ax.annotate(name,
                    xy=(km, ele + ele_range * 0.03),
                    xytext=(km, ele + ele_range * 0.10),
                    textcoords='data',
                    ha='left', va='bottom',
                    fontsize=8.5, color=color, rotation=50,
                    fontweight='bold', zorder=6)

        # Score en petit sous le sommet
        if score:
            ax.annotate(f'{score:.0f}',
                        xy=(km, ele - ele_range * 0.03),
                        xytext=(km, ele - ele_range * 0.03),
                        textcoords='data',
                        ha='center', va='top',
                        fontsize=6, color=color, fontweight='bold',
                        zorder=5)

    ax.set_xlabel('Distance (km)', fontsize=8)
    ax.set_ylabel('Altitude (m)', fontsize=8)
    ax.tick_params(labelsize=7)
    ax.grid(axis='y', alpha=0.3, linewidth=0.5)
    ax.set_xlim(0, cum_km[-1])
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    fig.tight_layout(pad=0.5, rect=[0, 0, 1, 0.88])

    buf = io.BytesIO()
    fig.savefig(buf, format='png', dpi=100, bbox_inches='tight', pad_inches=0.1)
    plt.close(fig)
    buf.seek(0)
    return Image.open(buf)

# ─── Profil d'un col ─────────────────────────────────────────────────────────

def build_col_profile(track, cum_km, col, width_px=1100, height_px=400):
    """Profil altimétrique détaillé d'un col avec gradient de pente."""
    s_idx   = col['s_idx']
    dist_km = col.get('dist_km') or 5.0
    km_foot = col.get('km_foot', 0)

    # Trouver l'idx du pied
    foot_idx = min(range(len(cum_km)), key=lambda i: abs(cum_km[i] - km_foot))
    # Ajouter un peu de contexte avant et après
    ctx_before = max(0, foot_idx - 20)
    ctx_after  = min(len(track)-1, s_idx + 30)

    seg_km  = [cum_km[i] for i in range(ctx_before, ctx_after+1)]
    seg_ele = [track[i][2] or 0 for i in range(ctx_before, ctx_after+1)]
    seg_sm  = smooth(seg_ele, 5)

    # Indices relatifs pied/sommet dans le segment
    rel_foot   = foot_idx - ctx_before
    rel_summit = s_idx    - ctx_before

    # Calculer pente par km sur le segment montée
    climb_km  = seg_km[rel_foot:rel_summit+1]
    climb_ele = seg_sm[rel_foot:rel_summit+1]

    # Couleur par pente (gradient vert → orange → rouge)
    def slope_color(pct):
        if pct < 5:   return '#44BB44'
        elif pct < 8: return '#E07800'
        elif pct < 12:return '#CC3300'
        else:         return '#880000'

    fig, ax = plt.subplots(figsize=(width_px/100, height_px/100), dpi=100)

    # Tracé général (contexte) en gris clair
    ax.fill_between(seg_km, seg_sm, alpha=0.15, color='#888888')
    ax.plot(seg_km, seg_sm, color='#AAAAAA', linewidth=1.2, zorder=1)

    # Segment montée avec gradient de couleur par tronçon de 500m
    if len(climb_km) > 2:
        step = max(1, len(climb_km)//20)
        for i in range(0, len(climb_km)-step, step):
            x0, x1 = climb_km[i], climb_km[min(i+step, len(climb_km)-1)]
            y0, y1 = climb_ele[i], climb_ele[min(i+step, len(climb_ele)-1)]
            dist_m = (x1 - x0) * 1000
            pct    = (y1 - y0) / dist_m * 100 if dist_m > 0 else 0
            color  = slope_color(pct)
            ax.fill_between([x0, x1], [y0, y1], alpha=0.5, color=color, zorder=2)
            ax.plot([x0, x1], [y0, y1], color=color, linewidth=2.5, zorder=3)

    # Ligne verticale au sommet
    summit_ele = track[s_idx][2] or 0
    ax.axvline(x=cum_km[s_idx], color='#333333', linewidth=1, linestyle=':', alpha=0.6)
    ax.plot(cum_km[s_idx], summit_ele, '^', color='#333333', ms=8, zorder=5)

    # Pente par km (annotation)
    if len(climb_km) > 4:
        n_annot = min(10, len(climb_km)//4)
        step_a  = max(1, len(climb_km)//(n_annot+1))
        for i in range(step_a, len(climb_km)-1, step_a):
            j = min(i+step_a, len(climb_km)-1)
            dx = (climb_km[j] - climb_km[i]) * 1000
            dy = climb_ele[j] - climb_ele[i]
            pct = dy/dx*100 if dx > 0 else 0
            xm  = (climb_km[i] + climb_km[j]) / 2
            ym  = (climb_ele[i] + climb_ele[j]) / 2
            ax.text(xm, ym + (summit_ele - min(seg_ele)) * 0.05,
                    f'{pct:.1f}%', ha='center', va='bottom',
                    fontsize=6.5, color=slope_color(pct), fontweight='bold', zorder=6)

    # Légende pentes
    legend_patches = [
        mpatches.Patch(color='#44BB44', label='< 5%'),
        mpatches.Patch(color='#E07800', label='5-8%'),
        mpatches.Patch(color='#CC3300', label='8-12%'),
        mpatches.Patch(color='#880000', label='> 12%'),
    ]
    ax.legend(handles=legend_patches, loc='upper left', fontsize=6.5,
              framealpha=0.7, ncol=4)

    ax.set_xlabel('Distance (km)', fontsize=8)
    ax.set_ylabel('Altitude (m)', fontsize=8)
    ax.tick_params(labelsize=7)
    ax.grid(axis='y', alpha=0.3, linewidth=0.5)
    ax.set_xlim(seg_km[0], seg_km[-1])
    ax.spines['top'].set_visible(False)
    ax.spines['right'].set_visible(False)
    fig.tight_layout(pad=0.3)

    buf = io.BytesIO()
    fig.savefig(buf, format='png', dpi=100, bbox_inches='tight')
    plt.close(fig)
    buf.seek(0)
    return Image.open(buf)

# ─── PIL image → ReportLab ImageReader ───────────────────────────────────────

def pil_to_rl(pil_img):
    buf = io.BytesIO()
    pil_img.save(buf, format='PNG')
    buf.seek(0)
    return ImageReader(buf)

# ─── Page 1 : résumé ─────────────────────────────────────────────────────────

def draw_page1(c, track, cum_km, cols, stats, title, logo_path):
    W, H = PAGE_W, PAGE_H
    M    = MARGIN
    y    = H - M

    # ── Logo optionnel
    if logo_path and os.path.isfile(logo_path):
        try:
            logo = Image.open(logo_path)
            lw, lh = logo.size
            max_h  = 18 * mm
            ratio  = min((W - 2*M) / lw, max_h / lh)
            dw, dh = lw*ratio, lh*ratio
            c.drawImage(pil_to_rl(logo), (W-dw)/2, y-dh, width=dw, height=dh, mask='auto')
            y -= dh + 3*mm
        except Exception:
            pass

    # ── Titre
    c.setFont('Helvetica-Bold', 18)
    c.setFillColorRGB(0.1, 0.1, 0.1)
    c.drawCentredString(W/2, y - 5*mm, title)
    y -= 12*mm

    # ── Stats rapides (bandeau)
    stat_items = [
        ('Distance', f"{stats['total_km']} km"),
        ('D+', f"{stats['d_plus']} m"),
        ('D-', f"{stats['d_minus']} m"),
        ('Alt. max', f"{stats['alt_max']} m"),
        ('Alt. min', f"{stats['alt_min']} m"),
        ('Cols', str(stats['n_cols'])),
    ]
    bh = 12*mm
    bw = (W - 2*M) / len(stat_items)
    for i, (label, val) in enumerate(stat_items):
        bx = M + i * bw
        c.setFillColorRGB(0.15, 0.30, 0.55)
        c.roundRect(bx+1, y-bh, bw-2, bh, 2*mm, fill=1, stroke=0)
        c.setFillColorRGB(1, 1, 1)
        c.setFont('Helvetica', 6.5)
        c.drawCentredString(bx + bw/2, y - 4.5*mm, label)
        c.setFont('Helvetica-Bold', 9)
        c.drawCentredString(bx + bw/2, y - 9.5*mm, val)
    y -= bh + 5*mm

    # ── Carte OSM
    map_h = 90 * mm
    print("  Génération carte OSM...")
    try:
        map_img = build_map_image(track, width_px=1200, height_px=900)
        c.drawImage(pil_to_rl(map_img), M, y - map_h,
                    width=W-2*M, height=map_h, preserveAspectRatio=True, anchor='c')
    except Exception as e:
        c.setFillColorRGB(0.9, 0.9, 0.9)
        c.rect(M, y-map_h, W-2*M, map_h, fill=1, stroke=0)
        c.setFillColorRGB(0.4, 0.4, 0.4)
        c.setFont('Helvetica', 10)
        c.drawCentredString(W/2, y - map_h/2, f'Carte non disponible ({e})')
    y -= map_h + 4*mm

    # ── Profil global
    prof_h = 55 * mm
    print("  Génération profil altimétrique...")
    prof_img = build_profile_image(track, cum_km, cols, width_px=1200, height_px=380)
    c.drawImage(pil_to_rl(prof_img), M, y - prof_h,
                width=W-2*M, height=prof_h, preserveAspectRatio=True, anchor='c')
    y -= prof_h + 5*mm

    # ── Liste des cols (tableau compact)
    if cols:
        c.setFont('Helvetica-Bold', 8)
        c.setFillColorRGB(0.1, 0.1, 0.1)
        c.drawString(M, y, 'Cols et montées')
        y -= 5*mm

        col_widths = [55*mm, 18*mm, 15*mm, 18*mm, 15*mm, 15*mm, 22*mm]
        headers    = ['Nom', 'Km départ', 'Dist.', 'D+', 'Pente', 'Score', 'Catégorie']
        row_h      = 5.5*mm

        # En-tête tableau
        c.setFillColorRGB(0.15, 0.30, 0.55)
        c.rect(M, y-row_h, W-2*M, row_h, fill=1, stroke=0)
        c.setFillColorRGB(1, 1, 1)
        c.setFont('Helvetica-Bold', 7)
        x = M
        for w, h in zip(col_widths, headers):
            c.drawString(x + 1.5*mm, y - row_h + 1.5*mm, h)
            x += w
        y -= row_h

        cat_labels = {'HC':'HC','1':'Cat. 1','2':'Cat. 2','3':'Cat. 3','4':'Cat. 4'}
        for idx, col in enumerate(cols):
            if y < M + row_h: break
            bg = 0.96 if idx % 2 == 0 else 1.0
            c.setFillColorRGB(bg, bg, bg)
            c.rect(M, y-row_h, W-2*M, row_h, fill=1, stroke=0)
            c.setFillColorRGB(0.1, 0.1, 0.1)
            c.setFont('Helvetica', 7)
            name = col['name'].split('|')[0].strip()
            if len(name) > 30: name = name[:29] + '.'
            row_vals = [
                name,
                f"{col['km_foot']:.1f} km",
                f"{col['dist_km']:.1f} km" if col['dist_km'] else '—',
                f"+{col['deniv']:.0f} m"    if col['deniv']   else '—',
                f"{col['pente']:.1f}%"      if col['pente']   else '—',
                f"{col['score']:.0f}"       if col['score']   else '—',
                cat_labels.get(col.get('cat'), '—'),
            ]
            x = M
            for w, val in zip(col_widths, row_vals):
                c.drawString(x + 1.5*mm, y - row_h + 1.5*mm, val)
                x += w

            # Badge catégorie coloré
            cat = col.get('cat')
            if cat:
                color = CAT_COLORS.get(cat, '#888888')
                r,g,b = int(color[1:3],16)/255, int(color[3:5],16)/255, int(color[5:7],16)/255
                c.setFillColorRGB(r, g, b)
                cx = M + sum(col_widths[:6])
                c.roundRect(cx+1, y-row_h+1, col_widths[6]-2, row_h-2, 1.5*mm, fill=1, stroke=0)
                c.setFillColorRGB(1, 1, 1)
                c.setFont('Helvetica-Bold', 7)
                c.drawCentredString(cx + col_widths[6]/2, y - row_h + 1.5*mm,
                                    cat_labels.get(cat, '—'))
            y -= row_h

# ─── Page col ────────────────────────────────────────────────────────────────

COLS_PER_PAGE = 6   # max cols par page (grille 2×3)
COLS_PER_ROW  = 2

def draw_col_mini(c, track, cum_km, col, col_num, total_cols, x0, y0, w, h):
    """
    Dessine la fiche d'un col dans le rectangle (x0, y0-h) → (x0+w, y0).
    Contenu : bandeau titre + 5 stats + profil + tableau pentes.
    """
    cat_labels = {'HC':'HC','1':'Cat. 1','2':'Cat. 2','3':'Cat. 3','4':'Cat. 4'}
    cat        = col.get('cat')
    cat_label  = cat_labels.get(cat, 'NC')
    color_hex  = CAT_COLORS.get(cat, '#888888')
    r,g,b      = int(color_hex[1:3],16)/255, int(color_hex[3:5],16)/255, int(color_hex[5:7],16)/255
    name       = col['name'].split('|')[0].strip()

    PAD = 2*mm
    y   = y0

    # Bordure légère de la cellule
    c.setStrokeColorRGB(0.85, 0.85, 0.85)
    c.setLineWidth(0.3)
    c.roundRect(x0, y0-h, w, h, 2*mm, fill=0, stroke=1)

    # ── Bandeau titre
    bh = 9*mm
    c.setFillColorRGB(r, g, b)
    c.roundRect(x0, y - bh, w, bh, 2*mm, fill=1, stroke=0)
    # Patch pour éviter les coins arrondis seulement en bas
    c.rect(x0, y - bh, w, bh/2, fill=1, stroke=0)
    c.setFillColorRGB(1, 1, 1)
    c.setFont('Helvetica-Bold', 8)
    # Tronquer le nom si nécessaire
    while c.stringWidth(name, 'Helvetica-Bold', 8) > w - 25*mm and len(name) > 4:
        name = name[:-1]
    if name != col['name'].split('|')[0].strip():
        name = name[:-1] + '.'
    c.drawString(x0 + PAD, y - bh + 3*mm, name)
    c.setFont('Helvetica-Bold', 7)
    c.drawRightString(x0 + w - PAD, y - bh + 3*mm, cat_label)
    y -= bh + 1*mm

    # ── Stats (2 lignes × 5 valeurs compactées en 1 ligne)
    stat_items = [
        (f"{col['ele']:.0f}m"      if col['ele']    else '—', 'Alt'),
        (f"{col['dist_km']:.1f}km" if col['dist_km'] else '—', 'Long'),
        (f"+{col['deniv']:.0f}m"   if col['deniv']  else '—', 'D+'),
        (f"{col['pente']:.1f}%"    if col['pente']  else '—', 'Pente'),
        (f"{col['score']:.0f}"     if col['score']  else '—', 'Score'),
        (f"{col['km_foot']:.1f}km" , 'Km départ'),
    ]
    sh = 7*mm
    sw = w / len(stat_items)
    for i, (val, label) in enumerate(stat_items):
        sx = x0 + i * sw
        c.setFillColorRGB(r*0.12+0.88, g*0.12+0.88, b*0.12+0.88)
        c.rect(sx, y-sh, sw, sh, fill=1, stroke=0)
        c.setFillColorRGB(0.35, 0.35, 0.35)
        c.setFont('Helvetica', 5)
        c.drawCentredString(sx + sw/2, y - 2.5*mm, label)
        c.setFillColorRGB(0.05, 0.05, 0.05)
        c.setFont('Helvetica-Bold', 6.5)
        c.drawCentredString(sx + sw/2, y - sh + 1.5*mm, val)
    y -= sh + 1.5*mm

    # ── Profil
    prof_h_pt = y - (y0 - h) - 10*mm  # espace restant moins tableau pentes
    if prof_h_pt > 20*mm:
        try:
            px = int(w / (1/100 * 2.83465))   # pt → px @100dpi approx
            py = int(prof_h_pt / (1/100 * 2.83465))
            prof_img = build_col_profile(track, cum_km, col,
                                         width_px=max(400, px),
                                         height_px=max(150, py))
            c.drawImage(pil_to_rl(prof_img), x0, y - prof_h_pt,
                        width=w, height=prof_h_pt,
                        preserveAspectRatio=True, anchor='c')
        except Exception:
            pass
    y -= prof_h_pt

    # ── Tableau pentes par km (1 ligne compacte)
    if col.get('dist_km') and col.get('s_idx') is not None and y - (y0-h) > 8*mm:
        s_idx    = col['s_idx']
        foot_idx = min(range(len(cum_km)), key=lambda i: abs(cum_km[i] - col['km_foot']))
        eles     = [track[i][2] or 0 for i in range(foot_idx, s_idx+1)]
        kms_seg  = [cum_km[i] for i in range(foot_idx, s_idx+1)]
        sm_e     = smooth(eles, 8)
        km_groups = {}
        for i in range(len(kms_seg)):
            k = int(kms_seg[i])
            km_groups.setdefault(k, []).append((kms_seg[i], sm_e[i]))
        if km_groups:
            row_h  = 5*mm
            cell_w = min(12*mm, w / max(len(km_groups), 1))
            xi     = x0
            for km_int in sorted(km_groups.keys()):
                pts = km_groups[km_int]
                if len(pts) >= 2:
                    dy_  = pts[-1][1] - pts[0][1]
                    dx_  = (pts[-1][0] - pts[0][0]) * 1000
                    pct  = dy_/dx_*100 if dx_ > 0 else 0
                else:
                    pct  = 0
                cs = CAT_COLORS['HC'] if pct>12 else ('#CC3300' if pct>8
                     else ('#E07800' if pct>5 else '#339933'))
                cr2,cg2,cb2 = int(cs[1:3],16)/255, int(cs[3:5],16)/255, int(cs[5:7],16)/255
                c.setFillColorRGB(cr2*0.15+0.85, cg2*0.15+0.85, cb2*0.15+0.85)
                c.rect(xi, y-row_h, cell_w, row_h, fill=1, stroke=0)
                c.setFillColorRGB(cr2, cg2, cb2)
                c.setFont('Helvetica-Bold', 5)
                c.drawCentredString(xi + cell_w/2, y - row_h + 1.5*mm, f'{pct:.1f}%')
                xi += cell_w


def draw_cols_pages(c, track, cum_km, valid_cols):
    """Dessine toutes les fiches cols en grille 2×3 (max 6 par page)."""
    W, H = PAGE_W, PAGE_H
    M    = MARGIN
    GAP  = 4*mm

    n_rows = COLS_PER_PAGE // COLS_PER_ROW
    cell_w = (W - 2*M - (COLS_PER_ROW-1)*GAP) / COLS_PER_ROW
    cell_h = (H - 2*M - (n_rows-1)*GAP) / n_rows

    total = len(valid_cols)
    for page_start in range(0, total, COLS_PER_PAGE):
        c.showPage()
        batch = valid_cols[page_start:page_start + COLS_PER_PAGE]
        print(f"  Page cols {page_start+1}–{page_start+len(batch)}/{total}...")
        for idx, col in enumerate(batch):
            row = idx // COLS_PER_ROW
            col_pos = idx % COLS_PER_ROW
            x0 = M + col_pos * (cell_w + GAP)
            y0 = H - M - row * (cell_h + GAP)
            name = col['name'].split('|')[0].strip()
            print(f"    Profil de {name}...")
            draw_col_mini(c, track, cum_km, col,
                          page_start + idx + 1, total,
                          x0, y0, cell_w, cell_h)

# ─── Génération PDF ───────────────────────────────────────────────────────────

def generate_pdf(gpx_path, title=None, logo_path=None):
    print(f"\n{'='*60}")
    print(f"Fichier: {gpx_path}")

    track, cum_km, cols, stats = parse_gpx(gpx_path)
    print(f"  {len(track)} pts | {stats['total_km']}km | D+{stats['d_plus']}m | {stats['n_cols']} col(s)")

    if title is None:
        title = os.path.basename(gpx_path).replace('.gpx','').replace('_',' ')

    base = os.path.splitext(os.path.basename(gpx_path))[0]
    out_path = os.path.join(os.getcwd(), base + '_resume.pdf')
    c = rl_canvas.Canvas(out_path, pagesize=A4)
    c.setTitle(title)

    # Page 1 — résumé
    draw_page1(c, track, cum_km, cols, stats, title, logo_path)

    # Pages cols (grille 2×3, max 6 par page)
    valid_cols = [col for col in cols if col.get('dist_km')]
    if valid_cols:
        draw_cols_pages(c, track, cum_km, valid_cols)

    c.save()
    print(f"  Sauvegardé: {out_path}")
    return out_path

# ─── Point d'entrée ───────────────────────────────────────────────────────────

if __name__ == '__main__':
    import glob

    parser = argparse.ArgumentParser(
        prog='resume_etape.py',
        description=(
            "Génère un résumé PDF A4 portrait depuis un fichier GPX enrichi.\n"
            "Le PDF contient :\n"
            "  • Page 1  : carte OSM du parcours, profil altimétrique global avec cols annotés,\n"
            "              bandeau de stats (distance, D+, D-, alt min/max) et tableau des cols.\n"
            "  • Pages suivantes : fiches détaillées des cols (profil avec gradient de pente,\n"
            "              stats, tableau des pentes par km), 6 cols par page maximum.\n"
            "\n"
            "Note : utilise les waypoints de cols générés par enrichir_gpx.py."
        ),
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog=(
            "Exemples :\n"
            "  python resume_etape.py mon_trajet_enrichi.gpx\n"
            "  python resume_etape.py mon_trajet_enrichi.gpx --titre \"Étape 1 — Vosges\"\n"
            "  python resume_etape.py *.gpx --logo logo.png --titre \"Groupetto 2025\"\n"
            "\n"
            "Dépendances :\n"
            "  pip install requests matplotlib pillow reportlab pypdf\n"
            "  + poppler (optionnel, pour pdf2image) :\n"
            "    macOS  : brew install poppler\n"
            "    Linux  : apt install poppler-utils"
        )
    )
    parser.add_argument(
        'files', nargs='*',
        help="Fichiers GPX enrichis à traiter. Si omis, traite tous les *.gpx du dossier courant."
    )
    parser.add_argument(
        '--titre', metavar='TITRE',
        help="Titre affiché en haut de la page de résumé (défaut : nom du fichier GPX)."
    )
    parser.add_argument(
        '--logo', metavar='IMAGE',
        help="Chemin vers un logo PNG ou JPG à afficher en haut de la page de résumé."
    )
    args = parser.parse_args()

    files = args.files or glob.glob('*.gpx')
    files = [f for f in files if '_resume' not in f]

    if not files:
        parser.print_help()
        sys.exit(1)

    logo_path = args.logo if args.logo and os.path.isfile(args.logo) else None

    for f in files:
        generate_pdf(f, title=args.titre, logo_path=logo_path)

    print("\nTerminé !")
