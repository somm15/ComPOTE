#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
competition.py — Gestionnaire de compétition cycliste sur tracés GPX enrichis
==============================================================================

Ce script gère une compétition (« race ») composée d'une ou plusieurs étapes.
Chaque étape est définie par un GPX enrichi (produit par enrichir_gpx.py), qui
contient le tracé de référence et des waypoints de cols catégorisés.

Les participants enregistrent leur passage en fournissant leur propre trace GPX
(« recording »). Le script :

  1. vérifie que le participant a bien suivi le tracé de l'étape (avec une marge
     d'erreur paramétrable, les GPS n'étant pas parfaits) ;
  2. calcule le temps d'ascension de chaque col classé ;
  3. calcule le temps de parcours de l'étape ;
  4. produit deux classements :
       • le classement de la montagne (« maillot à pois »), par points ;
       • le classement général (« maillot jaune »), par temps.
  5. agrège ces classements sur l'ensemble de la compétition.

Toutes les données (compétitions, étapes, cols, participants, enregistrements)
sont stockées dans une base SQLite, ce qui rend l'outil persistant entre deux
exécutions.

Sous-commandes principales
--------------------------
    create-race        Créer une compétition
    create-stage       Créer une étape à partir d'un GPX enrichi
    add-participant    Inscrire un participant à une compétition
    add-recording      Ajouter la trace GPX d'un participant sur une étape
    list-participants  Lister les participants
    list-races         Lister les compétitions
    list-stages        Lister les étapes d'une compétition
    rankings           (Ré)afficher les classements à la demande

Lancez « python competition.py <sous-commande> --help » pour l'aide détaillée.

Dépendances : pip install reportlab   (uniquement pour l'export PDF optionnel)
"""

import argparse
import math
import os
import re
import sqlite3
import sys
import xml.etree.ElementTree as ET
from datetime import datetime, timezone

# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  CONFIGURATION — tout ce qui se modifie facilement se trouve ici          ║
# ╚══════════════════════════════════════════════════════════════════════════╝

# --- Barème du classement de la montagne ------------------------------------
# Pour chaque catégorie de col, la liste donne les points attribués au 1er, 2e,
# 3e... coureur. Modifiez librement ces listes : leur longueur détermine combien
# de coureurs sont récompensés (les suivants reçoivent 0 point).
POINTS_MONTAGNE = {
    "HC": [20, 15, 12, 10, 8, 6, 4, 2],   # Hors Catégorie — 8 premiers
    "1":  [10, 8, 6, 4, 2, 1],            # 1re catégorie  — 6 premiers
    "2":  [5, 3, 2, 1],                   # 2e catégorie   — 4 premiers
    "3":  [2, 1],                         # 3e catégorie   — 2 premiers
    "4":  [1],                            # 4e catégorie   — 1er coureur
}

# --- Vérification du suivi de tracé ------------------------------------------
# Largeur du « couloir » autour du tracé de référence, en mètres. Un point de la
# trace du participant est considéré « sur le tracé » s'il est à moins de cette
# distance du tracé de l'étape.
MARGE_ERREUR_M = 60.0

# Fraction de points de la trace AUTORISÉS hors du couloir (tolérance pour les
# décrochages GPS ponctuels). 0.05 = 5 % des points peuvent dépasser la marge.
TOLERANCE_HORS_TRACE = 0.05

# Distance maximale (m) entre la trace du participant et le départ / l'arrivée
# de l'étape pour considérer que l'étape a réellement été parcourue en entier.
MARGE_DEPART_ARRIVEE_M = 150.0

# --- Sémantique des classements ----------------------------------------------
# Classement de la montagne : ordre de tri du temps d'ascension d'un col.
#   "croissant"  -> le plus RAPIDE est 1er (logique cycliste habituelle)
#   "decroissant"-> le plus LENT est 1er
MONTAGNE_ORDRE_TEMPS = "croissant"

# Classement général : base de temps utilisée.
#   "temps_ecoule"  -> durée du parcours = (arrivée - départ) de chaque trace.
#                      Robuste si les participants roulent des jours différents.
#   "heure_arrivee" -> heure absolue d'arrivée au point final (départ commun
#                      supposé). Le 1er fait 0 s, les autres l'écart.
CLASSEMENT_GENERAL_MODE = "temps_ecoule"

# --- Base de données ---------------------------------------------------------
DB_PATH_DEFAUT = "competition.db"

# --- Espace de noms GPX ------------------------------------------------------
GPX_NS = "http://www.topografix.com/GPX/1/1"
NS = {"gpx": GPX_NS}


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  OUTILS GÉOMÉTRIQUES                                                      ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def haversine(lat1, lon1, lat2, lon2):
    """Distance en mètres entre deux points (lat/lon en degrés)."""
    R = 6371000.0
    phi1, phi2 = math.radians(lat1), math.radians(lat2)
    dphi = math.radians(lat2 - lat1)
    dlam = math.radians(lon2 - lon1)
    a = math.sin(dphi / 2) ** 2 + math.cos(phi1) * math.cos(phi2) * math.sin(dlam / 2) ** 2
    return R * 2 * math.atan2(math.sqrt(a), math.sqrt(1 - a))


class GridIndex:
    """
    Index spatial simple par grille, pour trouver rapidement la distance
    minimale d'un point quelconque à un ensemble de points (le tracé).

    Évite le O(n*m) naïf lors de la vérification de trace : la recherche se fait
    par anneaux de cellules autour du point interrogé.
    """

    def __init__(self, points, cell_deg=0.0025):
        self.cell = cell_deg
        self.cell_m = cell_deg * 111320.0  # ~ mètres couverts par une cellule
        self.buckets = {}
        for (la, lo) in points:
            key = (int(la / cell_deg), int(lo / cell_deg))
            self.buckets.setdefault(key, []).append((la, lo))

    def min_dist(self, lat, lon, max_rings=80):
        """Distance (m) du point (lat, lon) au point le plus proche de l'index."""
        cx, cy = int(lat / self.cell), int(lon / self.cell)
        best = float("inf")
        ring = 0
        while ring <= max_rings:
            for dx in range(-ring, ring + 1):
                for dy in range(-ring, ring + 1):
                    if max(abs(dx), abs(dy)) != ring:
                        continue  # ne traiter que la « coquille » de l'anneau
                    bucket = self.buckets.get((cx + dx, cy + dy))
                    if not bucket:
                        continue
                    for (la, lo) in bucket:
                        d = haversine(lat, lon, la, lo)
                        if d < best:
                            best = d
            # Tout point situé au-delà de l'anneau courant est à au moins
            # ring * cell_m mètres : inutile d'élargir si on a déjà mieux.
            if best != float("inf") and best < ring * self.cell_m:
                break
            ring += 1
        return best


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  ANALYSE GPX                                                              ║
# ╚══════════════════════════════════════════════════════════════════════════╝

class TrackPoint:
    """Un point de trace : coordonnées, altitude et horodatage éventuels."""
    __slots__ = ("lat", "lon", "ele", "time")

    def __init__(self, lat, lon, ele, time):
        self.lat = lat
        self.lon = lon
        self.ele = ele
        self.time = time


def _parse_time(text):
    """Convertit un horodatage GPX ISO-8601 en datetime (UTC), ou None."""
    if not text:
        return None
    s = text.strip().replace("Z", "+00:00")
    try:
        dt = datetime.fromisoformat(s)
    except ValueError:
        for fmt in ("%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%dT%H:%M:%S.%f%z",
                    "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M:%S.%f"):
            try:
                dt = datetime.strptime(s, fmt)
                break
            except ValueError:
                dt = None
        if dt is None:
            return None
    if dt.tzinfo is None:
        dt = dt.replace(tzinfo=timezone.utc)
    return dt


def parse_gpx_track(xml_text):
    """Extrait la liste ordonnée des TrackPoint d'un GPX (trkpt, sinon rtept)."""
    root = ET.fromstring(xml_text)
    pts = root.findall(".//gpx:trkpt", NS) or root.findall(".//gpx:rtept", NS)
    track = []
    for p in pts:
        ele_el = p.find("gpx:ele", NS)
        time_el = p.find("gpx:time", NS)
        ele = float(ele_el.text) if ele_el is not None and ele_el.text else None
        time = _parse_time(time_el.text) if time_el is not None else None
        track.append(TrackPoint(float(p.get("lat")), float(p.get("lon")), ele, time))
    return track


def extract_classified_cols(xml_text):
    """
    Extrait les cols CLASSÉS (catégorie HC/1/2/3/4) des waypoints du GPX enrichi.

    Un col classé est un waypoint dont la description contient « Categorie: ».
    On en tire : nom propre, catégorie et longueur de la montée (« Montee: Xkm »).
    Les sommets non catégorisés sont ignorés (ils ne comptent pas au classement).
    """
    root = ET.fromstring(xml_text)
    cols = []
    for wpt in root.findall("gpx:wpt", NS):
        name = (wpt.findtext("gpx:name", "", NS) or "").strip()
        desc = (wpt.findtext("gpx:desc", "", NS) or "").strip()
        if "Categorie:" not in desc:
            continue  # waypoint non-col ou col non classé -> ignoré

        m_cat = re.search(r"Categorie:\s*([^|]+)", desc)
        raw_cat = m_cat.group(1).strip() if m_cat else ""
        if raw_cat.upper().startswith("HC"):
            category = "HC"
        else:
            category = raw_cat.replace("Cat.", "").strip()
        if category not in POINTS_MONTAGNE:
            continue  # catégorie inconnue -> ignoré

        m_km = re.search(r"Montee:\s*([\d.]+)\s*km", desc)
        climb_km = float(m_km.group(1)) if m_km else None

        ele_el = wpt.find("gpx:ele", NS)
        ele = float(ele_el.text) if ele_el is not None and ele_el.text else None

        # Nom propre : tout ce qui précède le premier « | » ajouté par le script.
        clean_name = name.split(" | ")[0].strip() or "Col"

        cols.append({
            "name": clean_name,
            "category": category,
            "climb_km": climb_km,
            "summit_lat": float(wpt.get("lat")),
            "summit_lon": float(wpt.get("lon")),
            "summit_ele": ele,
        })
    return cols


def cumulative_km(track):
    """Distances cumulées (km) le long d'une trace."""
    dist = [0.0]
    for i in range(1, len(track)):
        dist.append(dist[-1] + haversine(track[i - 1].lat, track[i - 1].lon,
                                         track[i].lat, track[i].lon))
    return [d / 1000.0 for d in dist]


def nearest_index(track, lat, lon, lo=0, hi=None):
    """Index du point de `track[lo:hi]` le plus proche de (lat, lon)."""
    hi = len(track) if hi is None else hi
    best_i, best_d = lo, float("inf")
    for i in range(lo, hi):
        d = haversine(lat, lon, track[i].lat, track[i].lon)
        if d < best_d:
            best_d, best_i = d, i
    return best_i, best_d


def find_foot_index(track, summit_idx, climb_km):
    """
    Détermine l'index du pied d'un col : on remonte le tracé depuis le sommet
    en accumulant la distance jusqu'à atteindre la longueur de montée annoncée.
    Si la longueur est inconnue, on s'arrête au minimum d'altitude local.
    """
    if climb_km and climb_km > 0:
        target_m = climb_km * 1000.0
        acc, i = 0.0, summit_idx
        while i > 0 and acc < target_m:
            acc += haversine(track[i].lat, track[i].lon,
                             track[i - 1].lat, track[i - 1].lon)
            i -= 1
        return i
    # Repli : recherche du point bas avant le sommet (altitude minimale).
    i = summit_idx
    best_i = summit_idx
    best_ele = track[summit_idx].ele if track[summit_idx].ele is not None else 0.0
    while i > 0:
        i -= 1
        ele = track[i].ele
        if ele is None:
            continue
        if ele <= best_ele:
            best_ele, best_i = ele, i
        elif ele > best_ele + 40:  # vraie bosse -> on s'arrête
            break
    return best_i


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  COUCHE BASE DE DONNÉES                                                   ║
# ╚══════════════════════════════════════════════════════════════════════════╝

SCHEMA = """
CREATE TABLE IF NOT EXISTS races (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    name        TEXT UNIQUE NOT NULL,
    created_at  TEXT NOT NULL
);

CREATE TABLE IF NOT EXISTS stages (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    race_id     INTEGER NOT NULL REFERENCES races(id),
    name        TEXT NOT NULL,
    gpx_xml     TEXT NOT NULL,
    total_km    REAL,
    ordre       INTEGER NOT NULL,
    created_at  TEXT NOT NULL,
    UNIQUE(race_id, name)
);

CREATE TABLE IF NOT EXISTS cols (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    stage_id    INTEGER NOT NULL REFERENCES stages(id),
    name        TEXT NOT NULL,
    category    TEXT NOT NULL,
    climb_km    REAL,
    summit_lat  REAL NOT NULL,
    summit_lon  REAL NOT NULL,
    summit_ele  REAL,
    foot_lat    REAL NOT NULL,
    foot_lon    REAL NOT NULL,
    ordre       INTEGER NOT NULL
);

CREATE TABLE IF NOT EXISTS participants (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    race_id     INTEGER NOT NULL REFERENCES races(id),
    name        TEXT NOT NULL,
    created_at  TEXT NOT NULL,
    UNIQUE(race_id, name)
);

CREATE TABLE IF NOT EXISTS recordings (
    id              INTEGER PRIMARY KEY AUTOINCREMENT,
    participant_id  INTEGER NOT NULL REFERENCES participants(id),
    stage_id        INTEGER NOT NULL REFERENCES stages(id),
    gpx_xml         TEXT NOT NULL,
    verified        INTEGER NOT NULL,
    pct_inside      REAL,
    max_ecart_m     REAL,
    created_at      TEXT NOT NULL,
    UNIQUE(participant_id, stage_id)
);
"""


def open_db(path):
    """Ouvre (et crée si besoin) la base SQLite."""
    conn = sqlite3.connect(path)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    conn.executescript(SCHEMA)
    return conn


def _now():
    return datetime.now(timezone.utc).isoformat()


def get_race(conn, name=None):
    """
    Récupère une compétition par son nom. Si `name` est None, renvoie l'unique
    compétition existante (erreur s'il y en a 0 ou plusieurs).
    """
    if name:
        row = conn.execute("SELECT * FROM races WHERE name = ?", (name,)).fetchone()
        if not row:
            raise SystemExit(f"Erreur : aucune compétition nommée « {name} ».")
        return row
    rows = conn.execute("SELECT * FROM races").fetchall()
    if len(rows) == 1:
        return rows[0]
    if not rows:
        raise SystemExit("Erreur : aucune compétition. Créez-en une avec "
                         "« create-race --name ... ».")
    noms = ", ".join(r["name"] for r in rows)
    raise SystemExit(f"Erreur : plusieurs compétitions existent ({noms}).\n"
                     f"Précisez-en une avec --race.")


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  VÉRIFICATION & MESURES SUR UNE TRACE DE PARTICIPANT                      ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def verify_recording(stage_track, rec_track, marge_m):
    """
    Vérifie qu'une trace de participant suit le tracé de l'étape.

    Renvoie (verified: bool, pct_inside: float, max_ecart_m: float).
      - pct_inside : proportion de points de la trace dans le couloir ;
      - max_ecart_m : plus grand écart constaté au tracé de référence.

    La trace est validée si la proportion de points hors couloir reste sous
    TOLERANCE_HORS_TRACE ET si elle passe bien par le départ et l'arrivée.
    """
    index = GridIndex([(p.lat, p.lon) for p in stage_track])
    inside = 0
    max_ecart = 0.0
    for p in rec_track:
        d = index.min_dist(p.lat, p.lon)
        max_ecart = max(max_ecart, d)
        if d <= marge_m:
            inside += 1
    pct_inside = inside / len(rec_track) if rec_track else 0.0

    # Couverture départ / arrivée : la trace doit s'approcher des deux extrémités.
    rec_index = GridIndex([(p.lat, p.lon) for p in rec_track])
    d_depart = rec_index.min_dist(stage_track[0].lat, stage_track[0].lon)
    d_arrivee = rec_index.min_dist(stage_track[-1].lat, stage_track[-1].lon)
    couvre_extremites = (d_depart <= MARGE_DEPART_ARRIVEE_M and
                         d_arrivee <= MARGE_DEPART_ARRIVEE_M)

    verified = (pct_inside >= 1.0 - TOLERANCE_HORS_TRACE) and couvre_extremites
    return verified, pct_inside, max_ecart


def elapsed_seconds(stage_track, rec_track):
    """
    Temps de parcours d'une étape (secondes) selon CLASSEMENT_GENERAL_MODE.

    Renvoie (elapsed_s, finish_dt) ou (None, None) si les horodatages manquent.
      - "temps_ecoule"  : durée arrivée - départ de la trace ;
      - "heure_arrivee" : on renvoie l'heure absolue d'arrivée (elapsed_s = 0,
                          les écarts sont calculés ensuite entre participants).
    """
    n = len(rec_track)
    if n < 2:
        return None, None
    # Point de la trace le plus proche du départ (1re moitié) et de l'arrivée
    # (2e moitié), pour ne pas confondre les passages sur un parcours en boucle.
    half = max(1, n // 2)
    i_start, _ = nearest_index(rec_track, stage_track[0].lat, stage_track[0].lon,
                               0, half)
    i_finish, _ = nearest_index(rec_track, stage_track[-1].lat, stage_track[-1].lon,
                                half - 1, n)
    t_start = rec_track[i_start].time
    t_finish = rec_track[i_finish].time
    if t_start is None or t_finish is None:
        return None, None
    if CLASSEMENT_GENERAL_MODE == "heure_arrivee":
        return 0.0, t_finish
    delta = (t_finish - t_start).total_seconds()
    if delta <= 0:
        # Repli : durée entre premier et dernier point horodatés.
        times = [p.time for p in rec_track if p.time is not None]
        if len(times) < 2:
            return None, None
        delta = (times[-1] - times[0]).total_seconds()
    return delta, t_finish


def col_ascent_seconds(rec_track, col):
    """
    Temps d'ascension (secondes) d'un col par un participant : différence entre
    l'horodatage au sommet et l'horodatage au pied, sur la trace du participant.

    Le pied est localisé en REMONTANT la trace du participant depuis le sommet
    sur la longueur de montée annoncée par le GPX enrichi. Cette mesure « par
    distance » est robuste aux parcours en boucle (contrairement à une simple
    recherche du point géographiquement le plus proche du pied, qui peut tomber
    sur un autre passage du tracé). Renvoie None si l'ascension est non mesurable.
    """
    si, _ = nearest_index(rec_track, col["summit_lat"], col["summit_lon"])
    if si == 0:
        return None
    climb_km = col.get("climb_km")
    if climb_km and climb_km > 0:
        target_m = climb_km * 1000.0
        acc, fi = 0.0, si
        while fi > 0 and acc < target_m:
            acc += haversine(rec_track[fi].lat, rec_track[fi].lon,
                             rec_track[fi - 1].lat, rec_track[fi - 1].lon)
            fi -= 1
    else:
        # Longueur de montée inconnue : repli sur le pied géographique du tracé.
        fi, _ = nearest_index(rec_track, col["foot_lat"], col["foot_lon"], 0, si + 1)
    t_summit = rec_track[si].time
    t_foot = rec_track[fi].time
    if t_summit is None or t_foot is None:
        return None
    dt = (t_summit - t_foot).total_seconds()
    return dt if dt > 0 else None


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  CALCUL DES CLASSEMENTS                                                   ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def compute_stage_results(conn, stage):
    """
    Calcule, pour une étape, toutes les mesures par participant.

    Renvoie un dict :
      {
        "stage": <row stage>,
        "cols":  [<row col>, ...],
        "participants": { participant_id: {
              "name": str, "verified": bool,
              "elapsed": float|None, "finish": datetime|None,
              "col_times": { col_id: float|None } } }
      }
    """
    stage_track = parse_gpx_track(stage["gpx_xml"])
    cols = conn.execute("SELECT * FROM cols WHERE stage_id = ? ORDER BY ordre",
                        (stage["id"],)).fetchall()
    recs = conn.execute(
        "SELECT r.*, p.name AS pname FROM recordings r "
        "JOIN participants p ON p.id = r.participant_id WHERE r.stage_id = ?",
        (stage["id"],)).fetchall()

    participants = {}
    for r in recs:
        rec_track = parse_gpx_track(r["gpx_xml"])
        elapsed, finish = elapsed_seconds(stage_track, rec_track)
        col_times = {}
        for col in cols:
            col_times[col["id"]] = col_ascent_seconds(rec_track, dict(col))
        participants[r["participant_id"]] = {
            "name": r["pname"],
            "verified": bool(r["verified"]),
            "elapsed": elapsed,
            "finish": finish,
            "col_times": col_times,
        }
    return {"stage": stage, "cols": cols, "participants": participants}


def _rank_times(items, ascending=True):
    """
    Classe une liste de (clé, temps) par temps. Renvoie [(rang, clé, temps), ...].
    Les éléments à temps None sont exclus.
    """
    valid = [(k, t) for k, t in items if t is not None]
    valid.sort(key=lambda x: x[1], reverse=not ascending)
    return [(i + 1, k, t) for i, (k, t) in enumerate(valid)]


def mountain_points_for_stage(results):
    """
    Calcule le classement de la montagne d'une étape.

    Renvoie :
      per_col : { col_id: [(rang, participant_id, temps_s, points), ...] }
      totals  : { participant_id: points_total }
    """
    ascending = (MONTAGNE_ORDRE_TEMPS == "croissant")
    per_col = {}
    totals = {pid: 0 for pid in results["participants"]}
    for col in results["cols"]:
        cid = col["id"]
        bareme = POINTS_MONTAGNE.get(col["category"], [])
        items = [(pid, info["col_times"].get(cid))
                 for pid, info in results["participants"].items()
                 if info["verified"]]
        ranked = _rank_times(items, ascending=ascending)
        rows = []
        for rang, pid, temps in ranked:
            pts = bareme[rang - 1] if rang - 1 < len(bareme) else 0
            totals[pid] = totals.get(pid, 0) + pts
            rows.append((rang, pid, temps, pts))
        per_col[cid] = rows
    return per_col, totals


def general_ranking_for_stage(results):
    """
    Classement général d'une étape : [(rang, participant_id, elapsed_s, ecart_s)].
    L'écart est calculé par rapport au premier (0 s pour le premier).
    """
    if CLASSEMENT_GENERAL_MODE == "heure_arrivee":
        items = [(pid, info["finish"].timestamp() if info["finish"] else None)
                 for pid, info in results["participants"].items()
                 if info["verified"]]
    else:
        items = [(pid, info["elapsed"])
                 for pid, info in results["participants"].items()
                 if info["verified"]]
    ranked = _rank_times(items, ascending=True)
    if not ranked:
        return []
    base = ranked[0][2]
    out = []
    for rang, pid, valeur in ranked:
        # En mode "temps_ecoule", on affiche la durée ; en "heure_arrivee",
        # la durée n'a pas de sens -> on affiche l'écart uniquement.
        elapsed = results["participants"][pid]["elapsed"]
        out.append((rang, pid, elapsed, valeur - base))
    return out


def compute_competition(conn, race):
    """
    Agrège les classements sur toute la compétition.

    Renvoie un dict avec :
      "stages"            : [résultats par étape] (ordre des étapes)
      "mountain_total"    : [(rang, pid, name, points), ...]
      "general_total"     : [(rang, pid, name, total_elapsed_s, ecart_s,
                              nb_etapes), ...]
    """
    stages = conn.execute("SELECT * FROM stages WHERE race_id = ? ORDER BY ordre",
                          (race["id"],)).fetchall()
    all_names = {p["id"]: p["name"] for p in conn.execute(
        "SELECT id, name FROM participants WHERE race_id = ?", (race["id"],))}

    stage_blocks = []
    mountain_total = {pid: 0 for pid in all_names}
    general_time = {pid: 0.0 for pid in all_names}
    general_count = {pid: 0 for pid in all_names}

    for stage in stages:
        results = compute_stage_results(conn, stage)
        per_col, m_totals = mountain_points_for_stage(results)
        g_rank = general_ranking_for_stage(results)
        for pid, pts in m_totals.items():
            mountain_total[pid] = mountain_total.get(pid, 0) + pts
        for rang, pid, elapsed, ecart in g_rank:
            if elapsed is not None:
                general_time[pid] += elapsed
                general_count[pid] += 1
        stage_blocks.append({
            "stage": stage, "results": results,
            "per_col": per_col, "mountain": m_totals, "general": g_rank,
        })

    # Classement montagne global : tri par points décroissants.
    m_list = sorted(((pid, all_names[pid], pts) for pid, pts in mountain_total.items()
                     if pts > 0), key=lambda x: -x[2])
    mountain_final = [(i + 1, pid, name, pts)
                      for i, (pid, name, pts) in enumerate(m_list)]

    # Classement général global : on classe d'abord les participants ayant
    # terminé le plus d'étapes, puis par temps cumulé croissant.
    g_list = [(pid, all_names[pid], general_time[pid], general_count[pid])
              for pid in all_names if general_count[pid] > 0]
    g_list.sort(key=lambda x: (-x[3], x[2]))
    general_final = []
    base = g_list[0][2] if g_list else 0.0
    for i, (pid, name, total, count) in enumerate(g_list):
        general_final.append((i + 1, pid, name, total, total - base, count))

    return {
        "race": race,
        "stages": stage_blocks,
        "mountain_total": mountain_final,
        "general_total": general_final,
    }


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  MISE EN FORME                                                            ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def fmt_duration(seconds):
    """Formate une durée en H:MM:SS (ou MM:SS si moins d'une heure)."""
    if seconds is None:
        return "—"
    seconds = int(round(seconds))
    sign = "-" if seconds < 0 else ""
    seconds = abs(seconds)
    h, rem = divmod(seconds, 3600)
    m, s = divmod(rem, 60)
    if h:
        return f"{sign}{h}:{m:02d}:{s:02d}"
    return f"{sign}{m}:{s:02d}"


def fmt_ecart(seconds):
    """Formate un écart de temps (« +M:SS »), « — » pour le premier."""
    if seconds is None:
        return "—"
    if abs(seconds) < 0.5:
        return "—"
    return "+" + fmt_duration(abs(seconds))


def _table(rows, headers):
    """Rend un tableau texte aligné pour l'affichage terminal."""
    cols = list(zip(*([headers] + rows))) if rows else [[h] for h in headers]
    widths = [max(len(str(c)) for c in col) for col in cols]
    line = "  " + "  ".join(str(h).ljust(w) for h, w in zip(headers, widths))
    sep = "  " + "  ".join("-" * w for w in widths)
    out = [line, sep]
    for r in rows:
        out.append("  " + "  ".join(str(c).ljust(w) for c, w in zip(r, widths)))
    return "\n".join(out)


def print_competition(comp):
    """Affiche tous les classements d'une compétition dans le terminal."""
    race = comp["race"]
    print("\n" + "=" * 74)
    print(f"  COMPÉTITION : {race['name']}")
    print("=" * 74)

    for block in comp["stages"]:
        stage = block["stage"]
        results = block["results"]
        names = {pid: info["name"] for pid, info in results["participants"].items()}
        print(f"\n┌── ÉTAPE {stage['ordre']} : {stage['name']}"
              f"  ({stage['total_km']:.1f} km)")

        # --- Classement de la montagne, col par col -------------------------
        if results["cols"]:
            print("│")
            print("│  CLASSEMENT DE LA MONTAGNE — détail par col")
            for col in results["cols"]:
                label = "HC" if col["category"] == "HC" else f"Cat. {col['category']}"
                print(f"│")
                print(f"│  ▸ {col['name']} ({label})")
                rows = []
                for rang, pid, temps, pts in block["per_col"][col["id"]]:
                    rows.append([rang, names.get(pid, f"#{pid}"),
                                 fmt_duration(temps), pts])
                if rows:
                    print(_indent(_table(rows, ["Rang", "Coureur",
                                                "Temps asc.", "Points"])))
                else:
                    print("    (aucun temps d'ascension exploitable)")
        else:
            print("│  (aucun col classé sur cette étape)")

        # --- Classement de la montagne de l'étape ---------------------------
        print("│")
        print("│  CLASSEMENT DE LA MONTAGNE — étape")
        m_rows = sorted(block["mountain"].items(), key=lambda x: -x[1])
        rows = [[i + 1, names.get(pid, f"#{pid}"), pts]
                for i, (pid, pts) in enumerate(m_rows) if pts > 0]
        print(_indent(_table(rows, ["Rang", "Coureur", "Points"]))
              if rows else "    (aucun point attribué)")

        # --- Classement général de l'étape ----------------------------------
        print("│")
        print("│  CLASSEMENT GÉNÉRAL — étape")
        rows = []
        for rang, pid, elapsed, ecart in block["general"]:
            rows.append([rang, names.get(pid, f"#{pid}"),
                         fmt_duration(elapsed),
                         "—" if rang == 1 else fmt_ecart(ecart)])
        print(_indent(_table(rows, ["Rang", "Coureur", "Temps", "Écart"]))
              if rows else "    (aucun classement — traces non vérifiées)")

        # Participants non vérifiés
        rejets = [info["name"] for info in results["participants"].values()
                  if not info["verified"]]
        if rejets:
            print(f"│  ⚠  Trace non conforme (hors classement) : "
                  f"{', '.join(rejets)}")
        print("└" + "─" * 60)

    # --- Classements cumulés de la compétition ------------------------------
    print("\n" + "═" * 74)
    print("  CLASSEMENT DE LA MONTAGNE — COMPÉTITION (cumul des étapes)")
    print("═" * 74)
    rows = [[r, name, pts] for r, pid, name, pts in comp["mountain_total"]]
    print(_table(rows, ["Rang", "Coureur", "Points"])
          if rows else "  (aucun point attribué)")

    print("\n" + "═" * 74)
    print("  CLASSEMENT GÉNÉRAL — COMPÉTITION (temps cumulé)")
    print("═" * 74)
    rows = []
    for rang, pid, name, total, ecart, count in comp["general_total"]:
        rows.append([rang, name, fmt_duration(total),
                     "—" if rang == 1 else fmt_ecart(ecart), count])
    print(_table(rows, ["Rang", "Coureur", "Temps cumulé", "Écart", "Étapes"])
          if rows else "  (aucun classement)")
    print()


def _indent(text, prefix="│    "):
    return "\n".join(prefix + line for line in text.split("\n"))


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  EXPORT PDF (optionnel)                                                   ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def export_pdf(comp, out_path):
    """Génère un PDF récapitulatif de tous les classements de la compétition."""
    try:
        from reportlab.lib.pagesizes import A4
        from reportlab.lib.units import cm
        from reportlab.lib import colors
        from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
        from reportlab.platypus import (SimpleDocTemplate, Paragraph, Spacer,
                                        Table, TableStyle)
    except ImportError:
        print("  ⚠  reportlab non installé — PDF ignoré (pip install reportlab).")
        return None

    styles = getSampleStyleSheet()
    h1 = ParagraphStyle("h1", parent=styles["Title"], fontSize=18, spaceAfter=4)
    h2 = ParagraphStyle("h2", parent=styles["Heading2"], fontSize=13,
                        textColor=colors.HexColor("#1a3c6e"), spaceBefore=14)
    h3 = ParagraphStyle("h3", parent=styles["Heading3"], fontSize=10,
                        textColor=colors.HexColor("#444444"), spaceBefore=8)
    small = ParagraphStyle("small", parent=styles["Normal"], fontSize=8,
                           textColor=colors.grey)

    def make_table(headers, rows, col_widths=None):
        data = [headers] + (rows if rows else [["—"] * len(headers)])
        t = Table(data, colWidths=col_widths, hAlign="LEFT")
        t.setStyle(TableStyle([
            ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#1a3c6e")),
            ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
            ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
            ("FONTSIZE", (0, 0), (-1, -1), 8),
            ("ROWBACKGROUNDS", (0, 1), (-1, -1),
             [colors.white, colors.HexColor("#eef2f7")]),
            ("GRID", (0, 0), (-1, -1), 0.4, colors.HexColor("#cccccc")),
            ("TOPPADDING", (0, 0), (-1, -1), 3),
            ("BOTTOMPADDING", (0, 0), (-1, -1), 3),
        ]))
        return t

    story = []
    race = comp["race"]
    story.append(Paragraph(f"Classements — {race['name']}", h1))
    story.append(Paragraph("Généré le " + datetime.now().strftime("%d/%m/%Y %H:%M"),
                           small))

    for block in comp["stages"]:
        stage = block["stage"]
        results = block["results"]
        names = {pid: info["name"] for pid, info in results["participants"].items()}
        story.append(Paragraph(f"Étape {stage['ordre']} — {stage['name']} "
                               f"({stage['total_km']:.1f} km)", h2))

        for col in results["cols"]:
            label = "HC" if col["category"] == "HC" else f"Cat. {col['category']}"
            story.append(Paragraph(f"Col : {col['name']} ({label})", h3))
            rows = [[r, names.get(pid, f"#{pid}"), fmt_duration(t), pts]
                    for r, pid, t, pts in block["per_col"][col["id"]]]
            story.append(make_table(["Rang", "Coureur", "Temps asc.", "Points"],
                                     rows, [1.6 * cm, 7 * cm, 3 * cm, 2 * cm]))

        story.append(Paragraph("Classement de la montagne — étape", h3))
        m_rows = sorted(block["mountain"].items(), key=lambda x: -x[1])
        rows = [[i + 1, names.get(pid, f"#{pid}"), pts]
                for i, (pid, pts) in enumerate(m_rows) if pts > 0]
        story.append(make_table(["Rang", "Coureur", "Points"], rows,
                                 [1.6 * cm, 9 * cm, 3 * cm]))

        story.append(Paragraph("Classement général — étape", h3))
        rows = [[r, names.get(pid, f"#{pid}"), fmt_duration(e),
                 "—" if r == 1 else fmt_ecart(ec)]
                for r, pid, e, ec in block["general"]]
        story.append(make_table(["Rang", "Coureur", "Temps", "Écart"], rows,
                                 [1.6 * cm, 7 * cm, 3 * cm, 3 * cm]))
        story.append(Spacer(1, 6))

    story.append(Paragraph("Classement de la montagne — COMPÉTITION", h2))
    rows = [[r, name, pts] for r, pid, name, pts in comp["mountain_total"]]
    story.append(make_table(["Rang", "Coureur", "Points"], rows,
                             [1.6 * cm, 9 * cm, 3 * cm]))

    story.append(Paragraph("Classement général — COMPÉTITION", h2))
    rows = [[r, name, fmt_duration(tot), "—" if r == 1 else fmt_ecart(ec), cnt]
            for r, pid, name, tot, ec, cnt in comp["general_total"]]
    story.append(make_table(["Rang", "Coureur", "Temps cumulé", "Écart", "Étapes"],
                             rows, [1.6 * cm, 6 * cm, 3.5 * cm, 3 * cm, 2 * cm]))

    doc = SimpleDocTemplate(out_path, pagesize=A4,
                            topMargin=1.5 * cm, bottomMargin=1.5 * cm,
                            leftMargin=1.8 * cm, rightMargin=1.8 * cm)
    doc.build(story)
    return out_path


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  SOUS-COMMANDES CLI                                                       ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def cmd_create_race(conn, args):
    """create-race : crée une nouvelle compétition."""
    try:
        conn.execute("INSERT INTO races (name, created_at) VALUES (?, ?)",
                     (args.name, _now()))
        conn.commit()
    except sqlite3.IntegrityError:
        raise SystemExit(f"Erreur : la compétition « {args.name} » existe déjà.")
    print(f"✓ Compétition créée : « {args.name} »")


def cmd_create_stage(conn, args):
    """create-stage : crée une étape à partir d'un GPX enrichi."""
    if not os.path.isfile(args.gpx):
        raise SystemExit(f"Erreur : fichier GPX introuvable : {args.gpx}")
    race = get_race(conn, args.race)

    with open(args.gpx, "r", encoding="utf-8") as f:
        xml_text = f.read()

    track = parse_gpx_track(xml_text)
    if len(track) < 2:
        raise SystemExit("Erreur : le GPX ne contient pas de tracé exploitable.")
    total_km = cumulative_km(track)[-1]
    cols = extract_classified_cols(xml_text)

    ordre = (conn.execute("SELECT COALESCE(MAX(ordre), 0) + 1 FROM stages "
                          "WHERE race_id = ?", (race["id"],)).fetchone()[0])
    try:
        cur = conn.execute(
            "INSERT INTO stages (race_id, name, gpx_xml, total_km, ordre, "
            "created_at) VALUES (?, ?, ?, ?, ?, ?)",
            (race["id"], args.name, xml_text, total_km, ordre, _now()))
    except sqlite3.IntegrityError:
        raise SystemExit(f"Erreur : l'étape « {args.name} » existe déjà dans "
                         f"cette compétition.")
    stage_id = cur.lastrowid

    # Cols : sommet sur le tracé + pied de la montée.
    for i, col in enumerate(cols):
        s_idx, _ = nearest_index(track, col["summit_lat"], col["summit_lon"])
        f_idx = find_foot_index(track, s_idx, col["climb_km"])
        conn.execute(
            "INSERT INTO cols (stage_id, name, category, climb_km, summit_lat, "
            "summit_lon, summit_ele, foot_lat, foot_lon, ordre) "
            "VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?)",
            (stage_id, col["name"], col["category"], col["climb_km"],
             col["summit_lat"], col["summit_lon"], col["summit_ele"],
             track[f_idx].lat, track[f_idx].lon, i))
    conn.commit()

    print(f"✓ Étape créée : « {args.name} » (compétition « {race['name']} »)")
    print(f"  Distance : {total_km:.1f} km — {len(track)} points de tracé")
    if cols:
        print(f"  Cols classés détectés ({len(cols)}) :")
        for col in cols:
            label = "HC" if col["category"] == "HC" else f"Cat. {col['category']}"
            km = f"{col['climb_km']:.1f} km" if col["climb_km"] else "?"
            print(f"    • {col['name']:32s} {label:7s} montée {km}")
    else:
        print("  Aucun col classé dans ce GPX.")


def cmd_add_participant(conn, args):
    """add-participant : inscrit un participant à une compétition."""
    race = get_race(conn, args.race)
    try:
        conn.execute("INSERT INTO participants (race_id, name, created_at) "
                     "VALUES (?, ?, ?)", (race["id"], args.name, _now()))
        conn.commit()
    except sqlite3.IntegrityError:
        raise SystemExit(f"Erreur : « {args.name} » est déjà inscrit à "
                         f"« {race['name']} ».")
    print(f"✓ Participant inscrit : {args.name} → « {race['name']} »")


def _resolve_participant(conn, name, race_name):
    """Trouve un participant par nom, éventuellement restreint à une compétition."""
    if race_name:
        race = get_race(conn, race_name)
        row = conn.execute("SELECT * FROM participants WHERE name = ? AND "
                           "race_id = ?", (name, race["id"])).fetchone()
        if not row:
            raise SystemExit(f"Erreur : « {name} » n'est pas inscrit à "
                             f"« {race_name} ».")
        return row
    rows = conn.execute("SELECT * FROM participants WHERE name = ?",
                        (name,)).fetchall()
    if not rows:
        raise SystemExit(f"Erreur : aucun participant nommé « {name} ».")
    if len(rows) > 1:
        raise SystemExit(f"Erreur : « {name} » est inscrit à plusieurs "
                         f"compétitions. Précisez --race.")
    return rows[0]


def cmd_add_recording(conn, args):
    """add-recording : ajoute la trace GPX d'un participant et calcule tout."""
    if not os.path.isfile(args.gpx):
        raise SystemExit(f"Erreur : fichier GPX introuvable : {args.gpx}")
    participant = _resolve_participant(conn, args.participant, args.race)
    with open(args.gpx, "r", encoding="utf-8") as f:
        rec_xml = f.read()
    rec_track = parse_gpx_track(rec_xml)
    if len(rec_track) < 2:
        raise SystemExit("Erreur : la trace GPX ne contient pas assez de points.")
    if not any(p.time for p in rec_track):
        print("⚠  La trace ne contient aucun horodatage : aucun temps ne "
              "pourra être calculé.")

    stages = conn.execute("SELECT * FROM stages WHERE race_id = ? ORDER BY ordre",
                          (participant["race_id"],)).fetchall()
    if not stages:
        raise SystemExit("Erreur : la compétition n'a aucune étape.")

    marge = args.margin if args.margin is not None else MARGE_ERREUR_M

    # Sélection de l'étape : explicite (--stage) ou auto-détection.
    if args.stage:
        stage = next((s for s in stages if s["name"] == args.stage), None)
        if not stage:
            raise SystemExit(f"Erreur : étape « {args.stage} » introuvable.")
        stage_track = parse_gpx_track(stage["gpx_xml"])
        verified, pct, ecart = verify_recording(stage_track, rec_track, marge)
    else:
        # On teste chaque étape, on retient celle dont le suivi est le meilleur.
        best = None
        for s in stages:
            st_track = parse_gpx_track(s["gpx_xml"])
            v, pct, ec = verify_recording(st_track, rec_track, marge)
            if best is None or pct > best[2]:
                best = (s, v, pct, ec)
        stage, verified, pct, ecart = best
        print(f"  Étape auto-détectée : « {stage['name']} » "
              f"(meilleur taux de suivi)")

    print(f"\nVérification du suivi de tracé (marge {marge:.0f} m) :")
    print(f"  Points dans le couloir : {pct * 100:.1f} %")
    print(f"  Écart maximal au tracé : {ecart:.0f} m")
    if verified:
        print("  ✓ Trace CONFORME — le participant a bien suivi l'étape.")
    else:
        print("  ✗ Trace NON CONFORME — le participant sera hors classement.")

    # Enregistrement (remplace une trace existante du même couple).
    conn.execute("DELETE FROM recordings WHERE participant_id = ? AND "
                 "stage_id = ?", (participant["id"], stage["id"]))
    conn.execute(
        "INSERT INTO recordings (participant_id, stage_id, gpx_xml, verified, "
        "pct_inside, max_ecart_m, created_at) VALUES (?, ?, ?, ?, ?, ?, ?)",
        (participant["id"], stage["id"], rec_xml, int(verified), pct, ecart,
         _now()))
    conn.commit()
    print(f"✓ Trace enregistrée pour {participant['name']} "
          f"sur l'étape « {stage['name']} ».")

    # Recalcul et affichage de tous les classements.
    race = conn.execute("SELECT * FROM races WHERE id = ?",
                        (participant["race_id"],)).fetchone()
    comp = compute_competition(conn, race)
    print_competition(comp)

    if args.pdf:
        path = _pdf_path(race["name"])
        result = export_pdf(comp, path)
        if result:
            print(f"✓ PDF généré : {result}")


def cmd_list_participants(conn, args):
    """list-participants : liste les participants (toutes compétitions ou une)."""
    if args.race:
        races = [get_race(conn, args.race)]
    else:
        races = conn.execute("SELECT * FROM races ORDER BY name").fetchall()
    if not races:
        print("Aucune compétition enregistrée.")
        return
    for race in races:
        parts = conn.execute(
            "SELECT p.name, p.created_at, "
            "(SELECT COUNT(*) FROM recordings r WHERE r.participant_id = p.id) "
            "AS nb FROM participants p WHERE p.race_id = ? ORDER BY p.name",
            (race["id"],)).fetchall()
        print(f"\nCompétition « {race['name']} » — {len(parts)} participant(s)")
        if parts:
            rows = [[p["name"], p["nb"]] for p in parts]
            print(_table(rows, ["Participant", "Traces enregistrées"]))
        else:
            print("  (aucun participant)")
    print()


def cmd_list_races(conn, args):
    """list-races : liste les compétitions."""
    races = conn.execute(
        "SELECT r.name, "
        "(SELECT COUNT(*) FROM stages s WHERE s.race_id = r.id) AS ns, "
        "(SELECT COUNT(*) FROM participants p WHERE p.race_id = r.id) AS np "
        "FROM races r ORDER BY r.name").fetchall()
    if not races:
        print("Aucune compétition enregistrée.")
        return
    rows = [[r["name"], r["ns"], r["np"]] for r in races]
    print()
    print(_table(rows, ["Compétition", "Étapes", "Participants"]))
    print()


def cmd_list_stages(conn, args):
    """list-stages : liste les étapes d'une compétition."""
    race = get_race(conn, args.race)
    stages = conn.execute("SELECT * FROM stages WHERE race_id = ? ORDER BY ordre",
                          (race["id"],)).fetchall()
    print(f"\nÉtapes de « {race['name']} » :")
    if not stages:
        print("  (aucune étape)")
        return
    rows = []
    for s in stages:
        nb_cols = conn.execute("SELECT COUNT(*) FROM cols WHERE stage_id = ?",
                               (s["id"],)).fetchone()[0]
        nb_rec = conn.execute("SELECT COUNT(*) FROM recordings WHERE stage_id = ?",
                              (s["id"],)).fetchone()[0]
        rows.append([s["ordre"], s["name"], f"{s['total_km']:.1f}", nb_cols, nb_rec])
    print(_table(rows, ["N°", "Étape", "km", "Cols classés", "Traces"]))
    print()


def cmd_rankings(conn, args):
    """rankings : (ré)affiche les classements d'une compétition à la demande."""
    race = get_race(conn, args.race)
    comp = compute_competition(conn, race)
    print_competition(comp)
    if args.pdf:
        path = _pdf_path(race["name"])
        result = export_pdf(comp, path)
        if result:
            print(f"✓ PDF généré : {result}")


def _pdf_path(race_name):
    """Nom de fichier PDF horodaté pour une compétition."""
    safe = re.sub(r"[^\w-]+", "_", race_name).strip("_")
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    return f"classement_{safe}_{stamp}.pdf"


# ╔══════════════════════════════════════════════════════════════════════════╗
# ║  POINT D'ENTRÉE / ARGPARSE                                                ║
# ╚══════════════════════════════════════════════════════════════════════════╝

def build_parser():
    """Construit l'analyseur d'arguments avec toutes les sous-commandes."""
    parser = argparse.ArgumentParser(
        prog="competition.py",
        formatter_class=argparse.RawDescriptionHelpFormatter,
        description=(
            "Gestionnaire de compétition cycliste sur tracés GPX enrichis.\n\n"
            "Flux de travail typique :\n"
            "  1. create-race      — créer la compétition\n"
            "  2. create-stage     — ajouter une ou plusieurs étapes (GPX enrichi)\n"
            "  3. add-participant  — inscrire les coureurs\n"
            "  4. add-recording    — déposer la trace d'un coureur sur une étape\n"
            "                        (vérifie le suivi + affiche les classements)\n"
            "  5. rankings         — réafficher les classements quand on veut"
        ),
        epilog=(
            "Exemples :\n"
            "  python competition.py create-race --name \"Vosges 2026\"\n"
            "  python competition.py create-stage --name \"Lac de Kruth\" \\\n"
            "                        --gpx le_lac_de_kruth_enrichi.gpx\n"
            "  python competition.py add-participant --name Simon "
            "--race \"Vosges 2026\"\n"
            "  python competition.py add-recording --participant Simon \\\n"
            "                        --gpx simon_kruth.gpx --pdf\n"
            "  python competition.py list-participants\n"
            "  python competition.py rankings --race \"Vosges 2026\" --pdf\n"
        ),
    )
    parser.add_argument("--db", default=DB_PATH_DEFAUT,
                        help=f"Chemin de la base SQLite (défaut : {DB_PATH_DEFAUT}).")
    sub = parser.add_subparsers(dest="command", metavar="<sous-commande>")

    p = sub.add_parser("create-race", help="Créer une compétition.")
    p.add_argument("--name", required=True, help="Nom de la compétition.")

    p = sub.add_parser("create-stage", help="Créer une étape (GPX enrichi).")
    p.add_argument("--name", required=True, help="Nom de l'étape.")
    p.add_argument("--gpx", required=True, help="Fichier GPX enrichi de l'étape.")
    p.add_argument("--race", help="Compétition cible (facultatif si une seule).")

    p = sub.add_parser("add-participant", help="Inscrire un participant.")
    p.add_argument("--name", required=True, help="Nom du participant.")
    p.add_argument("--race", help="Compétition cible (facultatif si une seule).")

    p = sub.add_parser("add-recording",
                       help="Ajouter la trace GPX d'un participant.")
    p.add_argument("--participant", required=True, help="Nom du participant.")
    p.add_argument("--gpx", required=True, help="Trace GPX réalisée.")
    p.add_argument("--stage", help="Étape concernée (sinon auto-détection).")
    p.add_argument("--race", help="Compétition (lève une ambiguïté de nom).")
    p.add_argument("--margin", type=float,
                   help=f"Marge d'erreur de suivi en mètres "
                        f"(défaut : {MARGE_ERREUR_M:.0f}).")
    p.add_argument("--pdf", action="store_true",
                   help="Exporter aussi les classements en PDF.")

    p = sub.add_parser("list-participants", help="Lister les participants.")
    p.add_argument("--race", help="Restreindre à une compétition.")

    sub.add_parser("list-races", help="Lister les compétitions.")

    p = sub.add_parser("list-stages", help="Lister les étapes d'une compétition.")
    p.add_argument("--race", help="Compétition cible (facultatif si une seule).")

    p = sub.add_parser("rankings", help="Afficher les classements.")
    p.add_argument("--race", help="Compétition cible (facultatif si une seule).")
    p.add_argument("--pdf", action="store_true", help="Exporter aussi en PDF.")

    return parser


COMMANDS = {
    "create-race": cmd_create_race,
    "create-stage": cmd_create_stage,
    "add-participant": cmd_add_participant,
    "add-recording": cmd_add_recording,
    "list-participants": cmd_list_participants,
    "list-races": cmd_list_races,
    "list-stages": cmd_list_stages,
    "rankings": cmd_rankings,
}


def main(argv=None):
    parser = build_parser()
    args = parser.parse_args(argv)
    if not args.command:
        parser.print_help()
        return 1
    conn = open_db(args.db)
    try:
        COMMANDS[args.command](conn, args)
    finally:
        conn.close()
    return 0


if __name__ == "__main__":
    sys.exit(main())
