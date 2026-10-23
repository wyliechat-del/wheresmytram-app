"""Collector data files (W2 Step 2), built from the timetable files by build_timetable.py.

The collector used to carry this data pasted into its code (SCHED_INDEX, DAY_STATS,
BEACON_STOP_CSV, PACE_STOPS/GEOM/PATTERNS/TRIPS). From W1.6 it reads it from the site:
  collector/manifest.json        build id, day stats, beacon allowlists, corridor list
  collector/sched-<day>.json     trip start times per route for one day type (GPS matching)
  collector/pair-<route>.json    one route's PTV-pairing tables (geometry, patterns, trips)
Encodings are exactly the old baked ones (same pattern ids), so the collector's decoders
are unchanged. bake() reproduces the July bake byte-for-byte from the June files.
"""
import hashlib, json
from collections import defaultdict

DAYS = {
    'weekday': ['schedule_weekday_a1.json', 'schedule_weekday_a2.json',
                'schedule_weekday_b.json', 'schedule_weekday_c.json'],
    'saturday': ['schedule_saturday.json'],
    'sunday': ['schedule_sunday.json'],
}
B36 = '0123456789abcdefghijklmnopqrstuvwxyz'


def b36(n, w):
    s = ''
    while n:
        s = B36[n % 36] + s
        n //= 36
    s = s or '0'
    if len(s) > w:
        raise ValueError('base-36 overflow: needs more than %d digits' % w)
    return s.rjust(w, '0')


def dumps(o):
    return json.dumps(o, separators=(',', ':'), ensure_ascii=False)


def bake(files):
    """files: name -> parsed schedule JSON. Returns the old constants as Python objects."""
    stops_all = {}
    day_data, day_stats, sched_index = {}, {}, {}
    for day, names in DAYS.items():
        trips, per, nstops = {}, {}, 0
        for f in names:
            d = files[f]
            stops_all.update(d['stops'])
            nstops = len(d['stops'])
            for r, arr in d['trips'].items():
                trips.setdefault(r, []).extend(arr)
                per.setdefault(r, set()).update(t['start'] for t in arr)
        day_data[day] = trips
        sched_index[day] = {r: sorted(v) for r, v in per.items()}
        day_stats[day] = {'routes': len(per), 'stops': nstops}

    # canonical distance per (route|dir, stop): trip-count-weighted mode of the rounded distance
    votes = defaultdict(lambda: defaultdict(int))
    for day, trips in day_data.items():
        for r, arr in trips.items():
            for t in arr:
                gk = '%s|%s' % (r, t['dir'])
                for sid, off, dist in t['stops']:
                    votes[gk][(str(sid), round(dist))] += 1
    canon = {}
    for gk, v in votes.items():
        best = {}
        for (sid, dist), n in v.items():
            cur = best.get(sid)
            if cur is None or n > cur[1] or (n == cur[1] and dist < cur[0]):
                best[sid] = (dist, n)
        canon[gk] = {sid: d for sid, (d, n) in best.items()}
    geom_sorted = {k: sorted(c.items(), key=lambda x: (x[1], x[0])) for k, c in canon.items()}
    geom_pos = {k: {sid: i for i, (sid, d) in enumerate(v)} for k, v in geom_sorted.items()}

    patterns, pat_list, trips_out = {}, [], {}
    for day, trips in day_data.items():
        td = trips_out.setdefault(day, {})
        for r, arr in trips.items():
            rd = td.setdefault(r, {})
            for t in arr:
                gk = '%s|%s' % (r, t['dir'])
                gp = geom_pos[gk]
                key = (gk, tuple((gp[str(s[0])], s[1]) for s in t['stops']))
                pid = patterns.get(key)
                if pid is None:
                    pid = len(pat_list)
                    patterns[key] = pid
                    pat_list.append(key)
                rd.setdefault(t['start'], set()).add(pid)

    enc_pat = []
    for gk, entries in pat_list:
        s, prev = [], 0
        for gi, off in entries:
            if off % 60:
                raise ValueError('a stop time is not a whole minute (%s)' % gk)
            dmin = off // 60 - prev
            if dmin < 0:
                raise ValueError('stop times go backwards (%s)' % gk)
            prev = off // 60
            s.append(b36(gi, 2) + b36(dmin, 2))
        enc_pat.append(gk + '|' + ''.join(s))
    enc_trips = {}
    for day, td in trips_out.items():
        ed = enc_trips.setdefault(day, {})
        for r, rd in td.items():
            ed[r] = ','.join(b36(st, 4) + '.' + '.'.join(b36(p, 3) for p in sorted(rd[st])) for st in sorted(rd))
    enc_geom = {k: ';'.join('%s,%s' % (sid, dist) for sid, dist in v) for k, v in geom_sorted.items()}
    enc_stops = {sid: [round(ll[0], 5), round(ll[1], 5)] for sid, ll in stops_all.items()}
    return {
        'DAY_STATS': day_stats, 'SCHED_INDEX': sched_index,
        'BEACON_STOP_CSV': ','.join(sorted(stops_all, key=int)),
        'PACE_STOPS': enc_stops, 'PACE_GEOM': enc_geom, 'PACE_PATTERNS': enc_pat, 'PACE_TRIPS': enc_trips,
    }


def constants_js(b):
    """The old pasted constant lines, for comparing with a baked collector."""
    return {
        'DAY_STATS': 'const DAY_STATS = ' + dumps(b['DAY_STATS']) + ';',
        'SCHED_INDEX': 'const SCHED_INDEX = ' + dumps(b['SCHED_INDEX']) + ';',
        'BEACON_STOP_CSV': "const BEACON_STOP_CSV = '" + b['BEACON_STOP_CSV'] + "';",
        'PACE_STOPS': 'const PACE_STOPS = ' + dumps(b['PACE_STOPS']) + ';',
        'PACE_GEOM': 'const PACE_GEOM = ' + dumps(b['PACE_GEOM']) + ';',
        'PACE_PATTERNS': 'const PACE_PATTERNS = ' + dumps(b['PACE_PATTERNS']) + ';',
        'PACE_TRIPS': 'const PACE_TRIPS = ' + dumps(b['PACE_TRIPS']) + ';',
    }


def collector_files(files, build, release):
    """name -> bytes for everything under collector/ (paths relative to collector/)."""
    b = bake(files)
    out = {}
    for day, idx in b['SCHED_INDEX'].items():
        out['sched-%s.json' % day] = dumps(idx)
    by_route = defaultdict(dict)
    for gk, enc in b['PACE_GEOM'].items():
        by_route[gk.split('|')[0]][gk] = enc
    for r in sorted(by_route, key=lambda x: (len(x), x)):
        geom = dict(sorted(by_route[r].items()))
        sids = set()
        for enc in geom.values():
            sids.update(seg.split(',')[0] for seg in enc.split(';'))
        stops = {sid: b['PACE_STOPS'][sid] for sid in sorted(sids, key=int)}
        pats = {str(pid): p for pid, p in enumerate(b['PACE_PATTERNS']) if p.split('|')[0] == r}
        trips = {day: b['PACE_TRIPS'][day][r] for day in DAYS if r in b['PACE_TRIPS'].get(day, {})}
        out['pair-%s.json' % r] = dumps({'stops': stops, 'geom': geom, 'patterns': pats, 'trips': trips})
    routes = sorted({r for idx in b['SCHED_INDEX'].values() for r in idx}, key=lambda x: (len(x), x))
    corridors = {k: len(v.split(';')) for k, v in sorted(b['PACE_GEOM'].items())}
    manifest = {
        'v': 1, 'build': build, 'release': release, 'dayStats': b['DAY_STATS'], 'routes': routes,
        'corridors': corridors, 'patterns': len(b['PACE_PATTERNS']), 'beaconStops': b['BEACON_STOP_CSV'],
        'files': {n: hashlib.sha256(v.encode('utf-8')).hexdigest()[:12] for n, v in sorted(out.items())},
    }
    out['manifest.json'] = dumps(manifest)
    return {n: v.encode('utf-8') for n, v in out.items()}
