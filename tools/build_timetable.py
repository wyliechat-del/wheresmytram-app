#!/usr/bin/env python3
"""WheresMyTram timetable builder (W2 Step 1).

Builds the viewer's timetable files from Transport Victoria's GTFS Schedule:
  schedule_weekday_a1/a2/b/c.json, schedule_saturday.json, schedule_sunday.json,
  tram_network.json
in exactly the format the viewer already reads (see claude/w2-design.md, section 1.7).

Which trips go in: for each weekday (Mon..Sun), the services running on its next
REGULAR date on or after the build date. A date is regular when no service is
removed that day and no one-off service runs (holiday copies run on 1-2 dates).
Weekday file = union of Mon..Fri, so it still holds both Mon-Thu and Friday
trips until the viewer can tell them apart (W2 Step 3).

Usage (the GitHub Action runs this):
  python3 tools/build_timetable.py --gtfs gtfs.zip --repo . --summary summary.md
  --gtfs   the DataVic gtfs.zip (folder 3 is read), a tram google_transit.zip, or a folder
  --date   build date YYYYMMDD (default: today in Melbourne)
  --allow-large-change   accept per-route trip-count changes over 15%
  --line-distances       measure stop distances along the route line (Step 1b)
Exit code 0 = files written; 1 = a check failed and nothing was written.
Standard library only.
"""
import argparse, csv, datetime as dt, hashlib, io, json, math, os, re, sys, zipfile
from collections import Counter, defaultdict

SCHEDULE_FILES = ['schedule_weekday_a1.json', 'schedule_weekday_a2.json', 'schedule_weekday_b.json',
                  'schedule_weekday_c.json', 'schedule_saturday.json', 'schedule_sunday.json']
NETWORK_FILE = 'tram_network.json'
WEEKDAY_PIECES = [  # route lists of the four weekday pieces, as in the June files
    ('schedule_weekday_a1.json', ['86', '75', '16', '6']),
    ('schedule_weekday_a2.json', ['58', '109', '59', '70']),
    ('schedule_weekday_b.json', ['19', '72', '1', '11', '96', '67', '48']),
    ('schedule_weekday_c.json', ['57', '12', '3', '64', '5', '78', '82', '30', '35']),
]
WEEKEND_ORDER = ['109', '11', '12', '1', '16', '19', '30', '3', '35', '48', '5', '57', '58', '59',
                 '6', '64', '67', '70', '72', '75', '78', '82', '86', '96']
TRAM_FOLDER = '3/google_transit.zip'
MAX_FILE_BYTES = 20 * 1024 * 1024
COUNT_TOLERANCE = 0.15
COVER_DAYS = 14
ONE_OFF_MAX_DATES = 2
ROUTE_STOP_SHARE = 0.05    # same cut as the viewer's trimForeignStops (TRIP_MIN_SHARE)
ON_LINE_M = 50             # Step 1b: every stop within this of the route line
LINE_START_M = 50          # Step 1b: rebase only trips starting this far into the line
DOW = ['Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat', 'Sun']


class BuildError(Exception):
    pass


# ── reading GTFS ────────────────────────────────────────────────────────────────
class Gtfs:
    def __init__(self, path):
        self.release = None
        self._zip = None
        self._dir = None
        if os.path.isdir(path):
            self._dir = path
        else:
            z = zipfile.ZipFile(path)
            names = z.namelist()
            if TRAM_FOLDER in names:              # the whole-of-Victoria gtfs.zip
                info = z.getinfo(TRAM_FOLDER)
                self.release = '%04d-%02d-%02d' % info.date_time[:3]
                self._zip = zipfile.ZipFile(io.BytesIO(z.read(TRAM_FOLDER)))
            elif 'stop_times.txt' in names:       # a tram google_transit.zip
                self._zip = z
            else:
                raise BuildError('%s has neither %s nor stop_times.txt' % (path, TRAM_FOLDER))
        if not self.release:
            self.release = 'unknown'

    def rows(self, name):
        if self._dir:
            f = open(os.path.join(self._dir, name), encoding='utf-8-sig', newline='')
        else:
            f = io.TextIOWrapper(self._zip.open(name), encoding='utf-8-sig', newline='')
        with f:
            r = csv.reader(f)
            header = next(r)
            for row in r:
                if row:
                    yield dict(zip(header, row))

    def stop_time_rows(self):
        """Fast path for the big file: yields (trip_id, seq, stop_id, arr, dep, dist)."""
        if self._dir:
            f = open(os.path.join(self._dir, 'stop_times.txt'), encoding='utf-8-sig', newline='')
        else:
            f = io.TextIOWrapper(self._zip.open('stop_times.txt'), encoding='utf-8-sig', newline='')
        with f:
            r = csv.reader(f)
            h = next(r)
            ti, qi, si = h.index('trip_id'), h.index('stop_sequence'), h.index('stop_id')
            ai, di = h.index('arrival_time'), h.index('departure_time')
            ki = h.index('shape_dist_traveled') if 'shape_dist_traveled' in h else None
            for row in r:
                if row:
                    yield (row[ti], int(row[qi]), row[si], row[ai], row[di],
                           row[ki] if ki is not None else '')


def secs(t):
    h, m, s = t.strip().split(':')
    return int(h) * 3600 + int(m) * 60 + int(s)


def ymd(d):
    return d.strftime('%Y%m%d')


def parse_ymd(s):
    return dt.date(int(s[:4]), int(s[4:6]), int(s[6:8]))


# ── which services run ─────────────────────────────────────────────────────────
class Calendar:
    def __init__(self, g):
        self.base = {}
        for r in g.rows('calendar.txt'):
            days = [r[k] == '1' for k in ('monday', 'tuesday', 'wednesday', 'thursday',
                                           'friday', 'saturday', 'sunday')]
            self.base[r['service_id']] = (days, parse_ymd(r['start_date']), parse_ymd(r['end_date']))
        self.added = defaultdict(set)
        self.removed = defaultdict(set)
        for r in g.rows('calendar_dates.txt'):
            d = parse_ymd(r['date'])
            (self.added if r['exception_type'] == '1' else self.removed)[d].add(r['service_id'])
        starts = [v[1] for v in self.base.values()] + list(self.added)
        ends = [v[2] for v in self.base.values()] + list(self.added)
        self.first, self.last = min(starts), max(ends)
        self.dates = [self.first + dt.timedelta(n) for n in range((self.last - self.first).days + 1)]
        self.active = {d: self._active(d) for d in self.dates}
        n = Counter(s for d in self.dates for s in self.active[d])
        self.one_off = {s for s, c in n.items() if c <= ONE_OFF_MAX_DATES}

    def _active(self, d):
        out = set(self.added.get(d, ()))
        for s, (days, a, b) in self.base.items():
            if a <= d <= b and days[d.weekday()]:
                out.add(s)
        return out - self.removed.get(d, set())

    def regular(self, d):
        # special day: a one-off service runs, or a normal service is cancelled
        # (cancelling a one-off service on its off days is just how GTFS encodes it)
        removed = self.removed.get(d, set()) - self.one_off
        return bool(self.active[d]) and not removed and not (self.active[d] & self.one_off)

    def pick(self, ref):
        """Per weekday: (date used, services) for its next regular date on/after ref."""
        out = {}
        for w in range(7):
            later = [d for d in self.dates if d >= ref and d.weekday() == w and self.regular(d)]
            if later:
                out[w] = (later[0], frozenset(self.active[later[0]]), False)
            else:
                earlier = [d for d in self.dates if d.weekday() == w and self.regular(d)]
                if not earlier:
                    raise BuildError('no regular %s in the release' % DOW[w])
                out[w] = (earlier[-1], frozenset(self.active[earlier[-1]]), True)
        return out


# ── geometry helpers (Step 1b) ────────────────────────────────────────────────────
def _segments(line, lat, lng):
    """Per segment of a polyline [[lat,lng,dist],...]: (metres off, distance along) of the nearest point."""
    kx = math.cos(math.radians(lat)) * 111320.0
    ky = 110540.0
    out = []
    for i in range(len(line) - 1):
        a, b = line[i], line[i + 1]
        ax, ay = (a[1] - lng) * kx, (a[0] - lat) * ky
        bx, by = (b[1] - lng) * kx, (b[0] - lat) * ky
        dx, dy = bx - ax, by - ay
        L = dx * dx + dy * dy
        t = 0.0 if L == 0 else max(0.0, min(1.0, -(ax * dx + ay * dy) / L))
        px, py = ax + t * dx, ay + t * dy
        out.append((math.sqrt(px * px + py * py), a[2] + (b[2] - a[2]) * t))
    return out


def project(line, lat, lng):
    """Nearest point on the line: (metres off, distance along)."""
    return min(_segments(line, lat, lng))


def candidates(line, lat, lng, within):
    """Every place the line passes within `within` m of the point (a line that goes out
    and back passes a stop twice): sorted distances along, one per pass."""
    runs, cur = [], None
    for off, along in _segments(line, lat, lng):
        if off <= within:
            if cur is None or off < cur[0]:
                cur = (off, along) if cur is None else min(cur, (off, along))
        elif cur is not None:
            runs.append(cur[1])
            cur = None
    if cur is not None:
        runs.append(cur[1])
    return sorted(runs)


def along_line(ent, cands):
    """Stop distances measured along the route line, or None if the trip can't be placed.
    Stops before the first / after the last on-line stop (depot spurs) keep their own
    spacing; an off-line stop in the middle (a detour) leaves the trip as it is."""
    on = [bool(c) for c in cands]
    if not any(on):
        return None
    first = on.index(True)
    last = len(on) - 1 - on[::-1].index(True)
    if not all(on[first:last + 1]):
        return None
    for c0 in cands[first]:
        seq = [c0]
        for i in range(first + 1, last + 1):
            nxt = [c for c in cands[i] if c >= seq[-1] - 1]
            if not nxt:
                break
            seq.append(nxt[0])
        if len(seq) == last - first + 1:
            break
    else:
        return None
    out = [None] * len(ent)
    for k, i in enumerate(range(first, last + 1)):
        out[i] = max(seq[k], out[i - 1] if i > first else seq[k])
    for i in range(first - 1, -1, -1):
        out[i] = out[i + 1] - (ent[i + 1][2] - ent[i][2])
    for i in range(last + 1, len(ent)):
        out[i] = out[i - 1] + (ent[i][2] - ent[i - 1][2])
    return out, first


# ── build ─────────────────────────────────────────────────────────────────────────
def build(gtfs_path, ref, line_distances=False):
    g = Gtfs(gtfs_path)
    cal = Calendar(g)
    pick = cal.pick(ref)
    day_services = {
        'weekday': frozenset().union(*(pick[w][1] for w in range(5))),
        'saturday': pick[5][1],
        'sunday': pick[6][1],
    }
    wanted = frozenset().union(*day_services.values())

    routes = {r['route_id']: r['route_short_name'].strip() for r in g.rows('routes.txt')}
    trips_all = {}
    for t in g.rows('trips.txt'):
        trips_all[t['trip_id']] = (routes[t['route_id']], int(t['direction_id'] or 0),
                                   t['service_id'], t['shape_id'])
    trips = {tid: v for tid, v in trips_all.items() if v[2] in wanted}
    stops_raw = {}
    for s in g.rows('stops.txt'):
        if s.get('location_type', '') in ('', '0'):
            stops_raw[s['stop_id']] = (s['stop_name'], float(s['stop_lat']), float(s['stop_lon']))

    st = defaultdict(list)
    for tid, seq, sid, arr, dep, dist in g.stop_time_rows():
        if tid in trips_all:
            st[tid].append((seq, sid, arr, dep, dist))
    missing = [tid for tid in trips if tid not in st]
    if missing:
        raise BuildError('%d trips have no stop times (e.g. %s)' % (len(missing), missing[0]))

    # all trips of all services (signatures), for describing holiday copies
    entries = {}
    for tid, rows in st.items():
        rows.sort()
        start = secs(rows[0][3])
        d0 = float(rows[0][4]) if rows[0][4] else None
        ent = []
        for seq, sid, arr, dep, dist in rows:
            if sid not in stops_raw:
                raise BuildError('trip %s uses stop %s, which is not in stops.txt' % (tid, sid))
            if dist == '' or d0 is None:
                raise BuildError('trip %s has no shape_dist_traveled' % tid)
            ent.append([int(sid), secs(arr) - start, round(float(dist) - d0, 1)])
        entries[tid] = (start, ent)

    # route lines: most-used shape per (route, dir) among the selected trips
    use = Counter((r, d, sh) for tid, (r, d, svc, sh) in trips.items())
    best_shape = {}
    for (r, d, sh), n in sorted(use.items(), key=lambda kv: (kv[0][0], kv[0][1], -kv[1], kv[0][2])):
        best_shape.setdefault((r, d), sh)
    need = set(best_shape.values())
    pts = defaultdict(list)
    for p in g.rows('shapes.txt'):
        if p['shape_id'] in need:
            pts[p['shape_id']].append((int(p['shape_pt_sequence']), float(p['shape_pt_lat']),
                                       float(p['shape_pt_lon']), float(p['shape_dist_traveled'] or 0)))
    lines = {}
    for (r, d), sh in best_shape.items():
        pp = sorted(pts[sh])
        lines[(r, d)] = [[round(a[1], 6), round(a[2], 6), round(a[3], 1)] for a in pp]

    rebased = left = 0
    if line_distances:
        cache = {}
        for tid, (r, d, svc, sh) in trips.items():
            line = lines.get((r, d)) or lines.get((r, 0))
            if not line:
                continue
            start, ent = entries[tid]
            cands = []
            for e in ent:
                k = (r, d, e[0])
                if k not in cache:
                    nm, la, lo = stops_raw[str(e[0])]
                    cache[k] = candidates(line, la, lo, ON_LINE_M)
                cands.append(cache[k])
            res = along_line(ent, cands)
            if res is None:
                left += 1
                continue
            dists, first = res
            if abs(dists[first] - ent[first][2]) <= LINE_START_M:
                continue        # already agrees with the line (starts at its start)
            for e, v in zip(ent, dists):
                e[2] = round(v, 1)
            rebased += 1

    stops_dict = {sid: [round(la, 6), round(lo, 6)] for sid, (nm, la, lo) in stops_raw.items()}
    stops_dict = dict(sorted(stops_dict.items()))

    # per day type: route -> sorted trip dicts (shape index filled later)
    day_trips = {}
    for day, svcs in day_services.items():
        per = defaultdict(list)
        for tid, (r, d, svc, sh) in trips.items():
            if svc in svcs:
                start, ent = entries[tid]
                per[r].append({'id': tid, 'dir': d, 'sh': sh, 'start': start, 'stops': ent})
        for r in per:
            per[r].sort(key=lambda t: (t['start'], t['id']))
        day_trips[day] = per

    notes = []
    files = {}
    # weekday pieces
    wk = day_trips['weekday']
    pieces = [(f, [r for r in rl if r in wk]) for f, rl in WEEKDAY_PIECES]
    known = {r for f, rl in WEEKDAY_PIECES for r in rl}
    for r in sorted(set(wk) - known):
        sizes = [sum(len(wk[x]) for x in rl) for f, rl in pieces]
        i = sizes.index(min(sizes))
        pieces[i][1].append(r)
        notes.append('New route %s added to %s.' % (r, pieces[i][0]))
    shape_ix = {}
    for f, rl in pieces:
        out = {}
        for r in rl:
            arr = []
            for t in wk[r]:
                if t['sh'] not in shape_ix:
                    shape_ix[t['sh']] = len(shape_ix)
                arr.append({'id': t['id'], 'dir': t['dir'], 'sh': shape_ix[t['sh']],
                            'start': t['start'], 'stops': t['stops']})
            out[r] = arr
        files[f] = {'stops': stops_dict, 'trips': out}
    # weekend files
    for day, f in (('saturday', 'schedule_saturday.json'), ('sunday', 'schedule_sunday.json')):
        per = day_trips[day]
        order = [r for r in WEEKEND_ORDER if r in per] + sorted(set(per) - set(WEEKEND_ORDER))
        shapes, ix, out = [], {}, {}
        for r in order:
            arr = []
            for t in per[r]:
                if t['sh'] not in ix:
                    ix[t['sh']] = len(shapes)
                    shapes.append(t['sh'])
                arr.append({'id': t['id'], 'dir': t['dir'], 'sh': ix[t['sh']],
                            'start': t['start'], 'stops': t['stops']})
            out[r] = arr
        files[f] = {'stops': stops_dict, 'shapes': shapes, 'trips': out}

    # tram_network.json
    share = defaultdict(Counter)
    ntrips = Counter()
    for tid, (r, d, svc, sh) in trips.items():
        ntrips[r] += 1
        for e in entries[tid][1]:
            share[r][str(e[0])] += 1
    members = defaultdict(set)
    for r, c in share.items():
        for sid, n in c.items():
            if n / ntrips[r] >= ROUTE_STOP_SHARE:
                members[sid].add(r)
    net_routes = {}
    for r in sorted({r for r, d in lines}):
        net_routes[r] = {str(d): lines[(r, d)] for d in sorted(d for rr, d in lines if rr == r)}
    net_stops = {sid: {'n': nm, 'lat': round(la, 6), 'lng': round(lo, 6), 'r': sorted(members.get(sid, ()))}
                 for sid, (nm, la, lo) in sorted(stops_raw.items())}
    files[NETWORK_FILE] = {'routes': net_routes, 'stops': net_stops}

    info = {
        'release': g.release, 'first': cal.first, 'last': cal.last, 'ref': ref,
        'pick': pick, 'day_services': day_services, 'calendar': cal, 'base': cal.base,
        'trips': trips, 'trips_all': trips_all, 'entries': entries, 'rebased': rebased, 'left_off_line': left,
        'notes': notes, 'stops_raw': stops_raw, 'lines': lines,
    }
    return files, info


def serialise(name, obj):
    text = json.dumps(obj, separators=(',', ':'), ensure_ascii=False)
    if name == NETWORK_FILE:
        text += '\n'
    return text.encode('utf-8')


# ── checks and summary ──────────────────────────────────────────────────────────
def route_defs(repo):
    p = os.path.join(repo, 'index.html')
    if not os.path.exists(p):
        return None
    src = open(p, encoding='utf-8').read()
    m = re.search(r'const ROUTE_DEFS\s*=\s*\{(.*?)\n\};', src, re.S)
    if not m:
        return None
    return re.findall(r"^\s*'([0-9a-z]+)'\s*:\s*\{", m.group(1), re.M)


def load_prev(repo):
    prev = {}
    for f in SCHEDULE_FILES + [NETWORK_FILE]:
        p = os.path.join(repo, f)
        if os.path.exists(p):
            prev[f] = json.load(open(p, encoding='utf-8'))
    return prev


def day_of(f):
    return 'weekday' if 'weekday' in f else ('saturday' if 'saturday' in f else 'sunday')


def trip_sets(files_by_name):
    """day -> route -> {'dirstart': set, 'full': set} (viewer-style dedupe)."""
    out = defaultdict(lambda: defaultdict(lambda: {'dirstart': set(), 'full': set()}))
    for f, d in files_by_name.items():
        if f == NETWORK_FILE:
            continue
        for r, arr in d['trips'].items():
            o = out[day_of(f)][r]
            for t in arr:
                o['dirstart'].add((t['dir'], t['start']))
                o['full'].add((t['dir'], t['start'], tuple((s[0], s[1]) for s in t['stops'])))
    return out


def svc_label(cal, s):
    if s not in cal.base:
        return s
    days = [DOW[i] for i, on in enumerate(cal.base[s][0]) if on]
    if days == DOW[:4]:
        lab = 'Mon-Thu'
    elif len(days) > 1 and DOW.index(days[-1]) - DOW.index(days[0]) == len(days) - 1:
        lab = days[0] + '-' + days[-1]
    else:
        lab = '/'.join(days)
    return '%s (%s)' % (s, lab)


def check_and_summarise(files, info, repo, allow_large):
    errors, warnings = [], []
    blobs = {f: serialise(f, files[f]) for f in SCHEDULE_FILES + [NETWORK_FILE]}
    prev = load_prev(repo)
    cal = info['calendar']
    ref = info['ref']

    defs = route_defs(repo)
    if defs is None:
        warnings.append('Could not read ROUTE_DEFS from index.html; route presence not checked.')
    else:
        for day in ('weekday', 'saturday', 'sunday'):
            have = set()
            for f in SCHEDULE_FILES:
                if day_of(f) == day:
                    have |= {r for r, a in files[f]['trips'].items() if a}
            missing = [r for r in defs if r not in have]
            if missing:
                errors.append('%s: routes in ROUTE_DEFS with no trips: %s' % (day, ', '.join(missing)))
    for f, b in blobs.items():
        if len(b) > MAX_FILE_BYTES:
            errors.append('%s is %.1f MiB (limit %d MiB)' % (f, len(b) / 1048576, MAX_FILE_BYTES // 1048576))
        try:
            json.loads(b.decode('utf-8'))
        except Exception as e:
            errors.append('%s does not parse: %s' % (f, e))
    net_stops = files[NETWORK_FILE]['stops']
    bad = set()
    backwards = []
    odd_offsets = 0
    for f in SCHEDULE_FILES:
        for r, arr in files[f]['trips'].items():
            for t in arr:
                for s in t['stops']:
                    if str(s[0]) not in files[f]['stops'] or str(s[0]) not in net_stops:
                        bad.add(s[0])
                    if s[1] % 60:
                        odd_offsets += 1
                if any(t['stops'][i + 1][1] < t['stops'][i][1] for i in range(len(t['stops']) - 1)):
                    backwards.append(t['id'])
    if backwards:
        errors.append('%d trips have times going backwards (e.g. %s)' % (len(backwards), backwards[0]))
    if bad:
        errors.append('stops referenced but missing: %s' % ', '.join(map(str, sorted(bad))[:20]))
    if odd_offsets:
        warnings.append('%d stop times are not whole minutes (the collector bake expects whole minutes).' % odd_offsets)
    if info['last'] < ref + dt.timedelta(COVER_DAYS):
        errors.append('the release ends %s, less than %d days after %s' % (info['last'], COVER_DAYS, ref))
    for w, (d, svcs, fallback) in info['pick'].items():
        if fallback:
            warnings.append('No regular %s left in the release; used %s.' % (DOW[w], d))

    new_sets = trip_sets(files)
    old_sets = trip_sets({f: v for f, v in prev.items() if f != NETWORK_FILE}) if prev else None
    rows = []
    large = []
    routes_all = sorted({r for day in new_sets.values() for r in day} |
                        ({r for day in old_sets.values() for r in day} if old_sets else set()),
                        key=lambda x: (len(x), x))
    for r in routes_all:
        cells = []
        changed = False
        for day in ('weekday', 'saturday', 'sunday'):
            n = new_sets[day][r] if r in new_sets[day] else {'dirstart': set(), 'full': set()}
            if old_sets is None:
                cells.append('%d' % len(n['dirstart']))
                continue
            o = old_sets[day][r] if r in old_sets[day] else {'dirstart': set(), 'full': set()}
            nn, on = len(n['dirstart']), len(o['dirstart'])
            same = len({k[:2] for k in n['full'] & o['full']})
            if on and abs(nn - on) / on > COUNT_TOLERANCE:
                large.append('%s %s: %d -> %d trips' % (r, day, on, nn))
            if not on and nn:
                large.append('%s %s: new (%d trips)' % (r, day, nn))
            if on and not nn:
                large.append('%s %s: removed (%d trips)' % (r, day, on))
            if same != nn or nn != on:
                changed = True
            cells.append('%d → %d (%d same)' % (on, nn, same) if (on != nn or same != nn) else '%d (all same)' % nn)
        rows.append((r, cells, changed))
    if large:
        msg = 'Trip counts changed by more than %d%%: %s' % (round(COUNT_TOLERANCE * 100), '; '.join(large))
        (warnings if allow_large else errors).append(msg + (' (accepted with --allow-large-change)' if allow_large else ''))

    # stops and lines vs previous network file
    stop_lines = []
    if NETWORK_FILE in prev:
        po = prev[NETWORK_FILE]['stops']
        pn = files[NETWORK_FILE]['stops']
        added = sorted(set(pn) - set(po), key=int)
        removed = sorted(set(po) - set(pn), key=int)
        moved = []
        for sid in set(po) & set(pn):
            a, b = po[sid], pn[sid]
            k = math.cos(math.radians(a['lat'])) * 111320
            m = math.hypot((a['lng'] - b['lng']) * k, (a['lat'] - b['lat']) * 110540)
            if m > 20:
                moved.append((m, sid))
        moved.sort(reverse=True)
        stop_lines.append('- Added: %d%s' % (len(added), (' (' + ', '.join(added[:30]) + ')') if added else ''))
        stop_lines.append('- Removed: %d%s' % (len(removed), (' (' + ', '.join(removed[:40]) + ')') if removed else ''))
        stop_lines.append('- Moved more than 20 m: %d%s' % (len(moved), (' (largest: ' + ', '.join('%s %d m' % (s, m) for m, s in moved[:8]) + ')') if moved else ''))
        idx = os.path.join(repo, 'index.html')
        if removed and os.path.exists(idx):
            src = open(idx, encoding='utf-8').read()
            named = [s for s in removed if re.search(r"['\"]%s['\"]" % s, src)]
            if named:
                warnings.append('Removed stops named in index.html: %s' % ', '.join(named))
        pr = prev[NETWORK_FILE]['routes']
        for r, dirs in files[NETWORK_FILE]['routes'].items():
            for d, line in dirs.items():
                old = pr.get(r, {}).get(d)
                if old and abs(line[-1][2] - old[-1][2]) > 500:
                    warnings.append('Route %s direction %s line length %.1f km -> %.1f km (check the map preview).'
                                    % (r, d, old[-1][2] / 1000, line[-1][2] / 1000))
                if not old:
                    warnings.append('Route %s direction %s line is new.' % (r, d))
        for r, dirs in pr.items():
            for d in dirs:
                if d not in files[NETWORK_FILE]['routes'].get(r, {}):
                    warnings.append('Route %s direction %s line no longer in the timetable (dropped).' % (r, d))

    # holidays and other special dates from the build date to the end of the release
    sig = defaultdict(set)
    for tid, (r, d, svc, sh) in info['trips_all'].items():
        if tid not in info['entries']:
            continue
        start, ent = info['entries'][tid]
        sig[svc].add((r, d, start, tuple((e[0], e[1]) for e in ent)))
    hol = []
    for day in cal.dates:
        if day < ref or cal.regular(day):
            continue
        act = sorted(cal.active[day])
        parts = []
        for s in act:
            if s in cal.one_off:
                twin = [x for x in sig if x not in cal.one_off and sig[x] and sig[x] == sig.get(s)]
                parts.append('%s = copy of %s' % (s, svc_label(cal, twin[0])) if twin else '%s (own timetable)' % s)
            else:
                parts.append(svc_label(cal, s))
        rem = sorted(cal.removed.get(day, ()))
        hol.append('| %s %s | %s | %s |' % (DOW[day.weekday()], day.isoformat(), ', '.join(parts) or 'no service',
                                           ', '.join(rem) or '-'))
    fp = hashlib.sha256()
    for f in SCHEDULE_FILES + [NETWORK_FILE]:
        fp.update(f.encode() + b'\0' + blobs[f] + b'\0')
    fingerprint = fp.hexdigest()[:12]

    L = []
    L.append('## Timetable update: GTFS release %s' % info['release'])
    L.append('')
    L.append('- **Valid:** %s to %s. **Built for:** %s.' % (info['first'], info['last'], ref))
    for day in ('weekday', 'saturday', 'sunday'):
        L.append('- **%s uses:** %s' % (day.capitalize(), ', '.join(svc_label(cal, s) for s in sorted(info['day_services'][day]))))
    if info['rebased'] or info['left_off_line']:
        L.append('- **Line distances (Step 1b):** %d trips measured along the route line; %d left as they were (they leave the line).'
                 % (info['rebased'], info['left_off_line']))
    L.append('- **Output fingerprint:** `%s`' % fingerprint)
    L.append('')
    L.append('> **Until W2 Step 2 ships, merging needs a matching collector update. Ask Claude before you merge.**')
    L.append('')
    L.append('### Checks')
    if errors:
        L += ['- ❌ ' + e for e in errors]
    else:
        L.append('- ✅ All checks passed.')
    L += ['- ⚠️ ' + w for w in warnings]
    L += ['- ℹ️ ' + n for n in info['notes']]
    L.append('')
    L.append('### Trips per route (distinct direction + start, as the viewer counts them)')
    L.append('')
    L.append('| Route | Weekday | Saturday | Sunday |')
    L.append('|---|---|---|---|')
    for r, cells, changed in rows:
        L.append('| %s%s | %s |' % (r, ' *' if changed else '', ' | '.join(cells)))
    L.append('')
    L.append('`*` = differs from the current files. "same" = trips whose start, stops and times are unchanged; '
             'the rest are new or retimed. A lower count where every trip is "same" means copies left over '
             'from older timetable versions were dropped.')
    if stop_lines:
        L.append('')
        L.append('### Stops')
        L += stop_lines
    L.append('')
    L.append('### Special dates ahead (from the timetable calendar)')
    if hol:
        L.append('')
        L.append('| Date | Runs | Removed that day |')
        L.append('|---|---|---|')
        L += hol
    else:
        L.append('None in this release.')
    L.append('')
    L.append('### Files')
    L.append('')
    L.append('| File | Before | After |')
    L.append('|---|---|---|')
    for f in SCHEDULE_FILES + [NETWORK_FILE]:
        p = os.path.join(repo, f)
        before = '%.1f MB' % (os.path.getsize(p) / 1e6) if os.path.exists(p) else '-'
        L.append('| %s | %s | %.1f MB |' % (f, before, len(blobs[f]) / 1e6))
    summary = '\n'.join(L) + '\n'
    return errors, warnings, blobs, summary, fingerprint


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--gtfs', required=True)
    ap.add_argument('--repo', default='.')
    ap.add_argument('--out', default=None, help='write files here instead of --repo')
    ap.add_argument('--date', default=None)
    ap.add_argument('--summary', default=None)
    ap.add_argument('--allow-large-change', action='store_true')
    ap.add_argument('--line-distances', action='store_true')
    a = ap.parse_args(argv)
    if a.date:
        ref = parse_ymd(a.date)
    else:
        try:
            from zoneinfo import ZoneInfo
            ref = dt.datetime.now(ZoneInfo('Australia/Melbourne')).date()
        except Exception:
            ref = (dt.datetime.utcnow() + dt.timedelta(hours=10)).date()
    try:
        files, info = build(a.gtfs, ref, a.line_distances)
        errors, warnings, blobs, summary, fp = check_and_summarise(files, info, a.repo, a.allow_large_change)
    except Exception as e:      # BuildError, or anything unexpected in PTV's data
        what = str(e) if isinstance(e, BuildError) else '%s: %s' % (type(e).__name__, e)
        errors, summary, fp = [what], '## Timetable build failed\n\n- ❌ %s\n' % what, None
        blobs = {}
    if a.summary:
        open(a.summary, 'w', encoding='utf-8').write(summary)
    print(summary)
    if errors:
        print('BUILD FAILED: nothing written.', file=sys.stderr)
        return 1
    out = a.out or a.repo
    os.makedirs(out, exist_ok=True)
    for f, b in blobs.items():
        with open(os.path.join(out, f), 'wb') as fh:
            fh.write(b)
    print('Wrote %d files to %s (fingerprint %s).' % (len(blobs), out, fp))
    return 0


if __name__ == '__main__':
    sys.exit(main())
