"""Publication integrity and exact hull review; does not rerun row arithmetic."""
from pathlib import Path
from fractions import Fraction as F
from hashlib import sha256
from itertools import combinations, product
import argparse, json, tarfile

def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('packet', type=Path)
    ap.add_argument('archive', type=Path)
    ap.add_argument('output', type=Path)
    a = ap.parse_args()
    root = a.packet.resolve()
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    assert manifest['new_original_cells'] == manifest['new_masks'] == 0
    assert manifest['standalone_portable'] is False
    source_copies = 0
    for entry in manifest['files']:
        assert digest(root / entry['path']) == entry['sha256']
        if 'source_path' in entry:
            assert digest(entry['source_path']) == entry['sha256']
            source_copies += 1
        assert (root / entry['path']).stat().st_size == entry['bytes']
    members = {}
    with tarfile.open(a.archive, 'r:xz') as tar:
        for member in tar:
            assert not member.issym() and not member.islnk()
            p = Path(member.name)
            assert not p.is_absolute() and '..' not in p.parts
            if member.isdir():
                continue
            assert member.isfile() and p.parts[0] == root.name
            rel = str(p.relative_to(root.name))
            assert rel not in members
            data = tar.extractfile(member).read()
            members[rel] = sha256(data).hexdigest()
            assert data == (root / rel).read_bytes()
    on_disk = {str(p.relative_to(root)): digest(p) for p in root.rglob('*') if p.is_file()}
    assert members == on_disk
    report = json.loads((root / 'reports/fresh_whole_state_replay.json').read_text())
    assert report['status'] == 'PASS_FRESH_WHOLE_C887_COMPLETE_DG_UNION_BOUNDS'
    assert report['whole_original_excluded'] is False
    assert report['old_starting_state_implied'] and not report['old_state_interval_deficits']
    assert report['missing_archived_bound_state_assumed'] is False
    dependencies = dict(report['input_sha256'])
    dependencies.update(report['initial_original_bounds']['local_transport']['input_sha256'])
    for filename, expected in dependencies.items():
        assert digest(filename) == expected
    dm = json.loads((root / 'records/dg8/MANIFEST.original.json').read_text())
    expected = [list(x) for x in product((3, 6), (0, 1), (-1, 1))]
    assert dm['alternatives'] == expected and len(dm['children']) == 8
    survivors = []
    for k, (entry, choice) in enumerate(zip(dm['children'], expected)):
        p = root / 'records/dg8' / entry['file']
        assert digest(p) == entry['sha256']
        rec = json.loads(p.read_text())
        assert entry['choice'] == choice and entry['index'] == k
        assert rec['status'] == entry['status']
        if rec['status'] == 'OPEN':
            survivors.append(rec['final'])
        else:
            assert rec['status'] == 'CANDIDATE_CLOSED'
    assert len(survivors) == 4
    parent = dm['initial']
    actual = report['certified_state']
    target = json.loads((root / 'bindings/old_starting_state.json').read_text())['state']
    assert parent['id'] == actual['id'] == target['id'] == 'negative-887236b78100baf3'
    assert parent['path'] == actual['path'] == target['path']
    checked = strict = 0
    def check_interval(before, values, literal, goal):
        nonlocal checked, strict
        lo = max(F(before[0]), min(F(v[0]) for v in values))
        hi = min(F(before[1]), max(F(v[1]) for v in values))
        assert lo <= hi and [lo, hi] == list(map(F, literal))
        gl, gu = map(F, goal)
        assert gl <= lo <= hi <= gu
        checked += 1
        strict += gl < lo or hi < gu
    for field, size in (('angles', 9), ('positions', 18), ('scalar', 36)):
        assert len(parent[field]) == len(actual[field]) == len(target[field]) == size
        for k in range(size):
            check_interval(parent[field][k], [v[field][k] for v in survivors], actual[field][k], target[field][k])
    pairs = set(combinations(range(9), 2))
    for field in ('differences', 'diagonal'):
        tables = []
        for v in [parent, *survivors, actual, target]:
            table = {tuple(e['pair']): e['intervals'] for e in v[field]}
            assert len(v[field]) == len(table) == 36 and set(table) == pairs
            tables.append(table)
        for pair in sorted(pairs):
            for axis in (0, 1):
                check_interval(tables[0][pair][axis], [t[pair][axis] for t in tables[1:5]], tables[5][pair][axis], tables[6][pair][axis])
    assert checked == 207 and strict == 165
    result = dict(status='PASS_PUBLICATION_INTEGRITY_AND_EXACT_HULL_REVIEW',
        archive_sha256=digest(a.archive), archive_bytes=a.archive.stat().st_size,
        archive_members_checked=len(members), source_copies_checked=source_copies,
        existing_native_dependencies_rehashed=len(dependencies),
        complete_dg_alternatives=8, excluded_alternatives=4, surviving_alternatives=4,
        target_intervals_independently_checked=checked, strictly_tighter_intervals=strict,
        fresh_row_arithmetic_rerun_by_this_review=False,
        exact_row_replay_evidence='reports/fresh_whole_state_replay.json',
        whole_original_excluded=False, standalone_portable=False,
        new_original_cells=0, new_masks=0,
        no_missing_archive_assumed=True, lean_lake_ci_run=False)
    a.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()
