"""Read-only source attachment audit; does not repeat scalar cover arithmetic."""
from pathlib import Path
from hashlib import sha256, sha1
import json
import sys

if not __debug__:
    raise RuntimeError('Assertions are required')

W = Path('/workspace/scratch/f9f48fcfb253')
P = W / 'd_work/actual_ab_743b_review'
OUT = Path(__file__).resolve().parent

def digest(p):
    return sha256(p.read_bytes()).hexdigest()

receipt = P / 'GIT_RESTORATION_RECEIPT.json'
assert digest(receipt) == 'd350c77c8e2a9f0644e5ac36a3df78047a1e83f41d9226c888996c347e916260'
restored = json.loads(receipt.read_text())
assert restored['commit'] == '743b768c3de1853b8524be8bba4064c5735e9cbc'
files = {}
for rel, expected in restored['files'].items():
    path = P / rel
    data = path.read_bytes()
    assert len(data) == expected['bytes']
    assert sha256(data).hexdigest() == expected['sha256']
    assert sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == expected['git_blob']
    files[rel] = expected
assert len(files) == 70 and sum(x['bytes'] for x in files.values()) == 230971

premises = {}
reports = []
for name, cover, leaf_count, coefficient_count in (
        ('actual_AB_two_link_row_064_v1', 'cover_0641', 121, 15125),
        ('universal_actual_AB_two_link_v1', 'cover', 351, 43875)):
    folder = P / 'research/nine/computer_assisted' / name
    for item in json.loads((folder / 'PREMISE_BINDINGS.json').read_text())['files']:
        candidates = [W / 'repo' / item['path'],
                      W / 'd_work/reset_sources_d989c83/sources' / item['sha256']]
        existing = [p for p in candidates if p.is_file() and digest(p) == item['sha256']]
        assert existing, item
        premises[item['path']] = {'sha256': item['sha256'], 'checked_at': str(existing[0])}
    manifest = json.loads((folder / cover / 'MANIFEST.json').read_text())
    report = json.loads((folder / 'EXACT_SCALAR_REPLAY.json').read_text())
    assert report['status'] == 'PASS_COMPLETE_EXACT_TWO_LINK_SCALAR_COVER'
    assert report['domains'] == 28 and report['leaves'] == leaf_count
    assert report['bernstein_coefficients'] == coefficient_count and report['frontier'] == 0
    assert report['strict_except_all_zero'] is True
    assert report['physical_lifting_separately_required'] is True
    assert report['new_original_cells'] == report['new_masks'] == 0
    assert len(manifest['domains']) == len(report['audits']) == 28
    assert {x['file'] for x in manifest['domains']} == {x['file'] for x in report['audits']}
    for a in report['audits']:
        assert digest(folder / cover / a['file']) == a['sha256']
    reports.append({'package': name, 'delivered_report_sha256': digest(folder / 'EXACT_SCALAR_REPLAY.json'),
                    'domains': 28, 'leaves': leaf_count, 'coefficients': coefficient_count,
                    'fresh_arithmetic_repeated_here': False})

result = {
    'status': 'PASS_INDEPENDENT_PHYSICAL_SOURCE_AND_SCOPE_REVIEW',
    'commit': restored['commit'],
    'source_audit_script_sha256': digest(Path(__file__)),
    'hand_review_sha256': digest(OUT / 'INDEPENDENT_PHYSICAL_REVIEW.md'),
    'git_restoration_receipt_sha256': digest(receipt),
    'exact_source_members': files,
    'inherited_premises': premises,
    'delivered_reports_checked': reports,
    'all_seven_selected_originals_distinct': True,
    'all_nine_caller_preserved': True,
    'strict_011_application_has_no_closed_Q_claim': True,
    'full_scalar_cover_replayed_here': False,
    'new_runtime_installation': False,
    'new_original_cells': 0,
    'new_masks': 0,
}
out = OUT / 'INDEPENDENT_PHYSICAL_REVIEW.json'
with out.open('x') as f:
    json.dump(result, f, indent=2, sort_keys=True)
    f.write('\n')
print(json.dumps({'status': result['status'], 'members': len(files), 'premises': len(premises),
                  'report': str(out), 'sha256': digest(out)}))
