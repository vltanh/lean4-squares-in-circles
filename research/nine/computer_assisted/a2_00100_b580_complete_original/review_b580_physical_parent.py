"""Source-bound original-domain pre-review; no exclusion or arithmetic credit."""
from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
import ast
import json

REPO = Path('/workspace/scratch/6b34cccf3741/repo')
W = REPO / 'research/nine/.runs/closure_20261104'
N = W / 'b_native/b_family_native_discovery_checkpoint_v1/native'
OUT = Path('/workspace/scratch/6b34cccf3741/a_work')
bindings = {}

def bind(p, expected=None):
    p = Path(p)
    h = sha256(p.read_bytes()).hexdigest()
    if expected is not None:
        assert h == expected, (p, h, expected)
    bindings[str(p)] = h
    return h

def read(p, expected=None):
    bind(p, expected)
    return json.loads(Path(p).read_text())

target = 'negative-580db3624cf4c2e2'
path = [['angle', 3, 0], ['angle_cut', [0, '0'], 0],
        ['position_cut', [11, '1/2'], 1], ['f_side_escape', [5, 7], [4]]]
parent = read(N / 'whole_B_roots' / (target + '.json'),
              'a9ac5ea57c4a74e39f413fdfe5c8e054453874fe9decdf2d1e9d49c510d27bf3')
assert parent['id'] == target and parent['path'] == path
assert target == 'negative-' + sha256(json.dumps(path, separators=(',', ':')).encode()).hexdigest()[:16]
assert parent['scope'] == 'WHOLE_UNCHANGED_ORIGINAL_PARENT' and parent['status'] == 'OPEN'
assert parent['all_nine_originals_retained'] and parent['all_original_corners_and_pairs_retained'] and parent['strict_CD_retained']
assert parent['original_cells_closed'] == parent['masks_closed'] == 0
state = parent['final']
assert state['id'] == target and state['path'] == path
assert len(state['angles']) == 9 and len(state['positions']) == 18 and len(state['scalar']) == 36
assert state['angles'] == [['-1', '0'] if i in (0, 3) else ['-1', '1'] for i in range(9)]
assert state['positions'][11] == ['1/2', '91/60']
assert all(F(state['scalar'][i][0]) > 0 for i in range(9))

register = N / 'b16a_I32_complete_H_checkpoint/ancestry/legacy/current_proof/original_register.json'
frozen = read(register, 'ea000e84c04675fe22424e5c20d3df9d735d659065349800aef2699170bff604')
current = read(REPO / 'research/nine/gates/A2_00100_FIXED_FRONTIER.json')
fields = ('id', 'sign', 'baseline_frontier_index', 'path')
def definitions(data):
    cells = data['cells']
    assert len(cells) == 231 and len({c['id'] for c in cells}) == 231
    return {c['id']: {k: c[k] for k in fields} for c in cells}
assert definitions(frozen) == definitions(current)
for data in (frozen, current):
    cell = next(c for c in data['cells'] if c['id'] == target)
    assert cell['status'] == 'OPEN' and cell['path'] == path
    assert cell['sign'] == 'negative' and cell['baseline_frontier_index'] == 68

geometry = N / 'b16a_I32_complete_H_checkpoint/ancestry/legacy/current_proof/shared_capacity_three_b_v4/geometry/weak_outer_numeric_strict_bulk_v14_verify.py'
bind(geometry)
text = geometry.read_text()
syntax = ast.parse(text)
fn = next(n for n in syntax.body if isinstance(n, ast.FunctionDef) and n.name == 'f_side_escape_rows')
env = {}
exec(compile(ast.Module(body=[fn], type_ignores=[]), str(geometry), 'exec'), env)
rows = env['f_side_escape_rows']((5, 7), 4, F(3, 5))
def canon(row):
    co, rhs = row
    combined = {}
    for k, v in co:
        combined[k] = combined.get(k, F(0)) + v
    return sorted((k, str(v)) for k, v in combined.items() if v), str(rhs)
expected = [([(10, 1), (14, -1)], 0), ([(7, 1), (11, -1)], -F(3, 5))]
assert list(map(canon, rows)) == list(map(canon, expected))
edge_assignment = next(n for n in syntax.body if isinstance(n, ast.Assign)
                       and any(isinstance(t, ast.Name) and t.id == 'EDGES' for t in n.targets))
assert ast.literal_eval(edge_assignment.value) == ((0, 1, 0), (1, 2, 0), (2, 3, 1), (4, 5, 0), (5, 6, 0))
assert "add([(14,1),(16,-1)],0,'extras_x_order')" in text
assert "add([(5,1),(7,-1)],-F(2,3),'remaining_bulk_transverse_two_thirds')" in text
assert "add([(6,1),(4,-1),(AL(2),-F(1,2)),(AB(2),-F(1,2)),(AL(3),-F(1,2)),(AB(3),-F(1,2))],0,'CD_weak')" in text
bind(N / 'source/verify_b_registered_originals.py', '6286316f6c671fc1665556ac3c6ddb984a0cd2d12034a3de3c801f3cdecb8376')
bind(N / 'source/independent_b_whole_domain.py', '0c692207bad5cf34fe9b02ad8c32a8dbc59bd8a3db45b692a8dc6737c7dca523')
bind(__file__)
report = dict(status='PASS_B580_ORIGINAL_PHYSICAL_DOMAIN_PRE_REVIEW',
              original_id=target, original_path=path, baseline_frontier_index=68,
              original_status='OPEN', all_231_definition_tuples_unchanged=True,
              literal_f_side_branch=4, literal_escape_rows=[canon(r) for r in rows],
              no_predecessor_height_rows_in_local_branch0=True,
              fixed_normalization=['x_H <= x_I', 'y_D-y_C > 2/3 after accepted low-gap exclusion and common reflection'],
              path_halfspaces=['t_A in [-1,0]', 't_D in [-1,0]', 'y_F >= 1/2', 'x_F <= x_H', 'y_D-y_F <= -3/5'],
              immediate_original_center_consequences=['x_F <= x_H <= x_I', 'y_F-y_D >= 3/5'],
              H_I_permutation_transport_assumed=False,
              all_nine_original_labels_retained=True, strict_CD_caller_retained=True,
              target='q < 1105/256; necessary corner inequalities may be weakened to closed Q',
              arithmetic_replayed=False, tree_or_terminal_table_reviewed=False,
              complete_original_exclusion_claimed=False, original_credit=0, mask_credit=0,
              blocking_findings=[], source_sha256=bindings)
(OUT / 'B580_ORIGINAL_PHYSICAL_PRE_REVIEW.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({k: v for k, v in report.items() if k != 'source_sha256'}, indent=2))

