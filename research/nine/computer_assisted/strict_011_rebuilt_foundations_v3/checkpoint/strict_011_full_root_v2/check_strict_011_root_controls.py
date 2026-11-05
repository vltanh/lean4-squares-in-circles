#!/usr/bin/env python3
"""Exact root, literal-row, residual, caller, and closed-cover controls.

Uses no numerical solver.  The weighted example is an explicitly constructed
three-row proof inside one proxy child; it claims no excluded domain.
"""
import argparse
import ast
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import strict_011_root as P
import independent_strict_011_adapter as I


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(name, path, expected):
    assert sha(path) == expected
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def printed(rows, indices=None):
    indices = range(len(rows)) if indices is None else sorted(indices)
    return [dict(index=k, name=rows[k][2],
                 coefficients=[[j, str(value)] for j, value in rows[k][0]],
                 rhs=str(rows[k][1])) for k in indices]


def family(row):
    return row[2].split(':')[1]


def check_rows(state, select=None):
    rows, bounds, current, terminal = P.collect(state)
    assert terminal is None
    indices = list(range(len(rows))) if select is None else [k for k, row in enumerate(rows) if select(row)]
    reconstructed, checked_bounds, independent_state = I.Adapter.rebuild(state, printed(rows, indices))
    assert bounds == checked_bounds and current == independent_state
    assert reconstructed == {k: rows[k] for k in indices}
    return len(indices), rows, bounds, current


def zero_record(state):
    return dict(initial=P.state_view(state), rounds=[], status='OPEN', final=P.state_view(state))


def unit_frame(halfangle):
    t = F(halfangle)
    answer = (1-t*t)/(1+t*t), 2*t/(1+t*t)
    assert answer[0]**2+answer[1]**2 == 1 and answer[0] >= abs(answer[1])
    return answer


def point(centers, frames, state=None):
    assert len(centers) == len(frames) == 9
    values = [F(z) for center in centers for z in center]
    values += [a for a, b in frames] + [b for a, b in frames]
    values += [abs(b) for a, b in frames] + [1/(2*(a+abs(b))) for a, b in frames]
    if state is not None:
        for pair, kind, choice in state['choices']:
            if kind != 'sat':
                continue
            i, j = pair
            owner, axis, sign = choice
            a, b = frames[owner]
            nx, ny = (sign*a, sign*b) if axis == 0 else (-sign*b, sign*a)
            ai, bi = frames[i]
            aj, bj = frames[j]
            values += [nx*(centers[j][0]-centers[i][0]), ny*(centers[j][1]-centers[i][1]),
                       ai*aj, bi*bj, ai*bj, bi*aj]
    return tuple(values)


def slack(row, values):
    return row[1]-sum(coefficient*values[k] for k, coefficient in row[0])


def corner_norms(center, frame):
    x, y = center
    a, b = frame
    return [((x+(e*a-t*b)/2)**2+(y+(e*b+t*a)/2)**2)
            for e, t in product((-1, 1), repeat=2)]


def pair_alternatives(centers, frames, pair):
    i, j = pair
    dx, dy = centers[j][0]-centers[i][0], centers[j][1]-centers[i][1]
    ai, bi = frames[i]
    aj, bj = frames[j]
    required = (1+abs(ai*aj+bi*bj)+abs(ai*bj-bi*aj))/2
    result = []
    for owner, axis, sign in product(pair, (0, 1), (-1, 1)):
        a, b = frames[owner]
        nx, ny = (sign*a, sign*b) if axis == 0 else (-sign*b, sign*a)
        if nx*dx+ny*dy >= required:
            result.append((owner, axis, sign))
    return result


def check_marked(centers, frames, labels, mask, normal=(F(1), F(0))):
    assert len(labels) == 9 and sorted(labels) == list(range(9))
    p, q = normal
    assert p*p+q*q > 0
    widths = [(abs(p*a+q*b)+abs(-p*b+q*a))/2 for a, b in frames]
    for (left, right), bit in zip(((0, 1), (1, 2), (2, 3), (4, 5), (5, 6)), mask.replace('/', '')):
        i, j = labels[left], labels[right]
        dx, dy = centers[j][0]-centers[i][0], centers[j][1]-centers[i][1]
        along, transverse = p*dx+q*dy, -q*dx+p*dy
        assert along >= abs(transverse)
        if bit == '0':
            assert along >= widths[i]+widths[j]
        else:
            assert along < widths[i]+widths[j]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, default=HERE.parents[1])
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--snapshots', type=Path)
    args = parser.parse_args()
    started = time.monotonic()
    workspace = args.workspace.resolve()
    generic_path = workspace/'b_work/independent_physical_sat_replay.py'
    proxy_path = workspace/'b_work/independent_physical_proxy_cover.py'
    G = load('strict011_frozen_generic_core', generic_path,
             '1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc')
    X = load('strict011_frozen_proxy_core', proxy_path,
             '3b46b8a966c712e23894ae4cd7964355730f2bfe3c58a04871ade9d35ddf1277')
    source_paths = [Path(P.__file__), Path(I.__file__), Path(__file__), generic_path, proxy_path]
    source_hashes = {str(p): sha(p) for p in source_paths}
    for path in (Path(P.__file__), Path(I.__file__)):
        syntax = ast.parse(path.read_text())
        for node in ast.walk(syntax):
            if isinstance(node, ast.Import):
                assert all(n.name in {'copy', 'fractions', 'itertools', 'math'} for n in node.names)
            elif isinstance(node, ast.ImportFrom):
                assert node.module in {'copy', 'fractions', 'itertools', 'math'}
    document = P.root_document()
    root = I.verify_root(document)
    assert root == P.fresh_state()
    root_count, baseline, bounds, propagated = check_rows(root)
    assert root_count == 1757 and len(bounds) == 54 and len(P.DIRECTIONS) == 32
    family_counts = {}
    for row in baseline:
        family_counts[family(row)] = family_counts.get(family(row), 0)+1
    assert family_counts['corner'] == 36*32 and family_counts['distance'] == 36

    damaged = []
    def reject(name, callback):
        try:
            callback()
        except (AssertionError, ValueError, KeyError, IndexError, TypeError):
            damaged.append(name)
        else:
            raise AssertionError('Damaged control was accepted: '+name)

    mutations = []
    for key, value in [('mask', '001/00'), ('radius_mode', 'closed'), ('target_q', '17/4'),
                       ('original_id', 'positive-821c9a2debeed0aa'),
                       ('extra_normalizations', ['theta_D>=0']),
                       ('inherited_001_premises', ['G above D']),
                       ('inherited_original_cells', ['registered001cell']),
                       ('installed_conditional_terminals', ['unproved_guard']),
                       ('whole_mask_credit', 1)]:
        bad = deepcopy(document); bad[key] = value
        mutations.append((key, bad))
    for key in ('original_corners', 'original_pairs', 'physical_originals', 'exact_mask_edges', 'owned_pair_cover'):
        bad = deepcopy(document); bad[key].pop()
        mutations.append(('omitted '+key, bad))
    bad = deepcopy(document); bad['initial']['angles'][3] = ['0', '1']
    mutations.append(('unproved endpoint sign in initial box', bad))
    bad = deepcopy(document); bad['initial']['path'] = [['angle', 3, 1]]
    mutations.append(('old registered path', bad))
    bad = deepcopy(document); bad['initial']['positions'][14] = ['-1', '0']
    mutations.append(('extra H position restriction', bad))
    bad = deepcopy(document); bad['exact_mask_edges'][1]['bit_relation'] = 'xj-xi >= hi+hj'
    mutations.append(('actual BC substituted', bad))
    bad = deepcopy(document); bad['extra_hidden_condition'] = 'x_H<=x_I'
    mutations.append(('extra hidden condition', bad))
    for name, bad in mutations:
        reject('caller: '+name, lambda bad=bad: I.verify_root(bad))

    sat_literals = proxy_literals = 0
    physical_sat_residuals = 0
    all_pairs = list(combinations(range(9), 2))
    halves = [F(-2, 5), F(-1, 3), F(-1, 5), F(0), F(1, 5), F(1, 3), F(2, 5)]
    for pair_index, pair in enumerate(all_pairs):
        i, j = pair
        for choice in product(pair, (0, 1), (-1, 1)):
            state = P.physical_child(root, 'sat', pair, choice)
            count, rows, _, current = check_rows(state, lambda row:
                (family(row) == 'bound' and int(row[2].split(':')[2]) >= 54)
                or family(row) in {'mccormick', 'separation', 'projection_floor', 'relative_cosine', 'relative_sine'})
            sat_literals += count
            frames = [unit_frame(0) for _ in range(9)]
            frames[i] = unit_frame(halves[pair_index % len(halves)])
            frames[j] = unit_frame(halves[(pair_index+3) % len(halves)])
            owner, axis, sign = choice
            a, b = frames[owner]
            normal = (sign*a, sign*b) if axis == 0 else (-sign*b, sign*a)
            centers = [(F(0), F(0)) for _ in range(9)]
            centers[i] = (-normal[0], -normal[1]); centers[j] = normal
            values = point(centers, frames, current)
            assert choice in pair_alternatives(centers, frames, pair)
            assert max(abs(centers[j][axis]-centers[i][axis]) for axis in (0, 1)) >= values[45+i]+values[45+j]
            descriptors, intervals = I.selected_products(current)
            for row in rows:
                if family(row) in {'mccormick', 'separation', 'projection_floor', 'relative_cosine', 'relative_sine'}:
                    assert slack(row, values) >= 0, row[2]
                    physical_sat_residuals += 1
                if family(row) == 'mccormick':
                    _, _, slot, offset, plane = row[2].split(':')
                    U, V, (ul, uu), (vl, vu) = descriptors[int(slot)][2][int(offset)]
                    u = sum(c*values[k] for k, c in U)
                    v = sum(c*values[k] for k, c in V)
                    residual = ((u-ul)*(v-vl), (u-uu)*(v-vu), (uu-u)*(v-vl), (u-ul)*(vu-v))[int(plane)]
                    assert residual == slack(row, values) >= 0
        for choice in product((0, 1), (-1, 1)):
            state = P.physical_child(root, 'proxy', pair, choice)
            count, _, _, _ = check_rows(state, lambda row: family(row) == 'proxy')
            proxy_literals += count
    assert sat_literals == 288*45 and proxy_literals == 144
    print(json.dumps({'checkpoint': 'ALL_288_SAT_AND_144_PROXY_LITERALS_PASS',
                      'sat_rows': sat_literals, 'mccormick_and_sat_physical_rows': physical_sat_residuals}), flush=True)

    angle_literals = 0
    for original in range(9):
        for cut in (F(-2, 3), F(0), F(1, 5)):
            for side in (0, 1):
                state = P.angle_child(root, original, cut, side)
                assert state == I.angle_child(root, original, cut, side)
                angle_literals += check_rows(state)[0]
    # A certified scalar sign can be stronger than an angle interval.  The
    # absolute-value upper row must use that sign, not a crossed-angle chord.
    sign_literals = 0
    for lower, upper in ((F(1, 8), F(1, 4)), (F(-1, 4), F(-1, 8)), (F(0), F(0))):
        state = deepcopy(root)
        scalar = list(state['scalar']); scalar[9] = (lower, upper); state['scalar'] = tuple(scalar)
        n, rows, _, _ = check_rows(state)
        sign_literals += n
        assert any(row[2] == f'strict011v2:absolute_upper:0:{1 if lower >= 0 else -1}' for row in rows)

    interval_checks = 0
    for halfangle in halves:
        a, b = unit_frame(halfangle)
        slope = b/a
        for interval in ((F(-1), F(1)), (slope, slope), (min(F(0), slope), max(F(0), slope))):
            box = [interval]*9
            assert P.analytic(box) == I.analytic(box)
            true = [a]*9+[b]*9+[abs(b)]*9+[1/(2*(a+abs(b)))]*9
            for value, (lower, upper) in zip(true, I.analytic(box)):
                assert lower <= value <= upper
                interval_checks += 1
    for endpoint in (F(-1), F(1)):
        ranges = I.analytic([(endpoint, endpoint)]*9)
        # Symbolic diagonal endpoint: alpha=|beta|=sqrt(1/2), g=sqrt(1/8).
        for k, square in ((0, F(1, 2)), (18, F(1, 2)), (27, F(1, 8))):
            lower, upper = ranges[k]
            assert lower >= 0 and lower*lower <= square <= upper*upper
            interval_checks += 1
        beta_lower, beta_upper = ranges[9]
        if endpoint < 0:
            assert beta_lower <= beta_upper < 0 and beta_upper**2 <= F(1, 2) <= beta_lower**2
        else:
            assert 0 < beta_lower <= beta_upper and beta_lower**2 <= F(1, 2) <= beta_upper**2
        interval_checks += 1

    # Exact physical single-square residual identities, with full signed beta.
    single_checks = 0
    universal_families = {'bound', 'fold', 'absolute_lower', 'width_floor', 'slope',
        'width_interval', 'absolute_chord', 'absolute_upper', 'unit_secant', 'unit_support',
        'inset_tangent', 'inset_secant', 'center_support', 'corner'}
    one_rows = [row for row in baseline if family(row) in universal_families
                and (family(row) != 'bound' or int(row[2].split(':')[2]) in (0, 1, 18, 27, 36, 45))
                and (family(row) == 'bound' or row[2].split(':')[2] == '0')]
    for halfangle in halves:
        frame = unit_frame(halfangle)
        for center in product((F(-1), F(-1, 2), F(0), F(1, 2), F(1)), repeat=2):
            if max(corner_norms(center, frame)) > P.Q:
                continue
            values = point([center]*9, [frame]*9)
            for row in one_rows:
                assert slack(row, values) >= 0, row[2]
                single_checks += 1
                if family(row) == 'inset_tangent':
                    sigma = F(row[2].split(':')[-1]); s = frame[0]+abs(frame[1])
                    assert slack(row, values) == (s-sigma)**2/(2*s*sigma*sigma)
                elif family(row) == 'inset_secant':
                    s = frame[0]+abs(frame[1]); low, high = I.frame_width_interval((-F(1), F(1)))
                    assert slack(row, values) == (s-low)*(high-s)/(2*low*high*s)
                elif family(row) == 'unit_secant':
                    variable = int(row[2].split(':')[-1])
                    low, high = propagated['scalar'][0]
                    vl, vu = (propagated['positions']+propagated['scalar'])[variable]
                    assert slack(row, values) == (values[18]-low)*(high-values[18])+(values[variable]-vl)*(vu-values[variable])

    # All complete physical covers stay OPEN in these zero-round fixtures.
    cover_counts = dict(sat_unions=0, proxy_unions=0, angle_unions=0)
    for pair in all_pairs:
        children = [(choice, zero_record(P.physical_child(root, 'sat', pair, choice)))
                    for choice in product(pair, (0, 1), (-1, 1))]
        audit, survivors = G.check_complete_cover(root, pair, children, I.Adapter())
        assert len(survivors) == 8 and audit['excluded_alternatives'] == 0
        cover_counts['sat_unions'] += 1
        children4 = [(choice, zero_record(P.physical_child(root, 'proxy', pair, choice)))
                     for choice in product((0, 1), (-1, 1))]
        audit, survivors = X.check_complete_proxy_cover(root, pair, children4, I.Adapter(), G.check_record)
        assert len(survivors) == 4 and audit['excluded_alternatives'] == 0
        cover_counts['proxy_unions'] += 1
    for original in range(9):
        children2 = [(side, zero_record(P.angle_child(root, original, 0, side))) for side in (0, 1)]
        audit, survivors = I.check_complete_angle_cover(root, original, 0, children2, G.check_record)
        assert len(survivors) == 2
        assert all(state['angles'][original][side == 0] == 0 for side, state in survivors)
        cover_counts['angle_unions'] += 1
    reject('SAT omitted boundary alternative', lambda: G.check_complete_cover(root, pair, children[:-1], I.Adapter()))
    reject('SAT duplicate alternative', lambda: G.check_complete_cover(root, pair, children[:-1]+children[:1], I.Adapter()))
    reject('proxy omitted alternative', lambda: X.check_complete_proxy_cover(root, pair, children4[:-1], I.Adapter(), G.check_record))
    reject('angle omitted half', lambda: I.check_complete_angle_cover(root, 8, 0, children2[:1], G.check_record))
    reject('angle duplicate half', lambda: I.check_complete_angle_cover(root, 8, 0, children2[:1]*2, G.check_record))

    # Construct one real rational bound certificate without invoking an LP.
    child = P.physical_child(root, 'proxy', (0, 1), (0, 1))
    rows, bound, before, terminal = P.collect(child)
    required = {'strict011v2:proxy:0:1:0:1', 'strict011v2:bound:45:-1', 'strict011v2:bound:46:-1'}
    indices = {k for k, row in enumerate(rows) if row[2] in required}
    assert len(indices) == 3
    weights = [[k, 1 << 40] for k in sorted(indices)]
    proved = -before['scalar'][27][0]-before['scalar'][28][0]
    upper = G.ceiling_grid(proved)
    objective = [[2, -1], [0, 1]]
    proposal = dict(kind='difference', key=[0, 1, 0], sign=-1, objective=objective,
        weights=weights, summed_rhs=str(proved), residual_coefficients=[],
        residual_correction='0', proved_upper=str(proved), upper=str(upper))
    after = deepcopy(before)
    old = after['differences'][0, 1]
    after['differences'][0, 1] = ((max(old[0][0], -upper), old[0][1]), old[1])
    round_record = dict(before=P.state_view(child), propagated=P.state_view(before),
        printed_rows=printed(rows, indices), absolute_variable_bounds=list(map(str, bound)),
        proposals=[proposal], physical_frame_inferences=[], after=P.state_view(after))
    weighted = dict(status='OPEN', initial=P.state_view(child), rounds=[round_record], final=P.state_view(after))
    weighted_audit, certified = G.check_record(weighted, child, I.Adapter())
    assert certified == after and weighted_audit['deductions'] == 1 and weighted_audit['printed_rows_checked'] == 3
    bad = deepcopy(weighted); bad['rounds'][0]['proposals'][0]['weights'][0][1] += 1
    reject('damaged exact multiplier', lambda: G.check_record(bad, child, I.Adapter()))
    for kind in family_counts:
        index = next(k for k, row in enumerate(baseline) if family(row) == kind)
        bad_row = printed(baseline, [index])[0]; bad_row['rhs'] = str(F(bad_row['rhs'])-1)
        reject('damaged row RHS: '+kind, lambda bad_row=bad_row: I.Adapter.rebuild(root, [bad_row]))
    sat = P.physical_child(root, 'sat', (0, 1), (0, 1, 1))
    sat_rows = P.collect(sat)[0]
    mc = next(k for k, row in enumerate(sat_rows) if row[2] == 'strict011v2:mccormick:0:0:0')
    bad_row = printed(sat_rows, [mc])
    reject('SAT row under wrong owner', lambda: I.Adapter.rebuild(P.physical_child(root, 'sat', (0, 1), (1, 1, 1)), bad_row))
    reject('SAT row without owned choice', lambda: I.Adapter.rebuild(root, bad_row))
    bad_state = deepcopy(root); bad_state['path'] = [['alternate_four_escape', [1, 7], [3]]]
    reject('old 001 escape in state', lambda: I.Adapter.rebuild(bad_state, []))
    empty = deepcopy(root)
    angles = list(empty['angles']); angles[0] = (F(1), F(1)); empty['angles'] = tuple(angles)
    scalar = list(empty['scalar']); scalar[0] = (F(9, 10), F(1)); empty['scalar'] = tuple(scalar)
    terminal = P.collect(empty)[3]
    assert I.Adapter.verify_early_terminal(empty, terminal)
    bad_terminal = deepcopy(terminal); bad_terminal['upper'] = '1'
    reject('damaged empty frame interval witness', lambda: I.Adapter.verify_early_terminal(empty, bad_terminal))

    # Preserve the seven-original obstruction: its two omitted extras cannot
    # be supplied by duplicating physical squares under the full 36-pair caller.
    seven_path = workspace/'global_work/other_mask_entrypoints/seven_original_all_open_masks_table.json'
    seven = json.loads(seven_path.read_text()); source_hashes[str(seven_path)] = sha(seven_path)
    centers, frames = [], []
    for x, y, t in seven['rows']['01100']:
        centers.append((F(seven['x_scale'])*x, F(seven['y_scale'])*y))
        frames.append(unit_frame(F(seven['half_angle_scale'])*t))
    assert len(centers) == 7
    assert max(q for c, frame in zip(centers, frames) for q in corner_norms(c, frame)) < F(17, 4) < P.Q
    assert all(pair_alternatives(centers, frames, pair) for pair in combinations(range(7), 2))
    # The five marked constraints use only A through G; dummy positions for
    # labels 7 and 8 do not affect this selected-seven check.
    extended_centers, extended_frames = centers+[centers[0], centers[1]], frames+[frames[0], frames[1]]
    check_marked(extended_centers, extended_frames, list(range(9)), '011/00')
    bad_pairs = [list(pair) for pair in combinations(range(9), 2)
                 if not pair_alternatives(extended_centers, extended_frames, pair)]
    assert [0, 7] in bad_pairs and [1, 8] in bad_pairs

    # The five known closed-Q full-nine witnesses remain valid controls for
    # every universal family in this new root.  Their different marked masks
    # are checked in their own witness bases; no 011 feasibility is claimed.
    entrypoints = workspace/'global_work/other_mask_entrypoints'
    four_path = entrypoints/'four_full_nine_mask_closed_q_boundary_witnesses/four_mask_closed_q_boundary/boundary_witnesses.json'
    fifth_path = entrypoints/'mask_11100_full_nine_closed_q_boundary/mask_11100_closed_q_boundary/boundary_11100.json'
    fifth_source = fifth_path.with_name('source_control.json')
    four, fifth, fifth_data = [json.loads(p.read_text()) for p in (four_path, fifth_path, fifth_source)]
    for p in (four_path, fifth_path, fifth_source):
        source_hashes[str(p)] = sha(p)
    boundary_checks, boundary_masks = 0, []
    packings = [
        ([(F(x, four['center_denominator']), F(y, four['center_denominator']))
          for x, y in [row['center_numerator'] for row in four['originals']]],
         [tuple(map(F, row['first_axis'])) for row in four['originals']]),
        ([tuple(F(x, fifth_data['center_denominator']) for x in pair) for pair in fifth_data['centers']],
         [tuple(F(x, fifth_data['frame_denominator']) for x in pair) for pair in fifth_data['first_axes']])]
    universal_rows = [row for row in baseline if family(row) not in {'cone', 'mask', 'cone_inset'}]
    for centers, frames in packings:
        assert len(centers) == len(frames) == 9
        assert max(q for c, frame in zip(centers, frames) for q in corner_norms(c, frame)) == P.Q
        assert all(a*a+b*b == 1 and a >= abs(b) for a, b in frames)
        assert all(pair_alternatives(centers, frames, pair) for pair in all_pairs)
        values = point(centers, frames)
        for row in universal_rows:
            assert slack(row, values) >= 0, row[2]
            boundary_checks += 1
    for witness in four['witnesses']:
        check_marked(*packings[0], witness['four']+witness['three']+witness['extras'],
                     witness['mask'], tuple(map(F, witness['direction_numerator'])))
        boundary_masks.append(witness['mask'])
    check_marked(*packings[1], fifth['main']+fifth['short']+fifth['extras'], fifth['mask'],
                 tuple(map(F, fifth['witness_frame']['direction_numerator'])))
    boundary_masks.append(fifth['mask'])
    assert set(boundary_masks) == {'101/11', '111/00', '111/01', '111/10', '111/11'}
    assert all(sha(path) == digest for path, digest in source_hashes.items())
    assert not any(name.split('.')[0] in {'numpy', 'scipy', 'z3', 'sympy', 'highspy'} for name in sys.modules)
    report = dict(status='PASS_FRESH_STRICT011_ROOT_LITERAL_AND_COVER_CONTROLS',
        scope='Root and necessary-row attachment only; no original cell or mask is proved excluded.',
        physical_frames=9, original_corners=36, original_pairs=36, marked_cones=5,
        owned_alternatives=288, root_necessary_rows=root_count, root_row_families=family_counts,
        selected_sat_literal_rows=sat_literals, selected_proxy_literal_rows=proxy_literals,
        angle_child_literal_rows=angle_literals, stronger_scalar_sign_literal_rows=sign_literals,
        exact_frame_interval_checks=interval_checks, exact_single_square_row_checks=single_checks,
        exact_sat_and_mccormick_residual_checks=physical_sat_residuals,
        complete_open_covers=cover_counts,
        synthetic_proxy_bound_exact_replay=weighted_audit,
        synthetic_proxy_bound=str(-upper), synthetic_fixture_scope='one guarded proxy child, remains OPEN',
        damaged_controls_rejected=damaged,
        selected_seven_strict011_control='PASS below17/4; duplicate extras rejected by full physical pairs',
        duplicate_extra_bad_pairs=bad_pairs,
        closed_Q_boundary_masks_retained=sorted(boundary_masks),
        closed_Q_universal_row_checks=boundary_checks,
        no_old_context_imported=True, numerical_solver_called=False,
        scalar_to_angle_contraction='None in v2; closed angle splitting remains available',
        conditional_terminal_installed=False, whole_original_credit=0, whole_mask_credit=0,
        source_sha256=source_hashes, seconds=time.monotonic()-started)
    if args.snapshots:
        args.snapshots.mkdir(parents=True, exist_ok=True)
        for name, value in [('ROOT_DOCUMENT.json', document),
                            ('BASELINE_ROW_TABLE.json', dict(rows=printed(baseline), absolute_bounds=list(map(str, bounds)))),
                            ('SYNTHETIC_PROXY_BOUND_EXACT_FIXTURE.json', weighted)]:
            with (args.snapshots/name).open('x') as stream:
                json.dump(value, stream, separators=(',', ':')); stream.write('\n')
    with args.output.open('x') as stream:
        json.dump(report, stream, indent=2); stream.write('\n')
    print(json.dumps({k: report[k] for k in ('status', 'root_necessary_rows', 'selected_sat_literal_rows',
        'exact_single_square_row_checks', 'exact_sat_and_mccormick_residual_checks',
        'complete_open_covers', 'whole_mask_credit', 'seconds')}), flush=True)


if __name__ == '__main__':
    main()
