#!/usr/bin/env python3
"""Exact representative-caller attachment controls, without an optimizer."""
if not __debug__:
    raise RuntimeError('Representative-root controls reject optimized Python.')

import argparse
from copy import deepcopy
from fractions import Fraction as F
from hashlib import sha256
import importlib.util
from itertools import combinations, product
import json
from pathlib import Path
import sys
import time

HERE = Path(__file__).resolve().parent
P_SHA = 'aae7441de9422d502bf9a9c9752942a7b5fc28689997b7863000976b5aa86c00'
I_SHA = 'c575144623b13c55fc3e57ed9bd17d1a90415991f5ddf3bdf0540f8ea8b69068'

def digest(path):
    return sha256(Path(path).read_bytes()).hexdigest()

def load(name, path, expected):
    assert digest(path) == expected
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def literal(rows, indices=None):
    if indices is None:
        indices = range(len(rows))
    return [dict(index=k, name=rows[k][2],
                 coefficients=[[i,str(c)] for i,c in rows[k][0]], rhs=str(rows[k][1])) for k in indices]

def write(path, value):
    with path.open('x') as f:
        json.dump(value, f, indent=2, sort_keys=True); f.write('\n')

def main():
    started = time.monotonic()
    parser = argparse.ArgumentParser()
    parser.add_argument('--workspace', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--snapshots', type=Path, required=True)
    args = parser.parse_args()
    P = load('representative011_control_producer', HERE/'representative_strict_011_root.py', P_SHA)
    I = load('representative011_control_independent', HERE/'independent_strict_011_adapter.py', I_SHA)
    G = load('representative011_generic_arithmetic', args.workspace/'b_work/independent_physical_sat_replay.py',
             '1d069c90f289dce136e41afeb5d564ec7016ac06f58eeb733ca7552801b6fafc')
    X = load('representative011_generic_proxy', args.workspace/'b_work/independent_physical_proxy_cover.py',
             '3b46b8a966c712e23894ae4cd7964355730f2bfe3c58a04871ade9d35ddf1277')
    C = load('representative011_symmetry_control', P.SYMMETRY/'check_full_mask_symmetries.py', I.SYMMETRY_CHECKER)
    document = P.root_document()
    root = I.verify_root(document)
    assert root == P.fresh_state()
    assert len(document['original_corners']) == len(document['original_pairs']) == 36
    assert len(document['physical_originals']) == 9 and len(document['exact_mask_edges']) == 5
    assert document['extra_normalizations'] and not document['installed_conditional_terminals']
    assert not document['inherited_original_cells'] and not document['inherited_001_premises']

    def check_rows(state, selected=None):
        rows, bounds, propagated, terminal = P.collect(state)
        assert terminal is None
        indices = list(range(len(rows))) if selected is None else [k for k,r in enumerate(rows) if selected(r)]
        rebuilt, rbounds, independent = I.Adapter.rebuild(state, literal(rows, indices))
        assert rebuilt == {k:rows[k] for k in indices} and rbounds == bounds and independent == propagated
        return len(indices), rows, bounds, propagated

    root_count, root_rows, root_bounds, propagated = check_rows(root)
    assert root_count == 1757
    norm_names = {'strict011v2:slope:3:0', 'strict011v2:difference:7:8:0:-1'}
    norms = [r for r in root_rows if r[2] in norm_names]
    assert len(norms) == 2
    assert norms[0] == (((30,F(-1)),), F(0), 'strict011v2:slope:3:0')
    assert norms[1] == (((14,F(1)),(16,F(-1))), F(0), 'strict011v2:difference:7:8:0:-1')
    selection = lambda r: r[2].split(':')[1] in {
        'mccormick','separation','projection_floor','relative_cosine','relative_sine','proxy'} or r[2] in norm_names
    sat_literals = proxy_literals = 0
    complete = {'sat':0, 'proxy':0, 'angle':0}
    def zero(state):
        return dict(status='OPEN', initial=P.state_view(state), rounds=[], final=P.state_view(state))
    for pair in combinations(range(9),2):
        eight = []
        for choice in product(pair,(0,1),(-1,1)):
            child = P.physical_child(root,'sat',pair,choice)
            assert child == G.sat_child(root,pair,choice,I.Adapter())
            sat_literals += check_rows(child,selection)[0]
            eight.append((choice,zero(child)))
        audit,survivors = G.check_complete_cover(root,pair,eight,I.Adapter())
        assert len(survivors) == 8
        complete['sat'] += 1
        four = []
        for choice in product((0,1),(-1,1)):
            child = P.physical_child(root,'proxy',pair,choice)
            assert child == X.proxy_child(root,pair,choice,I.Adapter())
            proxy_literals += check_rows(child,selection)[0]
            four.append((choice,zero(child)))
        audit,survivors = X.check_complete_proxy_cover(root,pair,four,I.Adapter(),G.check_record)
        assert len(survivors) == 4
        complete['proxy'] += 1
    for original in range(9):
        cut = F(1,2) if original == 3 else F(0)
        for side in (0,1):
            child = P.angle_child(root,original,cut,side)
            assert child == I.angle_child(root,original,cut,side)
            G.check_record(zero(child),child,I.Adapter())
        complete['angle'] += 1

    assignments = zero_faces = 0
    for seed in range(100):
        for face in (False,True):
            values = C.physical_assignment(seed,face)
            normalized,flags = C.M.normalize_physical_assignment(values)
            assert normalized[30] >= 0 and normalized[14] <= normalized[16]
            assert C.M.transform(normalized,**flags) == values
            assert all(a <= v <= b for v,(a,b) in zip(normalized,root['positions']+root['scalar']))
            assert all(a <= normalized[27+i]/normalized[18+i] <= b for i,(a,b) in enumerate(root['angles']))
            dx,dy = normalized[16]-normalized[14], normalized[17]-normalized[15]
            assert all(a <= v <= b for v,(a,b) in zip((dx,dy),root['differences'][7,8]))
            assignments += 1
            if face:
                assert flags == dict(reflect=False,swap_extras=False)
                zero_faces += 1

    rejected = []
    def reject(name, function):
        try:
            function()
        except (AssertionError, ValueError, KeyError, IndexError, TypeError):
            rejected.append(name)
        else:
            raise AssertionError('Damaged representative input accepted: '+name)
    def damage(name, mutate):
        bad = deepcopy(document); mutate(bad)
        reject(name,lambda:I.verify_root(bad))
    damage('remove ninth physical original',lambda d:d['physical_originals'].pop())
    damage('remove one physical pair',lambda d:d['original_pairs'].pop())
    damage('replace strict radius by closed',lambda d:d.__setitem__('radius_mode','closed'))
    damage('change BC exact weak bit',lambda d:d['exact_mask_edges'][1].__setitem__('bit',0))
    damage('import old 001 normalization',lambda d:d['inherited_001_premises'].append('large gap'))
    damage('add unproved D/G corridor',lambda d:d['extra_normalizations'].append('|x_G-x_D|<1'))
    damage('omit reflection from equivalence',lambda d:d['normalization_equivalence']['maps'].remove('vertical_reflection'))
    damage('replace symmetry binding',lambda d:d['normalization_equivalence'].__setitem__('symmetry_binding_sha256','0'*64))
    damage('erase representative difference rectangle',lambda d:d['initial'].__setitem__('differences',[]))
    damage('narrow D root without proof',lambda d:d['initial']['angles'].__setitem__(3,['1/4','1']))
    damage('old full-root identity',lambda d:d.__setitem__('original_id',P.P.ROOT_ID))
    reject('base caller cannot use representative adapter',lambda:I.Adapter.rebuild(P.P.fresh_state(),[]))
    for name in norm_names:
        row = literal(root_rows,[next(k for k,r in enumerate(root_rows) if r[2] == name)])
        reject('representative row on unnormalized caller: '+name,
               lambda row=row:I.B.Adapter.rebuild(I.B.expected_initial_state(),row))
        wrong = deepcopy(row); wrong[0]['rhs'] = '-1'
        reject('damaged representative literal: '+name,lambda wrong=wrong:I.Adapter.rebuild(root,wrong))
    wrong_state = deepcopy(root); wrong_state['differences'] = {}
    reject('drop inherited extra order',lambda:I.Adapter.rebuild(wrong_state,[]))
    wrong_state = deepcopy(root)
    a = list(wrong_state['angles']); a[3] = (F(-1),F(1)); wrong_state['angles'] = tuple(a)
    reject('drop inherited endpoint sign',lambda:I.Adapter.rebuild(wrong_state,[]))
    wrong_state = deepcopy(root); wrong_state['path'] = [['alternate_four_escape',[1,7],[3]]]
    reject('registered original path in representative state',lambda:I.Adapter.rebuild(wrong_state,[]))
    assert not any(n.split('.')[0] in {'numpy','scipy','sympy','z3','highspy'} for n in sys.modules)
    sources = I.dependency_hashes()
    for f in [Path(__file__).resolve(),HERE/'representative_strict_011_root.py',
              HERE/'independent_strict_011_adapter.py',HERE/'REPRESENTATIVE_ROOT_HAND_PROOF.md']:
        sources[str(f)] = digest(f)
    report = dict(status='PASS_REPRESENTATIVE_STRICT011_ROOT_AND_LITERAL_CONTROLS',
        root_id=P.ROOT_ID,mask='011/00',radius_mode='strict',physical_originals=9,
        original_corners=36,original_pairs=36,marked_cones=5,root_rows=root_count,
        selected_sat_and_normalization_literals=sat_literals,
        selected_proxy_and_normalization_literals=proxy_literals,
        complete_open_covers=complete, fresh_symmetry_audit=I.verify_whole_caller_symmetry(),
        rational_assignment_controls=assignments,shared_zero_face_controls=zero_faces,
        rational_assignments_are_packing_witnesses=False,damaged_controls_rejected=rejected,
        source_sha256=sources,conditional_terminal_installed=False,numerical_solver_called=False,
        whole_mask_credit=0,original_cell_credit=0,seconds=time.monotonic()-started)
    args.snapshots.mkdir(parents=True,exist_ok=False)
    write(args.snapshots/'ROOT_DOCUMENT.json',document)
    write(args.snapshots/'BASELINE_ROW_TABLE.json',dict(rows=literal(root_rows),absolute_bounds=list(map(str,root_bounds))))
    write(args.output,report)
    print(json.dumps({k:report[k] for k in ('status','root_rows','complete_open_covers',
        'rational_assignment_controls','whole_mask_credit','seconds')}))

if __name__ == '__main__':
    main()
