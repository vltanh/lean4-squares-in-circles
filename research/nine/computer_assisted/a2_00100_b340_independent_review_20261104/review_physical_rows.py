#!/usr/bin/env python3
"""Independent physical-literal and hand-table audit of the frozen B340 tree.

This file imports no mathematical code from the producer or exact checker.
It does not replace the separate full ancestry replay. Bound-round literal
checks use the round's saved propagated intervals; those intervals' ancestry
is the responsibility of the full exact replay. All affine terminal sums are
independently reconstructed, including their complete coefficient residual.
"""
from pathlib import Path
from fractions import Fraction as F
from collections import Counter
from hashlib import sha256
import argparse
import json
import re


def digest(p):
    return sha256(Path(p).read_bytes()).hexdigest()


def literal(row):
    co = {}
    for k, v in row['coefficients']:
        assert type(k) is int
        co[k] = co.get(k, F(0)) + F(v)
    return {k: v for k, v in co.items() if v}, F(row['rhs'])


def check_literal(row, co, rhs):
    expected = {k: v for k, v in co.items() if v}
    assert literal(row) == (expected, rhs), row['name']


def expand_disk(row):
    fields = row['name'][len('physical_corner_disk_'):].split('_')
    i, epsilon, tau = map(int, fields[:3])
    p, q, cap = map(F, fields[3:])
    assert len(fields) == 6 and 0 <= i < 9
    assert epsilon in (-1, 1) and tau in (-1, 1)
    assert p or q
    assert cap >= 0 and cap * cap >= F(1105, 256) * (p*p+q*q)
    co = {2*i:p, 2*i+1:q,
          18+i:(epsilon*p+tau*q)/2,
          27+i:(epsilon*q-tau*p)/2}
    check_literal(row, co, cap)


def signed_box(interval, sign):
    a, b = map(F, interval)
    assert a <= b
    return (a, b) if sign == 1 else (-b, -a)


def expand_corner(row, state, four):
    prefix = 'physical_unit_four_corner_' if four else 'physical_unit_corner_'
    fields = row['name'][len(prefix):].split('_')
    i, epsilon, tau = map(int, fields[:3])
    p, q = map(F, fields[3:5])
    bits = list(map(int, fields[5:]))
    assert len(bits) == (4 if four else 2) and set(bits) <= {0,1}
    assert 0 <= i < 9 and epsilon in (-1,1) and tau in (-1,1)
    if not four:
        bits = [bits[0],bits[0],bits[1],bits[1]]
    x, y = state['positions'][2*i:2*i+2]
    alpha = list(map(F,state['scalar'][i]))
    beta = list(map(F,state['scalar'][9+i]))
    assert alpha[0] <= alpha[1] and beta[0] <= beta[1]
    co = {2*i:2*p,2*i+1:2*q,18+i:F(0),27+i:F(0)}
    rhs = F(977,256)+p*p+q*q
    # Each row comes directly from the four signed products in ||corner||^2.
    for frame_col, frame_box, coord_col, coord_box, sign, bit in [
        (18+i,alpha,2*i,x,epsilon,bits[0]),
        (18+i,alpha,2*i+1,y,tau,bits[1]),
        (27+i,beta,2*i+1,y,epsilon,bits[2]),
        (27+i,beta,2*i,x,-tau,bits[3]),
    ]:
        a = frame_box[bit]
        b = signed_box(coord_box,sign)[bit]
        co[coord_col] += a*sign
        co[frame_col] += b
        rhs += a*b
    check_literal(row,co,rhs)


def chosen_sat(state, slot, i, j):
    selected = [(part[1], part[2]) for part in state['path'] if part[0] == 'sat']
    assert 0 <= slot < len(selected)
    pair, choice = selected[slot]
    assert pair == [i,j] and 0 <= i < j < 9
    owner, axis, sign = choice
    assert owner in pair and axis in (0,1) and sign in (-1,1)
    return owner, axis, sign


def expand_frame(row, state):
    fields = row['name'][len('physical_pair_square_'):].split('_')
    slot,i,j = map(int,fields[:3])
    x,y,a,b,c,d = map(F,fields[3:])
    assert len(fields) == 9
    chosen_sat(state,slot,i,j)
    z = 54+6*slot
    # Expansion of ||(x,y)+a u_i+b v_i+c u_j+d v_j||^2 >= 0.
    co = {18+i:-2*(x*a+y*b),27+i:-2*(y*a-x*b),
          18+j:-2*(x*c+y*d),27+j:-2*(y*c-x*d),
          z+2:-2*(a*c+b*d),z+3:-2*(a*c+b*d),
          z+4:-2*(b*c-a*d),z+5:2*(b*c-a*d)}
    check_literal(row,co,x*x+y*y+a*a+b*b+c*c+d*d)


def expand_projection(row,state):
    fields = row['name'][len('physical_projection_square_'):].split('_')
    slot,i,j = map(int,fields[:3])
    x,y,a,b = map(F,fields[3:])
    assert len(fields) == 7
    owner,axis,sign = chosen_sat(state,slot,i,j)
    diffs = {tuple(v['pair']):v['intervals'] for v in state['differences']}
    dx,dy = diffs[i,j]
    co = {}
    def add(k,v):
        co[k] = co.get(k,F(0))+v
    if axis == 0:
        add(18+owner,-2*a*x*sign)
        add(27+owner,-2*a*y*sign)
    else:
        add(27+owner,2*a*x*sign)
        add(18+owner,-2*a*y*sign)
    rhs = x*x+y*y+a*a
    for coordinate,w,interval in [(0,x,dx),(1,y,dy)]:
        lo,hi = map(F,interval)
        assert lo <= hi
        coefficient = -2*b*w-b*b*(lo+hi)
        add(2*j+coordinate,coefficient)
        add(2*i+coordinate,-coefficient)
        rhs -= b*b*lo*hi
    add(54+6*slot,-2*a*b)
    add(55+6*slot,-2*a*b)
    check_literal(row,co,rhs)


def check_reserve(terminal):
    rows = {r['index']:literal(r) for r in terminal['rows']}
    assert len(rows) == len(terminal['rows'])
    bounds = list(map(F,terminal['absolute_variable_bounds']))
    assert all(v >= 0 for v in bounds)
    co = [F(0)]*len(bounds)
    rhs = F(0)
    seen = set()
    for index,integer in terminal['weights']:
        assert type(integer) is int and integer > 0
        assert index not in seen
        seen.add(index)
        coefficients,constant = rows[index]
        weight = F(integer,1<<40)
        rhs += weight*constant
        for column,value in coefficients.items():
            co[column] += weight*value
    assert seen == set(rows)
    correction = sum(abs(c)*m for c,m in zip(co,bounds))
    reserve = -rhs-correction
    assert reserve > 0 and reserve == F(terminal['reserve'])
    assert rhs == F(terminal['weighted_rhs'])
    assert co == list(map(F,terminal['weighted_coefficients']))
    return reserve


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--packet',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    args=p.parse_args();root=args.packet.resolve()
    manifest_path=root/'records/whole_B340_adaptive_lazy_v8/manifest.json'
    manifest=json.loads(manifest_path.read_text())
    report=json.loads((root/'original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json').read_text())
    table={}
    for line in (root/'COMPLETE_TERMINAL_TABLE.md').read_text().splitlines():
        if re.match(r'^\| [0-9]+ \|',line):
            fields=[x.strip()for x in line.split('|')[1:-1]]
            leaf=int(fields[0]);assert leaf not in table;table[leaf]=fields
    counts=Counter();checked=Counter();reserves={};node_rows={};terminals={};bindings={}
    for entry in manifest['nodes']:
        filename=manifest_path.parent/entry['file']
        assert digest(filename)==entry['sha256']
        bindings[str(filename.relative_to(root))]=entry['sha256']
        node=json.loads(filename.read_text());record=node['record']
        counts['nodes']+=1;counts['rounds']+=len(record['rounds'])
        counts['deductions']+=sum(len(rr['proposals'])for rr in record['rounds'])
        for rr in record['rounds']:
            state=rr['propagated']
            for row in rr['printed_rows']:
                counts['round_rows']+=1
                name=row['name']
                if name.startswith('physical_unit_four_corner_'):
                    expand_corner(row,state,True);checked['four_product_round_literals']+=1
                elif name.startswith('physical_unit_corner_'):
                    expand_corner(row,state,False);checked['grouped_corner_round_literals']+=1
                elif name.startswith('physical_corner_disk_'):
                    expand_disk(row);checked['corner_disk_literals']+=1
                elif name.startswith('physical_pair_square_'):
                    expand_frame(row,state);checked['frame_square_literals']+=1
                elif name.startswith('physical_projection_square_'):
                    expand_projection(row,state);checked['projection_round_literals']+=1
        terminal=record.get('terminal')
        if terminal:
            terminals[entry['index']]=terminal['kind']
            counts['leaves']+=1
            assert not node['children']
            line=table[entry['index']]
            assert int(line[1])==node['depth'] and int(line[2])==node['parent']
            assert json.loads(line[3])==node['choice']
            assert int(line[4])==len(record['rounds'])
            assert int(line[5])==sum(len(rr['proposals'])for rr in record['rounds'])
            if terminal['kind']=='positive_exact_reserve':
                reserve=check_reserve(terminal);reserves[entry['index']]=reserve
                assert line[6].startswith('positive exact reserve ≥ ')
                lower=F(line[6].removeprefix('positive exact reserve ≥ '))
                assert 0<lower<=reserve
                counts['positive_reserves']+=1
                state=record['terminal_state']
                for row in terminal['rows']:
                    counts['terminal_rows']+=1
                    if row['name'].startswith('physical_corner_disk_'):
                        expand_disk(row);checked['corner_disk_literals']+=1
                    elif row['name'].startswith('physical_pair_square_'):
                        expand_frame(row,state);checked['frame_square_literals']+=1
            else:
                assert line[6]==terminal['kind']
        node_rows[entry['index']]=sum(len(rr['printed_rows'])for rr in record['rounds'])+len((terminal or {}).get('rows',[]))
    assert set(table)==set(terminals)
    assert counts['nodes']==report['nodes']==403
    assert counts['leaves']==report['terminal_leaves']==279
    assert counts['rounds']==report['local_rounds']==400
    assert counts['deductions']==report['local_deductions']==67336
    assert counts['round_rows']+counts['terminal_rows']==report['local_printed_rows']==203189
    assert counts['positive_reserves']==181
    assert checked['corner_disk_literals']==report['original_corner_rows']==77352
    assert checked['frame_square_literals']==report['frame_square_rows']==4482
    for e in report['leaf_table']:
        assert e['excluded']is True and terminals[e['index']]==e['terminal_kind']
        if e['reserve']is not None:assert reserves[e['index']]==F(e['reserve'])
    inspected=[
      'ORIGINAL_PROOF.json','INPUT_MANIFEST.json','RELEASE_MANIFEST.json',
      'COMPLETE_TERMINAL_TABLE.md','B340_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md',
      'records/REGISTERED_B_COMPLETE_TREE_HAND_PROOF.md',
      'original_audits/FRESH_COMPLETE_ORIGINAL_REPLAY.json',
      'records/whole_B340_adaptive_lazy_v8/manifest.json',
      'code/independent_physical_sat_replay.py',
      'code/independent_physical_pair_frame_squares.py',
      'code/independent_physical_projection_squares.py',
      'code/independent_physical_unit_four_corner_rows.py',
      'code/verify_b_four_corner_trees.py','code/verify_b_gram_square_tree.py',
      'code/verify_b_frame_square_tree.py',
      'code/accepted_unit_four_corner/FOUR_RECTANGLE_UNIT_CORNER_HAND_PROOF.md',
      'accepted_repo/research/nine/computer_assisted/physical_gram_square_rows_v1/PHYSICAL_PAIR_FRAME_SQUARE_HAND_PROOF.md',
      'accepted_repo/research/nine/computer_assisted/physical_gram_square_rows_v1/PHYSICAL_PROJECTION_SQUARE_HAND_PROOF.md',
      'accepted_repo/research/nine/computer_assisted/full_angle_common_side_row_v1/ROOT_PHYSICAL_REVIEW.md',
      'accepted_repo/research/nine/computer_assisted/coupled_three_energy_v1/COUPLED_THREE_SQUARE_ENERGY_HAND_PROOF.md',
    ]
    for name in inspected:bindings[name]=digest(root/name)
    for name,expected in bindings.items():assert digest(root/name)==expected
    result=dict(
      status='PASS_INDEPENDENT_PHYSICAL_LITERAL_AND_HAND_TABLE_AUDIT',
      original_id='negative-34029ea8b047982f',
      exact_parent_provenance_replayed_here=False,
      full_exact_ancestry_replay_required_separately=True,
      bound_round_literals_conditioned_on_saved_propagated_state=True,
      all_181_affine_terminal_residual_sums_repeated=True,
      all_279_hand_table_rows_match_literal_leaf_records=True,
      counts=dict(counts),independent_literal_checks=dict(checked),
      terminal_kind_counts=dict(Counter(terminals.values())),
      least_affine_reserve_node=min(reserves,key=reserves.get),
      least_affine_reserve=str(min(reserves.values())),
      all_source_and_node_hashes_rechecked_at_end=True,
      source_and_node_sha256=bindings,
      reviewer_script_sha256=digest(__file__),
      no_optimizer_or_mathematical_module_imports=True,
      lean_lake_ci_run=False)
    args.output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='source_and_node_sha256'},indent=2))


if __name__=='__main__':main()
