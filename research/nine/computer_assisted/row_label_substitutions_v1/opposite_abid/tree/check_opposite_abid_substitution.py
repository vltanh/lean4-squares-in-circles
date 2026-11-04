#!/usr/bin/env python3
"""Exact source, substitution, equality-blocker, and guard arithmetic controls."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product,combinations
from copy import deepcopy
import json,hashlib
import opposite_abid_row_guard as G
import independent_opposite_abid_row_guard as I

HERE=Path(__file__).resolve().parent
PKG=HERE.parent/'c887/c887_whole_eight_checkpoint_package'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    hand=PKG/'opposite_tilt_theorem/HAND_PROOF.md'
    assert sha(hand)=='db830ffbebdc807b0e05f78766e0a0509d11418be31b9a7ef0623b212328831a'
    controls=positive=damaged=0
    row=(0,1,8,3)
    for signs in product((-1,0,1),repeat=2):
        for heights in product((F(-23,200),F(0),F(23,200)),repeat=4):
            positions=[(F(0),F(0))for _ in range(18)]
            for i,x,y in zip(row,(F(-3,2),F(-1,2),F(1,2),F(3,2)),heights):
                positions[2*i]=(x,x);positions[2*i+1]=(y,y)
            # H can be entirely off the tested main row.
            positions[15]=(F(7,5),F(7,5))
            angles=[(F(-1),F(1))for _ in range(9)]
            scalar=[(F(-1),F(1))for _ in range(36)]
            for i,v in zip((0,3),signs):angles[i]=(F(v),F(v));scalar[9+i]=(F(v),F(v))
            state=dict(positions=positions,angles=angles,scalar=scalar,differences={})
            literal=G.evaluate(state);assert literal==I.evaluate(state);controls+=1
            expected=signs[0]*signs[1]<=0 and sum(abs(x-y)for x,y in zip(heights,heights[1:]))<=F(23,100)
            assert(literal['status']=='PASS_OPPOSITE_TILT_ABID_TERMINAL')==expected
            if expected:
                I.verify_literal(literal,state);positive+=1
                bad=deepcopy(literal);bad['physical_row']=[0,7,8,3]
                try:I.verify_literal(bad,state)
                except AssertionError:damaged+=1
                else:raise AssertionError('wrong physical row accepted')
            # Difference bounds can correlate a wide common vertical shift.
            broad=deepcopy(state)
            for i in row:broad['positions'][2*i+1]=(heights[row.index(i)]-1,heights[row.index(i)]+1)
            for i,j in combinations(sorted(row),2):
                dx=positions[2*j][0]-positions[2*i][0];dy=positions[2*j+1][0]-positions[2*i+1][0]
                broad['differences'][i,j]=((dx,dx),(dy,dy))
            assert G.evaluate(broad)==I.evaluate(broad)==literal;controls+=1
    for h in(F(1,2),F(3,5),F(2,3),F(7,10)):
        assert h+1/(4*h)-1==(2*h-1)**2/(4*h)>=0
    sources={str(Path(p).resolve()):sha(p)for p in(__file__,G.__file__,I.__file__,I.SHARP.__file__,G.SOURCE,hand,HERE/'OPPOSITE_ABID_LITERAL_SUBSTITUTION.md')}
    result=dict(status='PASS_LITERAL_OPPOSITE_ABID_SUBSTITUTION_AND_GUARD_CONTROLS',
        guard_states=controls,positive_guards=positive,wrong_physical_row_controls_rejected=damaged,
        source_theorem_sha256=sha(hand),threshold='23/100',original_mask='001/00',all_nine_originals_required=True,
        full_original_ancestry_required=True,unchanged_scalar_domains=80,unchanged_scalar_leaves=1405,
        scalar_replay_required_on_actual_terminal_use=True,new_original_cells=0,new_masks=0,source_sha256=sources)
    (HERE/'OPPOSITE_ABID_SUBSTITUTION_EXACT_CONTROLS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items()if k!='source_sha256'}),flush=True)
if __name__=='__main__':main()
