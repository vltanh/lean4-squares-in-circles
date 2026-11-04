"""B discovery with exact physical frame-square cuts suggested numerically."""
from pathlib import Path
import b_owner_free_runtime as BASE
import physical_pair_frame_squares as SQUARE
import physical_frame_square_separation as SEPARATE
E=BASE.E
ORIGINAL_PHASE=E.phase_solve
CURRENT=None
MAX_SEPARATION_PASSES=8

class Context(BASE.Context):
    def __init__(self,packet):
        super().__init__(packet);self.frame_squares={};self.current_choices=None
    def collect(self,state):
        global CURRENT
        rows,bounds,propagated,terminal=super().collect(state)
        self.current_choices=state['choices'];CURRENT=self
        if terminal is None:
            for slot,pair in enumerate(SQUARE.selected(state['choices'])):
                rows.extend(SQUARE.row(state['choices'],slot,q)for q in sorted(self.frame_squares.get(pair,set())))
        return rows,bounds,propagated,terminal

def phase_with_frame_squares(rows,bounds):
    assert CURRENT is not None
    for iteration in range(MAX_SEPARATION_PASSES+1):
        result=ORIGINAL_PHASE(rows,bounds);h,phase,point,terminal=result
        if terminal is not None or iteration==MAX_SEPARATION_PASSES:return result
        suggestions=SEPARATE.violated_parameters(point,CURRENT.current_choices)
        pairs=SQUARE.selected(CURRENT.current_choices);additions=[]
        for slot,q,eigenvalue,violation in suggestions:
            pair=pairs[slot];known=CURRENT.frame_squares.setdefault(pair,set())
            if q in known:continue
            known.add(q);row=SQUARE.row(CURRENT.current_choices,slot,q);additions.append(row)
            CURRENT.AH.SEED_NAMES.add(row[2])
        if not additions:return result
        rows.extend(additions)
    raise AssertionError('unreachable')

E.phase_solve=phase_with_frame_squares

def source_bindings():
    out=BASE.source_bindings()
    for p in(__file__,SQUARE.__file__,SEPARATE.__file__):out[str(Path(p).resolve())]=E.sha(p)
    return out
