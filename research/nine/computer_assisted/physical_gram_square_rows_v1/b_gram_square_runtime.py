"""B numerical Gram separation; every emitted row has an exact norm proof."""
from pathlib import Path
import b_frame_square_runtime as BASE
import physical_projection_squares as PROJECTION
import physical_projection_square_separation as SEARCH
E=BASE.E
CURRENT=None
MAX_SEPARATION_PASSES=10

class Context(BASE.Context):
    def __init__(self,packet):
        super().__init__(packet);self.projection_squares={};self.current_differences=None
    def collect(self,state):
        global CURRENT
        rows,bounds,propagated,terminal=super().collect(state)
        CURRENT=self
        if terminal is None:
            self.current_differences=propagated['differences']
            for slot,(pair,ch)in enumerate(PROJECTION.selections(state['choices'])):
                rows.extend(PROJECTION.row(state['choices'],self.current_differences,slot,q)for q in sorted(self.projection_squares.get(pair,set())))
        return rows,bounds,propagated,terminal

def phase_with_gram_squares(rows,bounds):
    assert CURRENT is not None
    for iteration in range(MAX_SEPARATION_PASSES+1):
        result=BASE.ORIGINAL_PHASE(rows,bounds);h,phase,point,terminal=result
        if terminal is not None or iteration==MAX_SEPARATION_PASSES:return result
        choices=CURRENT.current_choices;differences=CURRENT.current_differences
        pairs=BASE.SQUARE.selected(choices);additions=[]
        for slot,q,eigenvalue,violation in BASE.SEPARATE.violated_parameters(point,choices):
            known=CURRENT.frame_squares.setdefault(pairs[slot],set())
            if q not in known:known.add(q);additions.append(BASE.SQUARE.row(choices,slot,q))
        for slot,q,eigenvalue,violation in SEARCH.violated_parameters(point,choices,differences):
            known=CURRENT.projection_squares.setdefault(pairs[slot],set())
            if q not in known:known.add(q);additions.append(PROJECTION.row(choices,differences,slot,q))
        if not additions:return result
        for row in additions:CURRENT.AH.SEED_NAMES.add(row[2])
        rows.extend(additions)
    raise AssertionError('unreachable')

E.phase_solve=phase_with_gram_squares

def source_bindings():
    out=BASE.source_bindings()
    for p in(__file__,PROJECTION.__file__,SEARCH.__file__):out[str(Path(p).resolve())]=E.sha(p)
    return out
