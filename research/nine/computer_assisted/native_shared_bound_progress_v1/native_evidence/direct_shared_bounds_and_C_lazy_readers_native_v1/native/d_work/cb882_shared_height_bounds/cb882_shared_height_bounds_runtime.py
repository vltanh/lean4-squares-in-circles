"""Cb882 height-component continuation using whole-original certified bounds."""
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
AC=HERE.parents[1]/'ac_work/tree'
sys.path.insert(0,str(AC))
from cb882_height_consequence_four_runtime import Context as Parent,E,stateview,state_from_view,read_seed,SCOPE
import cb882_height_consequence_four_runtime as BASE
import cb882_whole_height_bound_rows as ROWS

class Context(Parent):
    def __init__(self,seed):
        super().__init__(seed)
        self.whole_height_bound_rows=ROWS.rows(seed['state'])
        self.whole_height_bound_reference=dict(path=str(ROWS.BINDING),sha256=ROWS.BINDING_SHA)
    def collect(self,state):
        binding=ROWS.declaration();path=binding['original_path']
        assert state['id']==binding['original_id']and state['path'][:len(path)]==path
        rows,bounds,physical,terminal=super().collect(state)
        if terminal is None:rows.extend(self.whole_height_bound_rows)
        return rows,bounds,physical,terminal

def sources(seed_path):
    answer=BASE.sources(seed_path)
    for path in (__file__,ROWS.__file__,ROWS.BINDING,ROWS.LITERAL.__file__):
        answer[str(Path(path).resolve())]=E.sha(path)
    return answer
