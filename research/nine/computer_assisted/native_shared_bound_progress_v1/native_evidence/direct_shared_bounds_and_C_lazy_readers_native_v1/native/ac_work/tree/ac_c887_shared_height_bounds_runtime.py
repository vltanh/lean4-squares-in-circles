"""C887 continuation with certified stronger whole-original parent bounds."""
from pathlib import Path
from ac_c887_global_union_height_consequence_runtime import Context as Parent,E,stateview,state_from_view
import ac_c887_global_union_height_consequence_runtime as BASE
import c887_whole_height_bound_rows as ROWS

class Context(Parent):
    def __init__(self,folder):
        super().__init__(folder)
        self.whole_height_bound_rows=ROWS.rows(self.union_state)
        self.whole_height_bound_reference=dict(path=str(ROWS.BINDING),sha256=ROWS.BINDING_SHA)
    def collect(self,state):
        rows,bounds,physical,terminal=super().collect(state)
        if terminal is None:rows.extend(self.whole_height_bound_rows)
        return rows,bounds,physical,terminal

def sources(folder):
    answer=BASE.sources(folder)
    for path in (__file__,ROWS.__file__,ROWS.BINDING,ROWS.LITERAL.__file__):
        answer[str(Path(path).resolve())]=E.sha(path)
    return answer
