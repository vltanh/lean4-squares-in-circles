"""Stronger conditional A3 bounds after using the completed A1 consequence."""
from pathlib import Path
import ac_a_c744_component3_a1_consequence_runtime as BASE
from ac_a_c744_component3_a1_consequence_runtime import E, stateview, state_from_view
import a_c744_component3_post_a1_bound_rows as POST


class Context(BASE.Context):
    def __init__(self, parent_state, component):
        assert type(component) is int and component == 3
        super().__init__(parent_state, component)
        co, rhs, name = self.escape
        domain = dict(coefficients=[[i, str(v)] for i, v in co], rhs=str(rhs), name=name)
        self.component3_post_a1_rows = POST.rows(parent_state, component, domain)
        self.component3_post_a1_bound_reference = dict(
            path=str(POST.BINDING), sha256=POST.BINDING_SHA, component=3)

    def collect(self, state):
        rows, bounds, physical, terminal = super().collect(state)
        if terminal is None:
            rows.extend(self.component3_post_a1_rows)
        return rows, bounds, physical, terminal


def sources():
    answer = BASE.sources()
    for path in (__file__, POST.__file__, POST.BINDING, POST.LITERAL.__file__):
        answer[str(Path(path).resolve())] = E.sha(path)
    return answer
