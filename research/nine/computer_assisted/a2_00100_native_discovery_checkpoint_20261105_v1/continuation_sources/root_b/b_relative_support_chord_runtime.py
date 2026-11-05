"""Experimental discovery only: relative-support chord rows over general cones."""
from pathlib import Path
import sys
import b_general_cone_runtime as BASE

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE/'relative_support_chords'))
import physical_relative_support_chords as CHORD
E = BASE.E

class Context(BASE.Context):
    def collect(self, state):
        rows, bounds, physical, terminal = super().collect(state)
        if terminal is None:
            rows.extend(CHORD.generate(physical['scalar'], physical['differences']))
        return rows, bounds, physical, terminal

def source_bindings():
    result = BASE.source_bindings()
    for path in (__file__, CHORD.__file__):
        result[str(Path(path).resolve())] = E.sha(path)
    return result
