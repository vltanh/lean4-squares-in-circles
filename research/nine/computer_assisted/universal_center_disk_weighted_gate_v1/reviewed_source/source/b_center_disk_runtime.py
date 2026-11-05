"""Universal center supports over the unchanged B four-corner runtime.

Search directions are untrusted; every weighted literal is checked by the
independent center-row decoder. Rows append only, preserving prior indices.
"""
from pathlib import Path
from fractions import Fraction as F
from math import cos, sin, pi
import sys
import b_four_complete_guards_runtime as BASE
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'universal_center_disk'))
import physical_center_disk_rows as CENTER
import physical_center_disk_separation as CSEARCH
E=BASE.E

class Context(BASE.Context):
    def __init__(self,packet):
        super().__init__(packet)
        context=self
        directions={(F(round(4096*cos(2*pi*k/64)),4096),F(round(4096*sin(2*pi*k/64)),4096))for k in range(64)}
        self.center_parameters={(i,a,b)for i in range(9)for a,b in directions}
        previous=self.AH.ActiveHighs
        class DynamicCenterHighs(previous):
            def run(self):
                for cycle in range(4):
                    answer=super().run()
                    if not context.gram_active or cycle==3 or self.inner.getModelStatus()!=self.H.HighsModelStatus.kOptimal:
                        return answer
                    point=list(map(float,self.inner.getSolution().col_value[:-1]))
                    rows=[]
                    for parameters,violation in CSEARCH.violated_parameters(point,tolerance=1e-7):
                        if parameters not in context.center_parameters:
                            context.center_parameters.add(parameters)
                            rows.append(CENTER.row(*parameters))
                    if not rows:return answer
                    self.append_rows(rows)
                raise AssertionError('unreachable')
        self.AH.ActiveHighs=DynamicCenterHighs
    def collect(self,state):
        rows,bounds,physical,terminal=super().collect(state)
        if terminal is not None:return rows,bounds,physical,terminal
        rows.extend(CENTER.row(*parameters)for parameters in sorted(self.center_parameters))
        return rows,bounds,physical,None

def source_bindings():
    result=BASE.source_bindings()
    for p in(__file__,CENTER.__file__,CSEARCH.__file__,HERE/'resume_b_center_disk_tree.py',HERE/'universal_center_disk/UNIVERSAL_CENTER_DISK_HAND_PROOF.md',HERE/'universal_center_disk/independent_physical_center_disk_rows.py'):
        result[str(Path(p).resolve())]=E.sha(p)
    return result
