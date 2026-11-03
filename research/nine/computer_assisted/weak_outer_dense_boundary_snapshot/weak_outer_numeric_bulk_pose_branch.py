#!/usr/bin/env python3
"""Discovery-only branch ordering for the unchanged full-nine pose LP.

The matrix and exact certificates are supplied by bulk_pose_lp. This wrapper
only chooses which exhaustive split is tried next. It responds to an actual
LP relaxation defect before adding further physical pair disjunctions.
"""
import numpy as np
import weak_outer_numeric_bulk_pose_lp as pose

base=pose.base
_linprog=pose.linprog
_last=None

def capture_lp(*args,**kwargs):
    global _last
    result=_linprog(*args,**kwargs)
    _last=result.x[:-1] if result.success else None
    return result

def select(box,pos,choices,point,data):
    if box[3][0]<0<box[3][1]:return ('angle',3)
    if _last is not None and len(_last)>=54:
        # On a true original frame AB=|BE|. A sign split makes its graph exact.
        defects=[max(0.,_last[36+i]-abs(_last[27+i]))
                 if box[i][0]<0<box[i][1] else 0. for i in range(9)]
        k=int(np.argmax(defects))
        if defects[k]>.03:return ('angle',k)
        # On a true original frame AL^2+BE^2=1. Wide arc chords are the
        # principal remaining orientation relaxation at these cells.
        deficits=[max(0.,1-_last[18+i]**2-_last[27+i]**2)
                  if box[i][1]-box[i][0]>.25 else 0. for i in range(9)]
        k=int(np.argmax(deficits))
        if deficits[k]>.06:return ('angle',k)
    selected={(p,kind) for p,kind,value in choices}
    for pair in ((2,3),(3,6),(2,6)):
        if (pair,'sat') not in selected:return ('sat',pair)
    return original_select(box,pos,choices,point,data)

if __name__=='__main__':
    original_select=base.select
    pose.linprog=capture_lp
    base.matrix=pose.matrix;base.solve=pose.solve;base.select=select
    base.main()
