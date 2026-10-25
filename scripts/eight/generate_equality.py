#!/usr/bin/env python3
"""Write interval expressions for the quantities of the model on the box of parameters.

    python3 -I scripts/eight/generate_equality.py

The eight variables are (q, y, z) of the chain, on the box sharpBox of generate_stationary.py
around the stationary point, and the five parameters (x, y, w, z, eta) of the family, on the box
InBox of SquaresInCircles/Eight/Stationary/Coordinates.lean. From the chain of
generate_stationary.py the script builds eighteen quantities of the model: the cosine and sine of
the central frame and of its angle to the frame of H and G, the coordinates of the centre in the
central frame, the seven separation margins of the central square, the room left in the
containment of T and G, the height of the highest point of H, and the height of the highest point
and the abscissa of the leftmost point of G at the largest offset eta = etaMax. Each is written to
SquaresInCircles/Eight/Stationary/Generated/EqualityBox.lean as a `ScalarExpr` whose nodes carry
the intervals of exact rational interval arithmetic on the box, rounded outwards to multiples of
2^-140 (`generate_stationary.evaluate`). Before it writes an expression the script checks that its
interval lies in the stated bounds, and it stops at the first that does not.
"""
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import generate_stationary as g
A=g.A;C=A.const
# the variables 0 to 2 are (q, y, z) of the chain, and 3 to 7 the parameters (x, y, w, z, eta)
x,yy,w,Z,eta=[A.var(i) for i in range(3,8)]
# the cosine and sine of the central frame and of its angle to the frame of H and G, and the
# thresholds W₀ and Wₜ of `EqualityParameters`, with the sines in place of their absolute values,
# as both sines are positive on the box
den=A.add(C(1),A.sq(w))
cc=A.div(A.sub(C(1),A.sq(w)),den)
ss=A.div(A.mul(C(2),w),den)
W0=A.div(A.add(A.add(C(1),cc),ss),C(2))
rc=A.add(A.mul(g.c,cc),A.mul(g.s,ss))
rs=A.sub(A.mul(g.c,ss),A.mul(g.s,cc))
Wt=A.div(A.add(A.add(C(1),rc),rs),C(2))
# the centres of H and G
hx=A.sub(A.mul(g.c,A.add(g.h1,C(Q(1,2)))),A.mul(g.s,A.add(g.h2,C(Q(1,2)))))
hy=A.add(A.mul(g.s,A.add(g.h1,C(Q(1,2)))),A.mul(g.c,A.add(g.h2,C(Q(1,2)))))
gx=A.sub(A.mul(g.c,A.add(g.h1,C(Q(3,2)))),A.mul(g.s,A.add(A.add(g.h2,C(Q(1,2))),eta)))
gy=A.add(A.mul(g.s,A.add(g.h1,C(Q(3,2)))),A.mul(g.c,A.add(A.add(g.h2,C(Q(1,2))),eta)))
subx=lambda a:A.sub(a,x)
suby=lambda a:A.sub(a,yy)
# the eighteen quantities of `boxData` (Stationary/EqualityBox.lean) and their stated bounds
targets={
 'centralCosine':cc,'centralSine':ss,'relativeCosine':rc,'relativeSine':rs,
 'coreFirst':A.add(A.mul(cc,x),A.mul(ss,yy)),
 'coreSecond':A.add(A.neg(A.mul(ss,x)),A.mul(cc,yy)),
 'AMargin':A.sub(subx(A.sub(g.x1,C(Q(1,2)))),W0),
 'BMargin':A.sub(A.add(A.mul(cc,subx(A.sub(g.x2,C(Q(1,2))))),
   A.mul(ss,suby(A.add(g.y,C(Q(3,2)))))),W0),
 'DMargin':A.sub(A.add(A.neg(A.mul(ss,subx(A.add(g.x3,C(Q(1,2)))))),
   A.mul(cc,suby(A.sub(g.y3,C(Q(1,2)))))),W0),
 'EMargin':A.sub(A.neg(subx(A.add(g.x4,C(Q(1,2))))),W0),
 'HMargin':A.sub(A.neg(A.add(A.mul(cc,subx(hx)),A.mul(ss,suby(hy)))),Wt),
 'GMargin':A.sub(A.sub(A.mul(g.s,subx(gx)),A.mul(g.c,suby(gy))),Wt),
 'TMargin':A.sub(suby(Z),W0),
 'topDiskReserve':A.sub(g.q,A.add(A.sq(A.sub(g.x2,C(1))),A.sq(A.add(Z,C(Q(1,2)))))),
 'tiltedDiskReserve':A.sub(g.q,A.add(A.sq(A.add(g.h1,C(2))),A.sq(A.add(g.h2,eta)))),
 'topH':A.add(A.mul(g.s,A.add(g.h1,C(1))),A.mul(g.c,A.add(g.h2,C(1)))),
 'topG':A.sub(A.mul(g.s,A.add(g.h1,C(2))),A.div(g.c,C(12))),
 'leftG':A.add(A.mul(g.c,A.add(g.h1,C(1))),A.div(g.s,C(12))) }
bounds={
 'centralCosine':(Q('.979'),Q('.981')),'centralSine':(Q('.195'),Q('.201')),
 'relativeCosine':(Q('.99'),Q(1)),'relativeSine':(Q('.072'),Q('.08')),
 'coreFirst':(Q('-.139'),Q('.139')),'coreSecond':(Q('-.030'),Q('.030')),
 'AMargin':(Q('.01'),Q(1)),'BMargin':(Q('.01'),Q(1)),
 'DMargin':(Q('.01'),Q(1)),'EMargin':(Q('.01'),Q(1)),
 'HMargin':(Q('.01'),Q(1)),'GMargin':(Q('.01'),Q(1)),
 'TMargin':(Q('.01'),Q(1)),
 'topDiskReserve':(Q('.055'),Q('.08')),'tiltedDiskReserve':(Q('.448'),Q('.48')),
 'topH':(Q('-1'),Q('-.30')),'topG':(Q('-.01'),Q('-.004')),
 'leftG':(Q('-.355'),Q('-.35')) }
# the box: sharpBox of generate_stationary.py in (q, y, z), and InBox in the parameters
yt=Q('-.92065667800760613175');zt=Q('.06189741100766035970')
qt=Q('3.91553413751747532652')
box=((qt-Q(2,10**16),qt+Q(1,10**16)),(yt-Q(1,10**12),yt+Q(1,10**12)),
 (zt-Q(1,10**12),zt+Q(1,10**12)),(Q('.139'),Q('.141')),(Q('-.001'),Q('.001')),
 (Q('.099'),Q('.101')),(Q('1.349'),Q('1.351')),(Q('-.321'),Q('-.319')))

def generate():
 """Check the bounds of the eighteen quantities and write EqualityBox.lean."""
 out=g.OUT/'EqualityBox.lean'
 lines=['''module

public import SquaresInCircles.Eight.Stationary.Expression

/-!
# Eight squares: interval expressions on the box of parameters

The box `box` of the eight variables: `sharpBox` of `LocalStationaryBounds.lean` in the squared
radius, the position and the tilt of the chain, and `InBox` in the five parameters
`(x, y, w, z, eta)` of the family. For each of eighteen quantities of the model there is an
interval expression (`ScalarExpr`, `Arithmetic/ScalarExpr.lean`) whose nodes carry rational
intervals; the kernel decides that they are valid on `box` (`_valid`), so the quantity lies
between rational bounds on the whole box (`_bound`). `Stationary/EqualityBox.lean` identifies the
expressions with the quantities of the model. Written by `scripts/eight/generate_equality.py`.
-/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
namespace SquaresInCircles.Eight.Stationary.EqualityGenerated
open Arithmetic
''','/-- The box `sharpBox` in `(q, y, z)` and `InBox` in the parameters `(x, y, w, z, eta)`. -/',
 'def box : QBox 8 := '+g.boxlit(box),'','''/-- An expression valid on `box` lies in every rational interval containing its range. -/
private theorem bound_of_valid {e : ScalarExpr 8} (hv : e.Valid box) {env : Fin 8 → ℝ}
    (he : box.Mem env) (l h : ℚ) {lr hr : ℝ} (hl : l ≤ (e.range box).lo)
    (hh : (e.range box).hi ≤ h) (hlr : (l : ℝ) = lr) (hhr : (h : ℝ) = hr) :
    lr ≤ e.eval env ∧ e.eval env ≤ hr := by
  have hb := QInterval.mem_mono (J := ⟨l, h⟩) (ScalarExpr.sound box e hv env he) hl hh
  exact ⟨hlr ▸ hb.1, hhr ▸ hb.2⟩
''']
 for name,target in targets.items():
  lo,hi=bounds[name];v=g.evaluate(box,[target],140)[target]
  if not lo<=v[0]<=v[1]<=hi:raise RuntimeError((name,tuple(float(x) for x in v),lo,hi))
  lines += [f'def {name}Expression : ScalarExpr 8 := by',
    *[s.replace('ScalarExpr 3','ScalarExpr 8') for s in g.expr_lines(box,target,140)],'',
    f'theorem {name}_valid : {name}Expression.Valid box := by decide +kernel',
    f'theorem {name}_bound (env : Fin 8 → ℝ) (he : box.Mem env) :',
    f'    ({g.rat(lo)}:ℝ)≤{name}Expression.eval env ∧ {name}Expression.eval env≤{g.rat(hi)} :=',
    f'  bound_of_valid {name}_valid he {g.bound_arg(lo)} {g.bound_arg(hi)} (by decide +kernel)',
    '    (by decide +kernel) (by norm_num) (by norm_num)','']
 lines += ['end SquaresInCircles.Eight.Stationary.EqualityGenerated','']
 lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
 out.write_text('\n'.join(lines));print({'bytes':out.stat().st_size,'expressions':len(targets)})
if __name__=='__main__':generate()
