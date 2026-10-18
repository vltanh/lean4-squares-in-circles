#!/usr/bin/env python3
"""Emit rational proof data for every point of the five-parameter box.

Writes SquaresInCircles/Eight/ExactFamily/Generated/EqualityBox.lean.
"""
from fractions import Fraction as Q
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import generate_stationary as g
A=g.A;C=A.const
x,yy,w,Z,eta=[A.var(i) for i in range(3,8)]
den=A.add(C(1),A.sq(w))
cc=A.div(A.sub(C(1),A.sq(w)),den)
ss=A.div(A.mul(C(2),w),den)
W0=A.div(A.add(A.add(C(1),cc),ss),C(2))
rc=A.add(A.mul(g.c,cc),A.mul(g.s,ss))
rs=A.sub(A.mul(g.c,ss),A.mul(g.s,cc))
Wt=A.div(A.add(A.add(C(1),rc),rs),C(2))
hx=A.sub(A.mul(g.c,A.add(g.h1,C(Q(1,2)))),A.mul(g.s,A.add(g.h2,C(Q(1,2)))))
hy=A.add(A.mul(g.s,A.add(g.h1,C(Q(1,2)))),A.mul(g.c,A.add(g.h2,C(Q(1,2)))))
gx=A.sub(A.mul(g.c,A.add(g.h1,C(Q(3,2)))),A.mul(g.s,A.add(A.add(g.h2,C(Q(1,2))),eta)))
gy=A.add(A.mul(g.s,A.add(g.h1,C(Q(3,2)))),A.mul(g.c,A.add(A.add(g.h2,C(Q(1,2))),eta)))
subx=lambda a:A.sub(a,x)
suby=lambda a:A.sub(a,yy)
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
yt=Q('-.92065667800760613175');zt=Q('.06189741100766035970')
qt=Q('3.91553413751747532652')
box=((qt-Q(2,10**16),qt+Q(1,10**16)),(yt-Q(1,10**12),yt+Q(1,10**12)),
 (zt-Q(1,10**12),zt+Q(1,10**12)),(Q('.139'),Q('.141')),(Q('-.001'),Q('.001')),
 (Q('.099'),Q('.101')),(Q('1.349'),Q('1.351')),(Q('-.321'),Q('-.319')))

def generate():
 out=g.OUT/'EqualityBox.lean'
 lines=['''module

public import SquaresInCircles.Eight.ExactFamily.Expression

/-! Exact interval certificates for the complete closed equality parameter box.
Every certificate is checked by evaluating its rational interval arithmetic in the
kernel. -/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option linter.all false
namespace SquaresInCircles.Eight.ExactFamily.EqualityGenerated
open Arithmetic
''','def box : QBox 8 := '+g.boxlit(box),'','''/-- An expression valid on `box` lies in every rational interval containing its range. -/
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
 lines += ['end SquaresInCircles.Eight.ExactFamily.EqualityGenerated','']
 lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
 out.write_text('\n'.join(lines));print({'bytes':out.stat().st_size,'expressions':len(targets)})
if __name__=='__main__':generate()
