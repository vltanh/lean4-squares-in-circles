#!/usr/bin/env python3
"""Emit exact interval data on a fixed stationary-graph cover.

Writes AdaptiveFormula.lean and AdaptiveBounds.lean in
SquaresInCircles/Eight/ExactFamily/Generated.  The floating evaluation only
proposes a rational root bracket.  Every bound that AdaptiveBounds.lean checks
(the two strict derivative signs of each box and the estimates on the hulls) is
first evaluated here by the same fixed-point interval arithmetic
(`generate_stationary.fx_*`); no floating value is a premise.  This source
generator never invokes Lean.
"""
from fractions import Fraction as Q
from pathlib import Path
import math
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent))
import generate_stationary as g

A=g.A
c,s,x1,x2,x3,y3,x4,y4,h1,h2=g.c,g.s,g.x1,g.x2,g.x3,g.y3,g.x4,g.y4,g.h1,g.h2
C=A.const
two=C(2)
rawA=A.div(c,A.mul(two,x1))
rawa=A.sub(s,A.div(A.mul(c,g.y),x1))
rawB=A.div(rawa,A.mul(two,A.add(g.y,two)))
rawb=A.div(A.mul(rawa,x2),A.add(g.y,two))
rawD=A.div(rawb,A.mul(two,A.neg(x3)))
rawd=A.mul(A.mul(two,rawD),y3)
rawH=A.inv(A.mul(two,A.neg(h1)))
rawe=A.div(A.neg(h2),A.neg(h1))
rawE=A.div(A.mul(s,rawe),A.mul(two,A.neg(x4)))
mass=A.add(A.add(A.add(A.add(rawA,rawB),rawD),rawE),rawH)
omega=A.inv(mass)
alpha,beta,delta,epsilon=[A.mul(omega,v) for v in (rawa,rawb,rawd,rawe)]
mu=[A.mul(omega,v) for v in (rawA,rawB,rawD,rawE,rawH)]
Y=A.sub(x1,x2)
J=A.sub(A.div(A.mul(epsilon,c),beta),A.div(A.mul(y3,A.neg(x4)),A.neg(x3)))
X=A.mul(beta,A.add(A.add(g.y,two),J))
K=A.mul(beta,A.add(y3,J))
L=A.div(A.mul(A.mul(epsilon,s),A.neg(y4)),A.neg(x4))
h2t=A.sub(A.neg(A.mul(c,A.add(x4,C(1)))) ,A.mul(s,y4))
N=A.neg(A.mul(epsilon,A.add(h1,h2t)))
reserves=[X,A.sub(A.mul(alpha,A.sub(C(1),Y)),X),K,A.sub(beta,K),
 A.mul(beta,A.sub(C(Q('-0.917')),J)),A.mul(beta,A.add(C(Q('1.057')),J)),
 L,A.sub(N,A.mul(C(Q('.392')),omega)),A.sub(A.mul(C(Q('.485')),omega),N)]
named={'omega':omega,'alpha':alpha,'beta':beta,'delta':delta,'epsilon':epsilon,'hTwo':h2}
for i,t in enumerate(reserves):named['reserve'+str(i)]=t
ka=A.div(A.mul(alpha,x1),c)
kb=A.mul(beta,A.add(g.y,two))
kd=A.mul(delta,A.neg(x3))
ke=A.div(A.mul(delta,A.neg(x4)),s)
kh=A.mul(epsilon,A.neg(h1))
ww=C(Q(4209,5000))
quadratic=A.add(A.add(A.div(A.add(A.mul(ka,s),ke),two),A.div(ww,two)),
 A.add(A.div(A.mul(epsilon,s),two),A.mul(C(Q(3,4)),ww)))
cubic=A.add(A.div(A.add(A.add(ka,kb),A.add(kd,kh)),C(6)),
 A.add(A.div(ww,C(6)),A.add(A.div(epsilon,C(6)),A.div(ww,two))))
named['quadratic']=quadratic
named['cubic']=cubic

qcenter=Q('3.91553413751747532652')
qlo,qhi=qcenter-Q(2,10**16),qcenter+Q(1,10**16)
NCELLS=256
step=Q(31,1000*NCELLS)
rho=Q(56793,5000000)
w=Q(4209,5000)

def float_value(target,box):
    vals={}
    for i in A.dependencies([target]):
        n=A.nodes[i];op=n[0]
        if op=='const':v=float(n[1])
        elif op=='var':v=float(box[n[1]])
        elif op=='add':v=vals[n[1]]+vals[n[2]]
        elif op=='mul':v=vals[n[1]]*vals[n[2]]
        elif op=='neg':v=-vals[n[1]]
        elif op=='inv':v=1/vals[n[1]]
        elif op=='pow':v=vals[n[1]]**n[2]
        elif op=='sqrt':v=math.sqrt(vals[n[1]])
        vals[i]=v
    return vals[target]

def cell(k):
    zl=Q(1,20)+step*k;zu=zl+step;zm=(zl+zu)/2
    lo,hi=-.937,-.895
    for _ in range(48):
        y=(lo+hi)/2
        if float_value(g.Fy,(qcenter,y,zm))<0:lo=y
        else:hi=y
    yc=Q(round((lo+hi)/2*10**8),10**8)
    rad=Q(1,5000)
    while True:
        yl,yu=yc-rad,yc+rad
        lowbox=((qlo,qhi),(yl,yl),(zl,zu))
        highbox=((qlo,qhi),(yu,yu),(zl,zu))
        low=g.evaluate(lowbox,[g.Fy],100)[g.Fy]
        high=g.evaluate(highbox,[g.Fy],100)[g.Fy]
        if low[1]<0<high[0]:break
        rad+=Q(1,10000)
    box=((qlo,qhi),(yl,yu),(zl,zu))
    return box,lowbox,highbox

header='''module

public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula

/-! Proof data for the complete fixed cover of the adaptive stationary curve: the formulas of
the adaptive estimates and the 256 graph boxes with their endpoint boxes. -/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option linter.all false
namespace SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
open Arithmetic Generated

'''

graph_facts='''set_option synthInstance.maxSize 100000 in
/-- The table of graph boxes: every radius interval is the sharp interval, the `z` intervals
are the consecutive cells of width `31/256000` from `1/20`, and every `y` interval is a
nondegenerate subinterval of `[-937/1000, -179/200]`. The quantifier is unrolled over the
256 boxes and the numerals are compared. -/
private theorem graphBoxes_data : ∀ i : Fin 256,
    graphBoxes i 0 = ⟨97888353437936878163/25000000000000000000,
      97888353437936885663/25000000000000000000⟩ ∧
    graphBoxes i 2 = ⟨1/20+31/256000*i.val, 1/20+31/256000*(i.val+1)⟩ ∧
    -(937/1000) ≤ (graphBoxes i 1).lo ∧ (graphBoxes i 1).lo < (graphBoxes i 1).hi ∧
      (graphBoxes i 1).hi ≤ -(179/200) := by
  simp (config := {maxSteps := 1000000}) only [Fin.forall_fin_succ, graphBoxes,
    Matrix.cons_val_zero, Matrix.cons_val_succ, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, IsEmpty.forall_iff, and_true, true_and, Fin.val_zero,
    Fin.val_succ, QInterval.mk.injEq]
  decide +kernel

theorem graph_shape (i : Fin 256) :
    (graphBoxes i 0).Mem q ↔ sharpLower ≤ q ∧ q ≤ sharpUpper := by
  rw [(graphBoxes_data i).1]
  norm_num [QInterval.Mem, sharpLower, sharpUpper]

theorem graph_z (i : Fin 256) (z : ℝ) :
    (graphBoxes i 2).Mem z ↔ zLo i ≤ z ∧ z ≤ zHi i := by
  rw [(graphBoxes_data i).2.1]
  simp only [QInterval.Mem, zLo, zHi]
  push_cast
  rfl

theorem graph_local (i : Fin 256) :
    -(937/1000:ℝ) ≤ yLo i ∧ yLo i < yHi i ∧ yHi i ≤ -(179/200) := by
  obtain ⟨-, -, h1, h2, h3⟩ := graphBoxes_data i
  refine ⟨?_, ?_, ?_⟩ <;> simp only [yLo, yHi]
  · have h := (Rat.cast_le (K := ℝ)).2 h1
    push_cast at h
    exact h
  · exact_mod_cast h2
  · have h := (Rat.cast_le (K := ℝ)).2 h3
    push_cast at h
    exact h
'''

BITS=100
BUFFER=Q(1,10**6)
QUADRATIC=Q(232,25)
CUBIC=Q(3,2)
HTWO=(Q(-29,20),Q(-7,5))

HULL=8   # graph boxes per hull

def graph_checks():
    """The five kinds of graph estimate: (formula, lower, upper), in the order of `hullCheck`."""
    return ([(t,rho,Q(2)) for t in reserves]+[(t,Q(1,100),w) for t in [alpha,beta,beta,delta,omega,omega,epsilon]]+
      [(h2,*HTWO),(quadratic,Q(0),QUADRATIC),(cubic,Q(0),CUBIC)])

def hulls(boxes):
    """Boxes containing `HULL` consecutive graph boxes each."""
    out=[]
    for m in range(0,NCELLS,HULL):
        bs=[boxes[k][0] for k in range(m,m+HULL)]
        assert all(b[0]==bs[0][0] for b in bs)
        out.append((bs[0][0],(min(b[1][0] for b in bs),max(b[1][1] for b in bs)),(bs[0][2][0],bs[-1][2][1])))
    return out

def check_bounds(boxes,hs):
    """Every check of AdaptiveBounds.lean, by the fixed-point arithmetic of the Lean evaluator."""
    for k,(b,lb,ub) in enumerate(boxes):
        if not g.fx_bounded(lb,g.Fy,Q(-1),-BUFFER,BITS): raise RuntimeError(('lower',k))
        if not g.fx_bounded(ub,g.Fy,BUFFER,Q(1),BITS): raise RuntimeError(('upper',k))
        if not g.inside(b,hs[k//HULL]): raise RuntimeError(('hull',k))
    for m,H in enumerate(hs):
        for t,lo,hi in graph_checks():
            if not g.fx_bounded(H,t,lo,hi,BITS): raise RuntimeError(('hull check',m))

def wrapped(items,indent,width=100):
    """Comma-separated items in lines of at most `width` characters."""
    lines=[];cur=indent
    for k,item in enumerate(items):
        piece=item+(', ' if k+1<len(items) else '')
        if len(cur)+len(piece.rstrip())>width and cur.strip():
            lines.append(cur.rstrip());cur=indent
        cur+=piece
    lines.append(cur.rstrip())
    return '\n'.join(lines)

def bounds_text(hs):
    nh=len(hs)
    hullnames=wrapped([f'hullCheck_{m}' for m in range(nh)],'    ')
    cellnames=wrapped([f'cellCheck_{k}' for k in range(NCELLS)],'    ')
    r,w_,(ha,hb),qd,cb=rho,w,HTWO,QUADRATIC,CUBIC
    bnd=lambda B,f,lo,hi: f'FixedEval.bounded {BITS} {B} {f} {lo} {hi}'
    return f"""module

public import SquaresInCircles.Eight.ExactFamily.Generated.AdaptiveFormula
public import SquaresInCircles.Eight.ExactFamily.FixedEval

/-!
# Uniform estimates along the stationary curve

There are 256 closed boxes but only seven kinds of bound. The strict signs of the derivative at
both ends of the position interval of each box, from which `Adaptive.lean` obtains the adaptive
stationary point, are checked box by box. The other five kinds of estimate are uniform on {nh}
hulls of {HULL} consecutive graph boxes each, so they are checked once per hull. Every enclosure is a
fixed-point interval evaluation in the kernel (`FixedEval`).
-/

@[expose] public section
noncomputable section
namespace SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
open Arithmetic Generated FixedEval

set_option maxRecDepth 1000000
set_option linter.all false

/-- Boxes containing {HULL} consecutive graph boxes each. -/
noncomputable def graphHull : Fin {nh} → QBox 3 := ![""" + ',\n  '.join(g.boxlit(H) for H in hs) + f"""]

/-- The hull of the graph box `i`. -/
noncomputable def hullOf (i : Fin 256) : Fin {nh} := ⟨i.val / {HULL}, by omega⟩

/-- The five kinds of graph estimate on a hull. -/
noncomputable def hullCheck (m : Fin {nh}) : Bool :=
  (List.finRange 9).all (fun j =>
    {bnd('(graphHull m)','(reserveFormula j)',f'({r.numerator}/{r.denominator})','2')}) &&
    (List.finRange 7).all (fun j =>
      {bnd('(graphHull m)','(lambdaFormula j)','(1/100)',f'({w_.numerator}/{w_.denominator})')}) &&
    {bnd('(graphHull m)','hTwoFormula',f'({ha.numerator}/{ha.denominator})',f'({hb.numerator}/{hb.denominator})')} &&
    {bnd('(graphHull m)','quadraticFormula','0',f'({qd.numerator}/{qd.denominator})')} &&
    {bnd('(graphHull m)','cubicFormula','0',f'({cb.numerator}/{cb.denominator})')}

/-- The derivative signs at both ends of the position interval of box `i`, and its hull. -/
noncomputable def cellCheck (i : Fin 256) : Bool :=
  {bnd('(lowerBoxes i)','FyFormula','(-1)',f'(-1/{BUFFER.denominator})')} &&
    {bnd('(upperBoxes i)','FyFormula',f'(1/{BUFFER.denominator})','1')} &&
    inside (graphBoxes i) (graphHull (hullOf i))

""" + ''.join(f'theorem hullCheck_{m} : hullCheck {m} = true := by decide +kernel\n' for m in range(nh)) + '\n' + \
      ''.join(f'theorem cellCheck_{k} : cellCheck {k} = true := by decide +kernel\n' for k in range(NCELLS)) + f"""
theorem hullCheck_all : ∀ m : Fin {nh}, hullCheck m = true := by
  intro m
  fin_cases m
  exacts [
{hullnames}]

theorem cellCheck_all : ∀ i : Fin 256, cellCheck i = true := by
  intro i
  fin_cases i
  exacts [
{cellnames}]

theorem hull_mem (i : Fin 256) {{env : Fin 3 → ℝ}} (he : (graphBoxes i).Mem env) :
    (graphHull (hullOf i)).Mem env := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  exact box_mem_of_subset (by simpa [inside] using h.2) he

theorem hull_bounds {{m : Fin {nh}}} {{env : Fin 3 → ℝ}} (he : (graphHull m).Mem env) :
    (∀ j : Fin 9, ((({r.numerator}/{r.denominator} : ℚ)) : ℝ) ≤ (reserveFormula j).eval env) ∧
    (∀ j : Fin 7, (lambdaFormula j).eval env ≤ ((({w_.numerator}/{w_.denominator} : ℚ)) : ℝ)) ∧
    ((({ha.numerator}/{ha.denominator} : ℚ)) : ℝ) ≤ hTwoFormula.eval env ∧
    hTwoFormula.eval env ≤ ((({hb.numerator}/{hb.denominator} : ℚ)) : ℝ) ∧
    quadraticFormula.eval env ≤ ((({qd.numerator}/{qd.denominator} : ℚ)) : ℝ) ∧
    cubicFormula.eval env ≤ ((({cb.numerator}/{cb.denominator} : ℚ)) : ℝ) := by
  have h := hullCheck_all m
  simp only [hullCheck, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, true_implies] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨fun j => (FixedEval.bounded_sound (h1 j) he).1,
    fun j => (FixedEval.bounded_sound (h2 j) he).2, (FixedEval.bounded_sound h3 he).1,
    (FixedEval.bounded_sound h3 he).2, (FixedEval.bounded_sound h4 he).2,
    (FixedEval.bounded_sound h5 he).2⟩

theorem lower_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (lowerBoxes i).Mem env) : FyFormula.eval env < 0 := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  have hb := (FixedEval.bounded_sound h.1.1 he).2
  push_cast at hb
  linarith

theorem upper_sign (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (upperBoxes i).Mem env) : 0 < FyFormula.eval env := by
  have h := cellCheck_all i
  simp only [cellCheck, Bool.and_eq_true] at h
  have hb := (FixedEval.bounded_sound h.1.2 he).1
  push_cast at hb
  linarith

theorem reserve_bound (i : Fin 256) (j : Fin 9) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    ({r.numerator}/{r.denominator} : ℝ) ≤ (reserveFormula j).eval env := by
  have h := (hull_bounds (hull_mem i he)).1 j
  push_cast at h
  exact h

theorem weight_bound (i : Fin 256) (j : Fin 7) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    (lambdaFormula j).eval env ≤ {w_.numerator}/{w_.denominator} := by
  have h := (hull_bounds (hull_mem i he)).2.1 j
  push_cast at h
  exact h

theorem hTwo_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) :
    -({-ha.numerator}/{ha.denominator}:ℝ) ≤ hTwoFormula.eval env ∧ hTwoFormula.eval env ≤ -({-hb.numerator}/{hb.denominator}) := by
  have h := hull_bounds (hull_mem i he)
  have h1 := h.2.2.1
  have h2 := h.2.2.2.1
  push_cast at h1 h2
  constructor <;> linarith

theorem quadratic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : quadraticFormula.eval env ≤ {qd.numerator}/{qd.denominator} := by
  have h := (hull_bounds (hull_mem i he)).2.2.2.2.1
  push_cast at h
  exact h

theorem cubic_bound (i : Fin 256) (env : Fin 3 → ℝ)
    (he : (graphBoxes i).Mem env) : cubicFormula.eval env ≤ {cb.numerator}/{cb.denominator} := by
  have h := (hull_bounds (hull_mem i he)).2.2.2.2.2
  push_cast at h
  exact h

end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
"""

def generate():
    out=g.OUT
    boxes=[cell(k) for k in range(NCELLS)]
    lines=[header]
    for i in A.dependencies(list(named.values())):
        lines.append(f'def adaptiveFormula{i} : Formula 3 := '+
          g.formula_node(A.nodes[i]).replace(' n',' adaptiveFormula'))
    for name,target in named.items():
        lines.append(f'def {name}Formula : Formula 3 := adaptiveFormula{target}')
    lines += ['def reserveFormula : Fin 9 → Formula 3 := !['+
      ','.join(f'reserve{i}Formula' for i in range(9))+']',
      'def lambdaFormula : Fin 7 → Formula 3 := ![alphaFormula,betaFormula,betaFormula,'+
      'deltaFormula,omegaFormula,omegaFormula,epsilonFormula]',
      'def graphBoxes : Fin 256 → QBox 3 := !['+
      ',\n  '.join(g.boxlit(b[0]) for b in boxes)+']',
      'def lowerBoxes : Fin 256 → QBox 3 := !['+
      ',\n  '.join(g.boxlit(b[1]) for b in boxes)+']',
      'def upperBoxes : Fin 256 → QBox 3 := !['+
      ',\n  '.join(g.boxlit(b[2]) for b in boxes)+']',
      'def yLo (i : Fin 256) : ℝ := ((graphBoxes i 1).lo:ℝ)',
      'def yHi (i : Fin 256) : ℝ := ((graphBoxes i 1).hi:ℝ)',
      'def zLo (i : Fin 256) : ℝ := 1/20+(31/256000)*(i.val:ℝ)',
      'def zHi (i : Fin 256) : ℝ := 1/20+(31/256000)*(i.val+1:ℝ)','',
      graph_facts,
      'end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated','']
    lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
    (out/'AdaptiveFormula.lean').write_text('\n'.join(lines))
    hs=hulls(boxes)
    check_bounds(boxes,hs)
    (out/'AdaptiveBounds.lean').write_text(bounds_text(hs))
    print({'cells':NCELLS,'hulls':len(hs)},flush=True)

if __name__=='__main__':generate()
