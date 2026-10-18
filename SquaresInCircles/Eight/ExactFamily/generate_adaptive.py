#!/usr/bin/env python3
"""Emit exact interval proofs on a fixed stationary-graph cover.

The floating evaluation only proposes a rational root bracket.  The emitted
Lean certificates contain the two strict derivative signs and every bound;
no floating value is a premise.  This source generator never invokes Lean.
"""
from fractions import Fraction as Q
from pathlib import Path
import math
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
named={'omega':omega,'alpha':alpha,'beta':beta,'delta':delta,'epsilon':epsilon,
 'Y':Y,'J':J,'X':X,'K':K,'L':L,'N':N,'hTwo':h2}
for i,t in enumerate(mu):named['mu'+str(i)]=t
for i,t in enumerate(reserves):named['reserve'+str(i)]=t

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

/-! Uncompiled proof data for the complete fixed cover of the adaptive
stationary curve.  Validity is ordinary rational `decide`, not native code. -/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated
open Arithmetic Generated

'''

def generate():
    out=Path(__file__).parent/'Generated'
    boxes=[cell(k) for k in range(NCELLS)]
    lines=[header]
    for i,n in enumerate(A.nodes):
        lines.append(f'def adaptiveFormula{i} : Formula 3 := '+g.formula_node(n).replace(' n',' adaptiveFormula'))
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
      'theorem graph_shape (i : Fin 256) :',
      '    (graphBoxes i 0).Mem q ↔ sharpLower ≤ q ∧ q ≤ sharpUpper := by',
      '  fin_cases i <;> norm_num [graphBoxes,QInterval.Mem,sharpLower,sharpUpper]','',
      'theorem graph_z (i : Fin 256) (z : ℝ) :',
      '    (graphBoxes i 2).Mem z ↔ zLo i ≤ z ∧ z ≤ zHi i := by',
      '  fin_cases i <;> norm_num [graphBoxes,QInterval.Mem,zLo,zHi]','',
      'theorem graph_local (i : Fin 256) :',
      '    -(937/1000:ℝ) ≤ yLo i ∧ yLo i < yHi i ∧ yHi i ≤ -(179/200) := by',
      '  fin_cases i <;> norm_num [yLo,yHi,graphBoxes]','',
      'end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated','']
    (out/'AdaptiveFormula.lean').write_text('\n'.join(lines))
    chunks=[]
    boundmins=[None]*9
    for start in range(0,NCELLS,16):
        name=f'AdaptiveBounds{start//16:02d}';chunks.append(name)
        lines=[header.replace('Generated.StationaryFormula','Generated.AdaptiveFormula')]
        def cert(nm,b,target,lo,hi):
            v=g.evaluate(b,[target],100)[target]
            if not Q(lo)<=v[0]<=v[1]<=Q(hi):
                raise RuntimeError((nm,tuple(float(x) for x in v),float(lo),float(hi)))
            lines.extend([f'def {nm}Expression : ScalarExpr 3 := by',*g.expr_lines(b,target,100),'',
              f'theorem {nm}_valid : (FormulaCertificate.mk {nm}Expression).Valid',
              f'    {g.boxlit(b)} adaptiveFormula{target} := by decide',
              f'theorem {nm}_bound (env : Fin 3 → ℝ) (he : ({g.boxlit(b)} : QBox 3).Mem env) :',
              f'    ({g.rat(Q(lo))}:ℝ) ≤ adaptiveFormula{target}.eval env ∧',
              f'      adaptiveFormula{target}.eval env ≤ {g.rat(Q(hi))} := by',
              f'  have hb := FormulaCertificate.sound {nm}_valid he',
              '  exact QInterval.mem_mono hb (by decide) (by decide)',''])
        for k in range(start,min(start+16,NCELLS)):
            b,lb,ub=boxes[k]
            cert(f'lower{k}',lb,g.Fy,Q(-1),Q(-1,1000000))
            cert(f'upper{k}',ub,g.Fy,Q(1,1000000),Q(1))
            for j,t in enumerate(reserves):
                cert(f'reserve{k}_{j}',b,t,rho,Q(2))
                v=g.evaluate(b,[t],100)[t][0]
                boundmins[j]=v if boundmins[j] is None else min(v,boundmins[j])
            for j,t in enumerate([alpha,beta,delta,omega,epsilon]):
                cert(f'weight{k}_{j}',b,t,Q(1,100),w)
            cert(f'hTwo{k}',b,h2,Q(-29,20),Q(-7,5))
        lines += ['end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated','']
        (out/(name+'.lean')).write_text('\n'.join(lines))
    lines=[header.replace('public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula',
      '\n'.join('public import SquaresInCircles.Eight.ExactFamily.Generated.'+nm for nm in chunks))]
    lines += ['theorem lower_sign (i : Fin 256) (env : Fin 3 → ℝ)',
      '    (he : (lowerBoxes i).Mem env) : FyFormula.eval env < 0 := by',
      '  fin_cases i']
    for k in range(NCELLS):lines.append(f'  · exact lt_of_le_of_lt (lower{k}_bound env he).2 (by norm_num)')
    lines += ['','theorem upper_sign (i : Fin 256) (env : Fin 3 → ℝ)',
      '    (he : (upperBoxes i).Mem env) : 0 < FyFormula.eval env := by',
      '  fin_cases i']
    for k in range(NCELLS):lines.append(f'  · exact lt_of_lt_of_le (by norm_num) (upper{k}_bound env he).1')
    lines += ['','theorem reserve_bound (i : Fin 256) (j : Fin 9) (env : Fin 3 → ℝ)',
      '    (he : (graphBoxes i).Mem env) :',
      '    (56793/5000000:ℝ) ≤ (reserveFormula j).eval env := by',
      '  fin_cases i <;> fin_cases j']
    for k in range(NCELLS):
        for j in range(9):lines.append(f'  · exact (reserve{k}_{j}_bound env he).1')
    lines += ['','theorem weight_bound (i : Fin 256) (j : Fin 7) (env : Fin 3 → ℝ)',
      '    (he : (graphBoxes i).Mem env) :',
      '    (lambdaFormula j).eval env ≤ 4209/5000 := by',
      '  fin_cases i <;> fin_cases j']
    for k in range(NCELLS):
        for j in [0,1,1,2,3,3,4]:lines.append(f'  · exact (weight{k}_{j}_bound env he).2')
    lines += ['','theorem hTwo_bound (i : Fin 256) (env : Fin 3 → ℝ)',
      '    (he : (graphBoxes i).Mem env) :',
      '    -(29/20:ℝ) ≤ hTwoFormula.eval env ∧ hTwoFormula.eval env ≤ -(7/5) := by',
      '  fin_cases i']
    for k in range(NCELLS):lines.append(f'  · exact hTwo{k}_bound env he')
    lines += ['','end SquaresInCircles.Eight.ExactFamily.AdaptiveGenerated','']
    (out/'AdaptiveBounds.lean').write_text('\n'.join(lines))
    print({'cells':NCELLS,'reserve_lower_bounds':[float(v) for v in boundmins],
      'bytes':sum(p.stat().st_size for p in out.glob('Adaptive*.lean'))},flush=True)

if __name__=='__main__':generate()
