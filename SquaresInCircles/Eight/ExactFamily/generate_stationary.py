#!/usr/bin/env python3
"""Generate exact rational interval data for the stationary equations.

The default output is the retained local existence and bracket data. The
active global uniqueness proof is geometric and needs no root cover.
`--legacy-root-cover` explicitly regenerates the historical search archive.
This program never invokes Lean, lake, a compiler, or CI; its output remains
subject to the ordinary Lean interval and closed-box predicates.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path
import json
import sys


class Algebra:
    def __init__(self):
        self.nodes = []
        self.memo = {}

    def node(self, op, *args):
        key = (op, *args)
        if key not in self.memo:
            self.memo[key] = len(self.nodes)
            self.nodes.append(key)
        return self.memo[key]

    def const(self, x): return self.node('const', Q(x))
    def var(self, i): return self.node('var', i)
    def neg(self, x):
        n = self.nodes[x]
        if n[0] == 'const': return self.const(-n[1])
        if n[0] == 'neg': return n[1]
        return self.node('neg', x)
    def add(self, a, b):
        if a == self.const(0): return b
        if b == self.const(0): return a
        if self.nodes[a][0] == self.nodes[b][0] == 'const':
            return self.const(self.nodes[a][1] + self.nodes[b][1])
        return self.node('add', a, b)
    def sub(self, a, b): return self.add(a, self.neg(b))
    def mul(self, a, b):
        if a == self.const(0) or b == self.const(0): return self.const(0)
        if a == self.const(1): return b
        if b == self.const(1): return a
        if self.nodes[a][0] == self.nodes[b][0] == 'const':
            return self.const(self.nodes[a][1] * self.nodes[b][1])
        return self.node('mul', a, b)
    def inv(self, a):
        if self.nodes[a][0] == 'const': return self.const(1/self.nodes[a][1])
        return self.node('inv', a)
    def div(self, a, b): return self.mul(a, self.inv(b))
    def sq(self, a): return self.node('pow', a, 2)
    def sqrt(self, a): return self.node('sqrt', a)

    def derivative(self, a, v, memo=None):
        if memo is None: memo = {}
        if (a,v) in memo: return memo[a,v]
        n = self.nodes[a]
        op = n[0]
        if op == 'const': r = self.const(0)
        elif op == 'var': r = self.const(int(n[1] == v))
        elif op == 'neg': r = self.neg(self.derivative(n[1],v,memo))
        elif op == 'add': r = self.add(self.derivative(n[1],v,memo),self.derivative(n[2],v,memo))
        elif op == 'mul':
            r = self.add(self.mul(self.derivative(n[1],v,memo),n[2]),
                         self.mul(n[1],self.derivative(n[2],v,memo)))
        elif op == 'inv':
            r = self.neg(self.div(self.derivative(n[1],v,memo),self.sq(n[1])))
        elif op == 'pow':
            assert n[2] == 2
            r = self.mul(self.const(2),self.mul(n[1],self.derivative(n[1],v,memo)))
        elif op == 'sqrt':
            r = self.div(self.derivative(n[1],v,memo),self.mul(self.const(2),a))
        else: raise ValueError(op)
        memo[a,v] = r
        return r

    def dependencies(self, targets):
        out = set()
        def walk(i):
            if i in out: return
            out.add(i)
            n = self.nodes[i]
            if n[0] in ('const','var'): return
            walk(n[1])
            if n[0] in ('add','mul'): walk(n[2])
        for i in targets: walk(i)
        return sorted(out)


A = Algebra()
q,y,z = [A.var(i) for i in range(3)]
c1,c2,c3 = [A.const(i) for i in (1,2,3)]
x1 = A.sqrt(A.sub(q,A.sq(y)))
x2 = A.sqrt(A.sub(q,A.sq(A.add(y,c2))))
x3 = A.sub(x2,c3)
y3 = A.sqrt(A.sub(q,A.sq(x3)))
y4 = A.sub(y3,c2)
x4 = A.neg(A.sqrt(A.sub(q,A.sq(y4))))
den = A.add(c1,A.sq(z))
c = A.div(A.sub(c1,A.sq(z)),den)
s = A.div(A.mul(c2,z),den)
h1 = A.sub(A.sub(A.add(A.mul(c,x1),A.mul(s,y)),c2),c)
h2 = A.sub(A.sub(A.add(A.neg(A.mul(s,x4)),A.mul(c,y4)),c1),s)
F = A.sub(A.add(A.sq(h1),A.sq(h2)),q)
Fq,Fy,Fz = [A.derivative(F,i) for i in range(3)]
Fyy = A.derivative(Fy,1)
Fyz = A.derivative(Fy,2)
Fzz = A.derivative(Fz,2)
outputs = [F,Fq,Fy,Fz,Fyy,Fyz,Fzz]


def floor_q(x): return x.numerator // x.denominator
def ceil_q(x): return -floor_q(-x)
def rounded(I,bits):
    D = 1 << bits
    return Q(floor_q(I[0]*D),D), Q(ceil_q(I[1]*D),D)
def sqrt_bounds(I,bits):
    D = 1 << bits
    def floor_sqrt(x):
        return isqrt((x.numerator*D*D)//x.denominator)
    if I[0] < 0: raise ValueError('negative radical interval')
    lo,hi = floor_sqrt(I[0]),floor_sqrt(I[1])
    if Q(hi*hi,D*D) < I[1]: hi += 1
    return Q(lo,D),Q(hi,D)

def evaluate(box,targets=outputs,bits=40):
    vals = {}
    for i in A.dependencies(targets):
        n = A.nodes[i]; op=n[0]
        if op == 'const': I=(n[1],n[1])
        elif op == 'var': I=box[n[1]]
        elif op == 'neg': I=(-vals[n[1]][1],-vals[n[1]][0])
        elif op == 'add':
            a,b=vals[n[1]],vals[n[2]]; I=(a[0]+b[0],a[1]+b[1])
        elif op == 'mul':
            a,b=vals[n[1]],vals[n[2]]; P=[u*v for u in a for v in b];I=(min(P),max(P))
        elif op == 'inv':
            a=vals[n[1]]
            if a[0] <= 0: raise ValueError('nonpositive inverse interval')
            I=(1/a[1],1/a[0])
        elif op == 'pow':
            a=vals[n[1]]
            # QInterval.pow uses multiplication, preserving its own semantics.
            P=[u*v for u in a for v in a]; I=(min(P),max(P))
        elif op == 'sqrt': I=sqrt_bounds(vals[n[1]],bits)
        else: raise ValueError(op)
        vals[i] = I if op in ('const','var','sqrt') else rounded(I,bits)
    return vals

def inside(a,b): return all(J[0]<=I[0] and I[1]<=J[1] for I,J in zip(a,b))

local = ((Q(7831,2000),Q(9789,2500)),(Q(-937,1000),Q(-179,200)),(Q(1,20),Q(81,1000)))
initial = ((Q(6241,1600),Q(9789,2500)),(Q(-1),Q(-1,2)),(Q(0),Q(1,10)))

def isolate():
    leaves=[]; nodes=[]
    def visit(box,depth=0):
        if inside(box,local):
            i=len(nodes);nodes.append(('inside',box));return i
        try:
            V=evaluate(box,[F,Fy,Fz])
            excluded=next((j for j in [F,Fy,Fz] if V[j][1]<0 or 0<V[j][0]),None)
        except ValueError:
            excluded=None
        if excluded is not None:
            i=len(nodes);nodes.append(('excluded',box,excluded));leaves.append(i);return i
        if depth >= 48: raise RuntimeError(('unresolved',box))
        widths=[(I[1]-I[0])*scale for I,scale in zip(box,[Q(8),Q(1),Q(3)])]
        axis=max(range(3),key=lambda i:widths[i])
        cut=(box[axis][0]+box[axis][1])/2
        L=list(box);R=list(box);L[axis]=(box[axis][0],cut);R[axis]=(cut,box[axis][1])
        li=visit(tuple(L),depth+1);ri=visit(tuple(R),depth+1)
        i=len(nodes);nodes.append(('split',axis,cut,li,ri));return i
    root=visit(initial)
    return nodes,root


def rat(q):
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def interval(I): return f'⟨{rat(I[0])},{rat(I[1])}⟩'
def boxlit(b): return '!['+', '.join(map(interval,b))+']'

def formula_node(n):
    op=n[0]
    if op=='const': return f'.const {rat(n[1])}'
    if op=='var': return f'.var {n[1]}'
    if op in ('neg','inv','sqrt'): return f'.{op} n{n[1]}'
    if op=='pow': return f'.pow n{n[1]} {n[2]}'
    return f'.{op} n{n[1]} n{n[2]}'

def expr_lines(box,target,bits=40):
    V=evaluate(box,[target],bits)
    lines=[]
    for i in A.dependencies([target]):
        n=A.nodes[i];op=n[0]
        core=formula_node(n)
        if op=='sqrt': core += f' {interval(V[i])}'
        elif op not in ('const','var'):
            core=f'.enclose ({core}) {interval(V[i])}'
        lines.append(f'  let n{i} : ScalarExpr 3 := {core}')
    lines.append(f'  exact n{target}')
    return lines

header='''module

public import SquaresInCircles.Eight.ExactFamily.RootCover

/-! Uncompiled deterministic exact-rational proof data.  Generated by
`ExactFamily/generate_stationary.py`.  All validity goals use ordinary
kernel-reduced `decide`; this file never imports an external pass flag. -/

@[expose] public section
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace SquaresInCircles.Eight.ExactFamily.Generated
open Arithmetic

'''

def write_lean(out,nodes,root):
    lines=[header,'def stationaryFormula : Formula 3 := by']
    for i in A.dependencies([F]): lines.append(f'  let n{i} : Formula 3 := {formula_node(A.nodes[i])}')
    lines += [f'  exact n{F}','',
      'def stationaryTargets : Fin 3 → Formula 3 :=',
      '  ![stationaryFormula, stationaryFormula.diff 1, stationaryFormula.diff 2]','',
      'def localBox : QBox 3 := '+boxlit(local),'',
      'def initialBox : QBox 3 := '+boxlit(initial),'',
      'end SquaresInCircles.Eight.ExactFamily.Generated','']
    (out/'StationaryFormula.lean').write_text('\n'.join(lines))
    chunks=[]
    chunk_size=128
    # A theorem is generated for each complete closed node, using previously
    # generated children.  Exact intervals are data, not user assumptions.
    for start in range(0,len(nodes),chunk_size):
        end=min(len(nodes),start+chunk_size)
        name=f'RootCover{start//chunk_size:03d}'
        imports=['SquaresInCircles.Eight.ExactFamily.RootCover',
          'SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula']
        needed=set()
        for n in nodes[start:end]:
            if n[0]=='split':
                for child in n[3:]:
                    if child<start: needed.add(child//chunk_size)
        imports += [f'SquaresInCircles.Eight.ExactFamily.Generated.RootCover{k:03d}' for k in sorted(needed)]
        text=header.replace('public import SquaresInCircles.Eight.ExactFamily.RootCover',
          '\n'.join('public import '+i for i in imports))
        lines=[text]
        for i in range(start,end):
            n=nodes[i]
            if n[0]=='split':
                _,axis,cut,li,ri=n
                b=list(nodes_box(nodes,li));b[axis]=(b[axis][0],nodes_box(nodes,ri)[axis][1]);b=tuple(b)
            else: b=n[1]
            lines += [f'def box{i} : QBox 3 := {boxlit(b)}','']
            if n[0]=='excluded':
                target=n[2];j={F:0,Fy:1,Fz:2}[target]
                lines += [f'def expression{i} : ScalarExpr 3 := by',*expr_lines(b,target),'',
                  f'theorem expression{i}_valid :',
                  f'    (FormulaCertificate.mk expression{i}).Valid box{i} (stationaryTargets {j}) := by decide','']
            lines += [f'theorem node{i} (env : Fin 3 → ℝ) (he : box{i}.Mem env)',
              '    (hz : SimultaneousZeros stationaryTargets env) : localBox.Mem env := by']
            if n[0]=='inside':
                lines += ['  apply box_mem_of_subset (box := box'+str(i)+') _ he',
                  '  intro j; fin_cases j <;> norm_num [box'+str(i)+',localBox]','']
            elif n[0]=='excluded':
                target=n[2];j={F:0,Fy:1,Fz:2}[target]
                lines += ['  have hn := interval_excludes_zero (FormulaCertificate.mk expression'+str(i)+')',
                  '    expression'+str(i)+'_valid (by decide) he',
                  f'  exact False.elim (hn (hz {j}))','']
            else:
                _,axis,cut,li,ri=n
                lines += [f'  exact closed_box_split box{i} {axis} {rat(cut)}',
                  f'    (fun x hx hxz => node{li} x (by',
                  f'      simpa [box{i},box{li},QBox.left,Function.update,QBox.Mem] using hx) hxz)',
                  f'    (fun x hx hxz => node{ri} x (by',
                  f'      simpa [box{i},box{ri},QBox.right,Function.update,QBox.Mem] using hx) hxz)',
                  '    env he hz','']
        lines += ['end SquaresInCircles.Eight.ExactFamily.Generated','']
        (out/(name+'.lean')).write_text('\n'.join(lines));chunks.append(name)
    text=header.replace('public import SquaresInCircles.Eight.ExactFamily.RootCover',
      'public import SquaresInCircles.Eight.ExactFamily.Generated.'+chunks[-1])
    text += f'''theorem stationary_localization (env : Fin 3 → ℝ)
    (he : initialBox.Mem env) (hz : SimultaneousZeros stationaryTargets env) :
    localBox.Mem env := by
  apply node{root} env _ hz
  simpa [box{root},initialBox] using he

end SquaresInCircles.Eight.ExactFamily.Generated
'''
    (out/'StationaryLocalization.lean').write_text(text)

def nodes_box(nodes,i):
    n=nodes[i]
    if n[0]!='split':return n[1]
    _,axis,cut,l,r=n
    b=list(nodes_box(nodes,l));b[axis]=(b[axis][0],nodes_box(nodes,r)[axis][1]);return tuple(b)

def write_local(out):
    quarter=A.const(Q(1,4))
    det=A.sub(A.mul(A.sub(Fyy,quarter),A.sub(Fzz,quarter)),A.sq(Fyz))
    yt=Q('-0.92065667800760613175');zt=Q('0.06189741100766035970')
    qcenter=Q('3.91553413751747532652')
    qlo=qcenter-Q(2,10**16);qhi=qcenter+Q(1,10**16)
    bounds={'F':F,'Fq':Fq,'Fy':Fy,'Fz':Fz,'Fyy':Fyy,'Fyz':Fyz,'Fzz':Fzz,
      'xOne':x1,'xTwo':x2,'yThree':y3,'xFour':x4,'cosine':c,'sine':s,'hOne':h1,'hTwo':h2,
      'determinant':det}
    local_header=header.replace('ExactFamily.RootCover','ExactFamily.Expression')
    lines=[local_header]
    for i,n in enumerate(A.nodes):
        core=formula_node(n).replace(' n',' formula')
        lines.append(f'def formula{i} : Formula 3 := {core}')
    lines += ['',*['def '+name+'Formula : Formula 3 := formula'+str(i) for name,i in bounds.items()],
      'def stationaryFormula : Formula 3 := FFormula',
      'def stationaryTargets : Fin 3 → Formula 3 := ![FFormula,FyFormula,FzFormula]',
      'def localBox : QBox 3 := '+boxlit(local),
      'def initialBox : QBox 3 := '+boxlit(initial),
      'def trialY : ℝ := '+rat(yt),'def trialZ : ℝ := '+rat(zt),
      'def sharpLower : ℝ := '+rat(qlo),'def sharpUpper : ℝ := '+rat(qhi),'',
      'theorem Fq_diff : FFormula.diff 0 = FqFormula := by decide',
      'theorem Fy_diff : FFormula.diff 1 = FyFormula := by decide',
      'theorem Fz_diff : FFormula.diff 2 = FzFormula := by decide',
      'theorem Fyy_diff : FyFormula.diff 1 = FyyFormula := by decide',
      'theorem Fyz_diff : FyFormula.diff 2 = FyzFormula := by decide',
      'theorem Fzz_diff : FzFormula.diff 2 = FzzFormula := by decide','']
    for name,target in bounds.items():
        lines += [f'def scalar{name} (q y z : ℝ) : ℝ := by']
        for i in A.dependencies([target]):
            n=A.nodes[i];op=n[0]
            if op=='const':core=f'(({rat(n[1])}:ℚ):ℝ)'
            elif op=='var':core=['q','y','z'][n[1]]
            elif op=='neg':core=f'-n{n[1]}'
            elif op=='inv':core=f'(n{n[1]})⁻¹'
            elif op=='sqrt':core=f'Real.sqrt n{n[1]}'
            elif op=='pow':core=f'n{n[1]}^{n[2]}'
            elif op=='add':core=f'n{n[1]}+n{n[2]}'
            elif op=='mul':core=f'n{n[1]}*n{n[2]}'
            lines.append(f'  let n{i} : ℝ := {core}')
        lines += [f'  exact n{target}',
          f'theorem {name}_eval (q y z : ℝ) : {name}Formula.eval ![q,y,z] = scalar{name} q y z := by rfl','']
    defs=', '.join('formula'+str(i) for i in range(len(A.nodes)))
    lines += ['theorem determinant_eval (env : Fin 3 → ℝ) :',
      '    determinantFormula.eval env =',
      '      (FyyFormula.eval env-1/4)*(FzzFormula.eval env-1/4)-(FyzFormula.eval env)^2 := by',
      '  norm_num [determinantFormula,FyyFormula,FyzFormula,FzzFormula,Formula.eval,'+defs+'] <;> ring','',
      'theorem mixed_partials (env : Fin 3 → ℝ) :',
      '    (FzFormula.diff 1).eval env = FyzFormula.eval env := by',
      '  norm_num [FzFormula,FyzFormula,Formula.diff,Formula.plus,Formula.minus,Formula.times,',
      '    Formula.power,Formula.reciprocal,Formula.quotient,Formula.eval,'+defs+']',
      '  simp only [mul_inv_rev,inv_pow]',
      '  ring','',
      'end SquaresInCircles.Eight.ExactFamily.Generated','']
    (out/'StationaryFormula.lean').write_text('\n'.join(lines))
    text=header.replace('public import SquaresInCircles.Eight.ExactFamily.RootCover',
      'public import SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula')
    lines=[text]
    def certificate(name,box,target,lo=None,hi=None,bits=80,regular=False):
        nonlocal lines
        lines += [f'def {name}Box : QBox 3 := {boxlit(box)}',
          f'def {name}Expression : ScalarExpr 3 := by',*expr_lines(box,target,bits),'',
          f'theorem {name}_valid : (FormulaCertificate.mk {name}Expression).Valid',
          f'    {name}Box formula{target} := by decide','']
        if regular:
            lines += [f'theorem {name}_regular (env : Fin 3 → ℝ) (he : {name}Box.Mem env) :',
              f'    formula{target}.RegularAt env := by',
              f'  rw [← {name}_valid.1]',
              f'  exact strictValid_regular {name}Box {name}Expression',
              f'    {name}_valid.2 (by decide) he','']
        if lo is not None and hi is not None:
            lines += [f'theorem {name}_bound (env : Fin 3 → ℝ) (he : {name}Box.Mem env) :',
              f'    ({rat(Q(lo))}:ℝ) ≤ formula{target}.eval env ∧ formula{target}.eval env ≤ {rat(Q(hi))} := by',
              f'  have hb := FormulaCertificate.sound {name}_valid he',
              f'  exact QInterval.mem_mono hb (by decide) (by decide)','']
    certificate('fullF',local,F,regular=True)
    certificate('fullFy',local,Fy,regular=True)
    certificate('fullFz',local,Fz,regular=True)
    certificate('fullFq',local,Fq,-4,-3)
    certificate('fullFyy',local,Fyy,6,9)
    for name,target,lo,hi in [
      ('localXOne',x1,Q('1.7428'),Q('1.7649')),
      ('localXTwo',x2,Q('1.6414'),Q('1.6691')),
      ('localYThree',y3,Q('1.4387'),Q('1.4643')),
      ('localXFour',x4,Q('-1.9049'),Q('-1.8974')),
      ('localCosine',c,Q('.9869'),Q('.9951')),
      ('localSine',s,Q('.0993'),Q('.1617')),
      ('localHOne',h1,Q('-1.4263'),Q('-1.3198')),
      ('localHTwo',h2,Q('-1.5316'),Q('-1.3202'))]:
        certificate(name,local,target,lo,hi)
    for i in range(4):
        for j in range(4):
            box=(local[0],(local[1][0]+(local[1][1]-local[1][0])*i/4,
              local[1][0]+(local[1][1]-local[1][0])*(i+1)/4),
              (local[2][0]+(local[2][1]-local[2][0])*j/4,
              local[2][0]+(local[2][1]-local[2][0])*(j+1)/4))
            certificate(f'det{i}{j}',box,det,10,100)
    lines += ['def determinantBoxes : Fin 4 → Fin 4 → QBox 3 :=',
      '  !['+', '.join('!['+', '.join(f'det{i}{j}Box' for j in range(4))+']' for i in range(4))+']','',
      'theorem determinant_bound (i j : Fin 4) (env : Fin 3 → ℝ)',
      '    (he : (determinantBoxes i j).Mem env) :',
      f'    (10:ℝ) ≤ formula{det}.eval env ∧ formula{det}.eval env ≤ 100 := by',
      '  fin_cases i <;> fin_cases j']
    for i in range(4):
        for j in range(4): lines.append(f'  · exact det{i}{j}_bound env he')
    lines += ['',
      'theorem determinant_cover (env : Fin 3 → ℝ) (he : localBox.Mem env) :',
      '    ∃ i j : Fin 4, (determinantBoxes i j).Mem env := by',
      '  have hq := he 0; have hy := he 1; have hz := he 2',
      '  norm_num [localBox,QInterval.Mem] at hq hy hz']
    def cover_y(depth,lo=0):
        if depth==3:
            cover_z(lo,0,0,'  '+'  '*depth);return
        cut=local[1][0]+(local[1][1]-local[1][0])*(lo+1)/4
        indent='  '+'  '*depth
        lines.append(indent+f'by_cases hy{lo} : env 1 ≤ ({rat(cut)}:ℝ)')
        lines.append(indent+'·')
        cover_z(lo,0,0,indent+'  ')
        lines.append(indent+'·')
        cover_y(depth+1,lo+1)
    def cover_z(i,depth,j,indent):
        if j==3:
            leaf(i,j,indent);return
        cut=local[2][0]+(local[2][1]-local[2][0])*(j+1)/4
        lines.append(indent+f'by_cases hz{j} : env 2 ≤ ({rat(cut)}:ℝ)')
        lines.append(indent+'·')
        leaf(i,j,indent+'  ')
        lines.append(indent+'·')
        cover_z(i,depth+1,j+1,indent+'  ')
    def leaf(i,j,indent):
        lines.append(indent+f'refine ⟨{i},{j},?_⟩')
        lines.append(indent+'intro k; fin_cases k <;>')
        lines.append(indent+f'  norm_num [determinantBoxes,det{i}{j}Box,QInterval.Mem] <;> constructor <;> linarith')
    cover_y(0)
    lines.append('')
    trialbox=(local[0],(yt,yt),(zt,zt))
    certificate('trialFy',trialbox,Fy,Q(-1,5000),Q(1,5000),100)
    certificate('trialFz',trialbox,Fz,Q(-1,2500),Q(1,2500),100)
    certificate('lowerTest',((local[0][0],local[0][0]),(yt,yt),(zt,zt)),F,Q(1,8000),Q(1,7000),160)
    certificate('upperTest',((local[0][1],local[0][1]),(yt,yt),(zt,zt)),F,Q(-1,4000),Q(-1,5000),160)
    for name,qv in [('sharpLow',qlo),('sharpHigh',qhi)]:
        b=((qv,qv),(yt,yt),(zt,zt))
        certificate(name+'F',b,F,Q(7,10**16) if name=='sharpLow' else Q(-4,10**16),
          Q(8,10**16) if name=='sharpLow' else Q(-3,10**16),200)
        certificate(name+'Fy',b,Fy,Q(-1,10**15),Q(1,10**15),200)
        certificate(name+'Fz',b,Fz,Q(-1,10**15),Q(1,10**15),200)
    sharpbox=((qlo,qhi),(yt,yt),(zt,zt))
    certificate('sharpTrialFy',sharpbox,Fy,Q(-1,10**15),Q(1,10**15),200)
    certificate('sharpTrialFz',sharpbox,Fz,Q(-1,10**15),Q(1,10**15),200)
    small=((qlo,qhi),(yt-Q(1,10**12),yt+Q(1,10**12)),
      (zt-Q(1,10**12),zt+Q(1,10**12)))
    lines += ['def sharpBox : QBox 3 := '+boxlit(small),'']
    for name,target,lo,hi in [
      ('sharpXOne',x1,Q('1.75152'),Q('1.75159')),
      ('sharpXTwo',x2,Q('1.65843'),Q('1.65852')),
      ('sharpYThree',y3,Q('1.45455'),Q('1.45464')),
      ('sharpXFour',x4,Q('-1.90214'),Q('-1.90211')),
      ('sharpCosine',c,Q('.99231'),Q('.99242')),
      ('sharpSine',s,Q('.12327'),Q('.12338')),
      ('sharpHOne',h1,Q('-1.36797'),Q('-1.36748')),
      ('sharpHTwo',h2,Q('-1.43022'),Q('-1.42976'))]:
        certificate(name,small,target,lo,hi,160)
    lines += ['end SquaresInCircles.Eight.ExactFamily.Generated','']
    (out/'LocalStationaryBounds.lean').write_text('\n'.join(lines))


if __name__ == '__main__':
    out=Path(__file__).parent/'Generated'
    out.mkdir(exist_ok=True)
    if '--legacy-root-cover' in sys.argv:
        cached=out/'root_cover_data.json'
        if cached.exists():
            cache=json.loads(cached.read_text());root=cache['root'];nodes=[]
            for n in cache['nodes']:
                if n[0]=='split': nodes.append((n[0],n[1],Q(n[2]),n[3],n[4]))
                else:nodes.append((n[0],tuple((Q(a),Q(b)) for a,b in n[1]),*n[2:]))
        else:nodes,root=isolate()
        rows=[]
        for i,n in enumerate(nodes):
            if n[0]=='split': rows.append([n[0],n[1],str(n[2]),n[3],n[4]])
            else: rows.append([n[0],[[str(a),str(b)] for a,b in n[1]],*n[2:]])
        (out/'root_cover_data.json').write_text(json.dumps({'root':root,'nodes':rows,'outputs':outputs,
          'algebra':[[n[0],*[str(x) if isinstance(x,Q) else x for x in n[1:]]] for n in A.nodes]},separators=(',',':')))
        print(json.dumps({'nodes':len(nodes),'excluded_leaves':sum(n[0]=='excluded' for n in nodes),
          'inside_leaves':sum(n[0]=='inside' for n in nodes),'algebra_nodes':len(A.nodes)}))
        write_lean(out,nodes,root)
    write_local(out)
    print(json.dumps({'lean_files':len(list(out.glob('*.lean'))),
      'lean_bytes':sum(p.stat().st_size for p in out.glob('*.lean'))}))
