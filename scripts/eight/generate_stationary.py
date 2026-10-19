#!/usr/bin/env python3
"""Generate exact rational interval data for the stationary equations.

Writes StationaryFormula.lean and LocalStationaryBounds.lean in
SquaresInCircles/Eight/ExactFamily/Generated.
This program produces Lean data, not a proof by external execution.  Every
interval is checked by the ordinary Lean predicates.
It never invokes Lean, lake, a compiler, or CI.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

OUT = Path(__file__).resolve().parents[2]/'SquaresInCircles'/'Eight'/'ExactFamily'/'Generated'


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

# The fixed-point interval arithmetic of `ExactFamily/FixedEval.lean`, integer for integer: an
# interval is a pair of integers read as multiples of 2^-p, and every operation rounds outwards.
def fx_ofrat(q,p):
    a=q.numerator<<p
    return (a//q.denominator,-((-a)//q.denominator))
def fx_box(box,p): return [(fx_ofrat(I[0],p)[0],fx_ofrat(I[1],p)[1]) for I in box]
def fx_mul(a,b,p):
    P=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]]
    return (min(P)>>p,-((-max(P))>>p))
def fx_eval(box,targets,p):
    """The intervals of `FixedEval.eval` on a rational box; ValueError where it fails."""
    B=fx_box(box,p);vals={}
    for i in A.dependencies(targets):
        n=A.nodes[i];op=n[0]
        if op=='const': I=fx_ofrat(n[1],p)
        elif op=='var': I=B[n[1]]
        elif op=='add': a,b=vals[n[1]],vals[n[2]];I=(a[0]+b[0],a[1]+b[1])
        elif op=='neg': a=vals[n[1]];I=(-a[1],-a[0])
        elif op=='mul': I=fx_mul(vals[n[1]],vals[n[2]],p)
        elif op=='inv':
            a=vals[n[1]]
            if a[0]<=0: raise ValueError('reciprocal')
            S=1<<(2*p);I=(S//a[1],-((-S)//a[0]))
        elif op=='sqrt':
            a=vals[n[1]]
            if a[0]<=0: raise ValueError('square root')
            I=(isqrt(a[0]<<p),isqrt(a[1]<<p)+1)
        elif op=='pow':
            a=vals[n[1]];I=(1<<p,1<<p)
            for _ in range(n[2]): I=fx_mul(I,a,p)
        else: raise ValueError(op)
        vals[i]=I
    return vals
def fx_enclosure(box,t,p):
    try: return fx_eval(box,[t],p)[t]
    except ValueError: return None
def fx_bounded(box,t,lo,hi,p):
    I=fx_enclosure(box,t,p)
    return I is not None and fx_ofrat(lo,p)[1]<=I[0] and I[1]<=fx_ofrat(hi,p)[0]

local = ((Q(7831,2000),Q(9789,2500)),(Q(-937,1000),Q(-179,200)),(Q(1,20),Q(81,1000)))


def rat(q):
    return str(q.numerator) if q.denominator==1 else f'({q.numerator}/{q.denominator})'
def interval(I): return f'⟨{rat(I[0])},{rat(I[1])}⟩'
def boxlit(b): return '!['+', '.join(map(interval,b))+']'
def const_arg(q):
    """A constant after `.const`: negative integers need parentheses."""
    t=rat(q)
    return f'({t})' if t.startswith('-') else t
def bound_arg(q):
    """A rational as an explicit argument of a lemma."""
    t=rat(q)
    return t if t.startswith('(') else f'({t})'

def formula_node(n):
    op=n[0]
    if op=='const': return f'.const {const_arg(n[1])}'
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

def header(imports,doc):
    return ('module\n\n'+''.join(f'public import {i}\n' for i in imports)+'\n/-! '+doc+' -/\n\n'
      '@[expose] public section\nnoncomputable section\nset_option maxRecDepth 100000\n'
      'set_option linter.all false\n\n'
      'namespace SquaresInCircles.Eight.ExactFamily.Generated\nopen Arithmetic\n\n')

FORMULA_DOC='''The formulas of the stationary point: the defect `F` of the chain in the variables `(q, y, z)`,
its first partial derivatives and its second derivatives in `y` and `z`, the coordinates of the
chain and the determinant of the shifted Hessian, with the box `localBox` and the bracket
of `qStar`. The derivative identities are decided by evaluating the symbolic derivative in
the kernel.'''

BOUNDS_DOC='''Interval certificates near the stationary point: regularity of `F`, `F_y` and `F_z` on
`localBox`, bounds there on `F_q`, `F_yy`, the coordinates of the chain and the determinant of the
shifted Hessian, and the values of `F` and its first derivatives at the trial point and at the ends
of the bracket of `qStar`. Every bound is decided in the kernel by fixed-point interval evaluation
(`FixedEval`).'''

BOUNDS_HELPERS='''/-- A fixed-point enclosure gives a bound with real endpoints. -/
private theorem bound_of_bounded {p : ℕ} {B : QBox 3} {f : Formula 3} (l h : ℚ) {lr hr : ℝ}
    (hb : FixedEval.bounded p B f l h = true) (hlr : (l : ℝ) = lr) (hhr : (h : ℝ) = hr)
    {env : Fin 3 → ℝ} (he : B.Mem env) : lr ≤ f.eval env ∧ f.eval env ≤ hr := by
  obtain ⟨h1, h2⟩ := FixedEval.bounded_sound hb he
  exact ⟨hlr ▸ h1, hhr ▸ h2⟩

/-- Rational endpoints as real numerals. -/
local macro "rat_cast" : tactic =>
  `(tactic| simp only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero])
'''

# the formulas whose value is also written as an explicit real expression (`scalarF`, ...)
SCALARS=['F','Fy','Fz','xOne','xTwo','yThree','xFour','cosine','sine','hOne','hTwo']

def write_local(out):
    quarter=A.const(Q(1,4))
    det=A.sub(A.mul(A.sub(Fyy,quarter),A.sub(Fzz,quarter)),A.sq(Fyz))
    yt=Q('-0.92065667800760613175');zt=Q('0.06189741100766035970')
    qcenter=Q('3.91553413751747532652')
    qlo=qcenter-Q(2,10**16);qhi=qcenter+Q(1,10**16)
    bounds={'F':F,'Fq':Fq,'Fy':Fy,'Fz':Fz,'Fyy':Fyy,'Fyz':Fyz,'Fzz':Fzz,
      'xOne':x1,'xTwo':x2,'yThree':y3,'xFour':x4,'cosine':c,'sine':s,'hOne':h1,'hTwo':h2,
      'determinant':det}
    lines=[header(['SquaresInCircles.Eight.ExactFamily.Expression'],FORMULA_DOC)]
    nodes=A.dependencies(list(bounds.values()))
    for i in nodes:
        core=formula_node(A.nodes[i]).replace(' n',' formula')
        lines.append(f'def formula{i} : Formula 3 := {core}')
    lines += ['',*['def '+name+'Formula : Formula 3 := formula'+str(i) for name,i in bounds.items()],
      'def localBox : QBox 3 := '+boxlit(local),
      'def trialY : ℝ := '+rat(yt),'def trialZ : ℝ := '+rat(zt),
      'def sharpLower : ℝ := '+rat(qlo),'def sharpUpper : ℝ := '+rat(qhi),'',
      'theorem Fq_diff : FFormula.diff 0 = FqFormula := by decide +kernel',
      'theorem Fy_diff : FFormula.diff 1 = FyFormula := by decide +kernel',
      'theorem Fz_diff : FFormula.diff 2 = FzFormula := by decide +kernel',
      'theorem Fyy_diff : FyFormula.diff 1 = FyyFormula := by decide +kernel',
      'theorem Fyz_diff : FyFormula.diff 2 = FyzFormula := by decide +kernel',
      'theorem Fzz_diff : FzFormula.diff 2 = FzzFormula := by decide +kernel','']
    for name in SCALARS:
        target=bounds[name]
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
          f'theorem {name}_eval (q y z : ℝ) : {name}Formula.eval ![q,y,z] = scalar{name} q y z := by',
          '  rfl','']
    defs=', '.join('formula'+str(i) for i in nodes)
    top=sorted((i for i in A.dependencies([det]) if i>max(Fyy,Fyz,Fzz)),reverse=True)
    assert len(top)==7
    t=[f'formula{i}' for i in top]
    lines += ['theorem determinant_eval (env : Fin 3 → ℝ) :',
      '    determinantFormula.eval env =',
      '      (FyyFormula.eval env-1/4)*(FzzFormula.eval env-1/4)-(FyzFormula.eval env)^2 := by',
      '  simp only [determinantFormula,'+','.join(t[:5])+',',
      '    '+','.join(t[5:])+',Formula.eval,FyyFormula,FzzFormula,FyzFormula]',
      '  push_cast',
      '  ring','',
      'theorem mixed_partials (env : Fin 3 → ℝ) :',
      '    (FzFormula.diff 1).eval env = FyzFormula.eval env := by',
      '  norm_num [FzFormula,FyzFormula,Formula.diff,Formula.plus,Formula.minus,Formula.times,',
      '    Formula.power,Formula.reciprocal,Formula.quotient,Formula.eval,'+defs+']',
      '  ring','',
      'end SquaresInCircles.Eight.ExactFamily.Generated','']
    lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
    (out/'StationaryFormula.lean').write_text('\n'.join(lines))
    lines=[header(['SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula',
      'SquaresInCircles.Eight.ExactFamily.FixedEval'],BOUNDS_DOC)+BOUNDS_HELPERS]
    def certificate(name,box,target,lo=None,hi=None,bits=80,regular=False):
        nonlocal lines
        lines += [f'def {name}Box : QBox 3 := {boxlit(box)}']
        if regular:
            if fx_enclosure(box,target,bits) is None: raise RuntimeError(('regular',name))
            lines += [f'theorem {name}_regular (env : Fin 3 → ℝ) (he : {name}Box.Mem env) :',
              f'    formula{target}.RegularAt env :=',
              f'  FixedEval.regular_sound (p := {bits}) (by decide +kernel) he','']
        if lo is not None and hi is not None:
            lo,hi=Q(lo),Q(hi)
            statement=[f'theorem {name}_bound (env : Fin 3 → ℝ) (he : {name}Box.Mem env) :',
              f'    ({rat(lo)}:ℝ) ≤ formula{target}.eval env ∧ formula{target}.eval env ≤ {rat(hi)} :=']
            call=f'bound_of_bounded (p := {bits}) {bound_arg(lo)} {bound_arg(hi)}'
            if fx_bounded(box,target,lo,hi,bits):
                lines += [*statement,'  '+call,'    (by decide +kernel) (by rat_cast) (by rat_cast) he','']
                return
            # The enclosure on the whole box is too wide: split the radius interval in half.
            mid=(box[0][0]+box[0][1])/2
            for b in [((box[0][0],mid),*box[1:]),((mid,box[0][1]),*box[1:])]:
                if not fx_bounded(b,target,lo,hi,bits): raise RuntimeError(('split',name))
            lines += [statement[0],statement[1]+' by',
              '  -- on each half of the radius interval the enclosure lies inside the bound',
              f'  rcases le_total (env 0) (({mid.numerator}/{mid.denominator} : ℚ) : ℝ) with h | h']
            for side in ['left','right']:
                lines += [f'  · exact {call}',
                  f'      (by decide +kernel) (by rat_cast) (by rat_cast) (QBox.mem_{side} he h)']
            lines.append('')
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
      '  have hq := he 0; have hy := he 1; have hz := he 2']
    def qcast(q): return f'(({q.numerator}/{q.denominator} : ℚ) : ℝ)'
    def cover_y(depth,lo=0):
        if depth==3:
            cover_z(lo,0,0,'  '+'  '*depth);return
        cut=local[1][0]+(local[1][1]-local[1][0])*(lo+1)/4
        indent='  '+'  '*depth
        lines.append(indent+f'by_cases hy{lo} : env 1 ≤ {qcast(cut)}')
        lines.append(indent+'·')
        cover_z(lo,0,0,indent+'  ')
        lines.append(indent+'·')
        cover_y(depth+1,lo+1)
    def cover_z(i,depth,j,indent):
        if j==3:
            leaf(i,j,indent);return
        cut=local[2][0]+(local[2][1]-local[2][0])*(j+1)/4
        lines.append(indent+f'by_cases hz{j} : env 2 ≤ {qcast(cut)}')
        lines.append(indent+'·')
        leaf(i,j,indent+'  ')
        lines.append(indent+'·')
        cover_z(i,depth+1,j+1,indent+'  ')
    def leaf(i,j,indent):
        # the cell (i, j) of the grid: the case hypotheses are its y and z bounds
        ylo='hy.1' if i==0 else f'le_of_lt (lt_of_not_ge hy{i-1})'
        yhi='hy.2' if i==3 else f'hy{i}'
        zlo='hz.1' if j==0 else f'le_of_lt (lt_of_not_ge hz{j-1})'
        zhi='hz.2' if j==3 else f'hz{j}'
        lines.append(indent+f'refine ⟨{i}, {j}, fun k => ?_⟩')
        lines.append(indent+'fin_cases k')
        lines.append(indent+f'exacts [hq, ⟨{ylo}, {yhi}⟩, ⟨{zlo}, {zhi}⟩]')
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
        if name=='sharpLow':
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
    lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
    (out/'LocalStationaryBounds.lean').write_text('\n'.join(lines))

if __name__ == '__main__':
    write_local(OUT)
