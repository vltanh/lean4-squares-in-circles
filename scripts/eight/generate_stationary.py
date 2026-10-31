#!/usr/bin/env python3
"""Write the formulas of the stationary point and their interval bounds.

    python3 -I scripts/eight/generate_stationary.py

The chain of SquaresInCircles/Eight/ExactFamily/Coordinates.lean is built as a formula in the
variables (q, y, z): the square roots x₁, x₂, y₃, x₄, the cosine and sine of the tilt in its
half-angle tangent z, the fifth corner (h₁, h₂) and the defect F = h₁² + h₂² - q. Derivatives are
taken by the rules of `Formula.diff` (ExactFamily/Expression.lean), so that the kernel can decide
that each written derivative is the symbolic derivative of its formula. The script writes, in
SquaresInCircles/Eight/ExactFamily/Generated,

- StationaryFormula.lean: aliases for F, F_y and F_z, the box localBox, the trial point
  and the bracket [sharpLower, sharpUpper] of qStar;
- LocalStationaryBounds.lean: trial gradient and endpoint bounds, and refined radius-bracket
  bounds.
  Coordinate and Hessian bounds are proved directly from the geometry.

Every numerical bound is evaluated with the fixed-point interval arithmetic of
ExactFamily/FixedEval.lean, integer for integer (`fx_eval`), before it is written, and the script
stops at the first that fails; where the enclosure on the whole box is too wide, the radius
interval is split in half. Adaptive-chain bounds follow from circle geometry directly.
"""
from fractions import Fraction as Q
from math import isqrt
from pathlib import Path

OUT = Path(__file__).resolve().parents[2]/'SquaresInCircles'/'Eight'/'ExactFamily'/'Generated'


class Algebra:
    """Formulas as a graph of shared nodes: a constant, a variable, or an operation on earlier
    nodes. The constant folding of `add`, `neg`, `mul` and `inv` is that of `Formula.plus`,
    `Formula.minus`, `Formula.times` and `Formula.reciprocal`, so `derivative` builds exactly the
    formula of `Formula.diff`."""
    def __init__(self):
        self.nodes = []
        self.memo = {}

    def node(self, op, *args):
        """The index of the node (op, *args), created once."""
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
        """The partial derivative of the node `a` in the variable `v`, by the rules of
        `Formula.diff`."""
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
        """The nodes that the targets depend on, in increasing order: children before parents."""
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


# The chain of ExactFamily/Coordinates.lean in the variables (q, y, z), the defect F, its first
# partial derivatives and its second derivatives in y and z.
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
# Keep the derivative node order stable for the adaptive formulas, although Fq's bound is geometric.
Fq,Fy,Fz = [A.derivative(F,i) for i in range(3)]
Fyy = A.derivative(Fy,1)
Fyz = A.derivative(Fy,2)
Fzz = A.derivative(Fz,2)
outputs = [F,Fq,Fy,Fz,Fyy,Fyz,Fzz]


def floor_q(x): return x.numerator // x.denominator
def ceil_q(x): return -floor_q(-x)
def rounded(I,bits):
    """The interval I rounded outwards to multiples of 2^-bits."""
    D = 1 << bits
    return Q(floor_q(I[0]*D),D), Q(ceil_q(I[1]*D),D)
def sqrt_bounds(I,bits):
    """A bracket at multiples of 2^-bits for the square roots of the interval I, whose lower end
    must be nonnegative: its lower end squared is at most I[0] and its upper end squared at least
    I[1], as `ScalarExpr.Valid` requires of a square root."""
    D = 1 << bits
    def floor_sqrt(x):
        return isqrt((x.numerator*D*D)//x.denominator)
    if I[0] < 0: raise ValueError('negative radical interval')
    lo,hi = floor_sqrt(I[0]),floor_sqrt(I[1])
    if Q(hi*hi,D*D) < I[1]: hi += 1
    return Q(lo,D),Q(hi,D)

def evaluate(box,targets=outputs,bits=40):
    """Interval values of the nodes on a box, by exact rational interval arithmetic: every
    operation is rounded outwards to a multiple of 2^-bits, and a square root gets the bracket of
    `sqrt_bounds`. `expr_lines` writes these values as the brackets of a `ScalarExpr`, and
    `ScalarExpr.Valid` repeats this computation. Raises ValueError where a reciprocal or a square
    root leaves its domain."""
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
            # the square of an interval is its product with itself, as in `QInterval.pow`
            P=[u*v for u in a for v in a]; I=(min(P),max(P))
        elif op == 'sqrt': I=sqrt_bounds(vals[n[1]],bits)
        else: raise ValueError(op)
        vals[i] = I if op in ('const','var','sqrt') else rounded(I,bits)
    return vals

# The fixed-point interval arithmetic of `ExactFamily/FixedEval.lean`, integer for integer: an
# interval is a pair of integers read as multiples of 2^-p, and every operation rounds outwards.
def fx_ofrat(q,p):
    """`DI.ofRat`: the outward enclosure of the rational q."""
    a=q.numerator<<p
    return (a//q.denominator,-((-a)//q.denominator))
# `ofBox`: the outward enclosure of a rational box
def fx_box(box,p): return [(fx_ofrat(I[0],p)[0],fx_ofrat(I[1],p)[1]) for I in box]
def fx_mul(a,b,p):
    """`DI.mul`: the least and the greatest corner product, rounded down and up."""
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
    """The enclosure of the node t by `FixedEval.eval`, or None where the pass fails."""
    try: return fx_eval(box,[t],p)[t]
    except ValueError: return None
def fx_bounded(box,t,lo,hi,p):
    """`FixedEval.bounded`: the enclosure of t lies in [lo, hi], rounded inwards."""
    I=fx_enclosure(box,t,p)
    return I is not None and fx_ofrat(lo,p)[1]<=I[0] and I[1]<=fx_ofrat(hi,p)[0]

# localBox: q in [qMinus, Q0] and (y, z) in the rectangle poseBox of ExactFamily/Analysis.lean
local = ((Q(7831,2000),Q(9789,2500)),(Q(-937,1000),Q(-179,200)),(Q(1,20),Q(81,1000)))


# Lean literals: a rational numeral, a `QInterval` and a `QBox`
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
    """The `Formula` constructor of the node n, with its children named n<index>."""
    op=n[0]
    if op=='const': return f'.const {const_arg(n[1])}'
    if op=='var': return f'.var {n[1]}'
    if op in ('neg','inv','sqrt'): return f'.{op} n{n[1]}'
    if op=='pow': return f'.pow n{n[1]} {n[2]}'
    return f'.{op} n{n[1]} n{n[2]}'

def expr_lines(box,target,bits=40):
    """The `let` lines of a `ScalarExpr` for the target on the box: a square root carries its
    bracket and every other operation is wrapped in `.enclose` with its interval, both from
    `evaluate`."""
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
    """The start of a generated module: the imports, the module docstring doc and the
    namespace."""
    return ('module\n\n'+''.join(f'public import {i}\n' for i in imports)+'\n/-!\n'+doc+'\n-/\n\n'
      '@[expose] public section\nnoncomputable section\nset_option maxRecDepth 100000\n\n'
      'namespace SquaresInCircles.Eight.ExactFamily.Generated\nopen Arithmetic\n\n')

FORMULA_DOC='''# The stationary bracket and local box

The equations and derivatives are named in `StationaryExpressions.lean`.
This module supplies the rational trial point, radius bracket and local box used by
`LocalStationaryBounds.lean`, plus the formula indices used by that checker.
Written by `scripts/eight/generate_stationary.py`.'''

BOUNDS_DOC='''# Eight squares: interval bounds near the stationary point

Bounds on the formulas of `StationaryFormula.lean`, each decided by the kernel with the
fixed-point interval evaluation of `ExactFamily/FixedEval.lean`, at 100 to 200 bits. At the trial
point `F_y` and `F_z` are small for every radius of
`localBox` (`trialFy_bound`, `trialFz_bound`); `F` is positive at `q = qMinus` and negative at
`q = Q0` (`lowerTest_bound`, `upperTest_bound`), and likewise at the two ends of the bracket of
`qStar` (`sharpLowF_bound`, `sharpHighF_bound`); and on the bracket `|F_y|` and `|F_z|` are at
most `10⁻¹⁵` (`sharpTrialFy_bound`, ...). `ExactFamily/Analysis.lean` and
`ExactFamily/Stationary.lean` use these derivative bounds. The coordinate bounds are proved
directly from circle equations and half-angle formulas in `Coordinates.lean` and `Stationary.lean`.
The Hessian and radius-slope bounds follow from circle derivatives and a sheared quadratic form in
`CriticalHessian.lean`; `Analysis.lean` identifies the geometric and symbolic derivatives. Written by `scripts/eight/generate_stationary.py`.'''

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

def decimal20(q):
    """Write a terminating rational exactly, using at most twenty decimal places."""
    scale=10**20
    if scale % q.denominator:
        raise ValueError('not a terminating decimal with at most twenty places')
    n=q.numerator*(scale//q.denominator)
    sign='-' if n<0 else ''
    n=abs(n)
    return (sign+str(n//scale)+'.'+f'{n%scale:020d}').rstrip('0').rstrip('.')

def write_local(out):
    """Write StationaryFormula.lean and LocalStationaryBounds.lean into the directory out."""
    # A short trial proves existence. The refined trial is only for the numerical bracket.
    yt0=Q("-0.92066");zt0=Q("0.0619")
    yt=Q('-0.92065667800760613175');zt=Q('0.06189741100766035970')
    qcenter=Q('3.91553413751747532652')
    qlo=qcenter-Q(2,10**16);qhi=qcenter+Q(1,10**16)
    bounds={'F':F,'Fy':Fy,'Fz':Fz}
    lines=[header(['SquaresInCircles.Eight.ExactFamily.StationaryExpressions'],FORMULA_DOC)]
    lines += [f'abbrev formula{i} : Formula 3 := {name}Formula' for name,i in bounds.items()]
    lines += ['']
    lines += [
      '/-- The box of `(q, y, z)`: `q` in `[qMinus, Q0]` and `(y, z)` in the rectangle `poseBox`',
      'of `ExactFamily/Analysis.lean`. -/',
      'def localBox : QBox 3 := '+boxlit(local),
      '/-- Refined trial position, used for the numerical bracket (`sharpPose_close`). -/',
      'def trialY : ℝ := '+decimal20(yt),
      '/-- Refined half-angle tangent, used only for the numerical bracket. -/',
      'def trialZ : ℝ := '+decimal20(zt),
      '/-- The lower end of the bracket of `qStar` (`qStar_bracket`). -/',
      'def sharpLower : ℝ := '+decimal20(qlo),
      '/-- The upper end of the bracket of `qStar`. -/',
      'def sharpUpper : ℝ := '+decimal20(qhi),'',
      'end SquaresInCircles.Eight.ExactFamily.Generated','']
    lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
    (out/'StationaryFormula.lean').write_text('\n'.join(lines))
    lines=[header(['SquaresInCircles.Eight.ExactFamily.Generated.StationaryFormula',
      'SquaresInCircles.Eight.ExactFamily.FixedEval'],BOUNDS_DOC)+BOUNDS_HELPERS]
    def certificate(name,box,target,lo,hi,bits=80):
        """Write <name>Box and its bound once fixed-point arithmetic confirms it."""
        nonlocal lines
        lines += [f'def {name}Box : QBox 3 := {boxlit(box)}']
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
    # at the trial point: F_y and F_z for every radius of localBox, F at the two ends of the
    # radius interval, F, F_y, F_z at the ends of the bracket of qStar and on the whole bracket
    trialbox=(local[0],(yt0,yt0),(zt0,zt0))
    certificate('trialFy',trialbox,Fy,Q(-1,5000),Q(1,5000),100)
    certificate('trialFz',trialbox,Fz,Q(-1,2500),Q(1,2500),100)
    certificate('lowerTest',((local[0][0],local[0][0]),(yt0,yt0),(zt0,zt0)),F,Q(1,8000),Q(1,7000),160)
    certificate('upperTest',((local[0][1],local[0][1]),(yt0,yt0),(zt0,zt0)),F,Q(-1,4000),Q(-1,5000),160)
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
    lines += ['end SquaresInCircles.Eight.ExactFamily.Generated','']
    lines=[('noncomputable '+l if l.startswith('def ') else l) for l in lines]
    (out/'LocalStationaryBounds.lean').write_text('\n'.join(lines))

if __name__ == '__main__':
    write_local(OUT)
