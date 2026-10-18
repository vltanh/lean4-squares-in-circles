#!/usr/bin/env python3
"""Serialize the F8 rational inputs as uncompiled Lean proof source.

This script performs exact coefficient construction only. It does not run
Lean, invoke a proof checker, execute the historical replay scripts, or
interpret a report's status as proof. Each emitted Row.Valid declaration
contains its own polynomial identity and Bernstein expansion for Lean.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import comb
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / 'research/eight'
OUT = ROOT / 'SquaresInCircles/Eight/Generated/Owner'
OUT.mkdir(parents=True, exist_ok=True)
D, S, C, Z = [Q(1), Q(0), Q(1)], [Q(0), Q(2)], [Q(1), Q(0), Q(-1)], [Q(0)]
SIGNS = [1, -1, 1, -1, 1, -1, -1]
ALIGNED = [0, 2, 3, 4, 5]
BASE_OWNERS = [1, 1, 1, 3, 1, 3, 2]

def add(*ps):
    r = [Q(0)] * max(map(len, ps))
    for p in ps:
        for i, x in enumerate(p):
            r[i] += x
    return r

def scale(p, x):
    return [x * y for y in p]

def mul(p, q):
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, x in enumerate(p):
        for j, y in enumerate(q):
            r[i + j] += x * y
    return r

def projection(i, owner, derivative=False):
    j = (i + 1) % 7
    sn, cs = ((Z, D) if i in [0, 2, 4] else (D, Z) if i in [3, 5]
              else (C, S) if i == 1 else (C, scale(S, -1)))
    r = [Z[:] for _ in range(14)]
    def put(k, p, x=1):
        r[k] = add(r[k], scale(p, Q(x)))
    if derivative:
        if owner == 1:
            put(j, cs); put(7+j, sn, SIGNS[j])
        elif owner == 2:
            put(i, sn); put(7+i, cs, SIGNS[i])
        elif owner == 3:
            put(i, cs); put(7+i, sn, -SIGNS[i])
        else:
            put(j, sn); put(7+j, cs, -SIGNS[j])
    elif owner == 1:
        put(7+i, D, SIGNS[i]); put(j, sn); put(7+j, cs, -SIGNS[j])
    elif owner == 2:
        put(i, cs, -1); put(7+i, sn, SIGNS[i]); put(j, D)
    elif owner == 3:
        put(i, sn); put(7+i, cs, SIGNS[i]); put(7+j, D, -SIGNS[j])
    else:
        put(i, D); put(j, cs, -1); put(7+j, sn, -SIGNS[j])
    return r

def cone_data():
    lower = [Q(1,2), Q(1,20), Q(0), Q(0), Q(1,20), Q(1,2), Q(0)]
    upper = [Q(1), Q(4,5), Q(1), Q(1), Q(4,5), Q(1), Q(1)]
    rows, values = [], []
    for i in range(7):
        floor = Q(7,12) if i in [1,4] else Q(447,800)
        ceiling = Q(349,250) if i in [1,4] else Q(283,200)
        for entries, rhs in [({i:1},floor),({i:-1},-ceiling),
                ({i:-lower[i],7+i:1},Q(0)),({i:upper[i],7+i:-1},Q(0)),
                ({7+i:-1},Q(-9,10))]:
            row = [Q(0)]*14
            for j, x in entries.items(): row[j] += x
            rows.append(row); values.append(rhs)
    return rows, values

def construct(mode, r):
    lo, hi = Q(r['lo']), Q(r['hi'])
    lam = [Q(n,10**8) for n in r['lambda']]
    mu = [Q(n,10**8) for n in r['mu']]
    kap = [Q(0)]*35
    for i,n in r['cone']: kap[i] = Q(n,10**8)
    A = [projection(i,j) for i,j in enumerate(r['owners'])]
    W = scale(add(D,C,scale(S,1 if lo>=0 else -1)),Q(1,2))
    rhs = add(*[scale(W if i in [1,6] else D,lam[i]) for i in range(7)])
    force = [add(*[scale(A[i][j],lam[i]) for i in range(7)]) for j in range(14)]
    eps = Q(3,200) if mode=='quarter' else Q(1,1000)
    if mode=='quarter': loss = eps*(Q(3,2)*sum(lam[i] for i in ALIGNED)+2*lam[6])
    elif mode=='mixed': loss = eps*(Q(1001,1000)*max(lam[i] for i in ALIGNED)+2*lam[6])
    else: loss = eps**2*(Q(1001,1000)*max(lam[i] for i in ALIGNED)+Q(9,8)*lam[6])
    rhs = add(rhs,scale(D,-loss))
    if mode=='tilt' and r['vertex'][0]>=0:
        i,j,s,_ = r['vertex']
        derivative = projection(i,j,True); last = projection(6,2,True)
        force = [add(p,scale(d,s*eps*lam[i]),scale(e,-s*eps*lam[6]))
                 for p,d,e in zip(force,derivative,last)]
        wp = scale(add(C,scale(S,-1)),Q(1,2)) if lo>=0 else scale(add(C,S),Q(-1,2))
        rhs = add(rhs,scale(wp,-s*eps*lam[6]),scale(D,eps*lam[i]/2))
    K,v = cone_data()
    force = [add(p,scale(D,sum(kap[k]*K[k][j] for k in range(35)))) for j,p in enumerate(force)]
    rhs = add(rhs,scale(D,sum(kap[k]*v[k] for k in range(35))))
    L = add(rhs,*[scale(p,Q(1,2)) for p in force])
    q = Q(1957767069,500000000) if mode=='tilt' else Q(9789,2500)
    p = add(mul(D,L),scale(mul(D,D),-q*sum(mu)),
        *[scale(add(mul(force[i],force[i]),mul(force[7+i],force[7+i])),
                -1/(4*mu[i])) for i in range(7)])
    p += [Q(0)]*(5-len(p))
    pw = [sum(p[n]*comb(n,j)*lo**(n-j)*(hi-lo)**j for n in range(j,5)) for j in range(5)]
    bs = [sum(pw[j]*Q(comb(i,j),comb(4,j)) for j in range(i+1)) for i in range(5)]
    return p,bs,lam,kap,mu

def rat(x):
    x=Q(x)
    return str(x.numerator) if x.denominator==1 else f'({x.numerator}/{x.denominator})'

def vec(xs): return '!['+', '.join(map(rat,xs))+']'
def lst(xs): return '['+', '.join(map(rat,xs))+']'
def alt(r):
    if r.get('vertex',[-1])[0]<0: return '.zero'
    i,j,s,_=r['vertex']; second = j != (3 if i in [3,5] else 1)
    return f'(.spike {ALIGNED.index(i)} {str(second).lower()} {str(s>0).lower()})'

HEADER = '''module

public import SquaresInCircles.Eight.Candidate.Dual

/-! Generated F8 rational data and algebraic proof source. Uncompiled.
No replay status or external decision procedure is a theorem premise. -/

@[expose] public section
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open scoped BigOperators
open SquaresInCircles.Eight.Candidate
open SquaresInCircles.Eight.Candidate.Dual
namespace SquaresInCircles.Eight.Generated.Owner

'''
END = '\nend SquaresInCircles.Eight.Generated.Owner\n'
REDUCE = '''Row.quartic, Row.L, Row.rhs, Row.forceA, Row.forceB,
      Row.errorA, Row.errorB, Row.errorRhs, Row.loss, Row.Q, Row.epsilon,
      Row.maxLambda, nominalA, nominalB, derivativeA, derivativeB,
      sinNumerator, cosNumerator, coefficient, edgeWidth, widthNumerator,
      lastWidthDerivative, signValue, signs, nominalOwner, Alternative.owner,
      coneA, coneB, coneRhs, lowerPrimary, upperPrimary, lowerRatio, upperRatio,
      alignedEdge, zeroEdges, otherQuarterEdges, mixedEdges, H, G, A, B, T, D, E,
      next, Dpoly, Cpoly, Spoly, listPoly, Fintype.sum_prod_type, Fin.sum_univ_succ'''

def emit_row(name,mode,r):
    p,bs,lam,kap,mu=construct(mode,r)
    reserve=Q(min(r['bernstein_lower_numerators']),10**12)
    cones='!['+', '.join(vec(kap[5*i:5*i+5]) for i in range(7))+']'
    text=f'''def {name} : Row :=
  {{ mode := .{mode}
    positive := {str(Q(r['lo'])>=0).lower()}
    interval := ⟨{rat(r['lo'])}, {rat(r['hi'])}⟩
    owners := {vec([x-1 for x in r['owners']])}
    lambda := {vec(lam)}
    cone := fun i => ({cones} i.1) i.2
    mu := {vec(mu)}
    alternative := {alt(r)}
    polynomial := {lst(p)}
    bernstein := {lst(bs)}
    reserve := {rat(reserve)} }}

theorem {name}_valid : {name}.Valid := by
  constructor
  · intro i; fin_cases i <;> norm_num [{name}]
  · intro i; rcases i with ⟨i,j⟩; fin_cases i <;> fin_cases j <;> norm_num [{name}]
  · intro i; fin_cases i <;> norm_num [{name}]
  · norm_num [{name}]
  · norm_num [{name}, {REDUCE}]
    ring
  · constructor
    · norm_num [{name}, Row.bernsteinRow]
    · rfl
    · intro t
      norm_num [{name}, Row.bernsteinRow, Arithmetic.QPoly.eval,
        Arithmetic.bernsteinEval, Arithmetic.bernsteinBasis,
        Arithmetic.BernsteinRow.coefficient, Finset.sum_range_succ]
      ring
    · intro i hi
      have hi' : i ≤ 4 := hi
      interval_cases i <;> norm_num [{name}, Row.bernsteinRow, Arithmetic.BernsteinRow.coefficient]
  · norm_num [{name}]

'''
    return text

def forall_proof(names,prop='Valid'):
    return 'by\n    intro r hr\n    simp only [List.mem_cons, List.mem_singleton] at hr\n    rcases hr with '+ ' | '.join('rfl' for _ in names)+'\n'+''.join(f'    · exact {n}_valid\n' for n in names)

manifest=[]; imports=[]; tables={'quarter':[],'mixed':[]}; bundles=[]
inputs=[('quarter','candidate_quarter_owner_large_mismatch_dual_data.json'),
        ('mixed','candidate_mixed_owner_shared_mismatch_hand_data.json'),
        ('tilt','candidate_tilt_signed_error_hand_data.json')]
for mode,filename in inputs:
    raw=(SOURCE/filename).read_bytes(); data=json.loads(raw)
    if mode=='tilt':
        # The entire closed chart [-3/8, 0] is proved geometrically in
        # Candidate/GeometricOwners.lean. Never regenerate its former
        # Tilt000--Tilt017 certificate dependencies.
        groups=[(k,b['vertices']) for k,b in enumerate(data['bundles'])
                if Q(b['hi']) > 0]
    else:
        pats=sorted({tuple(r['owners']) for r in data['rows']})
        groups=[(k,sorted([r for r in data['rows'] if tuple(r['owners'])==p],key=lambda r:Q(r['lo']))) for k,p in enumerate(pats)]
    rows_total=0
    for groupno,group in groups:
        chunkname=f'{mode.title()}{groupno:03d}'
        importname=f'SquaresInCircles.Eight.Generated.Owner.{chunkname}'
        imports.append(importname); text=HEADER; names=[]
        for k,r0 in enumerate(group):
            r=dict(r0)
            if mode=='tilt':
                b=data['bundles'][groupno]
                r.update({'lo':b['lo'],'hi':b['hi'],'lambda':b['lambda'],'owners':BASE_OWNERS})
            name=f'{mode}_{groupno:03d}_{k:03d}'
            text+=emit_row(name,mode,r); names.append(name); rows_total+=1
        if mode!='tilt':
            name=f'{mode}Table{groupno:03d}'; tables[mode].append(name)
            ns='['+', '.join(names)+']'; pat=vec([x-1 for x in group[0]['owners']])
            text+=f'''def {name} : OwnerTable where
  mode := .{mode}
  owners := {pat}
  rows := {ns}
  valid := {forall_proof(names)}
  same_mode := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                  rcases hr with {' | '.join('rfl' for _ in names)} <;> rfl
  same_owners := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                    rcases hr with {' | '.join('rfl' for _ in names)} <;> rfl
  no_error := by intro r hr; simp only [List.mem_cons, List.mem_singleton] at hr
                 rcases hr with {' | '.join('rfl' for _ in names)} <;> rfl
  cover := by decide
'''
        else:
            name=f'tiltBundle{groupno:03d}';bundles.append((name,Q(b['lo']),Q(b['hi'])))
            selector=f'{name}_row'
            text+=f'def {selector} : Alternative → Row\n'
            for n,r in zip(names,group):text+=f'  | {alt(r)} => {n}\n'
            text+=f'''\ndef {name} : TiltBundle where
  interval := ⟨{rat(b['lo'])}, {rat(b['hi'])}⟩
  lambda := {vec([Q(n,10**8) for n in b['lambda']])}
  row := {selector}
  valid := by
    intro a
    cases a with
    | zero => exact {names[0]}_valid
    | spike i second positive =>
      fin_cases i <;> cases second <;> cases positive <;>
        first | exact {(' | exact '.join(n+'_valid' for n in names[1:]))}
  same_interval := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_lambda := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_mode := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_owners := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_alternative := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
  same_sign := by intro a; cases a with
    | zero => rfl
    | spike i b s => fin_cases i <;> cases b <;> cases s <;> rfl
'''
        (OUT/(chunkname+'.lean')).write_text(text+END)
    manifest.append({'input':filename,'sha256':hashlib.sha256(raw).hexdigest(),'mode':mode,'groups':len(groups),'rows':rows_total})

text='module\n\n'+''.join('public import '+n+'\n' for n in imports)+HEADER.split('public import SquaresInCircles.Eight.Candidate.Dual\n',1)[1]
for mode in ['quarter','mixed']:
    text+=f'def {mode}Tables : List OwnerTable := ['+', '.join(tables[mode])+']\n\n'
    text+=f'''theorem {mode}_table_modes : ∀ T ∈ {mode}Tables, T.mode = .{mode} := by
  intro T hT
  simp only [{mode}Tables, List.mem_cons, List.mem_singleton] at hT
  rcases hT with {' | '.join('rfl' for _ in tables[mode])} <;> rfl

'''
left=[b for b in bundles if b[2]<=Q(1001,20000)];right=[b for b in bundles if b[1]>=Q(2,25)]
for side,bs,lo,hi in [('left',left,Q(0),Q(1001,20000)),('right',right,Q(2,25),Q(3,8))]:
    bs.sort(key=lambda b:b[1]);ns=', '.join(b[0] for b in bs)
    text+=f'''def tilt{side.title()} : List TiltBundle := [{ns}]

theorem tilt_{side}_cover : Arithmetic.ClosedChain {rat(lo)} {rat(hi)}
    (tilt{side.title()}.map TiltBundle.interval) := by decide

'''
(OUT.parent/'OwnerData.lean').write_text(text+END)
(OUT/'generation_index.json').write_text(json.dumps({'schema':'eight-owner-duals-v1','execution':'source generation only; Lean and historical replay not run','inputs':manifest},indent=2)+'\n')
print(json.dumps({'generated_groups':len(imports),'rows':sum(x['rows'] for x in manifest),'source_index':str(OUT/'generation_index.json')}))
