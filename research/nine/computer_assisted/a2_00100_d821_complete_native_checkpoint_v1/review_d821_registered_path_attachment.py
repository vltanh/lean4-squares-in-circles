#!/usr/bin/env python3
"""Literal source/path check for D821, with no optimizer or weighted replay."""
from pathlib import Path
import ast,hashlib,json

ROOT=Path('/workspace/scratch/f9f48fcfb253')
WORK=ROOT/'global_work/d821_work'
SOURCE=WORK/'published/cd_family_open_package_20261103/legacy/current_proof/shared_capacity_three_b_v4/geometry/weak_outer_numeric_strict_bulk_v14_verify.py'
REG=ROOT/'repo/research/nine/gates/A2_00100_FIXED_FRONTIER.json'
HAND=ROOT/'d_work/D821_REGISTERED_ORIGINAL_PHYSICAL_ATTACHMENT.md'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def decode(j):return json.loads(Path(j).read_text())
cell=next(c for c in decode(REG)['cells'] if c['id']=='positive-821c9a2debeed0aa')
path=[['angle',3,1],['angle_cut',[0,'0'],1],['alternate_four_escape',[1,7],[3]]]
assert cell['sign']=='positive' and cell['baseline_frontier_index']==26 and cell['path']==path
parsed=ast.parse(SOURCE.read_text())
defs=[x for x in parsed.body if isinstance(x,ast.FunctionDef)and x.name in ('alternate_chain','alternate_escape_specs')]
assert len(defs)==2
ns={};exec(compile(ast.Module(body=defs,type_ignores=[]),str(SOURCE),'exec'),ns)
from fractions import Fraction
specs=ns['alternate_escape_specs']((1,7),Fraction(1,2))
assert ns['alternate_chain']((1,7))==(0,1,7,3)
rows=[specs[3]]+[([(i,-v)for i,v in specs[k][0]],-specs[k][1])for k in range(3)]
canonical=lambda row:(tuple(sorted((int(i),Fraction(v))for i,v in row[0]if v)),Fraction(row[1]))
expected=[([(14,1),(2,-1),(15,1),(3,-1)],0),
          ([(0,1),(2,-1),(3,1),(1,-1)],0),
          ([(0,1),(2,-1),(3,-1),(1,1)],0),
          ([(2,1),(14,-1),(15,1),(3,-1)],0)]
assert list(map(canonical,rows))==list(map(canonical,expected))
root=decode(WORK/'fresh_root_bound4.json')
assert root['id']==cell['id'] and root['initial']['path']==path
binding=root['original_register'];frozen=decode(binding['path'])
assert sha(binding['path'])==binding['sha256']
fields=('id','sign','baseline_frontier_index','path')
project=lambda d:[{k:c[k]for k in fields}for c in d['cells']]
assert project(frozen)==project(decode(REG))
HAND.write_text(r'''# D821: exact original-path attachment

This attachment records the unchanged original domain for
`positive-821c9a2debeed0aa`, positive baseline frontier index 26. It adds no
exclusion by itself. The complete-original conclusion still requires the
five complementary domains and every continuation to pass exact replay.

## Registered path and literal halfspaces

The frozen original path is

```json
[["angle",3,1],["angle_cut",[0,"0"],1],
 ["alternate_four_escape",[1,7],[3]]]
```

Indices 0 through 8 are the original squares A through I. The frame slope
is `t_i=beta_i/alpha_i`, with `alpha_i>0`; it is not an angle in radians.
The two slope branches retain `t_D in [0,1]` and `t_A in [0,1]`, including
their shared zero faces.

The frozen `alternate_chain((1,7))` is `(A,B,H,D)`. The literal selected
escape is branch 3; each earlier escape is retained with its sign reversed
as a closed predecessor complement. Thus the four additional center
inequalities are exactly

\[
\begin{aligned}
x_H-x_B+y_H-y_B&\le0,\\
x_A-x_B+y_B-y_A&\le0,\\
x_A-x_B+y_A-y_B&\le0,\\
x_B-x_H+y_H-y_B&\le0.
\end{aligned}
\]

The first is the selected branch. The next three are the complements of
branches 0, 1 and 2 in that order. Every equality is retained. In particular,
no strict predecessor face is silently deleted and no alternative physical
label order is substituted. The accompanying literal audit evaluates only
the two frozen row-definition functions and checks every coefficient and
right-hand side against these four displayed expressions.

## Full physical caller

Each of the nine originals is a unit square with center `(x_i,y_i)` and
orthonormal frame determined by `(alpha_i,beta_i)`, where
`alpha_i^2+beta_i^2=1`. Its original corners are

\[
\left(x_i+\frac{\epsilon\alpha_i-\tau\beta_i}{2},
      y_i+\frac{\epsilon\beta_i+\tau\alpha_i}{2}\right),
\qquad \epsilon,\tau\in\{-1,1\}.
\]

All 36 corners lie in the closed disk of squared radius `1105/256`.
All 36 original pair interiors are disjoint. The exact `001/00` caller
retains actual AB, BC, EF and FG, strictly weak CD, and all five original
center-cone comparisons. The accepted normalization retains its original
large D/C height gap, both original sign roots and the H/I label order;
this registered path selects only its stated positive sign root and
subsequent clauses. All other inherited physical conditions remain active.

`fresh_root_bound4.json` starts from this literal registered domain. Its
initializer independently reconstructs the whole path before checking any
of the four bound rounds. The resulting D/G corridor, horizontal order
and height inequalities are proved consequences of the original domain.
They are not additional caller restrictions. The full mathematical use of
those consequences, the actual-AB theorem, its closed equality blocker and
the five closed complementary domains is given in
`D821_COMPLETE_ASSEMBLY_HAND_PROOF.md`.

The frozen original-definition source and the current status register have
the same 231 ID/sign/baseline-index/path tuples. Their status fields serve
different dates; proof attachment uses the immutable definitions. The
literal audit rechecks this exact equality and the root's original-source
hash. It neither repeats weighted arithmetic nor changes a closure ledger.
''')
report=dict(status='PASS_D821_LITERAL_REGISTERED_PATH_AND_PHYSICAL_ATTACHMENT',
    original_id=cell['id'],sign=cell['sign'],baseline_frontier_index=26,original_path=path,
    literal_rows=[dict(coefficients=[[i,str(v)]for i,v in canonical(row)[0]],rhs=str(canonical(row)[1]))for row in rows],
    all_231_original_definitions_unchanged=True,
    frozen_original_register=binding,current_register_sha256=sha(REG),
    row_definition_source=dict(path=str(SOURCE),sha256=sha(SOURCE)),
    fresh_root_bound_sha256=sha(WORK/'fresh_root_bound4.json'),
    hand_sha256=sha(HAND),reviewer_source_sha256=sha(__file__),
    weighted_arithmetic_repeated=False,numerical_optimizer_called=False,
    complete_original_replay_required=True,new_original_cells=0,new_masks=0)
out=ROOT/'d_work/D821_REGISTERED_PATH_LITERAL_ROOT_REVIEW.json'
out.write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(dict(status=report['status'],hand_sha256=sha(HAND),report_sha256=sha(out))))
