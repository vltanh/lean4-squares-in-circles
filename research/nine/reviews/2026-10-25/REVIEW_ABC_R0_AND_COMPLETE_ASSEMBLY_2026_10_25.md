# Independent review of the full-angle R0 theorem and complete ABC assembly

Date: October 25, 2026.
Reviewer: `abc_review`, independently of the R0 author and the current root.
Repository snapshot: `81bbe0167042ab7546b7ed3880fe69d628ba2b88`.

**Verdict: PASS.** The complete original strict R0/j return is excluded
by the full-angle pressure theorem. The earlier accepted full-feature
exclusions and the original owner/mask/load cover then close the entire
ABC orbit. Joining that result with the accepted single-/two-load C4
exits and both diamond-root exits closes the whole coarse cell
**C2.34.b0 at its existing selected-canonical-minimizer scope**.

This report does not edit the roadmap. The precise existing gates that
can be closed are listed in Section 9. It does not close other six-body
cells, any unrestricted theorem, original equality classification, or
the older full prerequisite-chain audit. The reviewed R0 proof is an
exact-arithmetic-assisted hand argument; its scalar lemma is not yet
table-free or Lean checked.

## 1. Frozen sources and review method

The complete new source, exact checker and direct original chart were
read at the following SHA-256 identities:

| Source | SHA-256 |
| --- | --- |
| `ABC_R0_FULL_ANGLE_BLOCK_PRESSURE.md` | `6a18da96a2d42621e6cb25cda611c4bb05789a4ca88b916b8c41ae7cd989b350` |
| `ABC_R0_TORQUE_CORRECTION_CHECK.py` | `d2edc86ee4cc607ef337261ef89e50cdad09319a0de09bf037822ae18e8b573b` |
| `ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md` | `bfdcfcc13d3594742ff6a67085ec382d1c018695000330c2e1803ddc1987e47b` |
| `BOWTIE_CELL_CLOSED.md` | `41fec95f68f153d4417651a556cdc65352a6e3f97d32f8f99c561dfb6282b772` |

The reviewer independently derived the endpoint torques, support-work
formula, middle torque, corrected pressure identity and final Cauchy
estimate from the actual physical equations. The saved standard-library
checker was read and run. A second implementation, using dense bivariate
Fraction arrays rather than the author's sparse-polynomial routines,
independently rebuilt the rational functions, common denominators,
ordinary coefficients, affine substitutions and Bernstein coefficients.
It verified every sign and full inverse identity. No floating-point
sample or numerical optimizer was used.

For the whole-family join, the original graph/load cover, the original
remaining fan, accepted radial-middle and UUS assemblies, complete far
review, adjacent-side and R1 reviews, opposite-circle source,
shared-side source, complete diamond assembly and C4 two-load assembly
were checked at their stated hypotheses. Previously accepted
whole-domain theorems and their independent reviews remain dependencies;
this review does not pretend to reprove every older transitive source or
to discharge the separately open foundational audit.

## 2. The exact original physical chart is preserved

The final ABC chart has true degrees H4/A2/B2/C2, an intact HXY petal,
and three arbitrary additional physical squares. A,B,C have one physical
circle corner each and strictly positive total circle loads. Neither a
second physical corner nor a zero individual radial weight is discarded:
the physically radial branches were separately covered before this chart.

In B's positively oriented frame `(f,g)`, the actual H normals are
`n=E f+D g`, `j=-D f+E g`, with `E>0` and `E^2+D^2=1`.
Writing the original positive magnitudes as `mu,gamma,nu,eta`, the actual
force equations are exactly

```
lambda_A*z_A = mu*n-gamma*g,
lambda_B*z_B = gamma*g+nu*f,
lambda_C*z_C = eta*j-nu*f.
```

These signs agree with the original minimum-g AB and minimum-f BC sides
of B. In particular the B circle corner is its positive f/positive g
corner in this side-return chart. The second B corner already belongs
to the separately exhausted far feature, not an omitted alternative
here. All four pair magnitudes and all three lambdas are positive.

For A, the original axes are `p=s f-c g`, `t_A=c f+s g`, with `s,c>0`;
the true applications are `P=z_A-p-t_A`, `T=z_A-p`. For C they are
`e=-S f+C0 g`, `t=-C0 f-S g`, with `S,C0>0`;
the true applications are `Q=z_C-e`, `R0=z_C-e+t`.
No original side mean, normal or position is reselected. The direct
adjacent fan justifies `HC=j` from the previously imposed fixed-tip
selection and the complete parallel-root exclusion. That justification
is only used at its genuine H4/intact-petal scope.

The R0 theorem itself uses only this actual chart, A2/B2/C2 and H's two
support identities. It does not require a force equation at H, a chosen
H offset, an HB contact, the previously proposed `|D|<=1/2` condition,
or a completion-capacity claim.

## 3. Both endpoint torques and the full angle interval

Take moments about the actual circle corner at each endpoint. At A,

```
mu*(u-v)+gamma*s=0,
u=E*s-D*c, v=E*c+D*s,
[mu*(E-D)+gamma]*s=mu*(E+D)*c.
```

At C, expanding the unchanged origin torque gives

```
eta*(E-D)*S=[eta*(E+D)+nu]*C0.
```

If `E+D<=0`, then `E-D>0`, so the two sides of the A equation have
opposite signs. Thus `E+D>0`. The right side of the C equation is then
positive, so `E-D>0`. Hence the complete physical interval is
`|D|<1/sqrt(2)`. This includes both tails `1/2<|D|<1/sqrt(2)`.

Normalizing the two positive vectors in these equations gives exactly
the source's formulas for `s,c,C0,S` and the norms `U,V`. Their squared
normalizations are

```
U^2=2*mu^2+gamma^2+2*mu*gamma*(E-D),
V^2=2*eta^2+nu^2+2*eta*nu*(E+D).
```

All denominators are strictly positive. Substitution gives the two
support-work identities of Section 2 of the source. These are
identities at the original forces, not support maxima substituted for
the physical squares.

## 4. Original support work and the genuine middle-body torque

Let `A=|mu*n-gamma*g|`, `B=sqrt(gamma^2+nu^2)` and
`C=|eta*j-nu*f|`. The positive circle equations give
`lambda_A*R=A`, `lambda_B*R=B`, `lambda_C*R=C`.
Pairwise cancellation in the corner-work sum gives

```
pressure=c_H dot (mu*n+eta*j)
        =R*(A+B+C)-[(mu+eta)/2+gamma+nu+U+V].
```

The four support contributions before using endpoint torques are

```
mu*(u+v+1/2), gamma*(1+c),
nu*(1+S), eta*(E*(C0+S)+D*(S-C0)+1/2).
```

The factors `1/2` come from actual H supports. The factors `1` in the
middle terms are B's actual unit widths. Their signs and the absence of
any omitted middle force were independently checked.

Write the actual B applications as
`T=L f+(W-1)g`, `Q=(beta-1)f+Yg`. Its true origin moment is
`gamma*L=nu*Y`. The original endpoint equations give

```
L=R*mu*E/A-s, Y=R*eta*E/C-C0,
R*E*(mu*gamma/A-eta*nu/C)=gamma*s-nu*C0.
```

Define `Tsum=A+B+C`, `Ssum=(mu+eta)/2+gamma+nu+U+V`.
Formal differentiation in D, holding all four magnitudes fixed, gives

```
Tsum'=-mu*gamma/A+eta*nu/C,
Ssum'=(-gamma*s+nu*C0)/E,
R*Tsum'=Ssum'.
```

Thus the corrected pressure identity

```
pressure=R*(Tsum-(D/2)*Tsum')-(Ssum-(D/2)*Ssum')
```

is an exact consequence of the original B2 moment. No variation through
physical packings is asserted. This is why the correction is permissible
without a deformation or stationary-configuration hypothesis.

## 5. Independent scalar-certificate review

For the source's scalar variables `x>=0`, `|d|<=1/sqrt(2)`, all of
`a,b,p,q_s` are positive. In particular `e>=|d|`,
`p=x^2+1-(3/2)*d*x>0`, and

```
q_s=2*x^2+1+x*(2*e-(3/2)*d+d^2/(2*e))>0.
```

The reduction from `H>0,P>0` to the strict scalar inequality is valid:
the first positive square root gives
`H>2*q_s*abs(t_s)*a*sqrt(b)`, and the second gives
`K*p/sqrt(a)>q_s/sqrt(b)+abs(t_s)`. Every squared side has the required
positive sign. In the alternative branch, `Z>0` and `t_s<0` immediately
give the same desired strict inequality. No sign is inferred merely
from squaring an expression of unknown sign.

The half-angle map `z=d/(1+e)` has actual interval
`[-sqrt(2)+1,sqrt(2)-1]`, contained in `[-5/12,5/12]`. On the enlarged
interval both `den=1+z^2` and `en=1-z^2` are positive.
The independent rational-function reconstruction produced exactly

```
Hnum=den^4*en^2*H,
Pnum=den^8*en^4*P,
Znum=den^3*en^2*Z.
```

It matched all **85, 313 and 61 nonzero ordinary coefficients** of the
three saved polynomials. The degrees are respectively `(6,12)`,
`(12,24)` and `(6,10)`. Both full reciprocal substitutions were checked
as polynomial identities.

All seven exact rows were separately reconstructed:

| Row | Coefficient count | Every coefficient exceeds |
| --- | ---: | ---: |
| H, small x / lower z | 91 | 2 |
| P, small x / lower z | 325 | 2 |
| Z, small x / upper z | 77 | 1 |
| H, reciprocal x | 91 | 7/10 |
| P, reciprocal interval 1 | 325 | 1/2 |
| P, reciprocal interval 2 | 325 | 9/100 |
| P, reciprocal interval 3 | 325 | 9/100 |

This is **1,559 exact strict signs**. For every row the independent
implementation expanded the entire Bernstein representation back into
ordinary powers and recovered every coefficient, including zeros.
The nonnegative basis sums to one throughout each whole rectangle.

The scalar cover is exhaustive: `0<=x<=1` splits at `z=1/4`, while
`x>=1` maps to `0<=u<1` and the three closed reciprocal intervals
cover it. In the upper-z small-x rectangle,
`h(d)-1/2>=103/850>0`, so `t_s<0`. All equality interfaces and both
physical angle endpoints are included. The original force ratios are
strictly positive and finite; allowing x=0 and the compactified endpoint
only enlarges the scalar comparison.

## 6. Final positive-pressure bound and exact degree scope

Apply the scalar lemma to `(x,d)=(mu/gamma,D)` and
`(eta/nu,-D)`, multiplying by the actual positive gamma and nu.
Their sum gives exactly the corrected Tsum/Ssum inequality. Cauchy's
inequality uses

```
[1+h(D)]^2+[1+h(-D)]^2<=2434/625.
```

The reviewer checked the final strict rational reserve independently:

```
(1263/640)^2-2434/625=569/10240000>0,
79/40-1/640=1263/640>0.
```

The corrected total `Tsum-(D/2)*Tsum'` is positive: its endpoint
numerators are
`mu^2+gamma^2-(3/2)*D*mu*gamma` and
`eta^2+nu^2+(3/2)*D*eta*nu`, both positive by
`x^2+y^2>=2xy` and `|D|<1`, and B is positive. Therefore raising the
radius from `79/40` only strengthens the inequality. The final result is

```
c_H dot F_block>B/640>0.
```

The true H4 equation with the intact petal is
`F_block+M_petal=0`. The complete end-triangle theorem in
`BOWTIE_CELL_CLOSED.md`, Section 2, has `c_H dot M_petal>0` while
allowing arbitrary further forces at H. These strict signs contradict
the unchanged H equation. All three extra physical squares remain;
there is no need to move them or assign a capacity to their pockets.

The same local R0 inequality does allow any H degree once its actual
R0 chart and exact A2/B2/C2 equations are hypotheses. A further root
resultant with nonnegative H pressure yields the same contradiction.
This local extension does not by itself export the older complete
H4 owner/parallel reductions to an arbitrary attachment.

## 7. Exhaustive ABC join

The original complete ABC assembly first uses the intact-petal pressure
and the actual three-boundary-path resultant cone to label a negative
physically unique endpoint A. The cone theorem does not omit B's force.
Physical radial endpoints have positive H pressure even when one radial
weight vanishes. Thus both-radial-endpoint families are excluded, and
the four remaining physical masks, ordered `(B,A,C)`, are
`SUS,UUS,SUU,UUU`.

The complete accepted radial-middle theorem excludes SUS and SUU.
`REVIEW_ABC_FAR_RADIAL_AND_UUS_JOIN_2026_10_25.md` records the full UUS
owner/radius/feature join, including both C-weight endpoints.
For UUU, the original negative-owner partition has A-owned singleton,
genuinely shared, free, and H-owned singleton HA. The first three have
their accepted full-window exits. In the shared branch its original
AB-free and B-owned alternatives are separately covered; a variable HA
mean is not subjected to a fixed-tip assertion.

For the remaining H-owned HA, the complete actual A support cover has
left singleton, left shared, upper singleton, upper shared, and the
strict upper-left vertex. All first four have their accepted full-window
exits, including the high/low join at q=17/4. The strict upper-left
applications are distinct fixed physical vertices, so the common
preselection leaves B-owned AB. No new selection is made at this stage.

The actual B2 equation then gives the complete outgoing support fan:

| Original BC feature | Complete accepted exit |
| --- | --- |
| Strict near B vertex | `NEGATIVE_H_OWNED_UPPER_LEFT_NEAR_VERTEX_EXCLUSION.md` |
| Strict far B vertex, either B circle corner | `REVIEW_ABC_COMPLETE_FAR_RETURN_2026_10_25.md` and its complete feature join |
| Genuine shared minimum-f BC, all original means | `ABC_UNIQUE_SHARED_SIDE_COMPLETE_EXCLUSION.md` |
| Strict B-owned minimum-f BC, opposite C circle corner | `ABC_UNIQUE_SINGLETON_SIDE_OPPOSITE_CORNER_EXCLUSION.md` |
| Strict B-owned minimum-f BC, adjacent C circle corner, HC side | Complete low/high-beta join in `REVIEW_ABC_COMPLETE_ADJACENT_SIDE_2026_10_25.md` |
| Same adjacent C corner, strict HC endpoint R1 | `REVIEW_ABC_ADJACENT_FRONT_RETURN_2026_10_25.md` |
| Same adjacent C corner, strict HC endpoint R0 | The full-angle theorem reviewed in Sections 2--6 above |

The adjacent fan proves those are all actual C corners and HC features.
Side-axis normals at overlap endpoints stay in the side row, and strict
vertex rows do not discard a shared-limit mean. The complete far review
explicitly retains `k_y=0`, `k_j=0`, both B corners and both physical C
masks. The current R0 proof has no beta or D tail restriction. Thus the
joins have no omitted angle, radius, owner, physical mask or mean endpoint.

Together these sources exclude the **entire original ABC orbit** on the
closed original radius interval. This is a core contradiction, not a
claim that an unexamined pocket has insufficient capacity.

## 8. Whole C4 and coarse C2.34.b0 join

`TRIANGLE_FOUR_BODY_BLOCK_LOAD_COVER.md`, Sections 1--3, gives the exact
C4 load representatives A, B, AB, AC and ABC up to the actual
root-preserving reflection. The attached triangle tips remain loaded
and the root physically circle-clear in every row.

| Whole original C4 load orbit | Complete exit |
| --- | --- |
| A or its reflected C image | The original positive transmitter-channel contradiction |
| B | The original two-transmitter alignment, radial force and incompatible root-axis support |
| AB or reflected BC | `TRIANGLE_C4_ADJACENT_LOAD_EXCLUSION.md` |
| AC | `TRIANGLE_C4_OPPOSITE_LOAD_BRANCH_CLOSED.md`, at the common canonical minimizer |
| ABC | Section 7 of this review |

The AC theorem needs the radius minimizer that also minimizes the sum of
squared center norms. Its canonical choice is made before common normal
preselection and stress extraction. This scope must be preserved when
the whole C4 or coarse cell is marked closed; the assembly is not a new
claim about every noncanonical stressed core or every equality packing.

`SIX_BODY_CYCLIC_FRONTIER.md`, Section 8, gives exactly three abstract
layouts for C2.34.b0: C4 attachment, diamond-hub attachment, and
diamond-tip attachment. K4 is excluded by the inherited global cover.
The C4 attachment now has all its load orbits excluded as above.
`REVIEW_COMPLETE_DIAMOND_ASSEMBLY_2026_10_25.md` closes the entire
diamond-hub layout at true H5/K3/A2/B2 scope. The diamond-tip layout
is excluded by `ROOTED_BLOCK_ATTACHMENT_OBSTRUCTIONS.md`, Section 2,
using the unchanged two degree-three hubs and degree-two other tip.

These are all three layouts. Hence the whole coarse cell C2.34.b0 is
closed at the existing selected-canonical-minimizer hand-proof scope,
with all three arbitrary completion squares retained.

## 9. Exact existing gates discharged

The following eight substantive unchecked gate IDs in the frozen
2,513-ID inventory may be checked, without creating new IDs:

1. `M6.TB4.C4.LABC.NONPARALLEL`
2. `M6.TB4.C4.LABC.UUU`
3. `M6.TB4.C4.LABC`
4. `M6.TB4.C4.LABC.NEGATIVE_OWNER.UUU.H_OWNED`
5. `M6.TB4.C4.LABC.NEGATIVE_OWNER.UUU.H_OWNED.LOW.AB_B_OWNED`
6. `M6.TB4.C4.LABC.NEGATIVE_OWNER.UUU.H_OWNED.HIGH.AB_B_OWNED`
7. `M6.TB4.C4_EXIT`
8. `M6.TB4.ALL`

The existing alternative gate
`M6.TB4.C4.LABC.COMPLETION.ARTICULATION_JOINT` is also discharged by
the whole ABC core exclusion. Its gate text expressly calls capacity an
alternative to a whole-core exit. If it is checked, the annotation must
say **vacuous after the whole-core exclusion**, rather than reporting a
new independent articulation-pocket capacity theorem. This yields nine
existing gate discharges in total and closes the one coarse cell above.

`G3.M6.ASSEMBLE` remains open: C1.4.b2, C1.5.b1 and C1.6.b0 retain
their original obligations. Both remaining alternating-C6 families,
larger mixed cells, unrestricted sharpness, original equality,
foundational audit and Lean integration remain open.

No Lean compilation, CI, workflow dispatch, post-extraction normal
change, fabricated review, omitted positive force, reassigned degree,
physical-mask substitution or sampled sign is part of this acceptance.
