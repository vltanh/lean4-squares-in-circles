# Geometric replacement of the mismatch angle tables

## Result and remaining scope

Whole-domain core geometry now removes **83,542 row constructors** across
all ten affine tables. Their active payload is **576,828 rows**, down from
660,370. The coarse mismatch table contains **110,425 rows**, down from
129,031; the enhanced coarse bound shares that same 18,606-row removal.
Five infeasible state/axis classes account for 78,736 removals. A direct
cost proof for every coarse core/core pair removes another 4,806 active
rows while preserving every original vertex label.

On a zero-quarter edge a target-primary separator requires an outer
target with primary coordinate greater than one, and a source-primary
separator requires the analogous outer source. Core-side and core-corner
primary coordinates are at most 7/12. At every angle a core center's
projection is at most 5/6, which also excludes two secondary-axis classes
when the corresponding signed transverse coordinate has the wrong sign.
Finally, a core/core quarter pair with positive source and negative target
signs has no feasible axis: the physical center-gap cap leaves too little
angular room for the transverse coordinates needed to separate the squares.

`Candidate/GeometricPrimaryExclusion.lean` proves the primary exclusions
from the complete original frame range. `GeometricSecondaryExclusion.lean`
proves the secondary exclusions at every angle.
`GeometricCoreQuarter.lean` proves the complete opposite-sign quarter
exclusion from the physical gap and two whole error-sign intervals.
`Candidate/GeometricAffineCoverage.lean` connects all five to actual feasible
axes before selecting an angle chain.
The data-only reader omits these constructors before Lean elaboration;
the retained domains use the original row checks, endpoint enclosures,
state coverage, and closed angle-chain predicate. The historical research
inputs remain intact. This is an active payload reduction, not a claim
that the remaining coarse charged bound has become table-free.

`GeometricCoreMarker.lean` supplies the whole coarse core/core cost from
center separation and bounds on the original markers. Its finite gates
are explicit: 496 endpoint-label inequalities on 124 existing core arcs,
structural conditions on those arcs, and seven edge-budget comparisons
with nonnegative-charge checks. `GeometricCoreCoverage.lean` selects each
vertex label once, applies this direct cost to core/core pairs, and uses
the original row proof for pairs with an outer endpoint. All 462 original
coarse arc labels remain in use; none is replaced or refitted.

The new table-free module
`SquaresInCircles/Eight/Candidate/GeometricMismatch.lean` proves an exact
contact-frontier reduction for **all four actual SAT axes**, both candidate
quarter words, both signs of the frame difference, and arbitrary real
state-dependent labels. Its mathematical content is:

> A charged pair inequality over an entire signed angle interval follows
> from the feasible left endpoint and at most two exact SAT contact roots.

The reduction uses a rational half-angle coordinate, the actual SAT
identities, monotonicity, the intermediate value theorem, and the quadratic
formula. It uses no angle mesh, multiplier fit, Taylor enclosure, generated
table, or Bernstein coefficient list. It also proves that every actual
candidate frame and every originally feasible axis enter this formulation.

This is a replacement for the **angular verification method**, not yet a
replacement for one of the four complete charged bounds. The endpoint and
contact-root inequalities must still be proved uniformly over their two
state parameters with one consistent potential per vertex. The primary
and secondary exclusions each remove 152 disjoint cases from the 960
semantic cases below. The opposite-sign quarter exclusion removes another
32, leaving at most 624. The complete core/core cost closes 160 more
semantic cases, leaving at most **464 outer-endpoint cases** in the coarse
state-positivity gate. All added Lean is an uncompiled draft, as requested.

## 1. The half-angle geometry

Write the actual canonical relative angle as

\[
\phi=k\pi/2+d,\qquad k\in\{0,1\},\qquad |d|<7/10.
\]

Set \(z=\tan(d/2)\), or equivalently choose the unique coordinate with
\(d=2\arctan z\). The existing analytic half-angle chart gives
\(-3/8<z<3/8\). Put \(D=1+z^2>0\). Then

\[
\sin d=\frac{2z}{D},\qquad
\cos d=\frac{1-z^2}{D}.
\]

In particular \(\cos d>0\) throughout the chart. The square support
width and the charged excess simplify exactly to

\[
\boxed{W(\phi)=\frac{1+|z|}{D}},\qquad
\boxed{h(\phi)=\frac{|z|-z^2}{D}}.
\tag{1}
\]

The quarter turn changes neither expression. There is one meaningful
sign split, at \(z=0\). Both closed sign branches include the common
zero endpoint, where their expressions agree.

## 2. All SAT inequalities are quadratic

Use the original unsigned coordinates and signs from `Candidate.Model`:
the source center in its own frame is \((a,-\sigma b)\), and the target
center in its own frame is \((A,-\tau B)\). This calculation assumes
neither a radial-boundary kind nor a sign pattern for \(\sigma,\tau\).
Let \(r=1\) on the nonnegative branch and \(r=-1\) on the nonpositive
branch, so \(|z|=rz\).

For each original retained axis \(j\), its margin satisfies

\[
D M_j=Q_j(z)=q_{2,j}z^2+q_{1,j}z+q_{0,j}.
\tag{2}
\]

The indices in this note and the Lean source are zero based: axes
\(0,1,2,3\) are source \(+f\), target \(+e\), target \(+f\),
and source \(-e\), respectively.

### Zero-quarter edges, \(k=0\)

| Axis | Constant \(q_0\) | Linear \(q_1\) | Quadratic \(q_2\) |
|---|---|---|---|
| 0 | \(\sigma b-\tau B-1\) | \(2A-r\) | \(\sigma b+\tau B\) |
| 1 | \(A-a-1\) | \(2\sigma b-r\) | \(A+a\) |
| 2 | \(\sigma b-\tau B-1\) | \(2a-r\) | \(-\sigma b-\tau B\) |
| 3 | \(a-A-1\) | \(-2\tau B-r\) | \(a+A\) |

### Quarter edges, \(k=1\)

| Axis | Constant \(q_0\) | Linear \(q_1\) | Quadratic \(q_2\) |
|---|---|---|---|
| 0 | \(\sigma b+A-1\) | \(2\tau B-r\) | \(\sigma b-A\) |
| 1 | \(A+\sigma b-1\) | \(2a-r\) | \(A-\sigma b\) |
| 2 | \(a-\tau B-1\) | \(-2\sigma b-r\) | \(-a-\tau B\) |
| 3 | \(a-\tau B-1\) | \(2A-r\) | \(a+\tau B\) |

For example, for axis 0 on a zero-quarter edge,

\[
\begin{aligned}
D M_0
&=\sigma b(1+z^2)+2Az-\tau B(1-z^2)-(1+rz)\\
&=(\sigma b+\tau B)z^2+(2A-r)z
   +\sigma b-\tau B-1.
\end{aligned}
\]

Because \(D>0\), **actual feasibility is equivalent to** \(Q_j(z)\ge0\).
This equivalence is exact, so interior feasible intervals, disconnected
feasible sets, double contact roots, and simultaneous feasible axes are
retained. A separate polynomial identity check expanded all eight formulas
with symbolic \(r\); all residuals were identically zero. This checks all
sixteen quarter/sign/axis cases without sampling. It is an algebra check,
not a Lean compilation or a replay of the existing certificates.

## 3. Why only the first feasible contact matters

Fix both states and their labels \(L_s,L_t\). The charged cost is

\[
F(z)=k\pi/2+2\arctan z
       -\beta\frac{|z|-z^2}{1+z^2}+L_s-L_t.
\tag{3}
\]

For \(|x|,|y|\le3/4\), the exact width estimate in
`Candidate.Projection` gives

\[
|h(y)-h(x)|\le\tfrac12|y-x|.
\]

Consequently, if \(x\le y\) and \(\beta\ge0\),

\[
(y-\beta h(y))-(x-\beta h(x))
\ge(1-\beta/2)(y-x).
\tag{4}
\]

For \(0\le\beta\le2\) this proves monotonicity; for \(\beta<2\)
it proves strict increase when \(x<y\). The actual charges
\(99/5000,1/400,1/200,1/20\), and the zero charge on mixed edges,
all satisfy this condition. Since \(2\arctan z\) increases with \(z\),
the cost (3) increases throughout the whole chart, independently of the
states and the potentials. The negative sign branch uses the same order
on **signed** \(z\); reversing its order would be an error.

Let \([l,u]\subseteq[-3/8,3/8]\) be an entire closed angle domain on
one sign branch. Suppose \(Q(z)\ge0\) at an actual coordinate
\(z\in[l,u]\). Exactly one of the following arguments applies:

1. If \(Q(l)\ge0\), then \(F(z)\ge F(l)\).
2. If \(Q(l)<0\), continuity supplies a root
   \(s\in[l,z]\) with \(Q(s)=0\), and \(F(z)\ge F(s)\).

Therefore the conditions

\[
Q(l)\ge0\Longrightarrow F(l)>\gamma,
\tag{5}
\]

\[
s\in[l,u],\ Q(s)=0\Longrightarrow F(s)>\gamma
\tag{6}
\]

prove the desired cost inequality at **every feasible angle**, with no
assumption that feasible angles form one interval. The proof is the
intermediate value theorem followed by (4). It does not assume that the
actual packing has a contact equality.

If \(q_2\ne0\), all roots in (6) are among

\[
s_\pm=\frac{-q_1\pm\sqrt{q_1^2-4q_2q_0}}{2q_2},
\tag{7}
\]

and a root implies a nonnegative discriminant. If \(q_2=0\ne q_1\),
there is only the linear candidate \(-q_0/q_1\). If the polynomial
is constant, either there are no feasible angles or condition (5)
already suffices. The Lean implementation selects the singleton linear
candidate when the quadratic coefficient vanishes, and otherwise the two
quadratic candidates. In either case it explicitly
checks both interval membership and the root equation before invoking a
root inequality. It never treats division by zero or a negative
discriminant as a geometric root.

## 4. Actual-cycle adapter and proof interface

`frame_coordinate` supplies the signed \(z\) for each actual candidate
edge. `frame_feasible_iff` transports **each** original feasible forward
axis to (2), using the existing exact margin identity. No desired owner
is presumed. `pair_bound_of_frontier` then proves the complete continuous
pair inequality from (5) and the finitely many instances of (6).

A geometric replacement for a charged table can therefore define a
single real function \(L_i\) on the entire state domain of each role,
prove (5)–(6) for those functions, and assemble `ChargedBound` directly.
The already proved cyclic telescoping and scalar contractions can be
reused unchanged. Potentials need not be affine for the new argument:
they are held fixed while the pair angle varies. At a state-branch
boundary the same chosen value must be used on both incident edges.

## 5. The finite state classification that remains

The coarse stage has 22 role/radial-kind/sign domains. Splitting only at
the **geometric** core-side/core-corner junction gives the following
numbers of one-dimensional state branches in cyclic order:

\[
(H,G,A,B,T,D,E):\qquad(6,2,6,6,2,6,3).
\]

The G/T ratio bounds stop at \(4/5<6/7\), so their core states have
only the side branch. These 31 branches give exactly

\[
6\cdot2+2\cdot6+6\cdot6+6\cdot2
 +2\cdot6+6\cdot3+3\cdot6=120
\]

directed state-branch pairs. With four original axes and two signs, there
are at most **960 semantic cases**, each with the same formulas above.
This is a fixed classification by geometry, not an arbitrary mesh. Many
cases are empty or share the same proof by reflection/reversal. Each
nonempty case retains two continuous state parameters.

For each such case the remaining work is precisely:

1. Choose a consistent explicit potential for each role/state branch.
2. Express the allowed angle endpoints, including the physical center-gap
   restrictions and any mismatch hypothesis established at an earlier stage.
3. Prove the endpoint inequality (5) and the at-most-two contact-root
   inequalities (6) over the **entire pair of state branches**.

The SAT quadratic, linear/constant degeneracies, signs, and complete angle
coverage are already handled by the new lemmas. State-branch positivity
is not yet handled. Proving it by again splitting states into dozens of
numerical intervals would restore the main problem, even if the resulting
tables were smaller.

## 6. Closed state gates for core separators

### Primary separation requires an outer receiver

The following elementary inequality holds on the entire original frame
range \(|d|\le7/10\). If \(Y\ge0\) and \(|v|\le Y\), then

\[
\boxed{X-Y\cos d+v\sin d-W(d)
\le X-1-\frac{11}{200}Y.}
\tag{8}
\]

Indeed,

\[
\cos d\ge1-\tfrac12(7/10)^2=151/200,
\qquad |\sin d|\le7/10=140/200,
\]

so \(\cos d-|\sin d|\ge11/200\). Also
\(v\sin d\le Y|\sin d|\) and \(W(d)\ge1\). Adding these
three inequalities gives (8). No containment, radial-kind, tangent-sign,
or total-mismatch restriction enters this calculation.

On a zero-quarter edge the target-primary margin is the left side of
(8) with \(X=A,Y=a,v=\sigma b\). Since \(a>0\), feasibility
forces \(A>1\). The source-primary margin has
\(X=a,Y=A,v=-\tau B\), and feasibility similarly forces \(a>1\).

Every core-side square has primary coordinate \(7/12\). A core-corner
square satisfies

\[
(a-1/2)^2+(b-1/2)^2=1/144,
\]

which implies \(a\le7/12\) as well. Hence:

- A core target excludes the target-primary axis on the whole zero-edge
  frame domain, independently of the source kind and both signs.
- A core source excludes the source-primary axis on that same domain,
  independently of the target kind and both signs.
- A core/core zero-quarter pair therefore has only the two secondary
  owners \(\{0,2\}\), before applying any coarse mismatch theorem.

These statements are implemented as `primary_margin_upper`,
`core_primary_upper`, `zero_target_primary_requires_outer`,
`zero_source_primary_requires_outer`, and `zero_core_pair_owners`.
They live in `GeometricPrimaryExclusion.lean`; the last three use actual
`Frame` objects and actual SAT feasibility.

The coarse state-branch counts are as in Section 5. Their core-branch
counts in the same order are \((4,1,4,4,1,4,2)\). On zero edges
0, 2, and 4 the one-sided exclusions remove

\[
2\bigl[(6\cdot1+4\cdot2)
 +(6\cdot4+4\cdot6)+(2\cdot4+1\cdot6)\bigr]=152
\]

axis/sign/state-pair cases. The remaining count is at most **808**,
before further geometric exclusions. A direct count of the existing
coarse row metadata found 3,014 target-core/target-primary rows and
3,014 source-core/source-primary rows. Counting those domains does not
replay their certificates or treat a numerical result as the proof of
infeasibility; (8) is the proof.

### Secondary exclusions at every angle

For a core center the canonical bounds give
\(0\le b\le a\le7/12\). Consequently

\[
a^2+b^2\le2(7/12)^2=49/72<25/36=(5/6)^2.
\]

For any real \(v\) with \(|v|\le a\), the exact orthogonal-projection
identity

\[
(a\sin\phi+v\cos\phi)^2+(a\cos\phi-v\sin\phi)^2=a^2+v^2
\]

therefore gives the whole-angle inequality

\[
\boxed{|a\sin\phi+v\cos\phi|\le5/6.}
\tag{9}
\]

The source-secondary margin is
\(\sigma b+A\sin\phi-\tau B\cos\phi-W(\phi)\).
If the target is core and \(\sigma b\le0\), then (9) and
\(W\ge1\) bound this margin by \(-1/6<0\). The target-secondary
margin is \(a\sin\phi+\sigma b\cos\phi-\tau B-W(\phi)\).
It has the same strict negative bound if the source is core and
\(\tau B\ge0\). These two exclusions impose no frame-angle or
total-mismatch restriction.

`GeometricSecondaryExclusion.lean` implements the projection estimate,
both negative margins, and their adapters to actual `Frame` feasibility.
In the 31 state branches of Section 5, the negative-sign branch counts
are \((3,2,3,3,0,3,3)\), the positive-sign counts are
\((3,0,3,3,2,3,0)\), and the core counts remain
\((4,1,4,4,1,4,2)\). Thus these two axis classes exclude

\[
2\sum_i\left(n_i^-c_{i+1}+c_i n_{i+1}^+\right)=152
\]

additional axis/sign/state-pair cases. They use the other two axes from
the primary exclusions, so the two sets are disjoint. Their combined
count is 304, leaving at most 656 semantic cases for further work.

### The complete opposite-sign core/core quarter class

Let both primary coordinates be in `[1/2,7/12]`, with unsigned transverse
coordinates `0≤b≤a` and `0≤B≤A`. Suppose the source signed transverse
coordinate is `b`, the target's is `−B`, and the relative phase is
`π/2+d`, where `|d|≤7/10`. The physical gap is then

\[
 g=\pi/2+d+\alpha+\theta,\qquad
 \alpha=\arctan(b/a),\quad \theta=\arctan(B/A).
\]

The other six gaps each exceed `19/25`, and the seven gaps sum to `2π`.
Using `π<22/7` gives `g<7/4`. Concavity of arctangent on `[0,1]` gives
`atan t≥πt/4≥3t/4`; hence each core coordinate satisfies
`b≤(7/9)α` and `B≤(7/9)θ`. Combining these with `π>31/10` yields

\[
 \boxed{b+B\le\frac79\left(\frac15-d\right).}
\tag{10}
\]

This is a whole-state angular restriction, independent of every candidate
cut, radial upper bound, total mismatch contraction, and generated label.
For `x=|d|≤7/10`, write `c=cos x` and `s=sin x`. The elementary bounds
`s≥9x/10`, `c≥1−x²/2`, `c,s≤1`, and `c,s≥0` hold on the full interval.

If `d=−x`, the two secondary margins have the form

\[
 b+Ac+Bs-\frac{1+c+s}{2}
 \le b+B-\frac5{12}-\frac9{20}x
 \le-\frac{47}{180}+\frac{59}{180}x
 \le-\frac{19}{600}<0.
\]

The exchanged source/target expression has the same bound. The two primary
margins have the form

\[
 A-as+bc-\frac{1+c+s}{2}
 \le b-\frac5{12}-s+\frac{x^2}{4}
 \le-\frac{47}{180}-\frac{11}{90}x+\frac{x^2}{4}
 \le-\frac{269}{1200}<0,
\]

where `x²≤7x/10` proves the last inequality. If `d=x`, the two secondary
margins are at most `b+7/12−1≤−47/180`, or its exchanged version.
For either primary margin, `W≥1` and `sin x≤x` give

\[
 A+a\sin x+b\cos x-W
 \le-\frac5{12}+\frac7{12}x+b
 \le-\frac{47}{180}-\frac7{36}x<0.
\]

Thus all four axes are impossible in both closed sign intervals, including
`d=0`. `GeometricCoreQuarter.lean` proves these estimates as
`core_quarter_negative_error`, `core_quarter_nonnegative_error`, and
`core_quarter_opposite_margin`. The actual adapter uses equality of signed
products, so either sign label at `b=0` or `B=0` remains covered.

In the coarse state classification this excludes the four ordered core-chart
pairs on `D+→E−`, all four axes, and both angular signs: 32 additional
semantic cases, disjoint from the previous 304. The remaining finite
state-positivity gate has at most **624** cases.

### Active coverage and row removal

`GeometricAffine.Excluded` recognizes exactly the five state/axis classes
above. Its `feasible_not_excluded` theorem applies (8), (9), and (10) to original
actual axes. The chosen arc's `Contains` predicate supplies the core
bound, so the proof does not assume that an endpoint shared by two radial
curves has a unique radial label. For the secondary exclusions, the
existing state cover's signed-product equalities transport the selected
arc sign to the actual transverse coordinate. This also preserves both
labels at a zero transverse coordinate.

`GeometricAffine.AngleValid` inserts the hypothesis `¬ Excluded` before
the original chain predicate. Every retained row must still match its
source, target, edge, quarter, original axis, angular sign, and charged
target. Every retained domain must still have complete closed coverage.
`GeometricAffine.chargedBound` selects each vertex's label once, proves
that actual feasibility excludes the omitted classes, and then uses the
same continuous row claim and telescoping assembly as before.

The notation

```lean
affine_rows% "...CANDIDATE_COARSE_MISMATCH_HAND_DATA.json" rows 129031
  excluding_core_pairs 110425
```

checks both input and retained counts. It filters by the edge, original
axis, radial kind, and transverse sign, with no list of excluded row identifiers or
replacement coverage table. A filter mistake cannot establish coverage:
the independent retained-domain predicate must still be proved.
The coarse `excluding_core_pairs` form includes the five infeasibility
classes and additionally omits all core/core rows. Its separate coverage
kernel proves the direct cost for those feasible domains, as detailed
in Section 7. The other nine tables retain `excluding_core_separators`.

The metadata-only audit gives these active payload counts:

| Affine table | Historical rows | Primary exclusions | Secondary exclusions | Opposite core quarter | Additional core cost | Active rows |
|---|---:|---:|---:|---:|---:|---:|
| Candidate coarse mismatch | 129,031 | 6,028 | 7,540 | 232 | 4,806 | 110,425 |
| D upper | 24,197 | 2,445 | 3,219 | 232 | 0 | 18,301 |
| G lower | 9,087 | 380 | 425 | 32 | 0 | 8,250 |
| G upper | 9,796 | 349 | 442 | 48 | 0 | 8,957 |
| H lower | 48,050 | 3,359 | 4,395 | 232 | 0 | 40,064 |
| Mismatch 0.015 to 0.001 | 144,709 | 0 | 8,899 | 0 | 0 | 135,810 |
| Mismatch 0.1 to 0.015 | 107,196 | 7,140 | 7,988 | 0 | 0 | 92,068 |
| Mismatch 0.26 to 0.1 | 131,255 | 7,040 | 9,409 | 0 | 0 | 114,806 |
| T lower | 49,971 | 3,281 | 4,512 | 464 | 0 | 41,714 |
| T upper | 7,078 | 299 | 330 | 16 | 0 | 6,433 |
| **Total** | **660,370** | **30,321** | **47,159** | **1,256** | **4,806** | **576,828** |

All 83,542 removals delete whole angle chains. In all ten tables, the
ordered row records in every retained chain are identical to the
historical records; only the row indices are renumbered by the unchanged
`AffineCertificate.cover` constructor. The enhanced coarse bound maps
its higher edge targets over the same retained coarse rows and uses the
same geometric coverage dispatcher.

The touched reader also now accepts the frozen finite decimal strings
exactly: `.89727` becomes `89727/100000`, `-0.125` becomes `-125/1000`,
and `19.9999997` becomes `199999997/10000000`. It parses only integer
digits and emits integer-ratio syntax, with no floating-point conversion.

## 7. The complete coarse core/core cost with unchanged labels

For the label selected at a vertex, define its marker by

\[
 \psi=\sigma\arctan(b/a)-L(a,b).
\]

The physical angle identity gives the exact charged pair cost

\[
 \phi+L_s-L_t-\beta_i h(\phi)
 =g-\psi_s+\psi_t-\beta_i h(\phi).
\tag{11}
\]

The radius of every core center is below `4/5`. Disjoint unit squares
have center distance at least one, so the core/core physical gap exceeds
`4/3`; this is the center-chord proof in `Arithmetic/CorePairGeometry.lean`.
The new `selected_core_gap` adapter derives the radius bound from the
selected arcs' `Contains` predicates. It therefore covers radial chart
junctions without assuming that the actual radial tag is unique.

### Whole-arc marker control

All 124 original coarse core labels have `p=0`. On each of the 88 side
arcs, `a=7/12`, so with `t=b/a` the marker is

\[
 f(t)=\sigma\arctan t-c-\frac7{12}qt.
\]

The affine slope disappears from the second derivative. For `t≥0`,

\[
 |f''(t)|=\frac{2t}{(1+t^2)^2}\le1,
 \qquad
 (1+t^2)^2-2t=t^4+t^2+(t-1)^2\ge0.
\]

On an original label interval `[l,u]`, suppose both endpoint values lie
between `L+e` and `U−e`, where `e=(u−l)²/8`. Then the complete marker
lies in `[L,U]`. To prove the lower bound, subtract
`(t−l)(t−u)/2` from `f`; the resulting function is concave and lies
above the smaller of its endpoint values. The identity

\[
 (u-l)^2+4(t-l)(t-u)=(2t-l-u)^2\ge0
\]

gives the error `e`. Apply the same argument to `−f` for the upper
bound. This also covers a degenerate interval. The Lean lemmas
`endpoint_lower`, `endpoint_bounds`, and `chart_bounds` prove these
statements without subdivision or a radical derivative.

All 36 original core-corner labels also have `q=0`. Their markers are
signed arctangent minus a constant, so monotonicity directly bounds the
whole closed interval by its endpoint values, with zero interpolation
error. Both labels at any shared endpoint are individually checked.

### Explicit endpoint gates and edge budgets

The rational marker bounds are:

| Role | Lower bound | Upper bound |
|---|---:|---:|
| H | −383/1000 | 90/1000 |
| G | −323/1000 | −120/1000 |
| A | −368/1000 | 100/1000 |
| B | −329/1000 | 134/1000 |
| T | −88/1000 | 96/1000 |
| D, negative sign | −319/1000 | −12/1000 |
| D, positive sign | −319/1000 | 643/1000 |
| E | −342/1000 | −111/1000 |

`ArcValid` exposes four rational endpoint-label inequalities per existing
core arc: **496 inequalities** in total. It reuses the existing arctangent
endpoint enclosures; it introduces no new endpoint coordinates. The
predicate also checks the zero coefficients, ordered tangent interval,
and negative sign on core E arcs. The exact endpoint-only audit found all
496 inequalities valid, with a minimum reserve above `0.00044264`.
These are small explicit finite obligations, not a claim that the original
piecewise vertex labels have disappeared.

The positive D upper bound is intentionally kept large. When both ends
of `D→E` are core, a positive D sign gives the impossible core/core quarter
class of Section 6. The actual feasibility theorem therefore removes that
case before applying D's negative-sign upper bound. A positive D marker
used as a target on the preceding edge still keeps its original value.

By the unit-circle identity, `h(φ)<21/100` at every angle. Thus (11) and
the two marker bounds give the whole pair estimate

\[
 \phi+L_s-L_t-\beta_i h(\phi)
 >\frac43-U_i+L_{i+1}-\frac{21}{100}\beta_i.
\tag{12}
\]

The seven rational comparisons against the coarse targets have reserves

| Edge | Reserve above the coarse target |
|---|---:|
| H→G | 14179/750000 |
| G→A | 56419/300000 |
| A→B | 2179/750000 |
| B→T | 157429/750000 |
| T→D | 12679/750000 |
| D→E | 76429/750000 |
| E→H | 49219/300000 |

The weakest lower bound in (12) is above `0.9001753`, compared with the
coarse target `0.89727`. Every enhancement, at most `23/1000000`, fits
inside these reserves. `BudgetsValid` states the seven comparisons and
nonnegative-charge checks explicitly for each of the coarse and enhanced
metadata records. The source leaves their ordinary `by decide` proofs
uncompiled, just like the retained table obligations.

### Actual coverage and remaining cases

`GeometricCoreCoverage.chargedBound` first selects exactly one original
arc label per vertex. It then splits on the two selected radial classes.
For core/core pairs, `GeometricCoreMarker.pair_bound` proves (12) using
the actual center gap and the same two label values. For pairs with an
outer endpoint, every remaining allowed actual axis uses the original
continuous row claim and original closed angle-chain predicate.

The historical coarse input contains 8,644 core/core rows. The five
infeasibility classes already removed 3,838 of them; the direct cost
removes the remaining **4,806**, leaving **110,425 active coarse rows**.
The 462 original arc labels and their state-cover selection are unchanged.
No two-state cost data or angular cover replaces the omitted core rows.

In the 960-case coarse semantic classification, 384 cases are core/core.
The five infeasibility classes remove 224 of these. Equation (12) closes
all 160 remaining core/core cases, leaving **464 outer-endpoint cases**
after the full 336-case infeasibility reduction. The complete coarse
`ChargedBound` continues to depend on those retained outer-endpoint rows.

## 8. What the old labels suggest, and what they do not establish

Inspection of the 462 coarse arc labels shows that **460 have no primary
coordinate coefficient**: they are piecewise functions \(c+q b\).
The only two nonzero primary coefficients occur on the final outer arcs
for A with positive sign and B with negative sign. This suggests trying
one explicit potential of the transverse coordinate per role/sign/radial
branch, with circular-support corrections near an active endpoint.
It does not prove that a particular smooth formula will satisfy (5)–(6).

The previous low/high affine potentials and whole-circle support formulas
provide useful candidate families, but their established lower constants
do not supply the near-sharp candidate charged bounds. No fit or sampled
positivity claim is used in the new lemmas.

A Bellman formulation can now be stated without an angular minimizer:
for each source state, take the lower envelope of its feasible endpoint
and contact-root costs over target states and the finite axis/sign choices.
A potential satisfying the resulting role-to-role inequalities would
close the corresponding charged bound. The remaining minimization is
two-dimensional state geometry. Merely naming that operator is not a
proof of its required reserve.

## 9. Current dependency and validation status

- New source: `Candidate/GeometricPrimaryExclusion.lean`,
  `Candidate/GeometricSecondaryExclusion.lean`,
  `Candidate/GeometricCoreQuarter.lean`,
  `Candidate/GeometricAffineCoverage.lean`, `Candidate/GeometricMismatch.lean`,
  `Candidate/GeometricCoreMarker.lean`, and `Candidate/GeometricCoreCoverage.lean`.
- New angle tables or generated coverage lists: none.
- Active affine payload: **576,828 rows** across ten tables, a reduction
  of 83,542 from the preserved historical inputs.
- Active coarse and enhanced payload: **110,425 rows**, sharing the same
  18,606-row geometric removal from the historical 129,031-row input.
- All four complete charged stages still retain active tables. The coarse
  and enhanced stages have no core/core row dependency; their remaining
  state-positivity gate has at most 464 outer-endpoint cases.
- Preserved coarse vertex data: all 462 original labeled arcs. Explicit
  new core-marker checks: 496 endpoint-label inequalities on 124 existing
  arcs, their structural conditions, and seven budget comparisons with
  nonnegative-charge checks for each coarse/enhanced stage.
- Complete geometric regions excluded analytically: all zero-edge
  target-core/target-primary and source-core/source-primary regions;
  all-angle target-core/source-secondary regions with nonpositive source
  transverse coordinate; and all-angle source-core/target-secondary
  regions with nonnegative target transverse coordinate; and all four
  axes on the positive-source/negative-target core/core quarter region.
  Together they remove 336 semantic cases and 13,800 historical coarse rows.
- Complete feasible class handled by a direct cost proof: every coarse
  core/core pair, closing 160 additional semantic cases and removing the
  remaining 4,806 core/core rows with the same shared marker values.
- Existing capture hypotheses strengthened or assumed: none.
- `sorry`, new axioms, external-oracle substitutions: none.
- Validation performed: exact symbolic polynomial expansion of all SAT
  coefficient formulas and the discriminant identity; static source review;
  metadata-only audits of whole-chain deletion and unchanged retained
  records in all ten tables; Python checks of exact conversion for all
  155,148 distinct-per-table row/gamma strings and ten positive/ten
  rejection grammar fixtures; exact rational reserves for both whole
  core-quarter error-sign intervals; endpoint-only rational checks for all
  496 core-marker inequalities and the seven coarse/enhanced edge budgets;
  exact polynomial identities in the curvature proof.
- Historical coarse input SHA-256 remains
  `ffa48df0d02e18880314907a72a70fcc6aaceea4ee1060ea76b4fdb04c23a5fa`.
- Lean compilation, CI, and full certificate replay: not run.

The Python conversion checks validate the exact string arithmetic and
input compatibility; they do not execute or validate the Lean elaborator.

The next gate is a complete positivity proof over the remaining
outer-endpoint state branches using (5)–(6). That gate has a concrete
finite geometric interface; it must close before the corresponding
charged-stage table import is removed.
