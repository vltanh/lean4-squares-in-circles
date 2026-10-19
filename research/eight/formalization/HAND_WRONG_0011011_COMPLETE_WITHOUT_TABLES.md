# The complete 0011011 word exclusion without scalar tables

**Theorem.** After the central-core, boundary, and frame-concentration
reductions, the exterior seven-cycle cannot have quarter word 0011011.
The complete core/core, mixed, and outer/outer dependencies are assembled
below, including the prior zero-primary cyclic exclusion.
No candidate-word capture or mismatch bound is an input to the argument.

This note replaces the dependency assembly in
../WRONG_0011011_WHOLE_WORD_HAND_PROOF.md. It retains the exact role
polynomials, intrinsic sign and radial cases, and cyclic cancellation,
and binds every former mixed or outer continuous scalar table to its
complete analytic replacement. Fixed rational endpoint comparisons
remain ordinary arithmetic in the corresponding calculus proofs.
No numerical cover, Bernstein coefficient row, recursive pair
certificate, or verifier result is a premise.

## 1. The theorem and its geometric inputs

Let eight unit squares with pairwise disjoint open interiors lie in
a disk with squared radius
\[
 q\le Q=\frac{9789}{2500}.
\]
Apply the geometric reduction in
[HAND_EXTERIOR_FRAME_CONCENTRATION](../HAND_EXTERIOR_FRAME_CONCENTRATION.md),
including its table-free central-band replacements and the
[fixed-axis radial-boundary reduction](../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md).
It produces seven exterior boundary states in cyclic center order.
Every state lies on the core side/corner or on the outer circle.
All physical square frames are preserved; neighboring open interiors
remain disjoint. The ordered center gaps and frame lifts satisfy
\[
 \delta_i>\frac{19}{25},\qquad
 \sum_{i=0}^{6}\delta_i=2\pi,\qquad
 \max_i\beta_i-\min_i\beta_i<\frac7{10}.                 \tag{1}
\]

**Theorem.** Such a boundary cycle cannot have quarter-increment word
\[
                    (k_0,\ldots,k_6)=(0,0,1,1,0,1,1).    \tag{2}
\]
Every radial assignment is included, as are every original signed
separating axis and all boundary ties.

Before considering (2), apply
[HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
to this same cycle. Its whole-domain primary-edge support and the
common G1 cycle inequality exclude the two primary axes on each
zero-quarter edge. Thus only its two original transverse axes can
remain. This uses the closed frame tour after (1); it does not
assume either wrong-word theorem, a candidate-word tangent cut, or
any bound on the mismatch sum.

This global premise matters: one mixed-zero family is removed by the
cycle theorem. The proof below is a theorem about actual boundary
cycles with these geometric properties. It does not substitute an
unproved isolated-pair estimate for that absent primary family.

## 2. States, exact labels, and edge costs

Set
\[
 a_c=\frac7{12},\qquad
 d_c=\frac12+\frac{\sqrt2}{24},\qquad
 d=\sqrt{Q/2}-\frac12.
\]
The core boundary is the union of the two closed pieces
\[
 a=a_c,\quad 0\le b\le\frac12,
\]
and
\[
 (a-\tfrac12)^2+(b-\tfrac12)^2=\frac1{144},
 \qquad\frac12\le b\le d_c,\quad a\ge b.                \tag{3}
\]
The outer boundary is
\[
 a=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\qquad0\le b\le d.   \tag{4}
\]
Write the actual center in its chosen nearest-axis frame as
\((a,-\sigma b)\), with \(\sigma\in\{-1,1\}\), and set
\[
 \alpha=\sigma\arctan(b/a)\in[-\pi/4,\pi/4].
\]
For the physical frame lifts in (1), use periodic indices
\(\beta_{i+7}=\beta_i\). Then
\[
 \phi_i=k_i\pi/2+\beta_{i+1}-\beta_i,\qquad
 \delta_i=\phi_i+\alpha_i-\alpha_{i+1}.                \tag{5}
\]
Every zero edge has \(|\phi_i|<.7\); every one edge has
\(|\phi_i-\pi/2|<.7\). All pair components below prove their
inequalities on the corresponding closed angle ranges.

The role labels are the following explicit polynomials:
\[
 L_i^\sigma(a,b)=c_i^\sigma+p_i^\sigma a+q_i^\sigma b
                      +r_i^\sigma b^2+s_i^\sigma ab.
\]
The five integers in each entry are divided by \(100000\).
They define the mathematical functions; their former JSON
representation is not a premise.

| Role | Radial kind and sign | \(100000(c,p,q,r,s)\) |
|---:|:---:|---|
| 0 | \(C+\) | \((125,0,103981,0,0)\) |
| 0 | \(C-\) | \((19911,0,63607,0,0)\) |
| 0 | \(O+\) | \((2478,0,93015,2363,-11055)\) |
| 0 | \(O-\) | \((394,0,33945,0,39635)\) |
| 1 | \(C+\), \(C-\) | \((19555,0,63132,0,0)\) |
| 1 | \(O+\), \(O-\) | \((0,-26,83194,-11864,17627)\) |
| 3 | \(C+\) | \((-1449,0,104240,0,0)\) |
| 3 | \(C-\) | \((22042,-34492,98439,-5334,0)\) |
| 3 | \(O+\) | \((0,-1025,16031,0,63457)\) |
| 3 | \(O-\) | \((1670,0,242322,-91744,-95769)\) |
| 4 | \(C+\) | \((4970,0,94831,0,0)\) |
| 4 | \(C-\) | \((16823,0,62312,0,0)\) |
| 4 | \(O+\) | \((3965,0,385510,-149748,-189442)\) |
| 4 | \(O-\) | \((0,-2112,29090,0,44642)\) |

The remaining roles are defined, with indices modulo seven, by
\[
                         L_{2-i}^{\sigma}=L_i^{-\sigma}. \tag{6}
\]
The role-1 entries satisfy their required self-reflection identity.
At a zero transverse coordinate or a nearest-axis tie, choose a
representation once for that vertex and use it in both incident
costs. The side and corner use the same polynomial at their join.
Alternative signed formulas need not have the same value at zero.

The corrected edge cost and the common threshold are
\[
 C_i=\phi_i+\sigma_iL_i^{\sigma_i}(a_i,b_i)
              -\sigma_{i+1}L_{i+1}^{\sigma_{i+1}}(a_{i+1},b_{i+1}),
 \qquad
 \gamma=\frac{17953}{20000}=.89765.                     \tag{7}
\]

## 3. The exact intrinsic case cover

The two consecutive zero-quarter edges in (2) give, by (1) and (5),
\[
 \alpha_0-\alpha_2
 =\delta_0+\delta_1-(\beta_2-\beta_0)
 >\frac{38}{25}-\frac7{10}
 =\frac{41}{50}>\frac\pi4.                             \tag{8}
\]
Because each local angle lies in \([-\pi/4,\pi/4]\), (8) forces
\(\alpha_0>0\) and \(\alpha_2<0\).
A zero-quarter edge cannot have sign pair \((-,+)\), since then
\(\alpha_i-\alpha_{i+1}\le0\) and
\(\delta_i\le\phi_i<.7<19/25\).

These restrictions give the following over-cover. No further
sign, radial, owner, or mismatch constraint is assumed.

| Edge | Quarter increment | Allowed signs |
|---:|---:|---|
| 0 | 0 | \(++,+-\) |
| 1 | 0 | \(+-,--\) |
| 2 | 1 | \(-+,--\) |
| 3 | 1 | \(++,+-,-+,--\) |
| 4 | 0 | \(++,+-,--\) |
| 5 | 1 | \(++,+-,-+,--\) |
| 6 | 1 | \(++,-+\) |

There are nineteen edge/sign cases and four ordered radial kinds
\(CC,CO,OC,OO\) for each. Thus there are seventy-six directed
pair cases and, before the geometric exclusion of primary zero
branches, \(76\cdot4=304\) original directed axis branches.

Reflection of the plane and reversal of center order send
\[
 (i,\sigma,\tau,K_s,K_t)
       \longmapsto(1-i,-\tau,-\sigma,K_t,K_s).          \tag{9}
\]
The word (2) is invariant under this operation, and (6) makes the
cost (7) invariant. The four signed axes are permuted by
\((1\ 3)(2\ 4)\) in the original one-based numbering.
This uses the stated labels; it does not interchange arbitrary
source and target functions.

The only fixed directed cases of (9) are edge 4 with signs
\((+,-)\) and equal radial kinds \(CC\) or \(OO\).
Consequently the seventy-six cases have thirty-nine reflection
classes: ten core/core, nineteen mixed, and ten outer/outer.
The directed counts are respectively 19, 38, and 19.
This is a finite geometric symmetry cover, not a subdivision of
any continuous state coordinate.

## 4. The complete edge inequality

We now prove for every physically possible case in Section 3 that
\[
                              C_i>\gamma.              \tag{10}
\]
The source notes below retain the original signed separating
projections. Only their continuous scalar premises are replaced.

### 4.1. Every core/core case

[WRONG_0011011_ALL_CORE_CORE_HAND_PROOF](../WRONG_0011011_ALL_CORE_CORE_HAND_PROOF.md)
already proves all ten core/core reflection classes by geometry
and calculus. Its uniform core-angle lemma is
\[
 0\le\arctan(b/a)-gb\le\frac\pi4-gd_c
                    \qquad(0\le g\le8/7),             \tag{11}
\]
on both pieces (3). It follows from one elementary side minimum
and convexity on the corner. Its one nonaffine core label is
bounded by the same lemma plus
\[
 -.05334d_c^2
 \le .34492(a_c-a)-.05334b^2\le0.
\]
Every core center has norm less than \(4/5\); neighboring center
distance is at least one. The cosine law therefore gives the
stronger core/core center gap \(\delta>27/20\).
Substituting (11) into the exact labels proves \(C_i>.91\)
in all ten intrinsic role/sign cases. These finite role
substitutions use no continuous scalar table.
Thus all nineteen directed core/core cases satisfy (10).

### 4.2. Every mixed radial case

[HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES](HAND_WRONG_0011011_MIXED_COMPONENTS_WITHOUT_TABLES.md)
is the complete mixed theorem. Its Sections 1–8 supply all
remaining support and derivative replacements; its Section 9
gives the exact nineteen-class assembly. It proves (10) for
all thirty-eight directed mixed cases and all 152 original
axis branches, treating absent primary zero branches by the
cycle theorem in Section 1.

For an explicit map of the replacements, its common actual-circle
support in Section 1 removes all nine former squared-polynomial
rows. Sections 2 and 4 complete the same-sign and opposite-sign
mixed zero families. Sections 3, 5, 6, 7, and 8 complete the
five remaining difficult whole quarter-one mixed families.
The untouched edge-2 negative core-to-outer theorem and the four
easy edge-3 mixed families already have whole-domain geometric
proofs.

The aligned mixed theorem and the edge-2 mixed quarter strip
are imported only at \(\phi=\pi/2\) and
\(|\phi-\pi/2|\le.02\), respectively. Their proofs use original
contact continuations, scalar monotonicity, concavity, and
single-reference strong convexity. They have no hidden
continuous-domain table. Every parent mixed theorem proves all
remaining angles, and includes its core side/corner join and
every zero-coordinate exit.

### 4.3. Every outer/outer case

The following map gives all ten outer/outer reflection classes.
The names in the “Original geometry” column have prefix
WRONG_0011011 and suffix HAND_PROOF.md. The successor supplies
every former interval or coefficient premise needed from its
original geometry.

| Edge | Signs | Original geometry | Complete analytic successor or retained proof |
|---:|:---:|---|---|
| 0 | \(++\) | SAME_OUTER_ZERO | [Same-sign outer zero](HAND_WRONG_0011011_SAME_SIGN_OUTER_WITHOUT_TABLES.md) |
| 0 | \(+-\) | ASYMMETRIC_OPPOSITE_OUTER_ZERO | [Original whole-angle proof](../WRONG_0011011_ASYMMETRIC_OPPOSITE_OUTER_ZERO_HAND_PROOF.md) |
| 2 | \(--\) | NEGATIVE_OUTER_QUARTER | [Negative quarter](HAND_WRONG_0011011_NEGATIVE_QUARTER_WITHOUT_TABLES.md) |
| 2 | \(-+\) | OPPOSITE_OUTER_EDGE2_QUARTER | [Opposite edge 2](HAND_WRONG_0011011_OPPOSITE_EDGE2_WITHOUT_TABLES.md) |
| 3 | \(++\) | EDGE3_POSITIVE_OUTER_PAIR | [Positive edge 3](HAND_WRONG_0011011_POSITIVE_EDGE3_WITHOUT_TABLES.md) |
| 3 | \(+-\) | POSITIVE_NEGATIVE_OUTER_QUARTER | [Original whole-angle proof](../WRONG_0011011_POSITIVE_NEGATIVE_OUTER_QUARTER_HAND_PROOF.md) |
| 3 | \(-+\) | EDGE3_OPPOSITE_AXES12 and EDGE3_OPPOSITE_AXES34 | [Opposite edge 3](HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md) |
| 3 | \(--\) | EDGE3_NEGATIVE_OUTER_QUARTER | [Negative edge 3](HAND_WRONG_0011011_EDGE3_NEGATIVE_WITHOUT_TABLES.md) |
| 4 | \(++\) | SAME_OUTER_ZERO | [Same-sign outer zero](HAND_WRONG_0011011_SAME_SIGN_OUTER_WITHOUT_TABLES.md) |
| 4 | \(+-\) | SYMMETRIC_OUTER_WHOLE_ANGLE | [Original whole-angle proof](../WRONG_0011011_SYMMETRIC_OUTER_WHOLE_ANGLE_HAND_PROOF.md) and [aligned quartic proof](../WRONG_0011011_SYMMETRIC_ALIGNED_OUTER_HAND_PROOF.md) |

Every listed conclusion is strictly stronger than (10).
The table's nine nonfixed classes recover their reflected
partners, while its final symmetric class is fixed.
Hence it covers all nineteen directed outer/outer cases
and all 76 of their original directed axis branches.

Here are the exact replacements that make this map a
table-free dependency chain.

* The same-sign zero successor proves one negative Hessian
  determinant on the entire stationary curve and one
  strong-convexity estimate on the entire source-diagonal
  contact. Its other boundary costs have whole-interval
  monotonicity or positive curvature. This removes the two
  stationary rows and six angle-curvature intervals.
* The negative edge-2 successor gives a whole aligned
  third-derivative sign, uniform inverse-contact concavity,
  and one derivative shape on the final-angle boundary.
  The aligned, contact, and endpoint interval tables are
  thereby removed.
* The opposite edge-2 successor replaces all axial-curve,
  source-ratio, support-concavity, and target-ratio rows
  with whole-domain derivative bounds and circular support.
* The opposite edge-3 successor covers all eight original
  axis/angle halves. It gives both aligned curvatures, one
  uniformly positive Hessian on the lower contact rectangle,
  a concavity exclusion outside it, the complete critical-curve
  envelope, and the upper-primary target-ratio concavity.
  The six critical-curve brackets and six third-derivative
  intervals are replaced by a single whole continuation
  and its derivative sign.
* The negative edge-3 successor replaces all three
  primary-coordinate speed rows by one strongly convex
  product. It replaces the six zero-target angle intervals
  by one linear angle bound and one scalar-label support.
* The positive edge-3 successor replaces all four early
  support intervals and all four source-cut contact rectangles.
  Its lower axis-4 estimate is one monotone scalar on the
  whole domain. Its remaining contact and endpoint arguments
  are the original analytic ones.

The last component has two mixed-source imports that must be
bound explicitly. Its later lower axis-1 zero-curve derivative
comes from Section 6.2 of the new mixed successor, replacing
the five old intervals in
EDGE3_POSITIVE_CORE_TO_POSITIVE_OUTER §3.2.
Its global affine bound for the target label \(J\) comes from
EDGE3_NEGATIVE_CORE_TO_POSITIVE_OUTER §1, which was already
proved by strong concavity and a convex-derivative endpoint
argument, without a scalar table.
Thus no old mixed table enters indirectly through this outer
component.

The unchanged asymmetric zero proof uses exact contact speeds,
whole-curve concavity, and complete diagonal exits for both
label orders and both angle signs. The unchanged symmetric
zero proof excludes all nonaligned minima by contact
derivatives; its aligned scalar follows from eliminating the
two radicals and completing a square in one strongly convex
quartic. The unchanged positive-to-negative quarter proof uses
two circular chords and a uniform bound on the sum of the
transverse coordinates. Each is already a whole-domain proof
on all original axes.

Together, Sections 4.1–4.3 prove (10) on the entire geometric
case cover. They make no restriction to an all-outer ring or
to a selected number of core vertices.

## 5. The cycle sum gives the exact contradiction

Use the representation of each vertex fixed in Section 2.
Each signed role label occurs once positively and once negatively
in the sum of (7), so it cancels exactly. The frame differences
in (5) telescope as well. Since the word (2) has four unit
quarter increments,
\[
 \sum_{i=0}^{6}C_i
 =\sum_{i=0}^{6}\phi_i
 =\frac\pi2\sum_{i=0}^{6}k_i
 =2\pi.                                                   \tag{12}
\]
This equality uses no continuity between alternative labels
at a tie, only consistent use of the chosen label at its two
incident edges.

On the other hand, the seven strict inequalities (10) imply
\[
 2\pi=\sum_iC_i>7\gamma=\frac{125671}{20000}.             \tag{13}
\]
The entirely rational reserve is
\[
 \frac{125671}{20000}-\frac{710}{113}
 =\frac{823}{2260000}>0,\qquad
 2\pi<\frac{710}{113}.                                  \tag{14}
\]
For completeness, the upper bound follows from Machin's
identity and adjacent alternating arctangent sums. If
\[
 T_n(x)=\sum_{j=0}^{n-1}\frac{(-1)^j x^{2j+1}}{2j+1},
\]
then
\[
 \pi=16\arctan(1/5)-4\arctan(1/239)
 <16T_5(1/5)-4T_2(1/239)<\frac{355}{113}.
\]
The last comparison is a single explicit rational inequality.
Equations (13) and (14) contradict each other and prove the
theorem.

## 6. Scope of the completed exclusion

The contradiction excludes the entire 0011011 branch after
the geometric boundary reduction, including all \(2^7\)
radial assignments, all allowed local signs, and every weak
separating contact. There is no equality configuration in
this branch because the common cyclic reserve is strict.

The finite label coefficients and intrinsic geometric case
maps above remain part of the hand proof. They define the
potentials and identify which exact theorem applies.
They are not numerical partitions of the side, corner,
outer coordinate, angle, stationary curve, or frame mismatch.
Those continuous domains have all been handled by the
analytic replacements in Section 4.

No old hand-closure manifest, source hash, coefficient
checker, or recursive interval certificate is used to
infer a mathematical inequality. The source formulas,
derivative signs, circle supports, explicit polynomial
identities, and elementary rational reference comparisons
are the premises that a reader can check.

This is one complete wrong-word exclusion. The separate
0010111 exclusion and the four double-increment word
exclusions are needed to finish the full word-selection
gate. Candidate-word tangent capture, mismatch contraction,
and the final equality theorem remain separate steps.
