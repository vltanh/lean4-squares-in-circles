# n=9: unrestricted minimizers have exact sparse actual-contact stresses

**Status: completed hand reduction, not the unrestricted sharp-radius theorem.**
This closes the compactness / minimizer / translational-stress portion of
G2.O3.0.2. It starts with the original independently rotated packing
predicate, not a common coordinate frame or a prescribed contact pattern.

**Main result.** If nine squares fit at any squared radius below
`Q = 1105/256`, there is a global minimizing packing at some `q0 < Q`
with a normalized nonnegative stress supported on **actual touching pairs**
and actual circle-contact vertices. One can choose at most **19 positive
scalar terms in total** (circle-vertex terms plus separating-edge terms).
The previously proved center-eliminating weak dual is **attained exactly**
at this minimizer. A connected positive-stress component suffices.

The theorem is necessary, not sufficient, for unrestricted optimality.
It does not prove `q0 >= Q`, nor that all resulting stresses use a common
perpendicular frame. It makes no planarity claim about the contact graph.
The separate companion ROTATION_STATIONARY_STRESS.md adds angular
stationarity with a different sparsity bound; the 19-term stress here
must not automatically be assumed to satisfy its torque equations.

## 1. Compactness with arbitrary frames and boundary contacts

For square `i`, use a center `c_i` and an orthonormal frame
`(u_i,v_i)`, where `u_i` is on the unit circle and `v_i = J u_i`.
Let

\[
 a_{i,\epsilon,\eta}=\tfrac12(\epsilon u_i+\eta v_i),
 \qquad p_{i,\epsilon,\eta}=c_i+a_{i,\epsilon,\eta},
 \qquad \epsilon,\eta\in\{-1,1\}.
\]

Every offset has squared norm `1/2`. Convexity of the disk gives the
exact containment criterion

\[
 \|p_{i,\epsilon,\eta}\|^2\le q\quad\text{for every corner}. \tag{1}
\]

The support halfwidth in unit direction `d` is

\[
 h_i(d)=\tfrac12(|d\cdot u_i|+|d\cdot v_i|)\ge\tfrac12.
\]

For any pair, disjoint open square interiors are equivalent to at least
one of the eight oriented own-axis inequalities

\[
 d\cdot(c_j-c_i)\ge h_i(d)+h_j(d),\qquad
 d\in\{\pm u_i,\pm v_i,\pm u_j,\pm v_j\}. \tag{2}
\]

Thus nonoverlap is a **finite union of closed conditions**, continuous
in the centers and the unit-frame coordinates. Contacts, ties between
possible axes, and square corners meeting at a point are included.

**Lemma 1.1 (attainment).** Given one packing of `n` unit squares in a
finite disk, the globally least squared containing radius is attained.
If a packing with `q < Q` exists, a global minimizer has `q0 < Q`.

*Proof.* Translate the disk center to zero. Use any known packing to
bound squared radius by `Q0`. Every square center lies in its square,
and therefore has norm at most `sqrt(Q0)`. The centers lie in a compact
product of closed disks; frames lie in `(S^1)^n`; take `q` in `[0,Q0]`.
Conditions (1) and (2) define a closed subset of this compact product.
The nonempty feasible set is compact, so the continuous coordinate `q`
attains its minimum. Every globally better packing could be translated
to center zero and would belong to this same compact sublevel set;
therefore the minimum is global, not just local to the construction.
If a subcritical packing exists, the minimum is no larger than its
squared radius and hence is strictly below `Q`. No deformation to a
row pattern has been used. QED.

For `n >= 2`, the attained squared radius is strictly greater than
`1/2`. Indeed the exact corner formula yields

\[
 q\ge\|c_i\|^2+\tfrac12+|c_i\cdot u_i|+|c_i\cdot v_i|
       \ge\|c_i\|^2+\|c_i\|+\tfrac12. \tag{3}
\]

If `q = 1/2`, all centers would be zero, so the inscribed open disks
of radius `1/2` of distinct squares would intersect.

## 2. Choose strict separators for all physically noncontacting pairs

**Lemma 2.1.** At any feasible packing, a pair whose **closed squares
are disjoint** has an own-axis separator with strictly positive gap.
For a pair whose closed squares intersect, every feasible separator
has gap zero.

*Proof.* The Minkowski difference of two squares is a convex polygon.
Its edge normals are among the two squares' side axes. If the closed
squares are disjoint, zero is outside that polygon, so at least one
of its facet inequalities is violated strictly; this is exactly a
strict version of (2). If a point belongs to both closed squares,
its projection belongs to both closed projection intervals. Feasible
disjoint interiors of those intervals can therefore only touch,
not have a positive gap. QED.

At a global minimizer, select **one** valid oriented separator for
each unordered pair: take a strict one for every noncontacting pair,
and any feasible one for a touching pair. Denote the resulting
oriented edges by `e = (i -> j,d_e)` and put

\[
 w_e=h_i(d_e)+h_j(d_e)\ge1,
 \qquad b_e(c)=w_e-d_e\cdot(c_j-c_i)\le0. \tag{4}
\]

Freeze these directions and all square orientations for the moment.
The center/radius problem is the finite convex problem

\[
 \min q,\qquad
 g_{i,k}(c,q):=\|c_i+a_{i,k}\|^2-q\le0,\quad b_e(c)\le0. \tag{5}
\]

Its feasible points are physical packings: keeping one valid
separator for every pair is sufficient. Consequently the original
global minimizer also minimizes (5). This is a restricted **feasible
branch**, not a replacement definition of unrestricted Packing.

There is no artificial `q <= Q` constraint in (5). That ceiling was
only used to obtain a global minimizer, not to manufacture a boundary
multiplier for the target value.

## 3. Elementary normal-cone lemma, including constraint qualification

We give the multiplier argument rather than merely assuming KKT
regularity. The same conclusion follows from Slater's theorem for
(5), but the following finite-dimensional proof exposes the exact
strict direction used here.

**Lemma 3.1 (active-gradient alternative).** Let finitely many `C^1`
inequalities `g_a(z) <= 0` hold at a local minimum `z0` of a linear
functional `ell(z)`. Suppose there exists a vector `v` with
`grad g_a(z0) dot v < 0` for every active inequality. Then

\[
 -\nabla\ell=\sum_{a\text{ active}} t_a\nabla g_a(z_0),
 \qquad t_a\ge0. \tag{6}
\]

One can choose at most `d` positive terms if all relevant gradients
and `-grad ell` belong to a vector space of dimension `d`.

*Proof.* The positive cone generated by finitely many active gradients
is closed. One elementary justification is to remove a generator
from any linearly dependent positive representation until the used
generators are independent. There are finitely many independent
subsets; for a convergent sequence in the cone, pass to one fixed
subset. Independence then bounds and determines its coefficient
sequence, whose limiting coefficients are nonnegative.

If `-grad ell` does not belong to this closed cone, finite-dimensional
separation supplies a vector `h` with `grad ell dot h < 0` and
`grad g_a dot h <= 0` for all active indices. For sufficiently small
positive `epsilon`, the vector `h + epsilon v` strictly decreases
both the objective and every active constraint to first order.
Differentiability and finiteness imply that a sufficiently short step
makes every active constraint strict; continuity preserves all
inactive constraints. This contradicts local minimality, proving (6).

For sparsity, if more than `d` positive generators occur, their
linear dependence gives coefficients `beta` with sum `beta_a grad g_a=0`.
Choose their sign so at least one `beta_a>0`, and subtract
`min_{beta_a>0}(t_a/beta_a)` times this relation. Coefficients remain
nonnegative and at least one vanishes. Repeat. QED.

**Lemma 3.2 (no abnormal multiplier obstruction).** The strict
direction required by Lemma 3.1 exists at the minimizing point of (5).

*Proof.* Set the center velocities equal to the original centers:
`dot c_i = c_i`. Choose a scalar `K` strictly greater than every
`2(c_i+a_{i,k}) dot c_i`, and set `dot q=K`. For circle inequalities,

\[
 \dot g_{i,k}=2p_{i,k}\cdot c_i-K<0.
\]

For every active separator,

\[
 \dot b_e=-d_e\cdot(c_j-c_i)=-w_e\le-1<0.
\]

This is a strict first-order feasible direction even at arbitrary
multiple contacts. Equivalently, expanding all centers by a factor
greater than one makes every selected separator strict, and a large
enough `q` makes all circle constraints strict. Such an expansion is
used **only** to prove regularity, not as a radius-decreasing packing
motion. QED.

## 4. At most 2n+1 active scalar terms

Apply Lemma 3.1 in the `2n+1` variables `(c_1,...,c_n,q)`.
Use circle multipliers `lambda_{i,k} >= 0` and separator multipliers
`mu_e >= 0`, supported only where their respective constraints are
active. The `q` component of (6) gives

\[
 \sum_{i,k}\lambda_{i,k}=1. \tag{7}
\]

Let

\[
 F_i=\sum_{e:i\to j}\mu_e d_e-\sum_{e:j\to i}\mu_e d_e.
\]

The center components of (6) give exact force balance:

\[
 2\sum_k\lambda_{i,k}p_{i,k}+F_i=0
       \qquad(i=1,\ldots,n). \tag{8}
\]

Complementarity gives

\[
 \lambda_{i,k}>0\Rightarrow\|p_{i,k}\|^2=q_0,
 \qquad
 \mu_e>0\Rightarrow d_e\cdot(c_j-c_i)=w_e. \tag{9}
\]

By the strict selection in Section 2, **every positive separator
multiplier joins two physically touching closed squares**. A tight
projection of a noncontacting pair was deliberately not selected.
This distinguishes the theorem from a certificate assembled from
arbitrary slack SAT owners.

Sparsity in Lemma 3.1 yields

\[
 \#\{(i,k):\lambda_{i,k}>0\}
       +\#\{e:\mu_e>0\}\le2n+1. \tag{10}
\]

For `n=9`, this total is **at most 19**. This is a bound on the number
of positive scalar terms, not a classification into 19 graph types.

## 5. Strong attainment of the existing explicit weak dual

Put `lambda_i = sum_k lambda_{i,k}`. For `lambda_i>0`, positive
corner multipliers occur only at corners maximizing the actual
squared norm, so their averaged offset is a subgradient witness for

\[
 f_i(c)=\|c\|^2+\tfrac12+|c\cdot u_i|+|c\cdot v_i|.
\]

Equation (8) says `c_i` minimizes the convex function
`lambda_i f_i(c) + F_i dot c`. If `lambda_i=0`, it says `F_i=0`.
Consequently the completed-square bound in
[SEPARATOR_GRAPH_CONVEX_DUAL.md](SEPARATOR_GRAPH_CONVEX_DUAL.md)
is an equality at this stress:

\[
\begin{split}
 q_0={}&\sum_e\mu_e w_e+\sum_{i:\lambda_i>0}
 \left[\frac{\lambda_i}{2}
 -\frac{(|F_i\cdot u_i|-\lambda_i)_+^2
       +(|F_i\cdot v_i|-\lambda_i)_+^2}{4\lambda_i}\right].
                                                        \tag{11}
\end{split}
\]

Zero-weight nodes contribute zero and must satisfy `F_i=0`.
This is an **attained dual identity**, not just existence of some
possibly weak lower bound.

For completeness, scalar minimization in the own-square coordinates
also recovers every positive-circle-weight center:

\[
 c_i\cdot u_i=-\frac{\operatorname{sgn}(F_i\cdot u_i)
                     (|F_i\cdot u_i|-\lambda_i)_+}{2\lambda_i},
 \quad
 c_i\cdot v_i=-\frac{\operatorname{sgn}(F_i\cdot v_i)
                     (|F_i\cdot v_i|-\lambda_i)_+}{2\lambda_i}. \tag{12}
\]

The equality of (11) follows either by substituting (12), or by
noting that every positive edge and circle multiplier is
complementary and every node term reaches its exact infimum.
No orientation optimization has been assumed convex.

## 6. Connected stressed cores and boundary-support restrictions

Make a graph whose edges are the pairs with `mu_e>0`, and include
all nodes carrying a positive circle multiplier. Other nodes can
be ignored for the stress, although they remain physical squares
of the full packing.

**Lemma 6.1.** Every nonempty positive-stress component has positive
total circle weight. It has at least **two distinct squares** with
positive circle weight whenever `q0>1/2`.

*Proof.* Suppose a component had zero circle weight. Then (8)
gives `F_i=0` at all its nodes. Dot these equations with the centers
and sum. Each edge contributes

\[
 \mu_e d_e\cdot(c_i-c_j)=-\mu_e w_e<0,
\]

which is impossible unless the component has no positive edge.
An isolated node with zero circle weight was not included.

For a component with positive weight, sum (8) over its nodes.
Internal edge forces cancel, hence

\[
 \sum_{i,k\text{ in the component}}\lambda_{i,k}p_{i,k}=0. \tag{13}
\]

Normalize its circle weights to have sum one. If all these boundary
vertices belonged to one square of center `c`, then

\[
 \tfrac12=\sum_k\lambda_k\|p_k-c\|^2
          =q_0+\|c\|^2,
\]

because the weighted boundary-vertex barycenter is zero. This
contradicts `q0>1/2`. QED.

**Consequences.**

1. The origin belongs to the convex hull of the positive-weight
   circle vertices of **each** component. This is not a claim that
   the origin lies in the interior of a packing square.
2. A zero-circle-weight square cannot be a degree-one leaf of the
   positive-stress graph: its one nonzero unit-direction force
   could not sum to zero.
3. At a zero-circle-weight degree-two node, the two incident force
   vectors are opposite, their magnitudes agree, and the two
   separator normals are parallel. This follows directly from
   balance of two nonzero vectors. It is **not** alignment of all
   square orientations.
4. Restrict to any positive-stress connected component and divide
   all its multipliers by its circle-weight sum. Equations (7)–(11)
   still hold, with the same value `q0`. Thus a **single connected
   stressed core** suffices. Sparsification followed by component
   selection preserves the 19-term bound.

These conditions remove entire graph classes: unsupported internal
self-stresses, one-boundary-square components, and internal leaves
are impossible. They do not yet imply a common coordinate frame,
a small enumerated list of all remaining graphs, or the value `Q`.

## 7. Explicit exact regression stress at the record packing

Use the seven aligned anchor centers

\[
 M=(-3/2,1/16),(-1/2,1/16),(1/2,1/16),(3/2,1/16),
 \qquad B=(-1,-15/16),(0,-15/16),(1,-15/16),
\]

and the two obliquely separated upper squares of
[NO_GLOBAL_ORTHOGONAL_FRAME.md](NO_GLOBAL_ORTHOGONAL_FRAME.md).
Put circle weight `23/64` on each outer M corner
`(+-2,9/16)` and `9/64` on each outer B corner
`(+-3/2,-23/16)`. Set all other circle weights to zero.

Stress each of the three horizontal M-neighbor edges by `23/16`,
each of the two horizontal B-neighbor edges by `27/64`, and each
of the two corresponding upward B-to-M edges by `207/512`.
There are **4 circle atoms + 7 edge atoms = 11 positive terms**.
All edge gaps are zero; every node satisfies (8); the weighted
boundary-vertex barycenter is zero; and (11) equals `1105/256`
exactly. The two obliquely separated upper squares have no stress
weight. Their existence therefore does not require any forced
common-frame separator between them.

The companion `check_sparse_stress.py` uses rational arithmetic to
check the 36 pairwise SAT conditions, all 36 corners, this balance,
and the exact dual value. It is a regression check of **one witness**,
not a proof of (11) for all configurations or a premise of Sections
1–6.

## 8. Gate impact and exact residual obligation

**CLOSED:** G2.O3.0.2's unrestricted minimizer / actual-contact /
normalized nonnegative stress reduction. There is no longer an
unproved transition from a hypothetical `q<Q` packing to a sparse,
actual-contact, exactly certifying translational stress at a global
minimizer. No row deformation is needed.

**STILL OPEN:** G2.O3.0.3 / O3.3 must compress these physically
realizable stressed graphs into a human-sized exhaustive structural
classification, and O3.0.4 / O4 must prove the resulting orientation-
uniform lower bound `q0>=Q`. A finite 19-term support bound does not
by itself make the graph enumeration small. The full n=9 sharp-radius
and equality theorems are not proved here.

**Equality caution:** replacing an arbitrary packing by a global
minimizer is sufficient for a contradiction to `q<Q`. It does not
classify all packings with `q=Q` before global optimality is proved.
Once optimality is established, each equality packing is itself a
global minimizer and the reduction applies to it without replacement.

**Verification:** hand derivation plus exact regression arithmetic;
no Lean build, CI run or independent full manuscript audit.

## Background reference

The finite-gradient argument is the elementary KKT / conic
separation principle. The usual convex Slater and KKT statements
are also given by Boyd and Vandenberghe, *Convex Optimization*,
Chapter 5 (the official Stanford duality slides, slides 5.13 and
5.21). Here strict feasibility and sparsity are explicitly proved
for square packings, so no numerical optimizer or external oracle
is an input to the mathematical reduction.
