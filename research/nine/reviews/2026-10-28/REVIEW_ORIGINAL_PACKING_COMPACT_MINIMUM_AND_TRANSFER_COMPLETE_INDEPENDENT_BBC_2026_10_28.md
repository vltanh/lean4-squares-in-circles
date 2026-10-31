# Complete independent review: original Packing compactness, canonical minimum and radius transfer

Date: October 28, 2026 UTC. Reviewer: `broad_s_families`.
Author of the reviewed source: root. The reviewer contributed neither its
discovery nor a repair.

**PASS UNCHANGED on the complete original finite-packing domain.**
The source gives compact attainment from the exact original `Packing`
predicate, with independent full square frames and all allowed contact
endpoints. It supplies a global radius minimum, a finite continuous
lexicographic refinement including the proposed center-energy minimum, and
the stated conditional minimum-to-original radius transfers. Its warning
that original equality packings need not minimize the secondary functional
is correct and essential.

The entire existing original fine gate **G4.2.a**, at zero-based index 2457,
is mathematically supplied. This is a complete gate result, rather than a
proper-domain feature. The review itself changes no authoritative flag;
separate root adoption and exact integration remain necessary. No other
whole gate, global selector compatibility, sharp geometric exclusion,
equality classification or certificate retirement follows from this source.

## 1. Frozen objects and extent of this independent read

| Object | Bytes | SHA256 | Git blob |
| --- | ---: | --- | --- |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | 15756 | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` | `78056e2005e0c2a01c0a4d0c466830edee9ed05c` |
| `INDEPENDENT_ORIGINAL_PACKING_COMPACT_MINIMUM_AND_TRANSFER_EXACT_RECORD_BBC_2026_10_28.json` | 21839 | `db06a50d9782dfe572783daa9699cc2923c6a4b62efbab72f6bdbdfd403639d4` | `2ca47a65c2dc40260c72ac3582a33b58d87449fa` |
| `SquaresInCircles/Geometry.lean` | 20319 | `64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94` | `14e10cb5be282f490ad46ac2cac63185de4ff566` |
| `research/nine/SPARSE_MINIMIZER_STRESS.md` | 16597 | `b182276dace03bf64d9903145e8861022712b05f7ff7317ad62f30f97850e9ac` | `5ee6d10f5e7a2770ae1916f0f65cf7ca73b4e868` |

The comparison head is
`bbc1e87f65168bba704d2b21a91faf0e313945c2`. I independently rehashed every
object above. The two published direct files have the exact byte sizes and
Git blobs in the complete current recursive tree. Their literal source-pin
rows agree with the reviewed manuscript. The candidate source remains its
frozen 15,756-byte, 312-line payload without a revision.

I read all 312 lines of the candidate, all 525 lines of the exact current
`Geometry.lean`, and all 419 lines of `SPARSE_MINIMIZER_STRESS.md`. The
latter is explicitly provenance for the already available attainment idea,
not an external proof premise. Its later translational stress and sparsity
statements are not imported. Reading them does not turn this review into a
new acceptance of their use in a torque-stationary certificate.

The independent exact record matches eleven actual definition blocks,
checks 27 exact polynomial identities and four basic endpoint facts, and
records the complete continuous-domain reconstruction and original gate
scope. These computations corroborate displayed algebra. They are not
sampled packing tests, finite pose exclusions or new computational geometry
certificates. The compactness, strict-limit, globality and quantifier
arguments below are mathematical arguments on the full continuous domain.

## 2. Exact match to the original definitions

The original point space is a pair of real coordinates. `UnitSquare` stores
its center, two real frame coordinates $C,S$, and exactly the relation
$C^2+S^2=1$. It does not impose a common frame, an angular interval, a
finite orientation set or a contact pattern. With

\[
 u=(C,S),\qquad v=(-S,C),
\]

one has $u\cdot u=v\cdot v=1$, $u\cdot v=0$, and determinant one.
The precise original definitions give

\[
 \operatorname{localX}(p)=(p-c)\cdot u,
 \qquad
 \operatorname{localY}(p)=(p-c)\cdot v.
\]

Direct expansion yields

\[
 ((p-c)\cdot u)u+((p-c)\cdot v)v=p-c.
\]

Conversely, at $p=c+xu+yv$, the two actual local coordinates are exactly
$x,y$. Thus the manuscript's closed and open coordinate boxes are both
exactly equivalent to the original predicates. The argument checks both
directions and preserves strict versus weak endpoints. It does not infer
open-square membership from closed membership.

The original `Packing` conjunction has three parts: $R\ge0$, whole closed
square containment in the squared disk, and absence of a common open-square
point for every pair of distinct labels. The source reproduces that entire
conjunction. In particular, nonoverlap is not strengthened to disjoint
closed sets. Shared sides, corner contacts, multiple junctions and arbitrary
circle tangencies remain permitted.

The source also correctly keeps the separate nonnegative-radius conjunct.
The bare squared `inDisk` relation would not distinguish $R$ from $-R$.
No minimization or square-root conclusion here discards the first Packing
conjunct. All order comparisons involving squared radii occur after the
nonnegative radii have been established.

The full original frame circle is retained for each label. Multiple frame
representations of the same physical square are harmless: compactness is
proved in the original coordinate representation, without quotienting by
those representations or choosing a preferred angular chart. The geometric
secondary functional used below is independent of this frame redundancy.

## 3. Translation is an exact equivalence, including the disk center

Let an actual original packing use disk center $o$. Replace each center
$c_i$ by $c_i-o$ and retain its own $C_i,S_i$. At the corresponding
point $p-o$, both local coordinates are unchanged because

\[
 (p-o)-(c_i-o)=p-c_i.
\]

The same identity preserves every strict or weak square-membership test.
The squared disk displacement also remains exactly $\lVert p-o\rVert^2$.
Consequently the translated packing satisfies the original predicate about
the origin with the same nonnegative radius. Translation back proves the
converse, including all pairwise nonoverlap tests and every original label.

This removes the otherwise unbounded containing-circle center from the
compact coordinate family without adding a physical premise. The operation
is one common translation, not an independent motion of selected bodies.
It neither changes any frame nor assumes uniqueness of the containing disk
center. Different original circles are allowed; each packing is translated
by its own actual disk center.

For the later secondary functional, the original geometric quantity is
therefore $\sum_i\lVert c_i-o\rVert^2$. In origin-centered coordinates it
is exactly the displayed $\Phi=\sum_i\lVert c_i\rVert^2$. No absolute
ambient coordinate origin is silently imposed on the original problem.

## 4. The full finite coordinate sublevel is compact

Fix any supplied original feasible packing and translate it as above. Its
radius $R_0$ is finite and nonnegative because it is a real coordinate and
satisfies the original predicate. For any finite $n$, the proposed ambient
set is

\[
 K_0=[0,R_0]\times\prod_{i\in\operatorname{Fin}n}
       \left(\overline D_{R_0}(0)\times S^1\right).
\]

Every factor is closed and bounded in a finite-dimensional real vector
space. The finite product is compact. For $n=0$, the square-coordinate
product is a one-point empty product, leaving the compact radius interval.
There is no loss at the frame circle's angular wrap because no half-open
angle parameter is introduced.

Every feasible origin-centered packing with radius at most $R_0$ belongs
to this product. Its actual center is in its own closed square, as both local
coordinates there are zero. Whole-square containment gives
$\lVert c_i\rVert\le R\le R_0$. Each frame satisfies its actual unit
relation. Hence $K_0$ contains all relevant feasible packings, not just a
selected contact stratum or a neighborhood of the witness.

The feasible subset $K$ is nonempty: the supplied translated witness at
the closed endpoint $R=R_0$ lies in it. The rest of the compactness proof
must show closedness of that exact feasible subset. It does so separately
for containment and open-interior nonoverlap.

## 5. Whole-square containment is exactly the four closed inequalities

For each label, the four vertices are

\[
 p_{\epsilon,\eta}
   =c+\frac{\epsilon u+\eta v}{2},
 \qquad \epsilon,\eta\in\{-1,1\}.
\]

They are continuous functions of the actual center and frame coordinates.
A point with own coordinates $x,y\in[-1/2,1/2]$ has the stated weights

\[
 w_{\epsilon,\eta}
    =\frac{(1+2\epsilon x)(1+2\eta y)}4.
\]

Each factor is nonnegative on that closed domain. Summing the four weights
gives one; their weighted signed half-coordinates give $x$ and $y$.
Therefore their weighted actual vertex sum is exactly $c+xu+yv$. The
independent polynomial checks verify all three weight identities and both
physical coordinate identities.

The closed Euclidean disk is convex, including the degenerate radius-zero
disk. Thus containment of all four vertices implies containment of every
actual closed-square point. The converse is immediate because every vertex
is an actual closed-square point. This proves the exact equivalence, rather
than only a sufficient corner test.

Each corner condition is the non-strict continuous inequality

\[
 \lVert p_{\epsilon,\eta}\rVert^2-R^2\le0.
\]

Their finite conjunction is closed in $K_0$. Points on sides and corners
are included: zero barycentric weights at those endpoints cause no problem.
No corner with zero later stress weight is omitted. No physical circle mask
or selected boundary atom enters the equivalence.

## 6. Original nonoverlap is closed without a separator selection

Consider a convergent sequence of feasible tuples and its limit in $K_0$.
If the limit violated the original pairwise condition, there would be two
distinct original labels $i,j$ and one actual point $p$ satisfying all
four strict local-coordinate inequalities.

Let $m$ be the maximum of the four absolute local coordinates at that same
point in the limit. Then $m<1/2$. Choose, for example,

\[
 \delta=\frac{1/2-m}{2}>0.
\]

Each of those four local absolute values is a continuous function of its
center and frame at the fixed point $p$. All four therefore differ from
their limit values by less than $\delta$ at sufficiently late sequence
indices. Their common upper bound is then

\[
 m+\delta=\frac{m+1/2}{2}<\frac12.
\]

The same physical point $p$ is consequently in both original open squares
at each such index. This contradicts feasibility of the sequence.

This proof is valid at every limiting contact configuration. Its strict
margin comes only from the hypothesized forbidden interior overlap; it does
not require an initially positive distance between the closed squares or
between a contact and a corner. It needs no moving intersection witness,
contact classification, chosen separating axis, continuous normal selection
or persistence of an active set. The source's nonoverlap argument is fully
independent of the old SAT formulation in the provenance manuscript.

In a finite-dimensional metric space this establishes the required
sequential closedness, hence closedness. Combining it with the closed corner
conditions proves $K$ is a nonempty closed subset of compact $K_0$.
Therefore $K$ is compact.

All original bodies survive. The coordinate product retains each original
label, and the limiting square at each label still has a unit frame and a
nonempty open interior. If two labels became the same geometric square,
their open interiors would coincide and violate the just-proved condition.
They may gain shared sides, new point contacts or additional physical circle
corners without leaving the feasible set. These are exactly the endpoints
allowed by the original definition.

## 7. Radius attainment is global over every original packing

The radius coordinate is continuous, so it attains a minimum $R_*$ on
nonempty compact $K$. The limiting coordinates reconstruct valid original
`UnitSquare` objects with their actual frame equations, and Sections 2--6
supply the original Packing predicate at that radius.

Globality requires comparison with packings outside the chosen compact
sublevel. Let any original packing of the same $n$ units have radius $R$
and any disk center. If $R\le R_0$, its exact origin translation belongs
to $K$, so $R\ge R_*$. If $R>R_0$, one already has
$R>R_0\ge R_*$. The boundary $R=R_0$ is included in the first case.
This exhausts every original feasible radius because all are nonnegative.
Thus the attained minimum is global, not merely a minimum within one graph,
frame pattern or local motion neighborhood.

The artificial ceiling $R_0$ serves only to produce compactness. No later
claim of globality depends on keeping that ceiling as an active constraint,
and this source introduces no multiplier associated with it. This avoids
silently changing an unrestricted optimization problem into a bounded
stationarity problem.

On the actual domain $0\le R_*\le R$, squaring preserves order:

\[
 R^2-R_*^2=(R-R_*)(R+R_*)\ge0.
\]

Consequently the same packing attains the global least squared radius. No
negative-radius branch or ambiguity of the squared disk definition remains.

## 8. Finite canonical refinement and its precise motion consequence

The fiber $K_*=\{z\in K:R(z)=R_*\}$ is compact and nonempty. For a
continuous real functional $f_1$, the extreme-value theorem supplies a
minimum on this fiber; its minimizer set is the inverse image of a closed
singleton inside $K_*$, hence compact and nonempty. Repeating this for the
prescribed finite ordered list gives the stated final nonempty set.

The resulting point is lexicographically minimizing. If another member of
$K_*$ first improved at coordinate $j$, agreement on earlier coordinates
would place it in the preceding minimizer fiber, contradicting the chosen
minimum of $f_j$ there. A list of length zero simply leaves $K_*$
unchanged. The proof asserts neither an infinite-stage intersection for
arbitrary selectors nor continuity of a chosen minimizer as parameters
vary, and it asserts no uniqueness.

For the actual proposed functional

\[
 \Phi=\sum_{i\in\operatorname{Fin}n}\lVert c_i\rVert^2,
\]

the sum is finite and continuous. The chosen tuple first minimizes the
original radius and then minimizes $\Phi$ among all original radius
minimizers after their exact origin translation. Every such minimizer has
radius $R_*\le R_0$, so all are already in $K_*$. No contact graph,
stressed subset, orientation restriction or selected normal is imposed
before this secondary minimization.

At that actual canonical packing, a competing configuration contradicts
secondary minimality if it keeps radius $R_*$, satisfies the original
Packing predicate for all $n$ labels, and strictly lowers the total
$\Phi$. It may change contact or stress information: preserving a previously
chosen certificate is unnecessary for this minimization contradiction.
However, every unchanged body and every original pairwise relation still
has to be included in the competitor's feasibility proof. A motion checked
only against a stressed subcomponent is not an original feasible competitor.

This is a useful precise entry interface for later motion arguments. It
does not supply any of those arguments' missing feasibility checks, and it
does not show that subsequent normal selections, uncrossing or thinning can
all be made compatible.

## 9. Empty families, small-n endpoints and the actual lower bound

For $n=0$, the empty family is feasible at radius zero and every original
radius is nonnegative. The minimum is exactly zero and $\Phi=0$. Every
argument above remains meaningful, including empty products, empty sums and
vacuous containment/nonoverlap quantifiers.

For $n\ge1$, direct expansion of the four actual vertices gives

\[
 \frac14\sum_{\epsilon,\eta}\lVert p_{\epsilon,\eta}\rVert^2
  =\lVert c_i\rVert^2+\frac12.
\]

Each term is at most $R^2$; hence
$R^2\ge\lVert c_i\rVert^2+1/2\ge1/2$ and
$R\ge1/\sqrt2>0$. The independent polynomial calculation verifies the
average before normalization as
$\lVert c_i\rVert^2+(C_i^2+S_i^2)/2$, so the displayed value uses exactly
the original frame equation and no directional convention.

At $R^2=1/2$, every center is zero. Each unit square contains the open disk
of radius $1/2$ about that common center: its local-coordinate squared norm
is the actual displacement squared norm, so each local absolute coordinate
is strictly below $1/2$ for every point of that disk. If $n\ge2$, two
labels then have a common open interior, contradicting the original
predicate. In fact the origin alone already gives the contradiction. Thus
for $n\ge2$ every feasible radius satisfies the strict squared lower bound
$R^2>1/2$. For $n=1$ the endpoint remains permitted.

This source supplies no stronger nine-unit lower window. A later use of the
accepted same-nine $R>2$ theorem must still use the same actual nine bodies.
Nothing here licenses applying a lower-n theorem to an artificial stressed
core while discarding other physical squares.

## 10. Conditional radius transfers and all equality quantifiers

For a proposed squared threshold $Q\ge0$, including the project's exact
$1105/256$, an original subcritical witness $R^2<Q$ gives the attained
radius/Phi minimizer with

\[
 0\le R_*\le R,\qquad R_*^2\le R^2<Q.
\]

This strict contradiction entry needs no independently known sharp upper
construction. The given counterexample itself is the compact-sublevel
witness. It retains all original units and their full allowed frame/contact
domain.

If a separate theorem excludes every such canonical subcritical minimum,
then an arbitrary original counterexample would generate one and contradict
that theorem. Equivalently, once $R_*^2\ge Q$ is actually proved, global
minimality and nonnegativity give $R^2\ge R_*^2\ge Q$ for every original
packing. The source correctly labels this as a conditional transfer and
never supplies the missing sharp geometric inequality by compactness.

If the universal lower bound is available and an actual original witness
has squared radius at most $Q$, both inequalities force its squared radius
and the attained optimum to equal $Q$. Nonnegativity then identifies the
least radius with $\sqrt Q$. This reasoning includes $Q=0$ whenever its
premises are consistent; no division by $R$ or $Q$ is used. It does not
assert an unverified upper construction.

After the universal lower bound is established, any particular original
packing with $R^2=Q$ is itself a global radius minimizer. It can therefore
be subjected to a necessary condition valid for every radius minimizer,
without replacing or moving its physical bodies. That conclusion does not
make it a secondary $\Phi$ minimizer.

Replacing such an equality packing by a different radius/Phi minimizer may
change unstressed units or other physical features. A strict
$\Phi$-decreasing motion excludes the chosen canonical minimizer only; its
conclusion cannot automatically classify all original equality packings.
The source makes this distinction explicitly. It preserves the original
open-and-closed congruence definition and claims no uniqueness of frames,
labels, circle center, stress weights, contact ownership or optimal model.

## 11. Exact old-source provenance and original gate coverage

The complete `SPARSE_MINIMIZER_STRESS.md` was read as stated by the author.
Its Section 1 already contains unrestricted compact attainment through a
finite union of closed SAT conditions. The present source supplies its own
full proof directly from the exact original predicate, independently of
that SAT statement, and adds the explicit finite continuous canonical
refinement and equality-transfer boundary.

The old source's later $2n+1$ translational sparsity result is not a premise
here. In particular its nineteen-term specialization is not smuggled into a
physical torque-stationary certificate. Nor does this proof select strict
point-contact normals, a unique positive component, a planar body graph or
application means. Those remain separate mathematical interfaces.

At the exact current checkpoint, the original index 2457 is
`{"id":"G4.2.a","checked":false}`. The complete current roadmap contains
exactly the original line:

> Start from the original nine-square Packing predicate and obtain a compact
> minimizer with no extra orientation/contact hypothesis.

The uniform finite-$n$ theorem applies at $n=9$ with precisely those
hypotheses and proves precisely that complete conclusion. The stronger
canonical refinement does not narrow the initial compactness domain: it is
chosen only after the entire original minimum family has been obtained.
Thus this is complete mathematical coverage of G4.2.a.

The roadmap and checkpoint were rehashed against the complete exact BBC
tree, and the independent record retains their full pins and the literal
original gate line. No renamed, split or invented gate is substituted. The
review proposes that this one original gate become eligible after separate
root adoption; it does not alter the checkpoint or roadmap itself.

The conditional implication relevant to G4.2.f is proved, but its missing
minimum lower-bound premise is not. This source does not close the literal
lower-window step G4.2.b, simultaneous selection G4.2.c, complete branch
exclusions G4.2.d, sharp minimum bound G4.2.e, the G4.2 parent, the equality
gates or the full G6.1 audit. It creates no certificate retirement.

## 12. Independent verdict and remaining boundary

No mathematical gap, domain loss, uncontrolled equality endpoint or mismatch
with the actual original definitions was found. The source is accepted
unchanged for every finite number of independently framed original unit
squares, with the exact stated translation, compactness, global minimum,
finite canonical refinement and conditional transfers. The entire original
G4.2.a is supplied at that scope.

The remaining global issues are substantive and separate: simultaneous
allowable normal choices, preservation through embedding/uncrossing and
thinning, and the still-open sharp geometric exclusions. This proof neither
assumes nor resolves them. Its canonical entry can be used when auditing
those interfaces, while its equality warning prevents exporting a
secondary-minimum exclusion beyond its proved domain.

All source and authoritative metadata bytes remain unchanged. This review
adds only its narrative report and exact record. It performs no actual
normal selection, deletion of physical units, force or mean replacement,
authoritative flag edit, Lean compilation, CI/workflow dispatch, remote
mutation or merge.
