# Full independent review: nonzero triangle and a closed-origin outside unit

Date: October 27, 2026.
Reviewer: rooted_blocks.

**Verdict: ACCEPT the complete uniform theorem and its stated block consequence.**

Reviewed source:
`GLOBAL_CLOSURE_NONZERO_TRIANGLE_CLOSED_ORIGIN_UNIT_EXCLUSION.md`

Frozen SHA-256:
`fb392c3d77524fe23eaca41f37975ba9230e7d5262e7bdd7f04f9384bfec48d2`.

I read all six sections and independently checked the new local
active-half-plane lemma, the nearby-interior-point homotopies, every
parallel and zero-proper-length endpoint, the final actual-area argument,
and the complete several-block conclusion. The imported noncollinearity,
positive concurrence and positive-ray statements have their precise
full-external-system scope. No load is divided or suppressed.

## 1. The new local hull lemma resolves the boundary-origin issue

If T contains O in its open interior, a distinct full-dimensional E
with O in its closure already overlaps T. Thus the nontrivial cases
are strict avoidance or origin-boundary containment of T.

In the strict-avoidance case, the positive actual ray point D=sF in T
makes the separating functional positive on F, hence on q=tF. The
compact hull conv(T,q) has positive distance from O, as stated.

At an origin-side or origin-vertex position, write all four actual
own-side inequalities with nonnegative offsets. Every active offset
is zero. Since q is a positive scalar multiple of the actual point D,
q satisfies each active inequality, including its equality case. So
does the entire convex hull. Every inactive face has a strictly
positive origin margin. A sufficiently small ball automatically
satisfies those remaining inequalities. Thus the hull is locally
contained in the original square, exactly as claimed.

This argument does not require D to be interior, q to be inside T,
or an acute angle between the external ray and an active side. It
also covers q lying far beyond an inactive face. The fixed small-ball
statement is enough because int E avoids every closed triangle unit.

## 2. Three nonparallel pairs retain the correct winding point

The unchanged proper-port relations put every edge application on
the segment between the two genuine concurrences. A zero sum of the
proper lengths would equate nonzero points on independent resultant
lines, impossible. Hence the force-concurrence triangle is nondegenerate,
and F_1+F_2+F_3=0 with all positive radial factors puts O strictly inside it.

Choose an interior point z of the actual E in a ball smaller than both
this interior radius and all local hull radii. Such z exists for a
closed-origin unit even at a vertex occurrence. Each square-chord
replacement stays in its corresponding hull and avoids z, by the new
local lemma and physical interior disjointness. The final force triangle
surrounds z, so the original contact loop has the same nonzero winding.

No winding at O is needed if O itself is on an actual contact image.
No claim that the homotopy avoids all of E is made or required.

## 3. The parallel-body correction remains uniformly away from O

There is at most one parallel pair. Its actual positive weighted
mean equation and nonzero common cycle moment give two nonzero,
opposite transverse port heights. The other two concurrences have
those same respective heights by properness.

The actual positive-ray point D of the parallel body lies strictly
on the positive axis. Each correction triangle D,p_i,q_i has strictly
one transverse sign except at D. It is compact and avoids O, even
when p_i=q_i. It therefore has a positive distance from O. Choosing
z closer to O than both distances makes both correction homotopies
legitimate, while the actual parallel-body chord replacement is wholly
inside its own square and avoids int E globally.

The resulting triangle D,q_I,q_J again has O strictly inside by
the exact full-resultant sum. This verifies the entire parallel
alternative without a fictitious concurrence or midpoint reset.

## 4. The final contradiction uses the actual contact triangle

The original contact loop's boundary lies in the actual three closed
units and avoids int E. Its nonzero winding at z is constant over
the connected int E. A coincident or collinear contact triangle has
zero winding and is already excluded. Otherwise the whole unit open
interior is inside the actual bounded triangle.

Its sides are square chords of length at most sqrt(2). The maximum
altitude over a longest side ell, with both other sides at most ell,
is sqrt(3)*ell/2. Thus its area is at most sqrt(3)/2<1, contradicting
the inclusion of int E. The source never substitutes a perturbed
graph area or a hull area for that actual contact area.

## 5. The several-block alternatives are exhaustive at their stated scope

The accepted routing theorem supplies at least one actual closed-origin
unit whenever two distinct triangular blocks exist. A nonzero-moment
block now forces every such unit to be one of its three vertices.
A zero-moment block has two distinct actual closed-origin units, by
its two nonparallel concurrences and proper mutual port at O. Since
distinct blocks share at most one vertex, zero and nonzero moment
blocks cannot coexist.

If all moments are nonzero, any two vertex-disjoint blocks are
impossible. Two blocks sharing H have intersection exactly {H},
so H is the unique actual closed-origin unit and belongs to every
triangular block. This uniqueness includes all other actual packing
units, not only positive-component vertices. The all-zero alternative
is retained explicitly. The theorem does not turn closed containment
at H into origin-interiority or remove any additional bridge forces.

The needed zero-external-moment condition is inherited from whole
original block-cut branches; no arbitrary triangular face in a larger
block is silently substituted. All complete source joins pass.

No correction was required. No original graph label, mean, force,
selected normal or shared ledger is changed by this review, and no
Lean compilation or CI was used.
