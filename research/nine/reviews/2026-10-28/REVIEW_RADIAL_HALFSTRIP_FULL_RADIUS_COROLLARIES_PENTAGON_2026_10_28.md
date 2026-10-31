# Independent review of the full radial half-strip corollaries

Date: October 28, 2026 UTC. Reviewer: pentagon, independent of author house.

**Verdict: PASS for the entire half-strip theorem, the arbitrary actual radial-S contact corollary, the inner radial-normal exclusion, and the stated cross-contact obstruction.** All closed transverse endpoints, weak support equalities and the whole domain d>1/sqrt(2) are included. No repair is required.

## 1. Exact current sources

The complete new source read in full is RADIAL_HALFSTRIP_FULL_RADIUS_BOUNDARY_SUPPORT_COROLLARIES.md at SHA-256

    e8cb01fa67033056433ce210ae0c286700606533cae5db18fc641e8d568804f8.

Its only imported mathematical theorem is RADIAL_SIDE_POINT_FULL_RADIUS_FORCE_FREE_HALFPLANE.md at

    baeb2ab8556a773212073d4fbf10eda66efe06a567070f5dfcbd4de3f36625d3.

That entire base proof was freshly read and independently checked in REVIEW_RADIAL_SIDE_POINT_FULL_RADIUS_FORCE_FREE_HALFPLANE_PENTAGON_2026_10_28.md at

    34aca5b9c6ccfa269a7fb9a183f05dc1eb9509d75a7e0eb7c46225bfee9bc4fa.

The current extension does not change those base bytes. Its new geometric deductions are printed in full and checked below.

## 2. The convex comparison proves the entire closed half-strip

Fix d>1/sqrt(2), R^2=(d+1)^2+1/4 and an orthonormal frame n,f about the fixed origin. The actual unit E contains Q with Q.n>=d and t=Q.f in [-1/2,1/2]. Under the hypothesized low support min_E(z.n)<=d-1, the two comparison units are

    E_+=E+(1/2-t)f,
    E_-=E+(-1/2-t)f.

Their corresponding Q points lie on the two exact edges of the base theorem. Their n projections and minimum n projections are unchanged. The base theorem requires no initial containment, so it applies to both comparison units even if translating a contained original unit could otherwise put a corner outside the original disk. Its stronger conclusion itself puts all comparison points strictly inside that disk.

For every fixed original z, with lambda=t+1/2, the translation coefficient in

    lambda z_+ +(1-lambda)z_-

is lambda-1/2-t=0. Thus the claimed convex identity is exact. Convexity of the squared norm gives |z|^2<R^2. This remains strict when lambda is zero or one, because the selected comparison point already has strict norm.

These comparisons do not move the actual packing or its forces. They prove a one-square norm inequality using auxiliary geometric copies. There is no unproved disjointness premise for the copies and no force or mean is transferred to them.

Hence the stronger implication holds for every actual point in the full closed half-strip. For a physical boundary E, its actual point of norm R contradicts that implication, proving the strict whole-closed-unit bound

    min_E(z.n)>d-1.

The strict endpoint in d is exactly the base theorem's premise. Every R>=2 satisfies it, with no upper-radius restriction.

## 3. Every physical radial-S contact is a valid entry

For the actual radial S square

    V=[d,d+1]n+[-1/2,1/2]f,

any actual shared point Q belongs to the half-strip. This is true on the inner radial side, either tangent side, any vertex, and every endpoint or mean of a positive-length contact. Consequently every physical boundary neighbor containing that actual point obeys the same strict half-plane bound.

The statement is about physical boundary contact. It does not depend on the support of the positive circle coefficients, and either individual zero coefficient on V or E is retained. Neither unit has to be a leaf or a true two-force tip. No equation or degree at any square is reduced.

An unshareable outer circle corner causes no exception: if no second physical square can contain such a point, that subcase is simply empty. The half-strip implication remains valid.

## 4. The inner radial-normal exclusion has the correct strict sign

If the unchanged V-to-E normal is -n, the actual support point has n coordinate d and E lies entirely in n.z<=d. Its maximum n projection is exactly d because it contains that point.

Every unit square has width at least one in every unit direction: its width is the sum of the absolute own-axis components of that direction. Therefore

    min_E(z.n)=d-width_E(n)<=d-1.

This contradicts the strict half-strip conclusion. It includes width exactly one, an endpoint-valued original shared mean, and either support owner at E.

The source correctly limits this exclusion to the actual inner radial normal. An oblique normal at an inner corner may have a different supporting half-plane and is not excluded merely by naming the corner.

## 5. The whole-unit cross-contact obstruction is valid at equality

Let the actual F have unchanged minimum-m support point P, with m.n<=0 and P.n<=d-2.

If F owns m, its normal displacement from P has coefficient in [0,1] and contributes nonpositively to n. Its actual tangent interval has length one and contributes at most one in the n direction. This retains arbitrary side means and both mean endpoints.

If m strictly exposes a vertex, its two inward own axes have positive m components. They cannot both have positive n components, since their orthonormal expansion would then imply m.n>0. At most one axis contributes a positive n increment, and that increment is at most one.

These cases exhaust the actual unit support features; an axis-valued vertex endpoint is already in the owned-side case. Hence

    max_F(z.n)<=P.n+1<=d-1<min_E(z.n).

The strict separation excludes even a closed physical contact E intersect F. The weak cases m.n=0 and P.n=d-2 are fully included. No circle load, degree or normal-selection assumption at F has been introduced.

A graph caller must still establish the actual half-strip point, the actual support data of F and its required E-F contact. The source states this requirement explicitly.

## 6. Review conclusion and scope

The extension is a correct force-free strengthening from two side lines to the full closed half-strip. Its three physical corollaries follow at their stated entire domains, and all signs, equality cases and actual-point meanings check.

No whole original graph/load row or parent follows from these geometric statements alone. The manuscript properly makes no such closure claim and leaves every caller's remaining hypotheses intact.

The review used exact identities, convexity and elementary support geometry. No numerical pose, optimization, mesh, Lean compilation, CI, workflow, shared ledger edit, commit or remote write was performed.

