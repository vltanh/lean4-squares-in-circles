# The full radial half-strip is a uniform boundary-neighbor barrier

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed hand corollaries of the accepted full-radius force-free theorem, submitted for root and separate review.** The original source is kept unchanged. The convex extension includes every actual point of a radial S square, not only its two tangent sides.

## 1. Complete half-strip theorem

Let

    d>1/sqrt(2), R^2=(d+1)^2+1/4,

and let n,f be an orthonormal frame about the unchanged circle origin. Let E be any closed unit square containing a point Q with

    Q.n>=d, |Q.f|<=1/2.                            (1)

If E contains any point of n projection at most d-1, then

    |z|<R for every z in E.                        (2)

Thus every actual contained physical boundary unit E meeting the entire closed half-strip in (1) satisfies

    z.n>d-1 for every z in E.                      (3)

No initial containment is needed for the stronger implication (1)--(2). There is no force, degree, owner, normal-selection, physical circle-mask, weight or other-unit premise.

All R>=2 satisfy the strict d threshold, as proved in the accepted base theorem. There is no upper-radius restriction.

## 2. Convex extension from the two actual strip edges

The accepted base is

RADIAL_SIDE_POINT_FULL_RADIUS_FORCE_FREE_HALFPLANE.md

at SHA-256

baeb2ab8556a773212073d4fbf10eda66efe06a567070f5dfcbd4de3f36625d3.

It proves (2) when Q.f=1/2 or Q.f=-1/2, without requiring the comparison square to be initially contained.

Put t=Q.f, so -1/2<=t<=1/2. Under the hypothesized violation min_E(z.n)<=d-1, consider only for geometric comparison the two translations

    E_+=E+(1/2-t)f,
    E_-=E+(-1/2-t)f.

Their corresponding points Q_+,Q_- have n coordinate Q.n>=d and f coordinates +1/2,-1/2. The minimum n projection of each translated unit is unchanged. The base theorem therefore puts every point of each comparison unit strictly inside D_R.

For any original z in E, let

    z_+=z+(1/2-t)f,
    z_-=z+(-1/2-t)f,
    lambda=t+1/2 in [0,1].

The exact identity is

    z=lambda*z_++(1-lambda)*z_-.

Convexity of the squared norm gives

    |z|^2
      <=lambda*|z_+|^2+(1-lambda)*|z_-|^2
      <R^2.

The strict conclusion includes lambda=0 or lambda=1 because the corresponding comparison point is already strictly inside. This proves (2) for the entire closed strip width.

The comparison translations are used only to prove a one-square norm inequality. They carry no forces, are not inserted into the packing and impose no mutual-disjointness assumption. Every actual square, application and original equation remains unchanged.

If E is an actual boundary unit, its actual point of norm R contradicts (2). This proves the whole closed-unit separation (3).

## 3. Every actual radial-S contact point is covered

Let the unchanged actual radial S square be

    V=[d,d+1]n+[-1/2,1/2]f.

Suppose an actual physical boundary unit E touches V at any actual point Q. Then Q belongs to E and automatically satisfies (1). Therefore

    min_E(z.n)>d-1.                                (4)

This includes points on either tangent side, on the inner or outer radial side, at a vertex, and every actual common mean or endpoint-valued mean on a shared contact. The proof uses the whole physical square V only to verify Q's coordinates. It makes no assumption about its two individual circle weights, which may include a zero coefficient.

A caller need not declare V to be a leaf or delete any of its other original forces. E may have any true degree and full circle/force system.

## 4. A radial inner-side normal cannot lead to a boundary unit

Retain the actual V and E of Section 3. Suppose their original V-to-E support normal is the inner radial side normal -n. The unchanged actual contact point then has n projection d, and the whole actual E lies in n.z<=d.

Every unit square has n width at least one. Since its maximum n projection is exactly d at that original contact,

    min_E(z.n)
      =d-width_E(n)
      <=d-1.

This contradicts (4).

Consequently an actual boundary neighbor cannot occur through that radial inner-side normal, for any original contact point or side mean. Positive shared contacts, side endpoints, either owner at E and every E frame are included. This is a force-free support exclusion; no two-force or proper-concurrence premise is used.

The statement concerns that actual normal and supporting half-plane. It does not exclude every oblique contact at an inner corner, whose original separator may point partly along f.

## 5. A complete reusable cross-contact obstruction

Let E,Q satisfy the boundary hypotheses of Section 1. Let F be another actual unit, with an unchanged actual minimum-m support point P, where m,n are unit vectors and

    m.n<=0, P.n<=d-2.                              (5)

The complete elementary unit-support estimate is

    max_F(z.n)<=P.n+1.

For an m-owned side, use the actual inward normal displacement and the unchanged tangent interval of length one. The normal displacement contributes nonpositively to n and the tangent part contributes at most one. Every original mean endpoint is included.

If m strictly exposes an actual vertex, both inward orthonormal side axes have positive m components. They cannot both have positive n components, since that would force m.n>0. At most one contributes positively to n, by at most its unit length one. These cases exhaust all support features.

Together with (3),(5),

    max_F(z.n)<=d-1<min_E(z.n).                    (6)

Hence the two whole closed units cannot physically touch. The weak equalities m.n=0 and P.n=d-2 are included, as are all original degrees, loads, support owners and means.

A graph caller must still prove its actual Q, P, n, m and its required physical E--F contact. Merely naming a radial S unit supplies no unproved graph join.

## 6. Exact proof and bookkeeping limits

The only imported mathematical input is the complete base theorem baeb2ab8556a773212073d4fbf10eda66efe06a567070f5dfcbd4de3f36625d3. Its separate independent full review is

REVIEW_RADIAL_SIDE_POINT_FULL_RADIUS_FORCE_FREE_HALFPLANE_PENTAGON_2026_10_28.md

at SHA-256

34aca5b9c6ccfa269a7fb9a183f05dc1eb9509d75a7e0eb7c46225bfee9bc4fa.

Sections 2,4,5 print their complete convexity and support deductions. The original base source and its exact accepted bytes are unchanged.

These are uniform geometric corollaries for the entire stated radius range. They do not supply a full original D02, pentagon, house or coarse-cell closure. All actual physical units and complete original equations remain, with no selected-normal change.

No sampled pose, numerical optimization, orientation mesh, new computational certificate, Lean compilation, CI, workflow, ledger edit or remote action is used.

