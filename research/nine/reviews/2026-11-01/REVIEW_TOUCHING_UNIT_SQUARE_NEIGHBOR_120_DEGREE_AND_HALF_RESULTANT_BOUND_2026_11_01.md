# Independent review: the sharp 120-degree touching-neighbor bound

Date: November 1, 2026 UTC. Reviewer: four_chain continuation.

**Decision: PASS the complete radius-free, force-free theorem, its
weighted consequence and its exact sharpness construction.**

The frozen target is
`TOUCHING_UNIT_SQUARE_NEIGHBORS_HAVE_AT_MOST_120_DEGREE_SUPPORT_NORMAL_SEPARATION_2026_11_01.md`,
SHA-256 `13639d350b816b98aa91fd824a6d810535c21a32e3e96d5f7e7333a75b016c1f`.
I read and independently checked the whole manuscript. The theorem
requires no previous geometric kernel, radius bound, equilibrium,
finite selector or numerical verification. I had proposed the sharp
constant and equality example before construction; this review separately
checks the author's complete all-support proof rather than claiming
independent discovery of that conjecture or example.

## 1. Support reach, with all application locations

At a minimum support vertex p, write the square as
p+[0,1]u+[0,1]v with n.u,n.v >= 0. If n_1 > 0, both side directions
cannot have negative first coordinate because n is their nonnegative
coordinate combination. For any negative first component, n.w >= 0
gives n_1 |w_1| <= |n_2| |w_2|. Squaring with both unit lengths yields
|w_1| <= |n_2|. At most one negative displacement therefore occurs,
which proves the bound on every actual point of the square.

For a relative-interior support-side mean the normal is the inward
own-side axis. Its normal displacement has nonnegative first component;
the complete possible tangential displacement has negative component
of magnitude at most |n_2|. Side endpoints are already covered by the
vertex proof. Reflection and exchange of axes preserve the asserted
bounds. In particular no application has been moved to a favorable
side endpoint.

## 2. Complete negative-dot-product cover

A negative dot product requires opposite strict signs in at least one
coordinate. After the allowed symmetries, n_A=(a,b), n_B=(-c,d) with
a,c > 0. Their actual U applications have first coordinates 1/2 and
-1/2, including side means. Applying the reach bounds to the same
actual point in A intersect B gives |b|+|d| >= 1.

This already rules out b=0 or d=0, because a,c > 0 imply the other
absolute component is strictly less than one. If b and d had opposite
signs, the actual U applications would be opposite vertices. The
horizontal and vertical reach bounds then put that same A/B contact
point strictly inside U: all of a,c,|b|,|d| lie strictly between zero
and one. A closed unit square with disjoint open interior cannot contain
a point inside open U, since its own interior points approximate every
one of its closed points. Thus this alternative is impossible.

The remaining components b,d have the same sign. Their absolute sum
is at least one, so |n_A+n_B| >= 1 and n_A.n_B >= -1/2. The original
nonnegative-dot-product branch was immediate. This exhausts every
actual support owner, side mean and normal-cone endpoint without a
strict-normal selection premise.

## 3. Weighted inequality and equality construction

The exact identity

    a^2+b^2-ab = (a+b)^2/4 + 3(a-b)^2/4

gives both the half-resultant bound and the stated reserve for unequal
positive magnitudes. A full unloaded three-force star transfers that
resultant magnitude to its third force exactly. At higher degree the
manuscript correctly asserts the bound only for the combined resultant
of every remaining force.

In the printed equality example, the side vectors are orthonormal.
Every interior point of A has y > 1/2 and x > 0; the reflected B has
y > 1/2 and x < 0. Thus all three open interiors are disjoint. Their
claimed U contacts are their base corners, and the A/B common vertex
is (0,1/2+sqrt(3)/2). Both chosen normals genuinely maximize on U and
minimize on the respective neighbor. Their dot product is -1/2 and
their equal-weight sum has norm one. This proves sharpness at the
declared force-free scope. The source explicitly retains the distinction
between these geometric normal endpoints and a selected full physical
stress, so no selected-certificate counterexample is claimed.

The older weaker bound and its conclusions remain unchanged. No script
has checked a mathematical inequality or geometric case in this review;
only document identity was hashed. No Lean, build, CI, frozen-source
edit, ledger change or remote mutation was performed.
