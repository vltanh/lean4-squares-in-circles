# A finite support table for any degree-two loaded VV body

**Status:** reviewed exact hand theorem; root and independent full
mathematical reviews passed (2026-10-31). This is a universal local restriction for the jointly
selected certificate, including its minimum-active representative after
[GENERIC_CONSOLIDATION_COMPATIBILITY.md](GENERIC_CONSOLIDATION_COMPATIBILITY.md).
It does not assume that the whole component is a simple cycle or that
the neighboring bodies are loaded. It closes no fixed family by itself.

Work in `79/40<=R<3/sqrt(2)`. Degree means the degree in the whole positive
body-pair graph. Let C be a degree-two loaded body with a unique geometric
circle vertex w. Suppose one of its two positive pairs e is a point-only
vertex/vertex (VV) contact, at P, with the selected normal n. Write Q and f
for the aggregate application point and normal of its other positive pair.
All normals below use the gradient convention, pointing from C toward
its neighbor; reversing a direction does not change any zero-set claim.

The following two rows exhaust the possibilities.

| Position of P | Necessary form of the other positive pair | Further consequence |
| --- | --- | --- |
| P is not on the line spanned by w | A positive-length shared side, with Q strictly inside the shared segment | The body has one strict vertex support and one side support |
| P is on the line spanned by w | Both positive applications coincide: Q=P | In suitable own axes, `C=[a,a+1]^2`, `P=(a,a)`, `w=(a+1,a+1)`, `a=R/sqrt(2)-1>0`; both neighbors are circle-clear and have center norm below one; the VV neighbor is an unloaded retained branch vertex |

In particular the second row cannot occur in a whole simple-cycle
component. Every unique-circle degree-two loaded body incident to a
positive VV pair in such a component satisfies the first row, regardless
of the component's number of loaded bodies.

## 1. The off-ray row follows from the selected concurrence factors

The two contact magnitudes mu,nu and the circle resultant coefficient
lambda are positive. Force and torque equilibrium about the disk center
give

```text
mu*n + nu*f + lambda*w = 0,
mu*(P cross n) + nu*(Q cross f) = 0.
```

Eliminating the three coefficients yields the necessary relation

```text
D=(P cross n)*(w cross f)-(Q cross f)*(w cross n)=0.  (1)
```

If P is off the line spanned by w, all fixed-point and shared-segment
endpoint candidates for the other pair were included in the finite
selection of
[LOADED_VV_GENERIC_RESTRICTION.md](LOADED_VV_GENERIC_RESTRICTION.md).
The only skipped factor has `f parallel w` and `Q cross f=0`. That
exception is impossible here without any ring-torque argument: nonradial
selection at the nonzero point P gives `P cross n!=0`, whereas the torque
equation would reduce to `mu*(P cross n)=0`.

Every other point-contact candidate and every endpoint candidate has
selected D nonzero, contrary to (1). Thus the other pair has a
positive-length shared side and its aggregate point is neither endpoint.
Aggregation puts Q in the closed shared segment, so Q lies in its relative
interior. This proves the first row for arbitrary neighboring bodies.

## 2. The on-ray contact is the positive inner corner

Choose own orthonormal axes, keeping the disk center as origin, so the
unique circle vertex is `w=(X,Y)` and

```text
C=[X-1,X] x [Y-1,Y],       X,Y>1/2,       X^2+Y^2=R^2.
```

P cannot be w: two interior-disjoint squares in the same disk cannot
share a point of its circle. Either adjacent corner is off the line
spanned by w, since collinearity would force X=0 or Y=0. At the opposite
corner `P=(X-1,Y-1)`, collinearity with w is equivalent to X=Y. Therefore
the on-ray case has exactly

```text
X=Y=a+1=R/sqrt(2),       P=(a,a),       0<a<1/2.     (2)
```

Here positivity follows already from `R>=79/40>sqrt(2)`. In particular
P is nonzero, is a positive scalar multiple of w, and is strictly inside
the open unit disk.

## 3. The other force must act at the same inner corner

Write P=t*w with t>0. The selected n is nonradial at P, so `w cross n!=0`.
Equation (1) becomes

```text
(w cross n)*((P-Q) cross f)=0.
```

Thus the other physical force line passes through P:

```text
(Q-P) cross f=0.                                    (3)
```

For the square in (2), the support condition and (3) leave only these
four geometric application possibilities:

| Q | Outward normal direction from C required by (3) | Outcome |
| --- | --- | --- |
| P | Any supporting direction compatible with the neighbor | Retained possibility |
| `(a+1,a)` | `(1,0)` | Impossible by the unit normal step below |
| `(a,a+1)` | `(0,1)` | Impossible by the reflected unit normal step |
| w | Parallel to `(1,1)` | Impossible because w lies on the containing circle |

To verify exhaustiveness without assuming the support feature, suppose
Q!=P and write `Q-P=(u,v)` with 0<=u,v<=1. The support inequality
`f dot(P-Q)<=0`, together with (3), makes Q-P a positive multiple of f.
Thus Q maximizes `(u,v) dot(x-P)` over C. Its attained value and the
square's support value give

```text
u^2+v^2=u+v.
```

Both u*(1-u) and v*(1-v) are nonnegative, so each is zero. Therefore
u,v belong to {0,1}, proving exactly the three Q!=P entries. This includes
aggregate application points of shared sides without any endpoint premise.

For completeness, if a unit square K contains a support point Q and its
inward supporting unit normal there is f, then `Q+f` belongs to K. If Q
is in a side interior this is the point directly across its unit width.
At a vertex, write f in the two incident inward unit edge directions:
its coefficients are nonnegative and at most one, so the same conclusion
holds. This also covers an edge endpoint with a side normal.

At `Q=(a+1,a)` with f=(1,0), the neighbor would therefore contain
`(a+2,a)`. But

```text
|(a+2,a)|^2 = 2*(a+1)^2+2 = R^2+2,
```

contradicting disk containment. The upper adjacent corner is identical
after exchanging coordinates. Hence Q=P, proving the second row's
coincident-application assertion.

## 4. Both neighbors are inner and the VV neighbor must branch

Every physical neighbor K containing P is strictly circle-clear by
[LOADED_INNER_CORNER_CLEARANCE.md](LOADED_INNER_CORNER_CLEARANCE.md),
because both coordinates of P are positive. Thus both positive neighbors
are unloaded. There is also a useful strict center bound.

If P is a vertex of K, let e_1,e_2 be its incident orthonormal unit edge
vectors. Their open sector avoids C's open first quadrant. The angular
argument of the inner-corner clearance lemma gives

```text
P dot (e_1+e_2) <= |a-a|=0.
```

The center c=P+(e_1+e_2)/2 consequently satisfies

```text
|c|^2 <= |P|^2+1/2 = 2*a^2+1/2 < 1.                (4)
```

If P is in a relative side interior, write the inward unit normal of K
as `(-u,-v)`, where u,v>=0 and u^2+v^2=1. For some |s|<1/2 its center is

```text
c=P+(-u,-v)/2+s*(v,-u).
```

Its offset has squared norm `1/4+s^2<=1/2`, and

```text
P dot (c-P)
 <= a*(-(u+v)/2+|u-v|/2) <= 0.
```

This proves (4) again. The vertex and side-interior cases exhaust K's
boundary, so both neighbors have center norm strictly below one.

The neighbor in the VV pair e cannot have whole positive degree two.
The reviewed two-force transmitter classification would make it S or D.
An S transmitter uses a side normal of its own square, contrary to the
strict VV selection at e; a D transmitter uses its own diagonal, contrary
to the diagonal-avoidance selection. It also cannot be an unloaded leaf,
by force balance. Hence it is an unloaded vertex of degree at least three,
which remains a branch vertex after suppression of degree-two bodies.

This proves the final column and the simple-cycle corollary. A two-circle-
vertex loaded body has a variable radial-side resultant and is outside
this table. Coincident on-ray contacts in a branching component remain
possible in this argument; no exclusion of that residual is claimed.
