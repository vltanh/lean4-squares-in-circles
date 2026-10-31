# Generic point-contact normals force a shared-side escape at a loaded VV incidence

**Status:** hand selection theorem; two independent full mathematical
reviews passed on 2026-10-29, including nonzero-polynomial selection,
all fixed-point candidates, and the shared-segment interior escape.

This selects a new physical stress at a fixed unrestricted minimizing
packing, before its positive components are classified. It strengthens
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md)
and retains all its strict, nonradial and nondiagonal normal exclusions.
It does not modify an arbitrary previously chosen positive graph.

**Theorem.** One may select the physical stress so that, in every entirely
loaded positive seven-ring, each endpoint body of a positive VV pair with
a unique geometric circle vertex has its other positive pair on a
positive-length shared side. The aggregate application point of that
other pair lies in the relative interior of the shared segment.

Consequently such a unique-circle endpoint is a mixed body. After the
incident mixed exclusion, its only local rows are U4,U5,U6,U7. Unique-circle
rows U8,U9,U10 cannot be incident to a positive VV pair in this selection.
No such conclusion is made for a radial-side endpoint, whose circle-load
resultant ray may vary with its load split.

## 1. A necessary concurrence polynomial

Fix a body with unique geometric circle vertex w. Suppose two nonzero
contact forces with directions n_e,n_f act at fixed points P_e,P_f. The
circle resultant is a positive multiple of w. Its torque about the origin
is zero. Force and torque equilibrium imply that the three columns

```text
(n_e.x, n_e.y, P_e cross n_e),
(n_f.x, n_f.y, P_f cross n_f),
(w.x,   w.y,   0)
```

are linearly dependent. Therefore the polynomial

```text
D(n_e,n_f)
 =(P_e cross n_e)*(w cross n_f)
  -(P_f cross n_f)*(w cross n_e)                      (1)
```

vanishes. Directions may be oriented either way; changing their signs
only multiplies (1) by a nonzero scalar and does not change its zero set.
The coefficients are fixed by the minimizing configuration.

Suppose P_e does not belong to the line spanned by w. If n_f is fixed,
write (1) as

```text
D(n_e,n_f)
 = [(w cross n_f)*P_e-(P_f cross n_f)*w] cross n_e.    (2)
```

If `w cross n_f!=0`, the bracket is nonzero because P_e is not collinear
with w. If `w cross n_f=0` but `P_f cross n_f!=0`, it is also nonzero.
The only identically zero case is

```text
n_f parallel w,       P_f cross n_f=0.                (3)
```

A contact in (3) has zero origin torque, so it cannot be a positive
contact of the loaded ring, whose common torque is strictly positive.
It therefore needs no polynomial exclusion.

If n_f is itself a freely chosen point-only VV normal, choose any
admissible value not parallel to w; its admissible interval is open.
For that value (2) is a nonzero linear polynomial in n_e. Thus (1) is
not identically zero as a polynomial in the two independent normal
variables. This proves nontriviality, not merely nontriviality for a
sampled direction.

## 2. All exclusions can be imposed simultaneously

At each geometric point-only vertex/vertex contact e, use a smaller
nonempty open interval of admissible strict common normal directions.
Represent its directions by nonzero vectors

```text
n_e(t_e)=a_e+t_e*b_e,       t_e in I_e,
```

where a_e,b_e are linearly independent and I_e is an open real interval.
Such an affine chart exists on any sufficiently small direction interval;
normalization to unit length is unnecessary for the zero-set conditions.
Distinct point contacts have independent variables.

Consider every geometric circle-contact body with a unique circle vertex
w, every incident point-only VV contact e with P_e not collinear with w,
and every other possible incident pair f of the following forms:

* a point contact, using its single geometric application point;
* a positive-length shared-side contact, using either one of its two
  overlap endpoints as a possible aggregate application point.

There are finitely many such choices. A point f has either its fixed
side normal or its independently chosen VV normal. A shared-side endpoint
has the fixed common side normal. Skip the harmless zero-torque case (3).
For every remaining choice, Section 1 gives a nonzero polynomial in the
parameters t_e,t_f (or just t_e). The affine charts do not make a nonzero
linear functional of a direction vanish identically, because a_e,b_e are
linearly independent. The same observation after fixing an admissible
n_f proves the two-variable claim.

Include also the finitely many nonzero linear polynomials forbidding the
radial and square-diagonal directions from the earlier normal selection.
The product of all these polynomials is nonzero. A nonzero real polynomial
cannot vanish on a nonempty open box: this follows by induction on the
number of variables from the fact that a nonzero univariate polynomial
has finitely many roots. Hence there is a choice of all the t_e in the
product of their open intervals at which the product does not vanish.
This simultaneously imposes every stated exclusion.

Use these chosen strict normals in the local smooth constraints and
construct the physical stress exactly as in Sections 2--3 of
[GENERIC_CONTACT_NORMAL_SELECTION.md](GENERIC_CONTACT_NORMAL_SELECTION.md).
Its qualification and normalized conic-multiplier argument hold for every
choice in the open admissible intervals. Thus they remain valid for this
joint selection. Shared-side endpoint forces are aggregated afterward
by their weighted-average physical application point.

No positive graph, degree, circle-load support, or stress weight was
prescribed when choosing the normals. The finite list included all
geometric candidates that might later become the two positive contacts
of a loaded ring body.

## 3. A strict vertex contact of a unique loaded ring body is off its load ray

Now inspect an entirely loaded positive seven-ring of the selected stress.
Let a body have unique circle vertex w. Use own coordinates

```text
w=(X,Y),       X,Y>1/2,       X^2+Y^2>=6241/1600.
```

Its strict V contact cannot be at w: two packed squares cannot share a
point of the containing circle. At an adjacent corner, collinearity with
w would force X=0 or Y=0, contrary to the coordinate signs. At the
opposite corner `(X-1,Y-1)`, collinearity would force X=Y. Then

```text
X=Y>=sqrt(6241/3200)>1.
```

Both opposite-corner coordinates would be strictly positive. The
[inner-corner clearance lemma](LOADED_INNER_CORNER_CLEARANCE.md) makes
any physical neighbor there strictly circle-clear, contrary to the
neighbor being loaded. Thus every strict V contact of this unique loaded
body is off the line spanned by its circle-load vector w.

## 4. The shared-side interior is the only remaining alternative

Suppose one positive pair e of this body is VV. Its point is one of the
free-normal contacts used in Section 2, and Section 3 verifies the
noncollinearity hypothesis. The loaded ring body has exactly one other
positive pair f.

If f were a point contact, its normal and geometric application point
were included in Section 2. In the zero-torque exception (3) it could not
be a positive ring edge. Otherwise (1) was selected to be nonzero, whereas
force and torque equilibrium require it to vanish. Both alternatives
are impossible. Thus f has a positive-length shared side.

The same argument applied to either overlap endpoint excludes an
aggregate application at that endpoint. Aggregation always places it in
the closed overlap segment, so it must lie in the relative interior.
Its normal exposes an edge of the body, while e exposes a strict vertex.
Hence the body is mixed. The unique-circle support alphabet leaves
U2,U3,U4,U5,U6,U7; the separate incident mixed theorem removes U2/U3.
This proves the stated restriction.

The open shared-segment interior is an essential escape in the argument.
Its aggregate application point varies with the two endpoint weights;
there is a continuum of such points, and no finite polynomial-avoidance
claim has been made for all of them. Likewise a radial-side body's
weighted circle mean varies continuously, so its load ray was deliberately
excluded from this theorem.
