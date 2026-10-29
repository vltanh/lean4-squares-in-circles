# Proper edge-vertex rings using only the inner boundary have no ten-square completion

**Status:** hand proof; two independent full mathematical reviews passed
on 2026-10-29, including the side-endpoint cut and the boundary orientation.

Use the entirely loaded physical seven-ring of a hypothetical strictly
subcritical ten-square packing. Its radius satisfies
`6241/1600<=R^2<9/2`; the estimates below allow the weaker upper bound
`R^2<=9/2`. The loaded-ring reduction puts all three remaining squares
in the central hole and gives their centers norm strictly below one.
Assume every ring body has a unique circle vertex,
every pair contact has one edge support and one strict vertex support,
and the local rows of
[SEVEN_RING_OWNERSHIP_ALPHABET.md](SEVEN_RING_OWNERSHIP_ALPHABET.md)
belong to

```text
U1: D -> L,       U6: D -> C,
U7: B -> L,       U10: B -> C.                        (1)
```

Thus the two contact points of each body lie on its two inner sides or
at the two noncircle vertices adjacent to its circle vertex. A support
edge may be contacted at an endpoint. Strict vertex support at the
opposite corner and radial-side circle bodies are not covered.

**Theorem.** No such ring can occur in a strictly subcritical ten-square
packing. Every inner square
would be contained in the centered disk of squared radius `83/50`, whereas
the established three-square minimum is `425/256>83/50`.

This includes all source/sink run schemes made only from (1), with
arbitrary force ratios and nonuniform frames. It does not exclude all
realizations of the 34 coarse schemes: other local rows or radial-side
bodies can still occur in those schemes.

## 1. Each contact is a local side/vertex spike

Let A_i denote the corner opposite body i's unique circle vertex.
For each pair contact P, temporarily direct the pair from its edge-support
body to its strict-vertex-support body. Reflect the drawing and reverse
the cyclic order if necessary, keeping this temporary direction S to V.
Because the rows are those in
(1), the local configuration can be written

```text
w=(X,-Y),       X,Y>1/2,
C=w+[-1,0]u+[0,1]v,       u=(1,0), v=(0,1),
A=w-u+v,
P=A+t u,       0<=t<=1,
u'=(cos d,sin d),       v'=(-sin d,cos d),
C'=P+[0,1]u'+[0,1]v',       w'=P+u',       B=P+v'.   (2)
```

Here A and B are the two opposite corners. The incoming force on C'
is a positive multiple of v. Since it strictly exposes the vertex P of
C', both coefficients of v in `(u',v')` are positive. Therefore
`0<d<pi/2`. No claim about the frame turn at C' or its other support is
needed for this local conclusion.

The equality `|w|=|w'|=R` and the unique-farthest-vertex signs exclude
`t=0`, by the endpoint calculation in Section 6 of
[SEVEN_RING_SIDE_SOURCE_CAP.md](SEVEN_RING_SIDE_SOURCE_CAP.md).
Thus the triangle `T=conv{A,P,B}` is nondegenerate, and

```text
(P-A) cross (B-A)=t cos d>0.                         (3)
```

Here the orientation bookkeeping can be checked directly in the alphabet's
positively oriented `(e_x,e_y)` frame. If the edge-support incidence is
outgoing `L`, take `(u,v)=(e_y,-e_x)`, a positive frame. The next body's
incoming strict vertex is `B`, and its frame is transformed in the same
way. If the edge-support incidence is incoming `D`, temporarily traverse
the pair backward and take `(u,v)=(e_x,-e_y)`, a negative frame. The
previous body's outgoing strict vertex is `C`, and its frame receives
that same reflection. Thus only the reversed traversal uses a reflection.
Returning to the original cyclic order reverses the triangle orientation
once more in that case. Therefore the triangle
`conv{A_i,p_i,A_(i+1)}` is counterclockwise in the original orientation
for every pair.

## 2. Which local cap theorem applies

If the edge-support body is U1, it has two adjacent inner edge supports.
The [side-source cap theorem](SEVEN_RING_SIDE_SOURCE_CAP.md) applies,
including any side endpoint, and gives squared cap radius below `83/50`.

Otherwise it is U6 or U7. In the temporary orientation of (2), its other
support is the strict vertex `w-u`, with inward unit normal
`n=(n_x,n_y)`, where both coefficients are positive. The physical neighbor
there contains `w-u-n` by the unit-normal-step lemma. Disk containment
therefore gives

```text
2(1+n_x)-2X(1+n_x)+2Y n_y<=0,
X-Y*n_y/(1+n_x)>=1,
X>1.                                                (4)
```

For this mixed body, t=1 is also impossible. Its other contact is the
adjacent vertex, and the same force/torque identity as in
[SEVEN_RING_ONE_CHIRALITY.md](SEVEN_RING_ONE_CHIRALITY.md) gives
`lambda*mu_out=mu_in*cos(delta)>0`, where `lambda=1-t` and
`0<delta<pi/2`. This is a local identity: it uses only the body's one
strict vertex normal and its edge normal, not the next body's outgoing
support type. Hence `t<1`.

Equations (2)--(4) are exactly the hypotheses of the reviewed chord and
radial cap bounds. They put the corresponding cap below squared radius
`33/20<83/50`.

Thus every proper pair contact in (1) has its diameter disk AB, restricted
to the inner half-plane through P,B, bounded by squared radius `83/50`.
The only remaining issue is to place inner-square vertices in that cap
when t=1; the next section handles this boundary contact explicitly.

## 3. The diameter-disk cut remains valid at t=1

When `0<t<1`, Section 5 of
[SEVEN_RING_SPIKE_REDUCTION.md](SEVEN_RING_SPIKE_REDUCTION.md) proves that
every vertex z of a square interior-disjoint from C,C' and lying in T
satisfies

```text
(A-z) dot (B-z)<=0.                                  (5)
```

Suppose now `t=1`, and let K be one of the inner squares. Its center has
norm strictly below one, by the loaded-ring theorem. We first show that
P cannot belong to K.

At P, C occupies the southwest quadrant, while C' occupies the sector
between u' and v'. The free sectors have angles `pi/2-d` and `pi/2+d`.
The smaller cannot contain the local interior sector of a square. The
larger has angle less than pi, so if K contains P, P must be a vertex
of K and its two incident unit edges have the form

```text
e=(sin beta,-cos beta), f=(cos beta,sin beta),
0<=beta<=d.
```

Its center would have first coordinate

```text
P_x+(sin beta+cos beta)/2 >= X+1/2>1,
```

because `P=A+u=(X,1-Y)` and `X>1/2`. This contradicts the inner-center
bound. Therefore `P` is not in K.

The proof of (5) now extends to t=1 with that exclusion. For clarity,
translate P to zero, so

```text
A=(-1,0), B=(-sin d,cos d), |A|=|B|=1,
A dot B=sin d in (0,1).
```

Assume the left side of (5) is positive. The ray from A through z
meets `[P,B]` at `rB`, where the ray computation gives
`0<=r<A dot B`. If r>0, then `|rB-A|^2=1+r^2-2r(A dot B)<1`.
If r=0, then z lies strictly between A and P because z is neither
A nor P, again giving `|z-A|<1`. The symmetric argument proves
`|z-B|<1`. Finally `|z-P|<1` by strict convexity of the unit disk,
since z belongs to T and is neither unit-norm endpoint A nor B.

Every point of T is consequently at distance strictly less than one
from z. Both unit edges of K from z leave T. Neither can cross the
two forbidden square sides AP and PB, and neither can leave through P,
which is not in K. Thus they must both point through the base AB.
The assumed positive scalar product says that this cone has angle less
than pi/2, contradicting the perpendicular edge directions. This proves
(5) also for t=1.

The whole triangle lies in the inner half-plane through P,B. Thus (5)
places every such inner-square vertex in the cap bounded in Section 2.

## 4. The inner boundary and the global radius bound

The two contacts of each body in (1) can be joined along its two inner
sides through A_i. These paths are simple and their endpoints are distinct.
Nonneighbor loaded bodies do not touch; a proper edge/strict-vertex pair
has only its one contact point in common. Hence the joined inner boundary
is a simple polygon. Replacing the center/contact ring by these paths
inside the loaded squares preserves its winding number around zero,
because loaded squares avoid the closed half-radius disk. The resulting
polygon still encloses the closed half-radius disk. Each inner square's
open inscribed half-radius disk meets that disk; its connected interior
cannot cross the polygon, whose segments belong to loaded bodies.
Consequently the polygon bounds the central free hole containing the
three inner squares.
This is precisely the boundary replacement used in the reviewed spike
reduction, now with the four explicitly listed inner-boundary rows.

Every contact triangle is counterclockwise by (3). As oriented chains,

```text
boundary(hole)
 =(A_0 A_1 ... A_6 A_0)+sum_i boundary(conv{A_i,p_i,A_(i+1)}).
```

The same winding-number argument as in Section 2 of the spike reduction
therefore puts every point of the hole outside `conv{A_i}` in one of
these contact triangles. All opposite corners have squared norm below
`36/25`, independently of the support pattern.

Let z be a vertex of an inner square. If z belongs to `conv{A_i}`, its
squared norm is below `36/25<83/50`. Otherwise Sections 2--3 put it in
a cap of squared radius below `83/50`. Thus every vertex of each of the
three inner squares belongs to the centered disk of squared radius
`83/50`, and convexity places each whole square in that disk.

The established three-square optimum is `425/256`, exceeding `83/50`
by `1/6400`. Three interior-disjoint unit squares cannot fit in the
smaller disk. This contradiction proves the theorem.

## 5. Consequence for the finite ownership classification

For proper SV/VS pair contacts, every source/sink scheme made only from
U1,U6,U7,U10 is excluded, not just either pure-chirality word. Therefore
any remaining proper-contact loaded ring must have either a radial-side
circle body or at least one of the opposite-corner rows

```text
U2,U3,U4,U5,U8,U9.
```

The theorem above does not itself treat those rows. The separate
[incident mixed exclusion](LOADED_INCIDENT_MIXED_EXCLUSION.md) now rules
out U2 and U3 in any entirely loaded ring, even when the pair supports
are SS or VV. Thus a still-possible proper-contact ring must contain
U4,U5,U8,U9 or a radial-side circle body. Rings with SS or VV pair
contacts remain outside the capacity theorem, subject to the same U2/U3
exclusion. No global C04 closure or unrestricted n=10 proof is claimed.
