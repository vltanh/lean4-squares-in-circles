# A strictly positive inner corner cannot touch another loaded square

This is a local hand lemma for a circle-loaded square. It gives a restriction
on loaded-ring contacts, not an exclusion of a seven-square ring.

Use the square's own orthonormal axes, with the disk center still at the
origin. Suppose the square is

```
C = P + [0,1]^2,       P=(x,y),       x,y>=0,
R^2 = (x+1)^2+(y+1)^2.
```

Thus its upper-right corner lies on the containing circle, its center has
coordinates `(x+1/2,y+1/2)`, and P is its opposite corner. Let K be any
other closed unit square with interior disjoint from C and containing P.
Put `M=max(x,y)` and `m=min(x,y)`.

**Lemma.** Every vertex z of K satisfies

```
|z|^2 <= |P|^2 + max(1+2M, 2+2|x-y|).                  (1)
```

Consequently, if x,y>0, every vertex of K lies strictly inside the radius-R
disk. If exactly one of x,y is zero and the other is positive, K can have a
vertex on that circle only if it is the axis-parallel square immediately
across the corresponding side of C:

```
y=0<x:       K=P+[0,1]x[-1,0],
x=0<y:       K=P+[-1,0]x[0,1].                         (2)
```

In particular, the exceptional neighbor in (2) has an actual shared side
with C. A supporting normal strictly inside C's corner normal cone cannot
serve that contact.

## 1. Vertex contact

Suppose P is a vertex of K. The two incident unit edges e,f form a right
angle. The open quadrant between them cannot intersect the open first
quadrant: such an intersection would give points of both square interiors
arbitrarily near P.

Each of e and f therefore has at least one nonpositive coordinate. It
follows that

```
P dot e <= M,       P dot f <= M.
```

For the opposite vertex, its offset e+f has length sqrt(2), and its angle
lies in the closed interval from 3pi/4 to 7pi/4. The maximum of its scalar
product with the first-quadrant vector P occurs at an endpoint of that
interval; the only interior stationary point is a minimum. Hence

```
P dot(e+f) <= max(y-x,x-y)=|x-y|.
```

Expanding the squared norms of P+e, P+f, and P+e+f proves (1). The vertex
P itself satisfies the same bound.

## 2. Side-interior contact

Suppose P lies in the relative interior of a side of K. Let n be the
inward unit normal of K at P. Separation from C forces

```
n=(-c,-s),        c,s>=0,        c^2+s^2=1.
```

Take tangent v=(s,-c). Every vertex of K is of the form

```
P+t v     or     P+n+t v,        -1<=t<=1.
```

The actual tangential interval has length one; enlarging it to [-1,1]
only makes the estimates weaker. The squared norm is a convex quadratic
in t, so it suffices to estimate t=1 and t=-1.

For the near-side endpoints, `|v|=1` and `|P dot v|<=M`. For the far-side
endpoints, `|n+v|^2=|n-v|^2=2`, while

```
P dot(n+v) = (x-y)s-(x+y)c <= |x-y|,
P dot(n-v) = (y-x)c-(x+y)s <= |x-y|.
```

These inequalities prove (1) for side-interior contact as well. The point
P cannot lie in K's interior, since then K would meet C's interior near P.
The two cases exhaust all possibilities.

## 3. Circle clearance and boundary equality

The squared containing radius is

```
R^2=|P|^2+2+2(x+y).
```

Its differences from the two bounds in (1) are respectively

```
1+2m,             4m.                                  (3)
```

Both are strictly positive when m>0, proving circle clearance.

Now suppose y=0<x. The incident-edge bound remains strictly below R^2.
For a vertex of K to lie on the circle, its offset from P must consequently
be a diagonal of length sqrt(2) attaining scalar product x. In the allowed
angular interval of Section 1, the unique such offset is (1,-1).
The incident unit edges are then (1,0) and (0,-1), giving the first square
in (2). In the side-contact estimate, attaining the same diagonal length
would require |t|=1, so P would have to be an endpoint of its actual unit
side. Thus a relative-interior side contact cannot add another equality
case. Exchanging x and y proves the other case in (2).

The shared side in the first case has normal (0,-1), on the boundary of
C's outward corner cone; the second case is analogous. This proves the
last assertion.

## 4. Consequences for the loaded ring

In a circle-loaded square's own axes, reflect signs so its center is
`(a,b)` with a,b>=0. If a,b>1/2, no other circle-loaded square can touch
its opposite corner `(a-1/2,b-1/2)`. At a=1/2 or b=1/2, only the stated
axis-parallel shared-side exception is possible when the other coordinate
is larger than 1/2.

In the n=10 radius range `R<=3/sqrt(2)`, one also has
`min(a,b)<=1`. Thus, when a,b>=1/2, `m=min(a,b)-1/2<=1/2`, and (1)--(3)
give the quantitative estimate

```
max_(z vertex of K) |z|^2 <= R^2-4(min(a,b)-1/2).         (4)
```

Here a "loaded" square has positive circle load in the physical stress
certificate and hence has a circle vertex. Therefore the lemma applies
to every opposite-corner contact between two bodies of an entirely loaded
component. It does not show that every body has such a contact: contacts
on the other two noncircle corners and side interiors remain possible.

## 5. Positive radial concurrence does not force an opposite-corner contact

The following exact local configuration explains a limit of the lemma.
Set

```
a=39/40,
d=(sqrt(6521)-20)/40,
R^2=3481/800.
```

Take three axis-parallel unit squares with centers

```
C: (a,a),       T: (-1/40,d),       U: (d,-1/40).
```

All three fit in the radius-R disk and have a unique circle vertex.
The farthest vertex of C is `(59/40,59/40)`. Those of T and U are
`(-21/40,sqrt(6521)/40)` and its coordinate exchange. Their squared
norms all equal `6962/1600=3481/800`.
The radius lies strictly in the working window: its square exceeds
`(79/40)^2=6241/1600` and is less than `9/2=7200/1600`.

Since `80<sqrt(6521)<81`,

```
3/2<d<61/40.
```

C and T meet along part of C's left edge `x=19/40`; C and U meet along
part of its bottom edge `y=19/40`. T and U have separated horizontal
projections because `d-1/2>1>19/40`. Their interiors are all disjoint.
The points

```
P=(19/40,5/4),        Q=(5/4,19/40)
```

lie in the relative interiors of the two shared segments: `d-1/2<41/40`
while the corresponding upper bound from C is `59/40`.

Apply to C the two inward contact forces `(59/40,0)` at P and `(0,59/40)`
at Q, and the inward circle force `(-59/40,-59/40)` at its circle vertex.
They sum to zero. The two contact torques about the origin cancel, and
the circle torque is zero. Both contact-force lines intersect at
`(5/4,5/4)`, strictly inside C and on the positive ray of its circle-load
resultant. Yet neither contact uses C's opposite corner `(19/40,19/40)`,
and both coordinates of C's center exceed 1/2.

This is a counterexample only to a **local** inference from C's force,
torque, positive radial concurrence, and loaded neighbors. The other two
bodies have not been supplied with balanced stresses, so no full positive
component or ten-square packing is asserted. A global ring argument may
still restrict this local pattern; that additional argument is necessary.
