# The origin lies strictly inside the loaded-ring force polygon

**Status:** exact hand proof with two independent full reviews. This strengthens
[SEVEN_RING_FORCE_CIRCULATION.md](SEVEN_RING_FORCE_CIRCULATION.md); it does
not classify nonuniform loaded rings or exclude their completion by three
inner squares.

Use the entirely loaded physical ring, the radius window
`79/40<=R<=3/sqrt(2)`, and the notation of that manuscript. Its force
polygon has vertices f_i, is strictly convex and counterclockwise, and

```
f_(i-1)-f_i=g_i,
p_i cross f_i=tau>0.
```

Here g_i is the positive sum of outward circle-load vectors on body i.
Write g_i=s_i m_i, with s_i>0 and m_i the corresponding weighted mean
of the loaded circle vertices. The original contact point p_i belongs
to bodies i and i+1; f_i points from i toward i+1.

**Theorem.** The origin lies in the strict interior of this force polygon.

## 1. The loaded body is strictly on the positive side of its load ray

The loaded center has norm greater than 5/4, and g_i makes an angle less
than pi/12 with that center ray. Every point x of the square is within
1/sqrt(2) of its center. Since cos(pi/12)>4/5,

```
g_i dot x / |g_i|
  >= |c_i| cos(angle(c_i,g_i)) - 1/sqrt(2)
  > 1 - 1/sqrt(2) > 0.                                  (1)
```

All these estimates were proved in the preceding ring manuscripts.

## 2. The origin cannot lie outside the force polygon

Suppose it does, and let z be the unique closest point of the closed
convex force polygon to the origin. There are two cases.

### 2.1. The nearest point is a vertex

If z=f_i, the nearest-point inequalities at its two neighbors give

```
f_i dot g_i >= 0,
f_i dot g_(i+1) <= 0.
```

Physical support at p_i, applied to the two weighted circle means, gives

```
f_i dot m_i <= f_i dot p_i <= f_i dot m_(i+1).
```

Because the means are positive multiples of the corresponding g vectors,
all three quantities in this chain must be zero. Hence
f_i dot g_i=f_i dot g_(i+1)=0. Both adjacent force-polygon vertices
lie on the line through f_i perpendicular to f_i. This contradicts its
strict convexity.

### 2.2. The nearest point is inside an edge

Write the edge as [f_(i-1),f_i], and abbreviate g=g_i. There is a
number 0<t<1 such that

```
z=(1-t)f_(i-1)+t f_i,
z dot g=0.
```

Since g=f_(i-1)-f_i, this implies

```
g dot f_(i-1)=t|g|²>0,
g dot f_i=-(1-t)|g|²<0.                                 (2)
```

The origin lies strictly to the right of this oriented edge: the polygon
is counterclockwise, while z is its closest point from outside. Thus

```
g cross f_(i-1)<0.
```

The two actual contact-force lines on body i therefore intersect at

```
X = [tau/(g cross f_(i-1))] g.                           (3)
```

Indeed the displayed point has cross product tau with both f_(i-1)
and f_i, so it lies on both lines. It is a negative multiple of g.
By (1), both original contact points have positive projection on g.
Equations (2)--(3) consequently show

```
p_(i-1)-X = a f_(i-1),
p_i-X     = b (-f_i),             a,b>0.                 (4)
```

The vectors on the right are inward supporting normals of body i at
the respective contact points. Each relation in (4) makes its contact
point the unique nearest point of the same convex square to X. For
example, if X=p-aF and F is an inward normal at p, then for every
square point y,

```
|y-X|²=|p-X|²+|y-p|²+2a F dot(y-p) >= |p-X|²,
```

with equality only at y=p. But the two contact points are distinct:
their polar rays lie on opposite sides of body i's center ray in the
physical ring. This is impossible.

Both nearest-point cases are excluded. The force polygon therefore
contains the origin.

## 3. A radial side body's inner face cannot touch a loaded neighbor

We need one elementary geometric lemma to make containment strict.
Let an axis-parallel radial side body have center (A+1/2,0), where
A>1/2, and let

```
R²=(A+1)²+1/4.
```

Any unit square K supported in x<=A and containing a point
P=(A,y), |y|<=1/2, has every vertex strictly inside the radius-R disk.

If P is a vertex, reflect vertically if necessary and write the other
vertex offsets from P as

```
(-c,-s), (-s,c), (-c-s,c-s),
c>=s>=0, c²+s²=1.
```

The first two nontrivial squared vertex norms are at most

```
A²+5/4+s-2Ac,
A²+5/4+c-2As.
```

Both are strictly less than A²+5/4+2A=R², since c,s<=1<2A.
The opposite vertex has squared norm at most

```
A²+9/4-2A(c+s)+(c-s) < R²,
```

because 2A(1+c+s)>1+c-s. The point P itself is also strictly inside.

If P is in a side interior, that supporting side is vertical, so K is
axis-parallel. All its vertices have absolute horizontal coordinate at
most A and absolute vertical coordinate at most 3/2. Hence their squared
norms are at most A²+9/4<R², again using A>1/2.

This proves the lemma. In particular such a neighbor cannot have positive
circle load.

## 4. The origin cannot lie on the boundary

No force-polygon vertex equals zero, because every contact magnitude is
positive. If the origin lies on the boundary, it therefore lies inside
some edge [f_(i-1),f_i]. Its endpoints are antiparallel: for a unit
vector e and positive a,b,

```
f_(i-1)=a e,      f_i=-b e,      g_i=(a+b)e.
```

The two inward contact forces on body i point in the same direction e.
Their weighted mean application point lies on the same support face.
Torque balance puts the mean force line through the origin. The local
loaded-leaf calculation in
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) therefore
applies: only radial side type S or radial diagonal type D is possible.
This uses only the one body's force, torque, and support geometry; the
two physical neighbor bodies have not been merged.

Type D has a unique inward support point, which would make
p_(i-1)=p_i, contrary to the strict physical-ring ordering. In type S,
rotate e to the positive horizontal direction. The body's center is
(A+1/2,0) and its inward face is x=A, |y|<=1/2, with

```
A=sqrt(R²-1/4)-1>9/10>1/2.
```

Both neighboring squares lie on the opposite side of this face and
contain their respective contact points. Section 3 says that neither
can be loaded. This contradicts the hypothesis that the whole component
is loaded, and excludes the boundary case.

The origin is consequently strictly inside the force polygon. The proof
does not assume that a circle-vertex ray lies between the two contact
rays of its body. No uniformity of contact magnitudes, frame gaps, or
contact ownership is asserted.

## 5. Positive radial concurrence

Strict origin containment places the origin strictly to the left of each
oriented force-polygon edge. Consequently

```
g_i cross f_(i-1)>0.
```

The two physical contact-force lines on body i are therefore nonparallel
and concur at the point

```
X_i = [tau/(g_i cross f_(i-1))] g_i.
```

This is a strictly positive point on the body's circle-load resultant
ray. The theorem does not locate X_i inside its square or inside the
containing disk; either such assertion would require a further argument.

