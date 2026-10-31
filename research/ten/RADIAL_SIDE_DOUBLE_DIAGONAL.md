# Exact angular restrictions for radial-side double-diagonal transmitters

**Status:** independently reviewed exact necessary conditions (2026-10-29).

Use the physical positive component `A-U-C-V-B-A` and radius window from
[RADIAL_SIDE_MIXED_TRANSMISSIONS.md](RADIAL_SIDE_MIXED_TRANSMISSIONS.md).
Both U and V are diagonal transmitters. This note proves exact necessary
angular restrictions and excludes `R^2>=17/4` and equal outward angles.
**The asymmetric double-diagonal case below `17/4` remains open**.

Assume the radial-side setup, reflected so that
`C=[-L-1,-L] x [-1/2,1/2]`. Its two DD contacts have coordinates
`P=(-L,h)` and `Q=(-L,-k)`, where `0<h,k<=1/2`. Set `d=h+k`.
Their outgoing unit directions are `(p,q)=(cos(theta),sin(theta))`
and `(r,-s)=(cos(eta),-sin(eta))`, respectively, with all coordinates
nonnegative. If `h<1/2`, then `theta=0`; if `k<1/2`, then `eta=0`,
because a relative-interior side contact has the horizontal normal.

## Angle range forced by the endpoint square

Any unit square supported at a point T with inward unit normal `(p,q)`,
`p,q>=0`, has a point of height at least `T_y+q`. For vertex support,
write the two inward orthonormal edge vectors as `u,v` and
`(p,q)=a u+b v`, where `a,b>=0` and `a^2+b^2=1`. Its upper height
relative to T is `max(u_y,0)+max(v_y,0)`, which is at least
`a u_y+b v_y=q`. For side support, its inward edge is `(p,q)` and
its tangent is `(-q,p)`; a translate of the contact by the inward edge
already gives a point of height `T_y+q`.

The upper endpoint A is supported at
`T=(-L+sqrt(2)p,h+sqrt(2)q)`. Thus its maximum height is at least
`h+(sqrt(2)+1)q`. If the transmission starts at the corner and
`theta>=pi/4`, this is at least
`1/2+(sqrt(2)+1)/sqrt(2)=3/2+1/sqrt(2)>3/sqrt(2)`, impossible.
A side-interior contact already has `theta=0`. Consequently
`0<=theta<pi/4`; reflection gives `0<=eta<pi/4`.

## Exact separating-axis calculation

Put `delta=theta+eta`, so `0<=delta<pi/2`. The upper and lower
transmitter centers differ by

```
D=((p-r)/sqrt(2), d+(q+s)/sqrt(2)).
```

The four possible separating axes can be represented by these upward
unit normals:

```
a_U=(p-q,p+q)/sqrt(2), b_U=(-p-q,p-q)/sqrt(2),
a_V=(-r+s,r+s)/sqrt(2), b_V=(r+s,r-s)/sqrt(2).
```

On each of these axes the sum of the two square half-widths is
`H=(1+cos(delta)+sin(delta))/2`. Direct multiplication gives

```
D.a_U=(1-cos(delta)+sin(delta))/2+d(p+q)/sqrt(2),
D.b_U=(-1+cos(delta)+sin(delta))/2+d(p-q)/sqrt(2),
D.a_V=(1-cos(delta)+sin(delta))/2+d(r+s)/sqrt(2),
D.b_V=(-1+cos(delta)+sin(delta))/2+d(r-s)/sqrt(2).
```

All four projections are nonnegative, since `cos(delta)+sin(delta)>=1`
and `p>q,r>s`. Therefore the separating-axis criterion for disjoint
interiors is that at least one of these projections is at least H.
The b-axes would respectively require `d(p-q)>=sqrt(2)` or
`d(r-s)>=sqrt(2)`, impossible because `d<=1` and `p-q,r-s<=1`.
Thus the exact condition is

```
d max(p+q,r+s) >= sqrt(2) cos(theta+eta).                 (1)
```

This includes boundary contact equality and the cases with one horizontal
transmission. It uses the actual oriented unit-square transmitters.

## Consequences

After exchanging upper and lower, assume `theta>=eta`. The function
`cos(t)+sin(t)` increases on `[0,pi/4)`, so (1) reads

```
d cos(pi/4-theta) >= cos(theta+eta).
```

Since `d<=1` and cosine is decreasing on `[0,pi/2]`, it follows that

```
2 theta+eta >= pi/4,                                    (2)
```

with strict inequality if `d<1`. In particular, the larger angle is at
least `pi/12`. If the lower contact is in the relative side interior,
then `eta=0,d<1`, so the upper angle obeys `theta>pi/8`.

Independently, any supported unit square with inward normal `(p,q)`
can extend down from its support point by at most p. For vertex support,
at most one incident edge points down and its vertical component has
magnitude at most p; for side support the full tangent side has vertical
length p. Hence

```
min_y A >= h+sqrt(2)q-p,
max_y B <= -k-sqrt(2)s+r.
```

The physical A--B contact requires these vertical projections to overlap,
so necessarily

```
d <= p+r-sqrt(2)(q+s).                                  (3)
```

Combining (1) and (3) gives a further necessary angular inequality.
These conditions do not themselves exclude the DD pattern: for example,
`theta=eta=pi/12,d=1` satisfies both (1) and (3).


## A further radius constraint

A unit square supported at a point T with inward unit normal n contains
T+n. At a vertex, write n=a u+b v in its two inward unit edge directions;
then 0<=a,b<=1, so T+n belongs to the square. At a side point, translation
by the unit inward normal maps the support side to its opposite side.

For an upper-corner transmission this forces

```
(-L+(sqrt(2)+1)p)^2+(1/2+(sqrt(2)+1)q)^2 <= R^2
 = (L+1)^2+1/4.
```

Expansion gives the exact necessary inequality

```
L >= [2+2sqrt(2)+(sqrt(2)+1)q] / [2((sqrt(2)+1)p+1)].
```

The denominator is positive. Reflection gives the same statement for a
lower-corner transmission. This condition uses containment only, and
should not be read as a loadedness or stress-sufficiency criterion.

## Exclusion in the upper radius window

**Theorem.** The radial-side double-diagonal component is impossible when
`17/4<=R^2<=9/2`.

Here `1<=L<17/16`. We prove that a loaded endpoint of an upper
transmission must lie wholly in `y>0`. Reflection then puts the other
loaded endpoint wholly in `y<0`, contradicting their physical contact.

First suppose the upper transmission starts at the corner. Write its
endpoint as

```
T=(x,y)=(sqrt(2)p-L,1/2+sqrt(2)q).
```

Suppose its supported unit square K meets `y<=0`.

If T is a vertex, precisely one of the two incident edges can point
strictly downward. The inward normal `(p,q)` makes that edge point
right; the other edge points upward and right. Thus the edges are
`(c,-s)` and `(s,c)`, with `c,s>=0`, `c^2+s^2=1`. Reaching zero and
support give `y<=s<=p`. In particular,

```
1/2+sqrt(2)q<=p,     q<1/3,     p>sqrt(8)/3,
0<x<=sqrt(2)-1,      c^2<=3/4.
```

For the bound on q, the function `sqrt(1-q^2)-sqrt(2)q` is strictly
decreasing, and at `q=1/3` it equals `sqrt(2)/3<1/2`. The lower bound
on x follows from `sqrt(2)p>4/3` and `L<17/16`.

The two vertices T and `T+(c,-s)` have squared norm less than 3.
The upper adjacent vertex obeys

```
x+s<=sqrt(2),       y+c<=s+c<=sqrt(2),
```

so its squared norm is at most 4. At the opposite vertex,

```
x+c+s<=2sqrt(2)-1,
|y+c-s|<=max(c,1/2)<=sqrt(3)/2.
```

Its squared norm is therefore at most

```
(2sqrt(2)-1)^2+3/4 = 39/4-4sqrt(2) < 17/4.
```

The last strict comparison is equivalent to `sqrt(2)>11/8`, whose
square is `128>121`. All vertices are strictly inside the disk.

If T is in a support side, write

```
K=T+[0,1](p,q)+[-u,1-u](-q,p),        0<=u<=1.
```

Meeting `y<=0` gives `y<=up<=p`, so the bounds on p,q,x above still
hold. Each squared vertex norm is a convex function of u; it suffices
to check `u=1` and `u=y/p`. The first is a vertex case already proved.
At the second endpoint, the lowest vertex is `(x',0)`, where

```
x'=x+yq/p = sqrt(2)/p-L+q/(2p).
```

Since `p>sqrt(8)/3>8/9`, `q<1/3`, and `L>=1`,

```
0<x'<3/4,
-1/3<x'-q<1/2,
0<x'+p<7/4,
-1/3<x'+p-q<3/2.
```

For the upper bounds involving `-q`, use
`q/(2p)-q<=0` and `sqrt(2)/p<3/2`.
The four vertices are

```
(x',0), (x'+p,q), (x'-q,p), (x'+p-q,p+q).
```

Their squared norms are respectively less than
`9/16`, `49/16+1/9`, `5/4`, and `9/4+2=17/4`.
Thus K is again circle-clear. This finishes the upper-corner case.

Now let the upper contact be in the relative side interior, at height
`0<h<1/2`. Its transmission direction is horizontal and

```
T=(x,h),       x=sqrt(2)-L,       0<x<=sqrt(2)-1<5/12.
```

For vertex support, use the same edges `(c,-s),(s,c)`. Reaching zero
gives `h<=s`. The vertices other than the opposite one have squared
norm at most 4, by `x+s<=sqrt(2)`, `h+c<=s+c<=sqrt(2)`, and the
immediate coordinate bounds for the remaining two vertices.
For the opposite vertex its squared norm is a convex function of h
on `[0,min(1/2,s)]`, so check the two endpoints. At `h=0` it is

```
x^2+2+2x(c+s) <= (x+sqrt(2))^2
 <= (2sqrt(2)-1)^2 <17/4.
```

If `s>=1/2`, the other endpoint is `h=1/2` and the previous
`39/4-4sqrt(2)` bound applies. If `s<1/2`, the endpoint is `h=s`;
then `c+s<=(sqrt(3)+1)/2<11/8`, and the squared norm is less than

```
(5/12+11/8)^2+1=2425/576<2448/576=17/4.
```

For side support the square is parallel to C. Meeting zero confines
its vertical coordinates between -1 and 1, while its horizontal
coordinates are x and x+1, with `0<x<x+1<=sqrt(2)`. Its squared vertex
norms are at most 3. Hence the relative-interior case is circle-clear
too, completing the theorem.


## Larger corner angles put a loaded endpoint above zero

Let `79/40<=R<=3/sqrt(2)` and `L=sqrt(R^2-1/4)-1`, so
`9/10<L<17/16`. Let `p=cos(theta),q=sin(theta)` with
`pi/12<=theta<pi/4`. Suppose a unit square K is supported at

```
Q=(x,y)=(sqrt(2)p-L, 1/2+sqrt(2)q)
```

with inward supporting unit normal `(p,q)`. If K meets `y<=0`, then
all its vertices have norm strictly less than R. In particular, a
circle-loaded K must lie wholly in `y>0`.

### Vertex support

If Q is a vertex, a point of K at nonpositive height requires one
incident edge to point down. Its companion must point up and right,
and the two edges therefore have the form

```
e=(c,-s), f=(s,c), c,s>=0, c^2+s^2=1.
```

The inward-normal condition `pc-qs>=0` gives `s<=p`. Meeting zero gives
`y<=s`. Since `theta>=pi/12`, we obtain

```
y>=sqrt(3)/2, y<=s<=p, c<=1/2.
```

Furthermore `q<1/3`: otherwise `1/2+sqrt(2)q<=sqrt(1-q^2)` would imply
`1/2+sqrt(2)/3<=2sqrt(2)/3`, or `3/2<=sqrt(2)`, impossible.
The following useful bounds follow:

```
0<x<1/2,
p+q<(2sqrt(2)+1)/3,
x+y=sqrt(2)(p+q)+1/2-L<sqrt(2),
s+c<11/8.
```

For the first, `p>=sqrt(3)/2` gives `sqrt(2)p>17/16`, and
`p<=cos(pi/12)` gives
`sqrt(2)p<11/8`, hence `x<11/8-9/10=19/40<1/2`.
For the third, use the second and `L>9/10` to get
`x+y<(4+sqrt(2))/3-2/5<sqrt(2)`; the last inequality is equivalent
to `sqrt(2)>7/5`. For the fourth, `s>=sqrt(3)/2` implies
`s+c<=(sqrt(3)+1)/2<11/8`.

The vertices Q and Q+e have squared norms below 2. The opposite vertex
Q+e+f has horizontal coordinate less than `15/8` and vertical coordinate
with absolute value at most `1/2`, so its squared norm is less than
`241/64`.

For the remaining vertex Q+f, maximize its squared norm over
`s>=y` with `c=sqrt(1-s^2)`. Equivalently maximize `xs+yc` over
`0<=c<=sqrt(1-y^2)<=1/2`. Its derivative with respect to c is
`y-xc/s>0`, because `y>=sqrt(3)/2`, `x<1/2`, `c<=1/2`, and
`s>=sqrt(3)/2`. Thus its maximum occurs at `s=y`, giving

```
|Q+f|^2 <= (x+y)^2+(y+sqrt(1-y^2))^2
         < 2+(11/8)^2
         =249/64
         <6241/1600=(79/40)^2<=R^2.
```

Here `y+sqrt(1-y^2)<=(sqrt(3)+1)/2<11/8` since
`y>=sqrt(3)/2`. The other vertex bounds are smaller, so K is circle-clear.

### Side support

If Q belongs to a side, write `n=(p,q),t=(-q,p)` and

```
K=Q+[0,1]n+[-u,1-u]t,   0<=u<=1.
```

Meeting zero is equivalent to `u>=y/p`, so once again `y<=p`, and the
bounds above hold. For each labelled vertex, its squared norm is a
convex quadratic in u. It suffices to bound the two endpoint positions
`u=y/p` and `u=1`.

At `u=1`, Q is a vertex with incident edges `(q,-p)` and `(p,q)`;
this is the preceding vertex case.

At `u=y/p`, put `P=(x+yq/p,0)`. The four vertices are P, P+n, P+t,
and P+n+t. We use the further elementary inequalities

```
p+q<(2sqrt(2)+1)/3<23/18,
x+p=(sqrt(2)+1)p-L<3/2.
```

The first follows from `sqrt(2)<17/12`. For the second, use
`p<=cos(pi/12)<39/40`, `sqrt(2)<10/7`, and `L>9/10`:
`x+p<663/280-9/10=411/280<3/2`.

Now P has horizontal coordinate in `(0,5/6)` and zero height.
The vertex P+n has horizontal coordinate less than
`x+p+q<1/2+23/18=16/9` and height q<1/3, so its squared norm is less
than `265/81`. The vertex P+t has horizontal absolute coordinate less
than `1/2` and height p<=1, so its squared norm is less than `5/4`.
Finally P+n+t has horizontal coordinate
`x+p-q+yq/p<=x+p<3/2` (and it is positive), and height
`p+q<23/18`. Its squared norm is therefore less than

```
(3/2)^2+(23/18)^2=629/162<6241/1600.
```

All four vertices at each endpoint of the u-interval are strictly inside
the containing circle. Convexity gives the same strict bound for every
intermediate u. This proves the side-support case and the lemma.


## Exact remaining domain

The radial-side DD component, if it exists, must satisfy

```
79/40<=R<sqrt(17)/2.
```

Choose the upper/lower labelling so that `theta>=eta`. The exact
transmitter separation condition gives `2 theta+eta>=pi/4`, hence
`theta>=pi/12`. The preceding clearance lemma puts A wholly in
`y>0`. If `eta>=pi/12`, its reflected version would put B wholly
in `y<0`, contradicting their contact. Therefore

```
0<=eta<pi/12<theta<pi/4,
2 theta+eta>=pi/4,
d cos(pi/4-theta)>=cos(theta+eta),
d<=cos(theta)+cos(eta)-sqrt(2)(sin(theta)+sin(eta)).
```

The strict lower bound on theta follows from `eta<pi/12` and
`2 theta+eta>=pi/4`. The endpoint A stays wholly above zero; B
must have a point of positive height in order to touch A. At a
side-interior lower contact, `eta=0,d<1` strengthens this to
`theta>pi/8`. Equal outward angles are thus excluded throughout
the original radius window. The remaining asymmetric, smaller-radius
domain has not been excluded.
