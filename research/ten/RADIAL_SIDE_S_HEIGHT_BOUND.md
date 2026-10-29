# A loaded side-transmission endpoint stays beyond the central body's height

**Status:** complete conditional hand proof; independent mathematical review
passed on 2026-10-29.

Suppose a radial-side loaded central square has the form

```text
C=[L,L+1] x [-1/2,1/2],
R^2=(L+1)^2+1/4,       1<=L<17/16.
```

At its upper-left corner `(L,1/2)`, let a width-one side transmitter
point in direction `(-p,q)`, where p,q>=0 and `p^2+q^2=1`.
Let K be its far endpoint square, supported at
`(L-p,1/2+q)` with inward normal `(-p,q)` and contained in the radius-R
disk.

**Theorem.** If K carries positive circle load, then every point of K
has height strictly greater than `1/2`. Reflection gives the lower-corner
version: its loaded endpoint lies wholly below `-1/2`.

This strengthens the height-zero conclusion of
[RADIAL_SIDE_MIXED_FIVE_CYCLE.md](RADIAL_SIDE_MIXED_FIVE_CYCLE.md)
under the additional hypothesis L>=1. That hypothesis is forced whenever
the other path at a radial-side C is SS, by Section 2 of
[SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md](SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md).

Reflect the horizontal coordinate for the proof. The endpoint support
point and its inward normal become

```text
Q=(p-L,1/2+q),       n=(p,q).
```

Assume K meets `y<=1/2`. We prove every vertex of K is strictly inside
the circle.

## 1. Vertex support

If Q is a vertex, one incident edge must point downward, or horizontally
in the boundary case q=0, to reach the stated half-plane.
The support condition makes that edge point right;
the orthogonal companion points upward and right. For some phi the
edge directions are

```text
e=(cos phi,-sin phi),       f=(sin phi,cos phi),
theta<=phi<=pi/2-theta,     p=cos theta, q=sin theta.
```

Thus `0<=theta<=pi/4`, so p>=q. Write `Q=(x,y)`. Since L>=1,
`x<=0<y`, while

```text
x+y=p+q+1/2-L>0.
```

The vertex Q and its lower adjacent vertex Q+e are circle-clear because

```text
|Q|^2+1-R^2=1+q-2L(p+1)<0,
Q dot e<=0.
```

For the upper adjacent vertex Q+f, the derivative of
`Q dot f=x sin phi+y cos phi` is nonpositive. Its norm is therefore
maximized at phi=theta. Put w=p+q, so `1<=w<=sqrt(2)`. At that endpoint
the vertex is `(w-L,1/2+w)`, with squared-radius excess

```text
2w^2+(1-2L)w-2L-1
 <=2w^2-w-3
 <=1-sqrt(2)<0.                                      (1)
```

The last polynomial increases for w>=1.

For the opposite vertex Q+e+f, its dot product with Q is

```text
(x+y)cos phi+(x-y)sin phi.
```

It strictly decreases on the allowed interval, because x+y>0 and x-y<0.
Again the maximum occurs at phi=theta, giving the vertex
`(2p+q-L,1/2+p)`. Its squared-radius excess is at most

```text
4(p^2+pq)-3p-2q-2 <= 2sqrt(2)-3<0.                   (2)
```

For the comparison, Cauchy's inequality gives

```text
p^2+pq = [1+(p^2-q^2)+2pq]/2 <= (1+sqrt(2))/2,
```

because `(p^2-q^2)^2+(2pq)^2=1`. Also

```text
(3p+2q)^2-9=q(12p-5q)>=0,
```

so 3p+2q>=3. These prove (2). All four vertices are strictly circle-clear.

## 2. Side support

If Q lies on a side, its support normal fixes the frame:

```text
K=Q+[0,1](p,q)+[-u,1-u](-q,p),       0<=u<=1.
```

Meeting `y<=1/2` forces `up>=q`. This implies p>0, since p=0 would
give q=1 and make the inequality impossible. Hence `u>=q/p`, so again
p>=q. Each vertex depends
affinely on u. Convexity of the norm reduces the check to u=1, covered
by the vertex case, and u=q/p. At the latter value the vertices are

```text
V00=(1/p-L,1/2),
V01=(1/p-q-L,1/2+p),
V10=(1/p+p-L,1/2+q),
V11=(1/p+p-q-L,1/2+p+q).
```

For any displayed vertex `(A-L,B)`, its squared-radius excess is
`A^2+B^2-5/4-2L(A+1)`. Here A>0, so the excess decreases with L.
It suffices to check L=1, where `R^2=17/4`.

For V00, `|x|<1/2` and y=1/2. For V01, `|x|<3/4` and y<=3/2,
giving squared norm below `45/16<17/4`. For V10,

```text
0<x<=3/sqrt(2)-1<5/4,
0<y<=1/2+1/sqrt(2)<5/4,
```

giving squared norm below `25/8<17/4`.

For V11 its coordinates x,y are positive, and

```text
3/2<=y<=1/2+sqrt(2),
x+y=1/p+2p-1/2<=5/2.
```

The latter expression increases for `1/sqrt(2)<=p<=1` and takes its
maximum at p=1. Thus

```text
x^2+y^2 <=(5/2-y)^2+y^2
 <=max(13/4,33/4-3sqrt(2))<17/4.
```

The quadratic is convex, so its maximum occurs at one of the two displayed
endpoints for y. The final strict comparison uses `3sqrt(2)>4`.

Every vertex is strictly circle-clear in both support cases. Hence a
loaded endpoint cannot meet `y<=1/2`, proving the theorem.
