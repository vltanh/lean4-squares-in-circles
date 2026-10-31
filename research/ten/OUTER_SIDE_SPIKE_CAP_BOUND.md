# A hand cap bound at an outer-side proper contact

**Status:** complete conditional hand argument; two independent full
mathematical reviews passed on 2026-10-30, including the radial-cap cutoff
and the endpoint-sensitive diameter-disk cut.
This bounds a proper outer-side contact spike by the same radius bound
as its extra core corner. That bound is still above the three-square
capacity threshold; no full C04 exclusion is claimed.

Use the outer-body notation and hypotheses of
[LOADED_OUTER_MIXED_RESTRICTIONS.md](LOADED_OUTER_MIXED_RESTRICTIONS.md):

```text
C=[X-1,X] x [-H-1,-H],
w=(X,-H-1),       q=R^2=X^2+(H+1)^2,
6241/1600<=q<=9/2,
1/2<X<H,       H<17/16,
B=(X,-H),      P=(X,-H-t),       0<t<1.
```

Suppose the neighbor K at the outer S incidence P has strict vertex
support, with inward normal `(1,0)`, and has a circle vertex adjacent
to P. Write its two incident unit edges as

```text
u=(c,-s),       v=(s,c),       c,s>0,       c^2+s^2=1.
```

Its adjacent circle vertex must be `w'=P+u`: if `P+v` were on the circle,
then `P+u+v` would be farther from zero since `P dot u>0`. The core
opposite w' is

```text
D=P+v.
```

Let `T=conv{B,P,D}`. For any unit inner square J with interior disjoint
from C and K, each vertex z of J in T satisfies

```text
|z|^2 < rho(q):=q-sqrt(2q-1)
            <=9/2-2sqrt(2).                           (1)
```

The theorem includes a neighbor initially allowed two geometric circle
vertices: the estimates below actually force w' to be its unique circle
vertex. A contact at K's opposite circle corner instead has a degenerate
contact triangle; this note addresses the nondegenerate adjacent-corner
case.

## 1. Exact circle identities and useful bounds

Put

```text
epsilon=H-X,
zeta=Ht+t^2/2,
K0=P dot u=Xc+(H+t)s,
L0=-P dot v=(H+t)c-Xs.
```

Equality of the two circle radii gives

```text
K0=H-zeta.                                            (2)
```

Containment of `w'+v` gives `L0>=1/2`. Also `K0>X`, because
`H+t>X`, c,s>0 and c+s>1. Hence

```text
0<zeta<epsilon,          t<epsilon/H<9/17.            (3)
```

Here `X/H>8/17` follows from X>1/2 and H<17/16. Equation (2) gives
`Xc+Hs<H`, so

```text
8/17<X/H<(1-s)/c=sqrt((1-s)/(1+s)),
s<225/353<2/3.                                       (4)
```

For `0<s<2/3`, one has `c>1-2s/5`: both sides are positive, and the
difference of their squares is `s(20-29s)/25>0`. Rearranging (2),

```text
epsilon=H(t+s)-X(1-c)+ts+t^2/2
       >H(t+s+c-1)
       >H(t+3s/5).
```

The elementary square `(t-3s/5)^2>=0` therefore gives

```text
ts < 5epsilon^2/(12H^2) < 135/1156 < 1/8.             (5)
```

We also have `H>3/4`: otherwise `X<H` would give
`q<H^2+(H+1)^2<=29/8<6241/1600`. In particular

```text
|B|^2=q-2H-1<2.                                      (6)
```

## 2. The neighboring core is shorter than B

Since u,v are orthonormal,

```text
L0^2=|P|^2-K0^2.
```

Using (2) and the definition of zeta gives the exact identity

```text
L0^2-(X+zeta)^2=2zeta*(1+epsilon-zeta)>0.
```

Both quantities compared are positive, so `L0>X+zeta>1/2`. In
particular `w'+v` is strictly inside the circle. The other two vertices
are also strictly inside: `|w'|^2-|P|^2=1+2K0>0`, and

```text
|D|^2-|B|^2=2zeta+1-2L0<1-2X<0.                    (7)
```

The bound on B in the outer-mixed note is strictly below q. Thus w'
is the unique circle vertex of K, and D is its usual opposite core.

## 3. The diameter cap's second line intersection

Consider the closed disk with diameter BD, intersected with the retained
half-plane

```text
(z-P) dot u <= 0.                                    (8)
```

Its line boundary intersects the diameter circle at D and

```text
V=P+tc*v=(X+tcs,-H-ts^2).                            (9)
```

Indeed, along `P+lambda*v` the diameter-circle equation factors as
`(lambda-1)(lambda-tc)=0`.

The squared norm increase from B to V is

```text
|V|^2-|B|^2
 =2ts(Xc+Hs)+t^2s^2
 =2Hts-2zeta*ts-t^2s^2
 <2Hts <5epsilon^2/(6H).                             (10)
```

On the other hand,

```text
rho(q)-|B|^2
 =2H+1-sqrt(2q-1)
 =2epsilon*(H+X)/(2H+1+sqrt(2q-1))
 >epsilon*(H+X)/(2H+1).                              (11)
```

The last strict comparison uses X<H. Finally

```text
6H(H+X)-5epsilon(2H+1)
 =X(16H+5)-H(4H+5)
 >(5/4-H)(4H+2)>0.
```

The first strict inequality uses X>1/2; the second uses H<17/16<5/4.
Combining (10)--(11) proves

```text
|V|^2<rho(q).                                        (12)
```

## 4. The full disk's radial maximum is cut off

Let M be the diameter disk's center and r its radius. In the u,v frame,

```text
M dot u=K0-ts/2 >7/16,
2r=sqrt((1-tc)^2+t^2s^2)>1-t>8/17.
```

These follow from X>1/2 and (3)--(5). By (6)--(7),

```text
0<|M|<sqrt(2)<3/2.
```

The farthest point of the full disk from zero is
`F=M+r*M/|M|`. Its excess in the u direction over M satisfies

```text
(F-M) dot u > (4/17)*(7/16)/(3/2)
             =7/102>1/16>ts/2.
```

But `P dot u-M dot u=ts/2`. Hence F violates the retained half-plane
(8). A norm maximum on the retained disk cap must therefore occur at
one of its two line/circle intersections D,V. On the straight segment
convexity reduces to the endpoints, and the circular arc has no other
local maximum of the norm. Equation (7) gives `|D|<|B|`, while (10)'s
first expression is positive and gives `|B|<|V|`. Thus every point of
the retained cap has squared norm at most `|V|^2<rho(q)`.

## 5. An inner-square vertex in the spike belongs to that cap

The triangle lies in (8), since its vertices have respective u offsets
`-ts,0,0` from P. It remains to prove the diameter-disk cut.

The point P cannot belong to an inner unit square. At P, C occupies
the left open half-plane and K occupies its right-angle vertex sector.
The remaining two angular gaps both have width strictly less than pi/2,
because c,s>0. A unit square containing P would have an interior tangent
sector of at least pi/2, so its interior would overlap C or K.

All three sides of T have length at most one:

```text
|P-D|=1,       |P-B|=t<1,
|B-D|^2=1+t^2-2tc<1.
```

For the last inequality, (3)--(4) give `t<9/17` and
`c>sqrt(5)/3>1/2`, so t<2c.

Suppose an inner-square vertex z in T lies outside the disk with
diameter BD. Then `(z-B) dot (z-D)>0`, so the angle subtended by BD
at z is strictly less than pi/2. The point z is neither B nor D, which
are on the diameter disk, nor P, which was excluded above. Each triangle
vertex is consequently at distance strictly less than one from z, and
so is every point of T. Both unit edges of the inner square issuing
from z must leave T before reaching their other endpoints.

They cannot cross PB or PD into the loaded squares C or K. If an edge
runs along one of these segments, it must leave at B or D, since leaving
through P would put P in the inner square. Thus both edge directions
must point through the base BD. But those directions are perpendicular,
whereas the directions viewing BD from z occupy an angle smaller than
pi/2. This is impossible. Therefore z belongs to the diameter disk and,
by (8), to the cap bounded in Section 4. This proves (1).

The remaining numerical obstruction is unchanged: `9/2-2sqrt(2)` is
strictly above `425/256`. The note supplies an exact local cap estimate,
not a capacity contradiction or a realization of its limiting geometry.
