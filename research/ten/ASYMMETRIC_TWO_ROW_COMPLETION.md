# Asymmetric two-row cores with two small centers have capacity at most nine

Put

```text
Q=9/2, R=3/sqrt(2), r=sqrt(1+1/sqrt(2)),
A=(sqrt(17)-1)/2.
```

Suppose a packing in the origin-centered disk of squared radius Q contains
four axis-parallel unit squares centered at

```text
(-1/2,-t), (1/2,-t), (-b_L,1-t), (b_R,1-t),
0<t<=5/12,
b_L,b_R>=1/4,       b_L+b_R>=1,
b_L^2+(1-t)^2<=1,  b_R^2+(1-t)^2<=1.
```

Then at most five additional unit squares fit, with arbitrary independent
orientations. In particular this extends
[SYMMETRIC_TWO_ROW_COMPLETION.md](SYMMETRIC_TWO_ROW_COMPLETION.md) to
unequal upper horizontal offsets, while slightly increasing the permitted
lower-row displacement. The lower centers have norm at most `sqrt(61)/12`.

This is a conditional hand theorem for the displayed core family. Neither
the two-row form nor the lower bound `b_L,b_R>=1/4` is asserted for general
four-inner-center configurations.

## 1. Core clearance and retained arcs

Write `h=1/2-t` and `z=3/2-t`. The lower squares fill
`[-1,1] x [-t-1/2,h]`. The upper horizontal intervals are

```text
I_L=[-b_L-1/2,-b_L+1/2],
I_R=[ b_R-1/2, b_R+1/2],
```

and their common vertical interval is `[h,z]`. The hypotheses give

```text
z>=13/12>27/25,       0<h<1/2,
b_L,b_R<=sqrt(95)/12<13/16,
g:=b_L+b_R-1>=0.
```

Every point of the closed unit disk has distance strictly less than `1/2`
from the core. Below height h its distance from the lower rectangle is at
most `1/2-t<1/2`. Above h its height is at most `1<z`; its horizontal
distance from `I_L union I_R` is at most the maximum of
`g/2`, `1/2-b_L`, and `1/2-b_R`, each strictly below `1/2`.
The open inscribed disk of an additional square therefore forces its
center to have norm greater than one. Its norm is also at most A, with
`A<25/16`, by the universal center bound.

The center-radius theorem consequently gives each additional square one
connected arc of angle at least `pi/4` on the test circle of radius r.

Retain only the first-quadrant trace of the upper-right square and its
second-quadrant counterpart on the upper-left square. Denote these arcs by

```text
[alpha_R,beta_R],  [pi-beta_L,pi-alpha_L].
```

Both have positive length. Their outward corner squared norms exceed
`(3/4)^2+(13/12)^2=125/72>r^2`, while their inward corners are inside the
circle. Any portions in the other upper quadrant are ignored; this only
enlarges the free gaps. Set

```text
a_y=asin(h/r),               gamma=acos(1/r),
a_x(b)=acos(min(1,(b+1/2)/r)).
```

Then

```text
alpha_i=max(a_y,a_x(b_i)),
0<a_y<pi/8,   0<alpha_i<3pi/8,
pi/8<gamma<pi/4,   beta_i>pi/4.                 (1)
```

Here `r sin(pi/8)=1/2`, while every upper inner vertical edge has
horizontal distance less than `5/16<1/2` from zero and `z>1`.
The upper endpoints can be written

```text
beta_i=min(theta,kappa_i),
theta=asin(z/r) if z<r, and theta=pi/2 otherwise,
kappa_i=acos(max(0,b_i-1/2)/r)>3pi/8.             (2)
```

The two lower endpoints also satisfy

```text
alpha_L+alpha_R<pi/2.                            (3)
```

If either endpoint equals `a_y`, (1) proves (3). Otherwise both are
`a_x` endpoints, and concavity of arccos on `[0,1]`, together with
`b_L+b_R>=1`, gives
`alpha_L+alpha_R<=2acos(1/r)=2gamma<pi/2`.

In particular the enlarged upper gap has angle
`pi-beta_L-beta_R<pi/2`. If it holds an additional arc, its angle is at
least `pi/4`. Formula (2) then implies

```text
z<=H=(1+sqrt(2))/2<5/4,
beta_L=beta_R=beta=asin(z/r)<=3pi/8.              (4)
```

Indeed if theta were greater than `3pi/8`, both beta values would be
greater than `3pi/8`. Otherwise both kappa values exceed theta, so both
beta values equal theta.

## 2. Six additional arcs require an upper-gap square and a small opening

First suppose the lower core squares do not cross the test circle:

```text
t<=t_0:=2^(-1/4)-1/2.
```

Their isolated tangencies, if any, may be ignored. The enlarged lower gap
has angle `pi+alpha_L+alpha_R<3pi/2`, so holds at most five additional
arcs. The upper gap holds at most one. Thus six additional squares would
require one in the upper gap and five in the lower gap, and hence

```text
alpha_L+alpha_R>=pi/4.                            (5)
```

We claim (5) forces `b_L+b_R<=sqrt(2)`.
If both alpha values come from their x bounds, concavity of arccos gives

```text
pi/4<=alpha_L+alpha_R
     <=2acos((b_L+b_R+1)/(2r)),
```

and `2r cos(pi/8)=1+sqrt(2)` proves the claim.

Otherwise one alpha equals `a_y<pi/8`; the other is at least
`pi/4-a_y` and is an x-bound endpoint. There are two elementary bounds
which make this case strictly stronger. First `t<=t_0<7/20`, using
`2^(-1/4)<17/20`, implies

```text
b_i<=sqrt(2t-t^2)<19/25.
```

Second `b_L+b_R>=1` implies `t>=1-sqrt(3)/2`, so
`h<11/30`. Since `r^2<239/140`, the increasing function
`sqrt(r^2-h^2)+h` obeys

```text
sqrt(r^2-h^2)+h
 <sqrt(239/140-(11/30)^2)+11/30
 <251/200+11/30=973/600.
```

Using `sqrt(2)>140/99`, the x-bound endpoint consequently satisfies

```text
b_other+1/2<=r cos(pi/4-a_y)
  =(sqrt(r^2-h^2)+h)/sqrt(2)
  <4587/4000<23/20.
```

Thus `b_other<13/20`, and
`b_L+b_R<19/25+13/20=141/100<sqrt(2)` as claimed.
In this noncrossing case, six extras therefore require

```text
g<=sqrt(2)-1<43/100,       z>23/20.              (6)
```

Now suppose `t>t_0`. The lower-right square has a fourth-quadrant arc
`[2pi-delta,2pi-gamma]`, where
`delta=asin((t+1/2)/r)>gamma`; the lower-left trace is its reflection.
The four enlarged gaps have angles

```text
pi-beta_L-beta_R,
alpha_L+gamma,
pi-2delta,
alpha_R+gamma.
```

By (1), the top holds at most one arc, each side at most two, and the
bottom at most two. Both sides cannot hold two: that would give
`alpha_i>=pi/2-gamma>pi/4`, making both endpoints x-bound endpoints and
forcing `b_i+1/2<=r sin(gamma)=2^(-1/4)`. Hence
`b_L+b_R<=2t_0<1`, a contradiction.

Six additional squares would therefore require one upper-gap arc, two
bottom arcs, and three side arcs. One side must hold two, so its
corresponding `b_i<=t_0<11/32`. The other b is less than `13/16`.
Consequently in this crossing case six extras require

```text
g<11/32+13/16-1=5/32<4/25.                       (7)
```

## 3. An upper-gap center cannot lie beyond either outer top corner

Suppose S were the required upper-gap square, with center `(x,y)` and
norm `u`, where `1<u<=A`. The radial point `r(x,y)/u` is in its open
inscribed disk because `|r-u|<1/2`. Its angle is therefore in the same
upper gap. From (4),

```text
beta<=arg(x,y)<=pi-beta,      sin(beta)=z/r.
```

In particular `y>z/r>h`. Also

```text
|x|<=A cos(beta)<9/10,                             (8)
```

since
`(25/16)^2[1-(27/25)^2/(239/140)]=47315/61184<81/100`.

Consider the region beyond the right upper square, `x>=q=b_R+1/2`.
Here `q>=3/4>2/3`. If `y<=z`, the center's distance from that core
square is `x-q<7/30<1/2`. If `y>=z`, its distance is the distance to
the upper-right corner `(q,z)`. Along a fixed ray this distance increases
as u increases, because both positive coordinate differences increase.
It is therefore bounded by the maximum on the radius-A arc

```text
(A cos(theta),A sin(theta)),
beta<=theta<=acos(q/A).
```

An empty angular interval needs no consideration. On this interval the
squared distance from `(q,z)` is

```text
A^2+q^2+z^2-2A(q cos(theta)+z sin(theta)).
```

The parenthesized function is concave, so the maximum distance occurs at
an endpoint. At theta=beta the coordinate differences satisfy

```text
0<=A cos(beta)-q<7/30,
0<A sin(beta)-z=(A/r-1)z<105/416,
```

using `r>13/10`, `A<25/16`, and `z<5/4`. Their squared sum is less than
`4600561/38937600<1/4`. At the other endpoint the horizontal difference
is zero and the vertical difference is less than

```text
sqrt((25/16)^2-(2/3)^2)-27/25
 <3/2-27/25=21/50<1/2.
```

Thus every center beyond the right outer edge has distance less than
`1/2` from the core. Reflection proves the same beyond the left outer
edge. Neither is possible for the center of S.

## 4. The remaining horizontal positions also violate clearance

If x belongs to `I_L` or `I_R`, its distance from the core is at most
`max(y-z,0)<A-z<193/400<1/2`.

The only remaining possibility is that x is in the middle opening,
whose width is g. Its distance from the nearer upper square is at most

```text
sqrt((g/2)^2+max(y-z,0)^2).
```

In the noncrossing case, (6) bounds its square strictly by

```text
(43/200)^2+(25/16-23/20)^2
 =34621/160000<1/4.
```

In the crossing case, (7) and `z>27/25` bound it strictly by

```text
(2/25)^2+(25/16-27/25)^2
 =38273/160000<1/4.
```

Every possible upper-gap center therefore lies at distance strictly less
than `1/2` from a core square. Its open inscribed disk would overlap that
square's interior, which is impossible. The necessary upper-gap square
does not exist, excluding six additional squares in both cases and proving
the theorem.
