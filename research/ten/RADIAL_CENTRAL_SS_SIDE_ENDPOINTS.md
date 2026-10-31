# A radial central body cannot have two side-supported SS endpoints

**Status:** reviewed hand subcase exclusion; root and independent
mathematical reviews passed on 2026-10-30.
This excludes the E/E endpoint branch of R-VV in
[LSLSLSS_SUPPORT_NORMALIZATION.md](LSLSLSS_SUPPORT_NORMALIZATION.md).
It does not exclude the V/E, E/V, or V/V endpoint branches or close
the whole LSLSLSS signature.

Consider the positive cycle `A-S-C-T-B-V-U-A`, with exactly A,B,C
loaded, two single S paths from C to A,B, and an SS path from A to B.
Assume `79/40<=R<=3/sqrt(2)`. Suppose C is radial-side loaded and its
two contacts are its two inner vertices (row R-VV). Suppose both
endpoint supports at the SS path are side normals (E/E). Applications
at the endpoints of those sides and arbitrary radial circle-load splits
are retained.

We prove these hypotheses impossible.

## 1. Normalize the SS strip and bound the radial axis angle

Rotate the SS direction vertically and name A as the upper endpoint.
Side support fixes the endpoint frames to be axis-parallel:

```text
A=[x_A-1/2,x_A+1/2] x [a,a+1],
B=[x_B-1/2,x_B+1/2] x [-b-1,-b],
a+b=2.
```

The reviewed width-two cap bounds in
[DOUBLE_SIDE_ENDPOINT_CHIRALITY.md](DOUBLE_SIDE_ENDPOINT_CHIRALITY.md)
give

```text
15/16<a,b<17/16,       R^2>=17/4.                     (1)
```

Containment also gives

```text
|x_A|+1/2<=sqrt(R^2-(a+1)^2)<sqrt(191)/16<7/8,
|x_A|<3/8,
|x_B|<3/8.                                          (2)
```

Here `191<196`; the same calculation applies to b.

Write C's radial geometry as

```text
L=sqrt(R^2-1/4)-1,       1<=L<17/16,
e=(cos phi,sin phi),       f=(-sin phi,cos phi),
c_C=(L+1/2)e,
P_+=L e+f/2,       P_-=L e-f/2.                     (3)
```

The two P points are C's inner vertices. Each S path separates its
endpoint centers by a strip of width one. The reviewed transmission
angle bound consequently makes each minor angle from C's center ray
to A's or B's center ray at least pi/2. Thus

```text
e dot (x_A,a+1/2)<=0,
e dot (x_B,-b-1/2)<=0.                              (4)
```

The radial axis cannot be vertical, since the two displayed endpoint
centers have opposite nonzero vertical signs. Reflect in the vertical
axis if necessary so cos(phi)>0. Dividing (4) by that positive cosine,
and using (1)--(2), gives

```text
|tan phi|< (3/8)/(23/16)=6/23,
cos phi>23/24,
|sin phi|<6/23.                                     (5)
```

For the cosine bound, `1+(6/23)^2=565/529<576/529=(24/23)^2`.
No alignment of C's radial axis with the SS strip is assumed.

The inner vertices therefore satisfy the exact useful bounds

```text
(P_+)_x,(P_-)_x
 >=cos(phi)*(L-|tan(phi)|/2)>5/6,
|(P_+)_y|,|(P_-)_y|< (17/16)(6/23)+1/2=143/184<15/16,
(P_-)_y< (17/16)(6/23)-(1/2)(23/24)
         =-223/1104<-1/5,
(P_+)_y>1/5.                                       (6)
```

The upper endpoint A cannot be reached from P_- by a unit S step:
every point of A has height at least a>15/16, so the vertical difference
would exceed `15/16+1/5>1`. Likewise B cannot be reached from P_+.
The actual endpoint contacts therefore are

```text
Q_A=P_++n_A in A,       Q_B=P_-+n_B in B,
|n_A|=|n_B|=1,                                      (7)
```

where n_A,n_B are the actual inward supporting normals on A,B.

## 2. Force balance and contact geometry fix the endpoint corners

Suppose x_A>0. All geometric circle vertices of A then have strictly
positive first coordinate. The positive circle-load resultant has
positive first coordinate as well. The SS force on A is vertical, so
force balance makes `(n_A)_x>0`. Such a supporting normal on the
axis-parallel square exposes its left side, giving
`(Q_A)_x=x_A-1/2<0` by (2). But (7) and (6) would give
`(Q_A)_x=(P_+)_x+(n_A)_x>0`, a contradiction. Thus x_A<=0.
The identical argument gives x_B<=0. Write

```text
x_A=-r_A,       x_B=-r_B,       r_A,r_B>=0.           (8)
```

The cases r_A=0 or r_B=0 are retained: the corresponding endpoint has
two possible circle vertices with arbitrary nonnegative load split.

Now `(n_A)_x>0` is again impossible, since its contact would lie on
A's negative-x left side. If `(n_A)_x=0`, (7) would put its contact
at x-coordinate greater than 5/6, while A's right side is at most 1/2.
Hence `(n_A)_x<0`, and its contact lies on A's right side.

If `(n_A)_y=0`, the contact height would equal `(P_+)_y<a`, outside A.
If `(n_A)_y<0`, the contact would be the upper right vertex, at height
a+1. Its vertical distance from P_+ would exceed
`31/16-143/184>1`, contradicting (7). Therefore `(n_A)_y>0` and the
contact is A's lower right vertex. Reflection gives the corresponding
upper right vertex on B:

```text
Q_A=(1/2-r_A,a),       Q_B=(1/2-r_B,-b).              (9)
```

This classification includes every E-boundary normal at the C-path
endpoints: horizontal and vertical normal alternatives were explicitly
excluded, not silently treated as strict vertex supports.

## 3. The equal circle radii couple the endpoint asymmetry

Because A and B are loaded, (8) gives the exact farthest-corner equations

```text
q=R^2=(r_A+1/2)^2+(a+1)^2
     =(r_B+1/2)^2+(b+1)^2.
```

Put `r=r_A+r_B` and `D=a-b`. Subtraction gives

```text
(r_A-r_B)(1+r)=-4D.                                 (10)
```

The sum of the two radical formulas, or Cauchy--Schwarz with a+b=2,
gives

```text
r+1=sqrt(q-(a+1)^2)+sqrt(q-(b+1)^2)
    <=2sqrt(q-4)<=sqrt(2),
0<=r<5/12,       |D|<1/8.                           (11)
```

The strict rational bound uses `sqrt(2)<17/12`. The formulas remain
valid when either endpoint has two circle vertices.

## 4. The two required unit steps have total squared length below two

Let

```text
S=|P_+-Q_A|^2+|P_--Q_B|^2.
```

Equations (7) require S=2. We derive a strict upper bound below two.
Using (3), (9), q=(L+1)^2+1/4, and a+b=2, direct expansion gives

```text
S=C_0-V_x*cos(phi)-V_y*sin(phi),
C_0=4L^2+4L-3-2r,
V_x=2L*(1-r)+2,
V_y=2L*D-(r_B-r_A)=D*(2L-4/(1+r)).                 (12)
```

The last identity is (10). In particular (3) and (11) give

```text
0<V_x<33/8,
|V_y|<1/4.                                         (13)
```

For the second bound, `4/(1+r)>48/17>17/8>2L`, while
`4/(1+r)-2L<=4-2=2`; multiply by |D|<1/8.

The value at zero axis angle is

```text
C_0-V_x=4L^2+2L-5+(2L-2)r
        <105/64+(1/8)(5/12)=325/192.                (14)
```

Here 1<=L<17/16 makes the expression increasing in both L and r.
Also (5) and the elementary inequality
`1-1/sqrt(1+t^2)<=t^2/2` imply

```text
1-cos(phi)<18/529,       |sin(phi)|<6/23.             (15)
```

Combining (12)--(15),

```text
S=(C_0-V_x)+V_x*(1-cos(phi))-V_y*sin(phi)
 <325/192+(33/8)(18/529)+(1/4)(6/23)
 =192805/101568<2,
2-192805/101568=10331/101568>0.                      (16)
```

This contradicts S=2. The radial central R-VV form with E/E supports
at the SS endpoints is therefore impossible. The remaining SS endpoint
feature combinations require separate arguments; no general R-VV or
whole-signature closure is inferred here.
