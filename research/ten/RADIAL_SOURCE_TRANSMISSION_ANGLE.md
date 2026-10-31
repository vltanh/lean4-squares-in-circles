# A radial-side endpoint strengthens every positive-width transmission angle

**Status:** reviewed exact hand proof; root and independent full mathematical
reviews passed on 2026-10-31, including the cap-domain reductions, both
polynomial identities, the positivity argument, and the angle-budget margin.
The final consequence excludes another entire circle-multiplicity branch
of LSLSLSS. It is not a whole-case completion theorem.

Work in `79/40<=R<=3/sqrt(2)` and put q=R^2. A square with two vertices
on the containing circle is called radial-side here; its two circle
weights need not be equal or both positive. In its own radial frame it is

```text
C=[L,L+1] x [-1/2,1/2],
L=sqrt(q-1/4)-1,       9/10<L<17/16.                 (1)
```

Suppose a transmission path of width W>=1 joins C to any unit square A
in the same disk. The path supplies its usual supporting strip, actual
endpoint contact displacement Wn, and unit inward endpoint normal n.
Let delta be the minor angle between the centers of C and A.

**One-radial-endpoint theorem.** Independently of the circle loading,
orientation, and other forces at A,

```text
delta > pi/2+atan(1/11).                             (2)
```

If both endpoints are radial-side, the additional estimate

```text
delta >= 4 atan(1/(2L)) > 4 atan(8/17)               (3)
```

holds. The use below only needs (3) at width one.

## 1. Reduce the one-radial-endpoint claim to one cap expression

Only C's inner side or its two inner vertices can start such a path.
The two outer vertices are on the containing circle and cannot be shared
with another square. A path from the outer side, top side, or bottom side
would, by the endpoint unit-normal-step lemma, put a point outside the
disk: respectively its radial coordinate is at least L+3, or its
transverse coordinate has absolute value at least 5/2. The boundary
normals at the inner vertices are included in these tests.

Orient the separator normal m toward C. After reflection it makes an
angle gamma in [0,pi/2) with C's outward radial axis e. Set

```text
c=cos(gamma),       s=sin(gamma).
```

C's inner supporting offset in direction m is `L c-s/2`. The opposite
endpoint A is therefore contained in the opposite cap with offset

```text
b=W-Lc+s/2 >= 1-Lc+s/2 > -1/16.
```

Use the reviewed cap function from
[TRANSMISSION_CAP_ANGLE_BOUND.md](TRANSMISSION_CAP_ANGLE_BOUND.md):

```text
Theta_q(a)=atan((sqrt(q-(a+1)^2)-1/2)/(a+1/2)).
```

The theorem applies to offsets at least -1/8. It bounds the angular
deviation of A's center from the outward cap normal by Theta_q(b).
It is decreasing in the offset and increasing in q. Replacing L by
17/16 and q by 9/2 consequently gives

```text
a=1-(17/16)c+s/2,
delta >= pi-gamma-Theta_q(b)
      >= pi-gamma-Theta_{9/2}(a).                    (4)
```

The last cap expression is defined: the actual cap is feasible, and the
replacements only enlarge it. In particular

```text
a>=-1/16,       a<=sqrt(17)/2-1<17/16,
8s-17c<1.                                           (5)
```

We will prove

```text
gamma+Theta_{9/2}(a) < pi/2-atan(1/11),              (6)
```

which implies (2) by (4). The initial angular inequality in (4) is the
triangle inequality for circular distance from e to -m and then to
A's center ray; it does not assume on which side of -m that ray lies.

## 2. An explicit positive polynomial proves the uniform cap bound

Define

```text
U=a+1/2,
V=sqrt(9/2-(a+1)^2)-1/2,
D=11s+c,       N=11c-s.
```

Here U>0, V>=0, and D>0. Also N>0. Indeed, `8sin(gamma)-17cos(gamma)`
strictly increases on [0,pi/2]. At gamma=atan(11) its value is
`71/sqrt(122)>1`, contrary to (5); hence gamma<atan(11).

Put x=tan(gamma/2), so `c=(1-x^2)/(1+x^2)` and `s=2x/(1+x^2)`.
Straight expansion gives the rational identity

```text
(a+1)^2 D^2 + [D/2+N(a+1/2)]^2 - (9/2)D^2
 = P(x)/[128(1+x^2)^3],                             (7)

P(x)=105965x^6+10944x^5+6643x^4+224192x^3
     -130093x^2+8576x+3149.
```

Here is a hand-checkable positivity proof over the whole larger domain
x>=0. The Taylor identity at x=1/3 is

```text
P(1/3+v)
 =105965v^6+222874v^5+(604474/3)v^4
  +(8739952/27)v^3+(3299512/27)v^2
  +(69184/81)v+93824/729.                           (8)
```

For v>=0 every coefficient is positive. For `0<=x<=1/3`, set
`w=1/3-x`, so 0<=w<=1/3. Group the quadratic/cubic and quartic/quintic
terms in (8):

```text
(3299512/27)-(8739952/27)w >=1158584/81>14000,
(604474/3)-222874w >=127200>0.
```

Since `93824/729>128` and `69184/81<855`, dropping the remaining positive
terms gives

```text
P(x) > 128-855w+14000w^2 > 0.                       (9)
```

The last quadratic is positive on the entire real line: its leading
coefficient is positive and
`4*128*14000-855^2=6436975>0`. Thus (7) is strictly positive for every
needed x.

Both sides being positive, (7) implies

```text
sqrt(9/2-(a+1)^2) < 1/2+NU/D,
DV<NU,
11(cU-sV)>sU+cV>0.                                 (10)
```

If G=gamma+Theta_{9/2}(a), equation (10) first gives cos(G)>0.
Here 0<=G<pi, so in fact 0<=G<pi/2. It then says cot(G)>1/11
when G>0; at G=0 the desired conclusion is immediate. Hence
`G<atan(11)=pi/2-atan(1/11)`, proving (6) and the theorem (2).

## 3. Two radial-side endpoints have a stronger elementary bound

Both radial-side centers have radius L+1/2. The general width-one
angle theorem gives delta>=pi/2. Bisect their center angle, and put
theta=delta/2 in [pi/4,pi/2]. Their two inner corners facing one another
then have identical horizontal coordinates and vertical coordinates

```text
+(L sin(theta)-(1/2)cos(theta)),
-(L sin(theta)-(1/2)cos(theta)).
```

These ordinates have the indicated signs by L>9/10 and theta>=pi/4.
The strip of width W>=1 forces the distance between every point of one
square and every point of the other to be at least one. Applying this
to the two displayed corners gives

```text
2L sin(theta)-cos(theta)>=1.                        (11)
```

The left side strictly increases for theta in [0,pi/2]. At
`theta_0=2atan(1/(2L))` it equals one, by the double-angle formulas.
Since L>1/2, theta_0<pi/2. Therefore theta>=theta_0, proving the first
inequality in (3); its strict rational version follows from L<17/16.

## 4. Consequence for the radial central branch of LSLSLSS

Consider loaded endpoints A,B joined by an SS path, and a radial-side
loaded C joined to each by an S path. Suppose at least one of A,B is
also radial-side. Relabel so that A is radial-side. No selected contact
support type at either SS endpoint is assumed.

Write

```text
alpha=4atan(8/17)-pi/2,
beta=atan(1/11),
T=atan((sqrt(2)-1)/3).
```

Equations (2)--(3) and the existing width-two angle theorem give

```text
delta_AC>pi/2+alpha,
delta_BC>pi/2+beta,
delta_AB>=pi-2T.                                    (12)
```

We check exactly that alpha+beta>2T. Here alpha is in (0,pi/2),
and the tangent identities give

```text
tan(alpha)=23359/122400,
tan(alpha+beta)=379349/1323041.
```

The first tangent is positive because `8/17>sqrt(2)-1`;
`(25/17)^2>2` verifies this comparison. The product
`tan(alpha)tan(beta)<1` ensures alpha+beta<pi/2, so these tangent
comparisons preserve the angle order. Also sqrt(2)<17/12 gives

```text
T<atan(5/36),
tan(2atan(5/36))=360/1271,
379349/1323041-360/1271=5857819/1681585111>0.
```

Thus the three minor angles in (12) have sum strictly greater than
2pi. Three rays can never have a sum of pairwise minor angles greater
than 2pi: if all three successive gaps are at most pi, their sum is
exactly 2pi; if one gap exceeds pi, the minor-angle sum is strictly
smaller. This contradiction excludes the stated branch.

Consequently a surviving radial central C in LSLSLSS must have **unique
circle vertices at both SS endpoints A and B**. Their SS supports may
still be mixed E/V or V/V; the earlier E/E exclusion in
[RADIAL_CENTRAL_SS_SIDE_ENDPOINTS.md](RADIAL_CENTRAL_SS_SIDE_ENDPOINTS.md)
remains independent. The conclusion does not exclude the known
numerical U-EE candidate, whose radial-side bodies are the two SS
endpoints while its central body has only one circle vertex.
