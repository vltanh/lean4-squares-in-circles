# The two strict-vertex ends of a width-two path have matching vertical signs

**Status:** reviewed hand lemma; root and independent mathematical reviews
passed on 2026-10-30. This is a
necessary geometric restriction, not a completion bound or a whole-cycle
exclusion.

Let two unit squares K_+,K_- lie in the centered disk of radius R, where
`79/40<=R<=3/sqrt(2)`. Suppose that

```text
K_+ is contained in x>=a,
K_- is contained in x<=-b,
a+b=2.
```

Assume these two supporting lines strictly expose vertices P_+,P_-,
respectively, and that the exposed vertices have the same second
coordinate. Then their positions relative to their own square centers
have the same vertical sign: either both exposed vertices are above
their centers or both are below.

Two consecutive degree-two S transmitters provide exactly the common-height
hypothesis, since their actual equal and opposite forces act on one
horizontal line. No positive circle loads on the endpoint squares are
needed. Side-supported endpoints are outside the assertion.

## 1. Both supporting offsets are close to one

A unit square has horizontal width at least one. Hence
`a,b<=R-1`, and `a,b>=3-R>7/8`. The one-square cap theorem in
[TRANSMISSION_CAP_ANGLE_BOUND.md](TRANSMISSION_CAP_ANGLE_BOUND.md)
therefore applies at both offsets. Existence of the corresponding square
makes its cap-height numerator nonnegative, giving

```text
sqrt(R^2-(a+1)^2)>=1/2,
a<=sqrt(R^2-1/4)-1<=sqrt(17)/2-1<17/16.
```

The same bound holds for b. Using `a+b=2`,

```text
15/16<a,b<17/16.                                    (1)
```

The strict square-root comparison follows from
`17/4=1088/256<1089/256=(33/16)^2`.

## 2. The total absolute center height is below one half

Write the centers as `(x_+,y_+)` and `(-x_-,y_-)`, with x_+,x_->0.
Let phi_+,phi_- be the nonnegative angular deviations of these two
center rays from their respective horizontal rays. The cap theorem
gives

```text
phi_+<=Theta_R(a),       phi_-<=Theta_R(b),
Theta_R(u)=atan((sqrt(R^2-(u+1)^2)-1/2)/(u+1/2)).
```

Its reviewed concavity argument, applied before taking the minor angle
between the two actual rays, gives

```text
phi_++phi_-<=2Theta_R(1)
          <=2atan((sqrt(2)-1)/3).                    (2)
```

This bounds the sum of the two absolute deviations, regardless of the
signs of y_+,y_-. Each center has norm strictly below 25/16. Since sine
is concave on `[0,pi/2]`, and increasing there, (2) implies

```text
|y_+|+|y_-|
 <=(25/16)*(sin(phi_+)+sin(phi_-))
 <=(25/8)*sin((phi_++phi_-)/2)
 <=(25/8)*sin(atan((sqrt(2)-1)/3))
 <(25/8)*(sqrt(2)-1)/3
 <125/288<1/2.                                      (3)
```

Here `sqrt(2)<17/12`, since `2=288/144<289/144`. The last rational
comparison is `125<144`. The strict sine/arctangent comparison is
`sin(atan t)=t/sqrt(1+t^2)<t` for the positive value
`t=(sqrt(2)-1)/3`.

## 3. Each exposed vertex has a large vertical displacement

For either square choose its unsigned frame angle theta in `[0,pi/4]`
and write

```text
c=cos(theta),       s=sin(theta),
w=c+s,             d=c-s.
```

Its horizontal width is w. For K_+, the largest first coordinate is
`a+w<=R`; the reflected statement holds for K_-. Consequently (1) and
`R<=3/sqrt(2)<17/8` give

```text
w<17/8-15/16=19/16,
d^2=2-w^2>151/256>9/16,
d>3/4.                                              (4)
```

The first square-root comparison uses `9/2<289/64`; the second is
`151>144`. In particular the diagonal limiting angle theta=pi/4 is
impossible. Strict vertex support also excludes theta=0. The exposed
leftmost or rightmost vertex is therefore at vertical displacement
`+d/2` or `-d/2` from its center, with a nonzero sign.

Suppose the two exposed vertices had opposite signs. Equality of their
second coordinates would then force

```text
|y_+-y_-|=(d_++d_-)/2>3/4.
```

But the triangle inequality and (3) give
`|y_+-y_-|<=|y_+|+|y_-|<1/2`. This contradiction proves the matching-sign
assertion.

The proof includes arbitrary independent endpoint orientations and either
sign of the common contact height. It does not assert that the common
height itself has the same sign as the vertex displacements, or that a
side-interior endpoint can be assigned one of these two signs.
