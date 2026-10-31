# The full opposite-return obtuse sector has a strict angle floor and one-sided point monotonicity

Date: October 31, 2026 UTC.

**Status: complete hand reductions, not a whole feature exclusion.** In the
original West/strict A-owned perpendicular-singleton opposite return,
an exterior aperture at least 90 degrees forces sin(alpha)>1/5.
Throughout that whole sector, the squared norm of the actual contained
B point decreases strictly as the scalar roof slider H increases to one.
This compares an original point with an explicit auxiliary endpoint;
it does not move a square or impose the full torque at that endpoint.

## 1. Original data, radius, and wholly hand entries

Retain all nine actual squares, the original containing circle and its
center, all physical contacts, original positive forces, full means,
true degrees, physical circle masks and individual nonnegative circle
weights. Use the complete chart and notation of

`WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md`,

Sections 1--3. Thus the original A3,D3,V2 stars and original B,C,N
applications remain. No endpoint force equation is shortened here.
Write

    h=(c,-s), e=(s,c), c^2+s^2=1, c,s>0,
    a^2+b^2=1, a,b>0,
    1/2<H<=1,
    x=1-a+H*s in (0,1), y=1-H*c+b in (0,1),
    m=x/y, p=sqrt(1+m^2),
    E=a*(c-s)-b*(c+s)>0,
    q=E/b>0,
    B0=d*s+c/2,
    P=(d,1/2), K=P-h+y*e,
    b_ext=(-m*h+e)/p, w=Jrot(b_ext),
    R^2=(d+1)^2+1/4.                              (1)

The hand adjacent-return/low-c theorem gives c>3/4. The whole hand
opposite-component theorem

`PERPENDICULAR_SINGLETON_COMPLETE_CONTINUOUS_SLIDER_GAIN_AND_OPPOSITE_TWO_FIFTHS_EXCLUSION_2026_10_29.md`

gives 0<b<2/5. Its printed derivative compensation, continuous
slider-gain polynomial comparisons and joining endpoints are the
dependency here, not a generated side, diagonal or endpoint cover.
That source's larger-b inputs are the complete hand comparisons in

* `PERPENDICULAR_SINGLETON_FULL_STAR_OPPOSITE_LARGE_COMPONENT_AND_RETURN_RATIO_EXCLUSION_2026_10_29.md`;
* `PERPENDICULAR_SINGLETON_UPPER_RETURN_ANGLE_COMPENSATION_AND_LARGE_SIDE_COMPONENT_EXCLUSION_2026_10_29.md`.

The full original V/A/D moments still give

    H-1/2=m*q*B0.                                (2)

All nine actual squares are retained when using the hand R>2 theorem.
Its explicit analytic path is
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
with the fixed values and derivative in
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6,
joined in `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.
The printed measure has mass 8997/1000<9 and gives every contained
unit square mass at least one, so disjointness excludes nine units
in the radius-two disk. Historical checker programs are not inputs.
Consequently

    14/15<d<61/60.                               (3)

Indeed sqrt(15)/2-1>14/15 because
15/4-(29/15)^2=11/900>0. The upper comparison is the unchanged
original radius-window bound.

The original actual minimum-b_ext support at K ensures that
K+b_ext belongs to the same physical B. This is true for any
original endpoint degree and every original support-face mean.

## 2. A uniform strict floor for the entire closed obtuse sector

Let Theta be the actual clockwise exterior-axis aperture. In the
notation of the aperture theorem,

    Theta=pi/2+atan(m)-atan((s+q)/c).

Suppose Theta>=pi/2, including its exact orthogonal boundary. Then

    m>=(s+q)/c=(a/b)*(1-s/c)-1.                  (4)

For fixed a,b,c,s, m(H)=(1-a+Hs)/(1-Hc+b) increases strictly
with H. Its denominator stays positive all the way to H=1. Thus

    m<=m1=(1-a+s)/(1-c+b)
       <=b/(1+a)+s/b,                           (5)

where 1-a=b^2/(1+a) and 1-c+b>=b. Combining (4),(5), and
multiplying by positive b, gives

    2*a-b-1<=s*(1+a/c).                         (6)

If s<=1/5, then c^2>=24/25>(97/100)^2, so c>97/100.
Also b<2/5 gives a^2>21/25>(91/100)^2, hence a>91/100.
The two sides of (6) then satisfy

    2*a-b-1>21/50,
    s*(1+a/c)<(1/5)*(1+100/97)=197/485<21/50.

The last rational comparison has positive numerator
21*485-197*50=335. This contradicts (6). We have proved

    s>1/5                                      (7)

on the entire original Theta>=pi/2 sector. No full endpoint
equation, physical B/C mask, N transmission length or endpoint
mean has been used in this floor.

## 3. A positive original moment with a fixed rational reserve

Define the scalar

    M_B=m*B0+d*c-s/2-1+x.                       (8)

It is the exact original origin moment in the positive normalization
whose A exterior force is -m*h+e:

    M_B=p*det(K,b_ext), K.w=-M_B/p.              (9)

Since q>0, (4) gives m>s/c. Since x=1-a+Hs>Hs>s/2,
equations (3),(7) imply

    M_B > (s/c)*(d*s+c/2)+d*c-s/2-1+x
        =d/c-1+x
        >14/15-1+1/10=1/30.                    (10)

This is an original full-moment identity and a hand lower bound.
It does not replace either original loaded endpoint's circle force
by a selected corner or discard an individual zero coefficient.

## 4. The actual contained point has a scalar endpoint comparison

Fix the original a,b,c,s,d and introduce only the auxiliary scalar
variable z in [H,1]. Set

    x(z)=1-a+z*s, y(z)=1-z*c+b,
    m(z)=x(z)/y(z), p(z)=sqrt(1+m(z)^2),
    b(z)=(-m(z)*h+e)/p(z), w(z)=Jrot(b(z)),
    X(z)=P-h+y(z)*e+b(z).                       (11)

The notation b(z) denotes the unit vector in this section, not
the fixed positive scalar b of (1). No auxiliary point in (11)
is asserted to belong to a new square or to obey (2).

The denominator y(z)>=1-c+b>0. Direct differentiation gives

    m'(z)=[s*y(z)+c*x(z)]/y(z)^2>0,
    X'(z)=-c*e+[m'(z)/p(z)^2]*w(z).             (12)

The obtuse inequality (4) persists along this scalar interval,
because m increases and the right side stays fixed. The proof of
(10), with z in place of H, therefore gives the same strict
positive bound for M_B(z). Also

    X(z).e=B0+y(z)+1/p(z)>0,
    X(z).w(z)=-M_B(z)/p(z).

Consequently

    d|X(z)|^2/dz
       =-2*c*(B0+y(z)+1/p(z))
          -2*m'(z)*M_B(z)/p(z)^3
       <0.                                     (13)

The whole scalar comparison is therefore

    |K+b_ext|^2=|X(H)|^2>=|X(1)|^2,             (14)

with strict inequality when H<1. The radius in (14) is the
same original radius, because d was fixed. The endpoint is explicit:

    y1=1-c+b, x1=1-a+s, m1=x1/y1,
    X(1)=(d,1/2)-h+y1*e
            +(-m1*h+e)/sqrt(1+m1^2).           (15)

Thus any original point in this entire closed obtuse sector whose
endpoint (15) has norm greater than R is impossible by actual B
containment. This is a one-sided necessary comparison, not a claim
that the endpoint alone excludes the whole sector.

For completeness the ordinary height decreases too. With
gamma(z)=atan(m(z))-alpha and alpha=atan(s/c), (4) implies
0<gamma(z)<pi/2, and

    X(z)_Y=1/2+s+c*y(z)+cos(gamma(z)),
    dX(z)_Y/dz=-c^2-sin(gamma(z))*m'(z)/(1+m(z)^2)<0.

## 5. Exact retained torque equation and the remaining step

Solving the original A ratio for the original H gives

    H=[m*(1+b)+a-1]/(m*c+s).

Combining it with the same original full torque (2), without
selecting a quadratic root, gives the exact necessary equation

    q*B0*c*m^2
      +[q*B0*s-(1+b-c/2)]*m
      +(1-a+s/2)=0.                              (16)

Both possible roots, a repeated root, H=1, and every original
circle-weight endpoint remain before the following complete sector
argument. No general root ordering is assumed solely from obtuseness.

### 5.1. The entire q>=3/5 sector selects the upper root by hand

Write the polynomial in (16) as

    P_m(z)=L*z^2+B1*z+B,
    L=q*B0*c>0, B=1-a+s/2>0,
    m0=(s+q)/c.

Suppose q>=3/5. Since B0>=c/2, while b<2/5 and a>9/10,

    L*m0^2=(q*B0/c)*(s+q)^2
             >=(3/10)*(s+3/5)^2,
    B=b^2/(1+a)+s/2<8/95+s/2.

The exact identity

    (3/10)*(s+3/5)^2-(8/95+s/2)
       =(3/10)*(s-7/30)^2+17/2280>0             (17)

therefore proves L*m0^2>B. An original positive root m exists
by the original full torque. The product of the two roots is B/L>0;
since one root is positive, both are positive. The smaller one is
at most their geometric mean sqrt(B/L), which is strictly below
m0. Hence every original m>=m0 in this whole sector is necessarily
the larger root. A repeated root would equal the geometric mean
and cannot be in this obtuse sector.

This also yields a useful exact endpoint consequence. As a polynomial
in the same original H, the full torque is

    F(H)=(H-1/2)*(1-H*c+b)
             -q*B0*(1-a+H*s)=0.

Its leading coefficient is -c<0. On positive m the inverse formula
H(m)=[m(1+b)+a-1]/(mc+s) has positive derivative numerator
s(1+b)+c(1-a). For either positive root of (16), the same algebra
also gives H=1/2+m*q*B0>1/2 and

    1-H*c+b=[s*(1+b)+c*(1-a)]/(m*c+s)>0.

Thus the correspondence preserves both roots and their order.
The original obtuse solution is its larger H root.
Since this original H is at most one, F(1)<=0. Dividing by the
strictly positive y1=1-c+b gives

    m1*q*B0>=1/2.                               (18)

Equality is allowed and is exactly the original H=1 endpoint in
this sector. The full torque has not been imposed at an auxiliary
endpoint. Equation (18) is a consequence of its genuine root order.

For 0<q<3/5, neither this root-order conclusion nor (18) is asserted.
The physical containment premise must continue to be retained there;
obtuseness alone is not a justified replacement for it.

Equations (7), (10), and (13)--(18) are complete continuous hand
reductions for the full closed obtuse sector. They do not exclude
every radial endpoint, the whole diagonal channel, the whole
two-unique side channel, or the entire original load row. No
generated certificate, mathematical script, normal reselection,
changed mean, shortened star, Lean build or CI is a proof input.

