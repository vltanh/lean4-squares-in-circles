# A whole-domain hand C-cap obstruction excludes the far-return radial-B mask

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of the remaining original Type II
far-return B-radial/C-unique side mask.** In fact the new local
inequality excludes every radial-B instance of this full hub chart
with q<=1/3, without any equation or physical circle mask at C,N.
It contradicts the actual contained-unit cap at C using the original
radial support at B and the full original A,D,V chart.

The proof uses one explicit whole-interval polynomial table. Every
coefficient below is obtained by the displayed finite polynomial
identities; it is not a generated pose cover or a numerical sample.
The entire radial/radial and C-radial/B-unique masks have separate
hand completion proofs and are not used as premises of this local
inequality.

## 1. Original feature, actual radial support and the necessary C-cap inequality

Retain all nine actual unit squares, the same circle and origin,
the complete original A3,D3,V2,B2,C2,N2 stars, all positive
contact magnitudes and normals, every original application and
full side mean, and all physical circle corners with their
individual nonnegative coefficients.

The feature is the unique-physical-circle V, Type II D-owned
roof-direction contact with the strict far A return. N is an
unloaded true2 and is in its side alternative. The exact hand
chart and original radial-mask entry are recorded in

    UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md,
    TYPE_II_FAR_SIDE_COMPLETE_PHYSICAL_RADIAL_ENDPOINT_MASK_ALTERNATIVE_2026_10_29.md,
    TYPE_II_FAR_SIDE_UNIFORM_C_TANGENT_BOUND_AND_COMPLETE_RADIAL_C_AXIS_REDUCTION_2026_10_29.md,
    TYPE_II_FAR_RETURN_B_RADIAL_GAP_AND_COMPLETE_RADIAL_MASK_HAND_REDUCTION_2026_10_31.md.

The last source proves that B radial and C physically unique
imply q<1/3. The already accepted full-chart lower bound q>1/5
and z<11/12 are retained, although the new inequality below
works on the larger comparison interval 0<=q<=1/3.

Use the original oriented frame (d0,n), and distinguish the
radial scalar D from the physical hub D_hub:

    D=sqrt(R^2-1/4)-1,
    0<e<1/2, J=sqrt(1+e^2),
    M=sqrt((1+e)^2+(1+q)^2),
    d=(1-e)/J, L=(1+e)/J,
    P=sqrt(1+q^2),
    z=(1+e)/(1-e)*(1-J^3/M),
    F=(1,z), Z=lambda*F, lambda>0,
    H=(1+e)/M, k=(1+q)/M.

These are full original hub and V equations. In particular Z
is the original physical V circle corner, not a chosen point on
the same ray. The actual exterior applications satisfy

    Q_B=Z-D_B,
    D_B=(d+H*(1+e)+k, L-k),
    Q_C.y=lambda*z-L-1.                       (1)

The actual inward B axis is f=(-1,q)/P. In the present mask
B is physically radial along f, so its original exterior
application has

    Q_B.f=D.                                  (2)

No equality between its two circle coefficients is assumed.
The full unchanged genuine B side coordinate and every possible
coefficient endpoint remain in this mask.

The identity

    D_B.x-q*D_B.y=M+d-q*L

follows directly from M^2=(1+e)^2+(1+q)^2. Thus (1)--(2)
give the exact original radial-support equation

    lambda*(1-q*z)=M+d-q*L-D*P.                (3)

The actual C, regardless of its support owner or circle mask,
obeys the universal contained-unit maximum-n cap

    Q_C.y>=-D,
    lambda*z>=L+1-D.                          (4)

Here Q_C is the unchanged maximum-n support, including a full
original side mean. This is the same force-free unit cap proved
in the universal cap source; it does not make C radial.

The actual hand domain has 1-q*z>0. Multiply (4) by that
positive number and use (3). The result is the necessary
inequality

    Ccap(e,q,D):=L+1-D-z*G <=0,
    G=M+d+q-D*(P+q).                          (5)

No division by 1-z*(P+q) is made; that expression can have
either sign. In particular (5) retains the original cap without
selecting a mean, circle coefficient or channel direction.

The same-nine analytic hand R>2 theorem and the unchanged upper
radius give

    117/125<D<61/60.                          (6)

Use `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections
1--3, `NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`,
Sections 2--6, and the accepted hand join in
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`, Section 3.
The printed measure mass is 8997/1000<9. No historical
computational measure certificate is a dependency. For the
convenient lower comparison in (6),
15/4-(242/125)^2=119/62500>0. For the upper comparison,
(121/60)^2+1/4-1105/256=31/57600>0.

We now prove the uniform strict opposite of (5):

    Ccap(e,q,D)>29/1000                       (7)

throughout the larger closed comparison domain

    0<=e<=1/2, 0<=q<=1/3,
    117/125<=D<=61/60.

The strict original intervals and all their possible coefficient
endpoints are thereby included at once.

## 2. The entire q interval reduces monotonically to q=1/3

The comparison formulas are defined with positive denominators
on the whole closed domain. Write A=1+e and B=1-e in the
scalar calculations below; these two letters denote scalar
expressions only, not replacements for the physical units.

First M>J^3 throughout the domain, since

    M^2-J^6
      >=1+2*e-2*e^2-3*e^4-e^6
      >=19/64>0.

Consequently z>0. Also P+q is increasing in q and

    D*(P+q)<(61/60)*(25/18)=305/216<17/12,

using sqrt(10)<19/6. Since M>=sqrt(2)>7/5 and
d>=1/sqrt(5)>2/5, one has G>23/60>0.

At fixed e,D,

    dz/dq=(A/B)*J^3*(1+q)/M^3>0,
    dG/dq=(1+q)/M+1-D*(1+q/P)>13/90>0.        (8)

For the last bound, (1+q)/M>=2/sqrt(13)>1/2,
q/P<=1/3 and D<=61/60. Thus

    d(Ccap)/dq=-(dz/dq)*G-z*(dG/dq)<0.         (9)

The smallest comparison is therefore at q=1/3. This changes
only the scalar formula for a necessary inequality, not any
physical square or original force ratio.

For the rest of the proof set

    q=1/3, P=sqrt(10)/3,
    M=sqrt(A^2+16/9),
    z=(A/B)*(1-J^3/M).

## 3. Two exact derivative identities and a uniform lower bound for dz/de

At fixed q=1/3 and D, direct differentiation gives

    L'=B/J^3,
    G'=-z*B/J^3.                              (10)

The second identity follows from
M'=A/M and d'=-A/J^3. Therefore

    Ccap'=(B/J^3)*(1+z^2)-z'*G.               (11)

We first establish the whole-interval bound

    z'>B=1-e.                                (12)

Put r=J/M and C=2+3*e+2*e^2-3*e^3. Differentiating the
exact z formula and collecting terms gives

    z'=[2-C*r+A^2*B*r^3]/B^2.                (13)

The convenient rational upper bound

    r<=u:=(15-2*e)/25<=3/5                    (14)

has a complete positive squared comparison:

    (15-2*e)^2*M^2-625*J^2
       =(e/9)*(2550-4580*e-468*e^2+36*e^3)
       >=(143/9)*e>=0.

Both sides compared in (14) are positive. Further,
A^2*B<=32/27 on [0,1/2], as follows by differentiating
1+e-e^2-e^3, whose maximum occurs at e=1/3. The cubic
2-C*r+A^2*B*r^3 therefore strictly decreases as r ranges
over [0,3/5]: its r derivative is at most

    -2+3*(9/25)*(32/27)=-18/25<0.

It is enough to substitute u in (13). Expanding, exactly,

    15625*(2-C*u+A^2*B*u^3-B^3)
       =250+23275*e-66420*e^2+44397*e^3
            -2588*e^4-172*e^5+8*e^6.           (15)

For a whole-interval positivity check, the quadratic

    Q(e)=23275-66420*e+44397*e^2

decreases on [0,1/2] and has Q(1/2)=4657/4.
At the same time

    2588*e^3+172*e^4<=1337/4.

Group the right side of (15) as
250+e*Q(e)-e*(2588*e^3+172*e^4)+8*e^6. It is greater
than or equal to 250+830*e+8*e^6>0. Thus the numerator
in (13) is strictly greater than B^3, proving (12).

## 4. A whole-interval lower bound for G

We will use

    G>19/12-e/2.                              (16)

First the exact z formula has the simple linear upper bound

    z<=2/5+(6/5)*e.                           (17)

For a direct hand verification, (17) is equivalent to

    5*A*J^3>=M*(3+e+6*e^2).

All terms are positive. After squaring and multiplying by nine,
the difference is

    225*A^2*(1+e^2)^3
       -(25+18*e+9*e^2)*(3+e+6*e^2)^2
      =e*(138-214*e+330*e^2-99*e^3
                  +594*e^4+576*e^5+450*e^6+225*e^7).

It is nonnegative throughout [0,1/2]:
138-214*e>=31, 330*e^2-99*e^3>=0, and the remaining
terms are nonnegative. Equality at e=0 is retained.

Since J^3>=(1+3*e^2/2), (17) gives

    (1/2)*J^3-z*B
      >=1/10-(4/5)*e+(39/20)*e^2>0.            (18)

The last quadratic has positive leading coefficient and
discriminant -7/50. By (10), (18) yields G'>-1/2.
At e=0,

    G(0)=3-D*(sqrt(10)+1)/3>19/12,

using the same bound D*(P+q)<17/12 as in Section 2.
Integrating G'>-1/2 proves (16) on the entire comparison
interval. This is a scalar derivative argument, not a motion
of the original square configuration.

## 5. One explicit positive-polynomial table gives the remaining ratio bound

We next show, uniformly on [0,1/2],

    (1+z^2)/J^3<19/12-e/2<G.                  (19)

The first elementary comparison is r=J/M>5/9. Indeed

    81*J^2-25*M^2=56*e^2-50*e+104/9>0;

the discriminant is -796/9. In particular

    z<U:=A*(4-5*e^2)/(9*B).                   (20)

All factors are positive on the closed interval. The following
lower radical bound is also exact:

    J^3>=T:=1+(3/2)*e^2+(1/3)*e^4.            (21)

Its squared reserve is

    (1+e^2)^3-T^2=e^4*(1/12-e^4/9)>=0,

strict for e>0, since e^4<=1/16. At e=0 equality is
harmless. Both compared sides are positive.

It remains to prove 1+U^2<(19/12-e/2)*T. Multiplication
by the positive factor 5832*B^2 gives exactly the polynomial

    R(e)=2250-12024*e+24813*e^2-29232*e^3
             +26757*e^4-15102*e^5+3222*e^6-972*e^7.
                                                               (22)

For transparency, before expansion this is

    R(e)=81*B^2*(19-6*e)*(6+9*e^2+2*e^4)
               -5832*B^2-72*A^2*(4-5*e^2)^2.

Here is one finite exact coefficient table proving positivity
over the whole interval, rather than at sampled points. Set
t=2*e, so 0<=t<=1. The identity

    13440*R(t/2)
      =sum_{k=0}^7 beta_k*binom(7,k)*t^k*(1-t)^(7-k)

has the following strictly positive integer coefficients.

| k | beta_k |
| ---: | ---: |
| 0 | 30240000 |
| 1 | 18696960 |
| 2 | 11124000 |
| 3 | 6117984 |
| 4 | 2917944 |
| 5 | 1103040 |
| 6 | 387180 |
| 7 | 408240 |

One direct way to check every entry without evaluating a pose
is to use the coefficient list

    c=(30240000,-11543040,3970080,-1403136,
                       642168,-302040,96660,-102060)

and the exact formula

    beta_k=sum_{i=0}^k binom(k,i)*c_i.

This is the ordinary power-to-Bernstein identity: c_i is the
coefficient of t^i in 13440*R(t/2), divided by binom(7,i).
Expanding either displayed form reproduces (22). Every
Bernstein basis term is nonnegative on [0,1], and their sum
is one. Thus R(e)>0 at every point, including both endpoints.

Equations (20)--(22) imply

    1+z^2<1+U^2<(19/12-e/2)*T
                      <=(19/12-e/2)*J^3.

The multiplying factor 19/12-e/2 is positive. This proves
the first part of (19), while (16) proves the second.

## 6. Monotonicity in e and the single endpoint cap contradiction

Combine (11),(12),(19). Since G>0 and B>0,

    Ccap'
      =(B/J^3)*(1+z^2)-z'*G
       <B*((1+z^2)/J^3-G)<0.                  (23)

Thus the smallest comparison over the entire e interval is at
e=1/2. At q=1/3,e=1/2 the exact quantities are

    J=sqrt(5)/2,
    M=sqrt(145)/6,
    d=1/sqrt(5), L=3/sqrt(5),
    z_*=3-45/(4*sqrt(29)),
    P+q=(sqrt(10)+1)/3.

Here 9/10<z_*<11/12. For the lower bound use
sqrt(29)>43/8, which gives z_*>39/43>9/10. For the upper
bound use sqrt(29)<27/5, which gives z_*<11/12.
Since P+q>4/3,

    d(Ccap(1/2,1/3,D))/dD=z_*(P+q)-1>1/5>0.

The smallest D comparison is therefore D0=117/125.
At this one endpoint, elementary radical comparisons give

    L>67/50,
    M<201/100,
    d<9/20,
    P+q>83/60.

Consequently

    G<201/100+9/20+1/3-(117/125)*(83/60)
       =11239/7500<3/2.

Both G and z_* are positive. The exact cap reserve is now

    Ccap(1/2,1/3,117/125)
       >67/50+1-117/125-(11/12)*(3/2)
        =29/1000>0.                           (24)

The monotonicities (9),(23) and the final D comparison prove
(7) on its entire enlarged closed domain. Equation (7)
contradicts the actual necessary inequality (5).

## 7. Complete original conclusion and literal scope

Every original Type II far-return B-radial/C-unique side mask
has q<1/3 by the complete hand radial-gap theorem. It retains
the full original formula for z and the actual radial support
and C cap (1)--(4), as well as all nine units for (6).
Sections 2--6 therefore exclude this entire mask, including
every original side mean, every physical circle-coefficient
endpoint and the full original continuous angle domain.

The new local theorem is stronger: any instance of this full
A/D/V chart with B physically radial and q<=1/3 violates
actual containment at C. The inequality does not use C's
physical uniqueness, a C or N force equation, a chosen B
transverse coordinate, or the V-circle norm equation after
the original support identities are obtained. The original
full stars and actual means remain present in its caller.

The radial/radial mask with larger q and the complementary
C-radial/B-unique mask have their separate complete hand
proofs. This manuscript supplies the missing B-radial/C-unique
entry for the full far-return hand assembly; that assembly
must retain its original physical-mask cover and diagonal exit.
No whole original fine/coarse row is declared closed here.

All scalar expansions, derivative bounds, radical comparisons
and the complete positive coefficient table are printed above.
The polynomial table proves one inequality over one whole
interval and contains no subdivision tree, pose test or
generated exclusion. No external mathematical proof script,
Lean/Lake, CI or numerical certificate is a proof input.
