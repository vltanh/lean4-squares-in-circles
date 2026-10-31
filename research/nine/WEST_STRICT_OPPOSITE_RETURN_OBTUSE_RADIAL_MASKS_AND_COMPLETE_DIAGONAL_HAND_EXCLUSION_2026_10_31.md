# Both radial masks in the obtuse opposite return, and the entire diagonal feature, are excluded by hand

Date: October 31, 2026 UTC.

**Status: complete hand original-feature exclusions.** In the West/strict,
A-owned perpendicular-singleton opposite return, neither exterior endpoint
can have its exterior-axis physical radial position when the exterior
aperture is at least 90 degrees. These two whole-mask results exclude the
entire original diagonal N feature, at every allowed radius, without the
historical 1,873-node projection certificate.

The B proof uses one concave quadratic and one full-torque comparison.
The C proof uses a continuous trigonometric concavity argument, with four
printed rational comparison intervals, followed by one universal radial
support bound. No finite pose cover or mathematical script supplies a sign.

## 1. The complete unchanged chart and the closed obtuse sector

Retain all nine actual unit squares and their disjoint interiors, the same
circle and origin, the original positive graph and full stars, all physical
contacts, original means, physical circle corners and individual nonnegative
circle coefficients. Use exactly Sections 1--3 of

`WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md`.

In particular the original A,D,N are unloaded true3,true3,true2; V,B,C
are loaded true2. A's and D's original three distinct singleton stars
give the same genuine exterior owners at K,L under the already common
selector. No normal is reselected and no degree is shortened here.

Write

    P=(d,1/2), Q=(d,-t), H=t+1/2, 0<t<=1/2,
    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    a=cos(psi), b=sin(psi), a,b,c,s>0,
    u=a*c-b*s=cos(alpha+psi),
    v=a*s+b*c=sin(alpha+psi),
    E=u-v>0, q=E/b>0,
    x=1-a+H*s in (0,1), y=1-H*c+b in (0,1),
    m=x/y, p=sqrt(1+m^2), B0=d*s+c/2,
    K=P-h+y*e,
    L=(d-u-v,-t-E),
    b_ext=(-m*h+e)/p,
    c_ext=(c*h+(s+q)*e)/sqrt(c^2+(s+q)^2).       (1)

Here v is the positive scalar edge height, not a vector. The actual
D edge vectors remain (-u,v),(-v,-u). Since E>0,

    0<theta=alpha+psi<pi/4.

The complete original V/A/D moments retain

    H-1/2=m*q*B0.                               (2)

The wholly hand adjacent/low-c and continuous-slider sources give

    c>3/4, 0<b<2/5, a>9/10, d<61/60.           (3)

The precise b input is
`PERPENDICULAR_SINGLETON_COMPLETE_CONTINUOUS_SLIDER_GAIN_AND_OPPOSITE_TWO_FIFTHS_EXCLUSION_2026_10_29.md`,
with its printed derivative and two continuous polynomial interval
arguments, not a generated endpoint cover. Its complete larger-b hand
inputs and the unchanged original chart are named in the companion
monotonicity source. No generated b restriction is being imported.

Retaining all nine units, the hand measure proof gives R>2 through
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6,
and the adopted join `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`,
Section 3. Its printed measure has mass 8997/1000<9 and assigns mass
at least one to every actual open unit square. Historical checker programs
are not premises. Thus, more specifically,

    R^2=(d+1)^2+1/4,
    d>sqrt(15)/2-1>117/125.                     (4)

The final rational comparison follows from
15/4-(242/125)^2=119/62500>0.

Let Theta be the clockwise angle from b_ext to c_ext. The closed
obtuse sector treated in Sections 2--5 is precisely

    Theta>=pi/2,
    m>=m0=(s+q)/c=(a/b)*(1-s/c)-1.             (5)

Every equality endpoint in (5) remains. The previously proved complete
aperture bound Theta<3pi/4 remains available, but is not needed for the
two radial exclusions below.

## 2. A genuine radial B port gives one exact angle inequality

Suppose B has its entire physical radial position along b_ext:

    B=[d,d+1]*b_ext+[-1/2,1/2]*w,
    w=Jrot(b_ext).

The original genuine K port has K.b_ext=d and |K.w|<1/2.
Put eta=atan(1/m), so 0<eta<pi/2 and

    b_ext=-cos(eta)*h+sin(eta)*e,
    w=-sin(eta)*h-cos(eta)*e.

Let A=alpha+eta. Since alpha<pi/4, 0<A<3pi/4. Expanding the
original support identity K.b_ext=d gives

    d*(1+cos(A))
       =cos(eta)+y*sin(eta)+(1/2)*sin(A).        (6)

Set X=-K.w. Substituting (6) into its exact other coordinate yields

    X-1/2
       =tan(A/2)*(cos(eta)+y*sin(eta))
          -sin(eta)+y*cos(eta).                 (7)

The genuine original side interval gives X<1/2. Its positive
denominator in (7) implies sin(eta)-y*cos(eta)>0 and then

    tan(A/2)<tan(eta-atan(y)).

Both comparison angles lie in (0,pi/2), so

    alpha+2*atan(y)<eta.                        (8)

This identity uses the same actual radial square and the original port;
it does not choose a new side coordinate. It is independent of the
two individual original circle weights.

## 3. The whole obtuse B-radial mask is impossible

### 3.1. All q>=1/4 by one concave quadratic

Assume q>=1/4 and write z=tan(alpha)=s/c. The original D-return
identity, divided only by positive c, gives

    q*b/c=a-b-(a+b)*z.

Consequently

    0<z<=T=(a-5*b/4)/(a+b).                     (9)

The upper endpoint T is positive, since a>9/10 and b<2/5.
Define the scalar quadratic

    F(z)=[(a/b)*(1-z)-1]*(a^2*z+2*b)
             -(a^2-2*b*z).

Its leading coefficient is -a^3/b<0, so it is concave. At zero,

    F(0)=2*a-2*b-a^2>0,

using a>9/10, b<2/5 and a^2<1. Direct expansion at the other
endpoint in (9) gives exactly

    16*(a+b)^2*F(T)
       =4*a^2-73*a^3*b+72*b*(1-2*b^2).         (10)

The elementary bound sqrt(1-b^2)<=1-b^2/2 gives

    a^3<=(1-b^2)*(1-b^2/2).

Thus the right side of (10) is at least

    J(b)=4-b-4*b^2-(69/2)*b^3-(73/2)*b^5.

Every nonconstant coefficient is negative, so J decreases on [0,2/5].
Its exact endpoint value is

    J(2/5)=1182/3125>0.

Therefore F(T)>0. Concavity proves F(z)>0 over the entire interval
(9), not just at its endpoints.

If alpha+2atan(b)>=pi/2, it already exceeds eta. Otherwise its
tangent has positive denominator a^2-2bz. The inequality F(z)>0
then says

    m0*tan(alpha+2*atan(b))>1,
    alpha+2*atan(b)>atan(1/m0)>=eta,

where the final comparison uses the original obtuse inequality (5).
Since the original y=1-Hc+b>b, this contradicts (8). This covers
the entire q>=1/4 interval, including q=1/4.

### 3.2. All 0<q<1/4 by the full original torque

Now suppose 0<q<1/4. From (5), m>s/c, so eta<pi/2-alpha.
Together with the same genuine port inequality (8), this gives

    y<tan(pi/4-alpha)=(c-s)/(c+s)
       =(b/a)*(1+q/(c+s))
       <b*(1+q)/a.                              (11)

Here c+s>1 and q>0. Therefore

    H*c=1+b-y
       >1-b*(1-a+q)/a
       >1-7/45=38/45.                           (12)

For the last bound use a>9/10, 1-a<1/10, b<2/5 and q<1/4.
Since H<=1, (12) implies c>38/45>5/6. Hence

    s<sqrt(11)/6<5/9,
    B0<(61/60)*(5/9)+1/2=115/108<13/12.          (13)

The squared comparison for sqrt(11)/6<5/9 is 891<900.

The original y>b and tan(psi/2)=b/(1+a)<b give

    alpha+2*atan(y)>alpha+2*atan(b)>alpha+psi=theta.

Thus (8) implies m=cot(eta)<cot(theta)=u/v. On the other hand

    u-v=q*b<1/10,
    u^2+v^2=1

force u/v<5/4. Indeed u/v>=5/4 would give v<=4u/5,
u>=5/sqrt(41), and u-v>=u/5>=1/sqrt(41)>1/10.
Consequently m<5/4. The unchanged full torque (2), with (13), gives

    H<1/2+(5/4)*(1/4)*(13/12)=161/192<38/45.

The last comparison has positive cross-product difference
38*192-161*45=51. It contradicts (12), since Hc<=H.

The two exhaustive q intervals prove:

**Theorem 3.1.** In the whole original closed obtuse opposite-return
sector, B cannot have its exterior-axis physical radial position.

## 4. One continuous angle theorem for every obtuse opposite return

**Theorem 4.1.** The entire original sector (5) satisfies

    v=sin(alpha+psi)>8/15.                       (14)

This theorem does not assume either endpoint mask or use their equations.
It uses the original A ratio, the opposite D direction and H<=1.

### 4.1. Reduce the whole angle domain to one explicit concave function

For fixed actual a,b,c,s, m(H) increases with H and has positive
denominator up to one. Thus (5) also holds at the scalar comparison
endpoint H=1. Write x1=1-a+s and y1=1-c+b. Multiplying the
endpoint inequality by positive b gives

    F=bc*x1-(bs+E)*y1>=0.                       (15)

No full torque is imposed at this auxiliary endpoint. Put

    theta=alpha+psi, eta=theta/2,
    delta=(alpha-psi)/2 in (-eta,eta),
    u=cos(theta), v=sin(theta),
    f=cos(eta)-sin(eta)=sqrt(1-v)>0.

A direct expansion of twice the same expression F is

    g(delta)=2*F
       =3*v-u-cos(2*delta)-sin(2*delta)
          +f*((u-3*v)*cos(delta)+(u-v)*sin(delta)
                         +cos(3*delta)+sin(3*delta)).     (16)

For example,

    x1=1-f*(cos(delta)-sin(delta)),
    y1=1-f*(cos(delta)+sin(delta)),
    bc=(v-sin(2*delta))/2,
    bs+E=(u+cos(2*delta)-2*v)/2,

which verify (16) by multiplication. We prove g<0 throughout
0<v<=8/15 and |delta|<=eta. This contradicts (15).

On this whole comparison domain,

    u>21/25, f>17/25, u-v>0,
    0<eta<pi/10.

The first two rational bounds follow by squaring. For the angle bound,
sin(theta)<=8/15<sin(pi/5); the latter comparison follows from
sin(pi/5)>sin(pi/6)=1/2 together with the exact square formula,
or directly from sin(pi/5)^2=(5-sqrt(5))/8>64/225.
For the direct formula, sqrt(5)<9/4 gives (5-sqrt(5))/8>11/32>64/225.

For 0<=delta<=eta, subtracting (16) at opposite arguments gives

    g(delta)-g(-delta)
       =2*sin(delta)*[-2*cos(delta)
          +f*(u-v+3-4*sin(delta)^2)].            (17)

The bracket is bounded below by

    -2+f*(1+3*u-v)
       >-2+(17/25)*(224/75)=58/1875>0.

Thus g(-delta)<=g(delta); it suffices to treat delta>=0.

Since eta<pi/10,

    cos(3*delta)+sin(3*delta)
       >=cos(2*delta)+sin(2*delta)>=1.           (18)

The first difference is
2*sin(delta/2)*[cos(5*delta/2)-sin(5*delta/2)]>=0.
Differentiating (16) twice and using (18) gives

    g''(delta)
       <=(4-9*f)*(cos(2*delta)+sin(2*delta))
          +f*(3*v-u)*cos(delta).                (19)

The discarded term is -f*(u-v)*sin(delta)<=0. If 3v-u<=0,
(19) gives g''<=4-9f<-53/25. If 3v-u>0, it gives

    g''<=4-f*(9-3*v+u)
        <4-(17/25)*(206/25)=-1002/625<-8/5.      (20)

In particular g is strictly concave throughout this full positive
delta interval.

### 4.2. The entire first interval 0<v<=3/8

Direct substitution and differentiation at delta=eta give

    g(eta)=-2*(u-v)*(1-u)<0,
    g'(eta)=2*[u*(1-3*v)+v^2].                  (21)

For v<=1/3 the derivative is positive. For 1/3<=v<=3/8,
the coefficient 1-3v is nonpositive and u<=1, so

    u*(1-3*v)+v^2>=1-3*v+v^2>=1/64>0.

The final polynomial decreases on that whole interval and takes 1/64
at 3/8. Concavity makes g' decreasing, so g'(delta)>=g'(eta)>0
for 0<=delta<=eta. Therefore g(delta)<=g(eta)<0 throughout
this complete first v interval.

### 4.3. Four continuous comparisons cover every remaining v

At zero the exact values are

    g(0)=-(1-f)*(1+u-3*v),
    g'(0)=-2+f*(3+u-v).                         (22)

On each interval below, the displayed rational constants satisfy
g(0)<-A, g'(0)<B and g''<-K on the entire delta interval.

| Whole v interval | A | B | K | A-B^2/(2K) |
| --- | ---: | ---: | ---: | ---: |
| [3/8,21/50] | 2/15 | 41/50 | 51/20 | 19/12750 |
| [21/50,23/50] | 19/160 | 2/3 | 11/5 | 281/15840 |
| [23/50,1/2] | 9/100 | 8/15 | 9/5 | 89/8100 |
| [1/2,8/15] | 12/175 | 5/12 | 8/5 | 5773/403200 |

Here are the full interval checks, so the table is not an unproved sign
list. On all four intervals 3v-u>0, so the curvature bound is
K<f*(9-3v+u)-4 from (20).

* On [3/8,21/50], use f<19/24, f>19/25, u>9/10 and
  u-v<14/25. The last comparison follows from u<93/100 at v>=3/8.
  These give (1-f)(1+u-3v)>(5/24)(16/25)=2/15,
  g'(0)<491/600<41/50, and
  f*(9-3v+u)-4>1604/625>51/20.
* On [21/50,23/50], use f<61/80, f>73/100, u>22/25 and
  u-v<49/100 (because u<91/100 at v>=21/50). Then the first
  product is greater than (19/80)(1/2)=19/160,
  g'(0)<5289/8000<2/3, and the curvature quantity is greater
  than (73/100)(17/2)-4=441/200>11/5.
* On [23/50,1/2], use f<147/200, f>7/10, u>43/50 and
  u-v<43/100 (because u<89/100 at v>=23/50). Then the first
  product is greater than (53/200)(9/25)=477/5000>9/100,
  g'(0)<10421/20000<8/15, and the curvature quantity is greater
  than (7/10)(209/25)-4=463/250>9/5.
* On [1/2,8/15], use f<5/7, u>21/25 and u-v<3/8
  (because u<7/8 at v>=1/2). Then the first product exceeds
  (2/7)(6/25)=12/175, and g'(0)<23/56<5/12.
  The full-domain bound (20) gives K=8/5.

Every square-root comparison just used follows by squaring positive
rationals against u^2=1-v^2 or f^2=1-v at the stated interval endpoint.
All joining endpoints are included. Integrating the uniform curvature
bound for each fixed v gives

    g(delta)<-A+B*delta-(K/2)*delta^2
             <=-A+B^2/(2*K)<0.                 (23)

Together with (17),(21), the four rows prove g<0 over the entire
comparison domain. This contradicts (15), and proves (14).

## 5. The whole obtuse C-radial mask has radius less than two

Suppose C has its entire exterior-axis physical radial position along
-c_ext. Then its original maximum-c_ext support L satisfies

    L.c_ext=-d.

In world coordinates c_ext is proportional to (1+q*s,q*c), whose
two entries are strictly positive. Write c_ext=(cos(chi),sin(chi))
with 0<chi<pi/2, and put U=u+v. The same original L in (1) gives

    d*(1+cos(chi))
       =U*cos(chi)+(t+E)*sin(chi).              (24)

For z=tan(chi/2)>0 and the original t<=1/2, this implies

    d=(U/2)*(1-z^2)+(t+E)*z
       <=U/2+(1/2+E)*z-(U/2)*z^2
       <=U/2+(1/2+E)^2/(2*U)
        =(9/4+E)/(2*U),                        (25)

where U^2+E^2=2 was used. This is a whole positive quadratic bound;
no angle or radius is chosen to make an auxiliary value physical.

Theorem 4.1 gives v>8/15. Therefore

    E=u-v<(sqrt(161)-8)/15<8/25,
    U^2=2-E^2>1186/625>(11/8)^2.                (26)

For the first rational comparison use sqrt(161)<64/5. The second
has positive cross-product difference 1186*64-121*625=279.
Equations (25)--(26) force

    d<257/275<117/125,

contrary to (4). The last positive cross-product difference is
117*275-257*125=50.

**Theorem 5.1.** In the whole original closed obtuse opposite-return
sector, C cannot have its exterior-axis physical radial position.
This proof retains both physical C circle vertices and every original
individual coefficient. It uses neither physical uniqueness nor a
chosen circle mean at C.

## 6. Complete original diagonal exclusion and exact side consequences

Keep the original unloaded true2 N. If it is a diagonal transmitter,
the initially common incident-diagonal avoidance makes the actual T,U
relative-side-interior points of B,C. Both endpoints therefore own its
same original direction n, and their actual square frames are parallel.

The already common three-singleton owner theorem gives the same
genuine b_ext,c_ext axes from (1). Their determinant is strictly
negative, so they are nonparallel. As own axes of parallel square
frames, they must therefore be perpendicular. Thus Theta=pi/2,
which is included in all preceding theorems.

The strict support-cone identity in
`WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md`
and the complete loaded-endpoint theorem
`LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`
put n in the closed positive cone of b_ext,c_ext. That theorem
explicitly retains both side and diagonal lengths, all parallel cases,
coincident original applications, full means and physical-zero masks.
Since n is a common own axis, only n=b_ext or n=c_ext remains.

In the first direction B's two complete incoming forces are parallel;
the full parallel theorem makes B physically radial along b_ext,
contrary to Theorem 3.1. In the second direction the same full theorem
makes C physically radial along -c_ext, contrary to Theorem 5.1.
Every original diagonal direction is excluded. This proves the entire
original opposite-return diagonal feature by hand, with all actual
completion squares and every full original star retained.

For an original side N, the previous complete aperture/mask theorem
already covers every original direction by B exterior-axis radial,
C exterior-axis radial, or two physically unique endpoints with
45<delta_B,delta_C<90 and 90<Theta<135 degrees. Theorems 3.1
and 5.1 now put either radial alternative strictly in Theta<90.
At Theta=90 there can be no side channel at all: the two intermediate
angles add to 90, so one is at most 45 and the full closed-cone
theorem makes its endpoint radial, already excluded here.

Thus the exact remaining opposite side obligations have disjoint
angular domains: an acute exterior aperture with at least one radial
endpoint, or the strict two-unique obtuse sector. The central pentagon
is already empty throughout the latter by the complete hand area theorem.
Neither remaining whole side domain is declared excluded in this source.

No generated 1,873-node certificate, generated radial or unique-endpoint
cover, changed mean, altered normal, shortened star, Lean build or CI is
a dependency of these proofs. The continuous rational table in Section 4
is justified in full by the displayed derivatives and inequalities.
No original parent flag or complete nine-unit theorem is claimed closed
solely from this feature.

