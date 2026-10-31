# A radial boundary mask excludes the horizontal leaf at the sole AB owner

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root and
separate independent review.** This closes the entire exactly-one-owner
mixed-mask domain in which the sole owner has an owned West genuine leaf.
It does not claim the remaining strict outer-lower leaf domain.

Keep all nine actual units and the full component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,

in the strict-high range

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60,       R^2<=1105/256.

A,B are physically clear genuine S roots and C,D are positively loaded
physical boundary units. Exactly one root owns AB; name it A, normalize
the actual normal to East, and choose the positive cycle moment.

We use the complete all-mask necessary-domain theorem
ADJACENT_S_LEAF_C4_ONE_OWNER_ALL_MASK_LEAF_REDUCTION.md.
Its horizontal A type is already impossible when D is two-corner.
It remains here to take C two-corner and D unique-corner, with

    A_x=[-d,-epsilon],
    P_AB=(-epsilon,-k),       0<k<1/5.

A's actual vertical unit interval contains zero. Its full A3 equation
makes AD East, with its original mean

    P_AD=(-epsilon,y),       4/5<y<=1.                    (1)

The weak upper endpoint follows from the actual unit interval containing
zero. The force-free height bound and full moment supplying (1) are
Section 4.2 of the cited source. No D alignment or changed mean is used.

The proof places the centers of C and D in two explicit open angular
intervals whose maximum separation is less than pi/6, contradicting the
strict 2*pi/9 separation of physical boundary centers.

## 1. A physical center-angle lemma at the actual D port

The following local conclusion requires only that D is a physical
boundary unit in x>=-epsilon containing (-epsilon,y), with
4/5<y<=1. Its degree, circle mask and other contact are immaterial.

Every contained unit center has norm less than 91/60 by the sharp
center bound d+1/2. Every physical boundary unit center has norm greater
than 27/20: its actual circle corner is at distance 1/sqrt(2) from the
center, so the center norm is at least R-1/sqrt(2). Here
sqrt(2)<17/12 and

    17/4-(27/20+17/24)^2=191/14400>0

prove R-1/sqrt(2)>27/20 throughout the declared strict-high range.

If D owns the horizontal support axis, its center has

    c_D,x=1/2-epsilon,
    c_D,y>=y-1/2>3/10.

If instead the actual port is its strict minimum-x vertex, write the
real square as

    D=(-epsilon,y)+[0,1](p,q)+[0,1](q,-p),
    p,q>0,       p^2+q^2=1.

Its center satisfies

    c_D,x=(p+q)/2-epsilon>=1/2-epsilon,
    c_D,y=y+(q-p)/2>3/10.

In this vertex case physical boundary status forces

    |p-q|>1/2.                                          (2)

Indeed, if |p-q|<=1/2, its opposite corner has squared norm at most

    epsilon^2+y^2+2-2epsilon(p+q)+2y(q-p)
       <=epsilon^2+4<17/4.

Both adjacent corners have squared norm at most
epsilon^2+y^2+1+2y<=epsilon^2+4<17/4 as well, and the original
port is smaller. Thus the whole actual D would be physically clear.
This proves (2). It implies

    p+q<sqrt(7)/2<4/3.

In either complete D feature we therefore have

    29/60<c_D,x<2/3,       c_D,y>0.

Writing its actual center angle as theta_D in the first quadrant,

    cos(theta_D)<(2/3)/(27/20)=40/81<1/2,
    cos(theta_D)>(29/60)/(91/60)=29/91>3/10>cos(5pi/12).

The last strict comparison follows, for example, from
cos(5pi/12)=(sqrt(6)-sqrt(2))/4<3/10.
Consequently

    pi/3<theta_D<5pi/12.                                (3)

This lemma retains the owned-side case and every physical contact
endpoint. It does not use a D2 concurrence or a circle weight.

## 2. The two actual B leaf charts and the radial C corner

The sole-owner theorem supplies the entire actual B frame at P_AB:

    f=(c,s),       j=(s,-c),
    c,s>0,       c^2+s^2=1,
    B=P_AB+[0,1]f+[0,1]j.

In the actual (j,f) coordinates put

    xi=-epsilon*s+k*c,
    w=k*s+epsilon*c,
    B=[xi,xi+1] times [-w,1-w].

The complete actual genuine-leaf cover leaves exactly two types:

* a strict lower adjacent leaf at (U,-w), where U=1+xi,
  U^2+w^2=d^2 and -epsilon<xi<epsilon;
* an owned far-j leaf, with xi=epsilon and radial point (d,0).

Because C has two physical circle corners, the whole radial-boundary
theorem forces BC to be B-owned North at a relative-side-interior
point. Write the unchanged actual point as

    Q_BC=(xi+ell,1-w)=(t,H),
    0<ell<1,       H=1-w,       t>1/2.                  (4)

The strict t bound is part of the actual radial-corner calculation in
RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md,
Sections 2--3. It keeps both original C weights and every CD feature.

We prove the same useful bound in both real leaf types:

    c<1/4.                                             (5)

## 3. The strict B leaf gives (5) directly from its actual North mean

Here w^2<=k^2+epsilon^2<1/25+1/3600, so w<13/60.
Also U>59/60. Let mu be the original AB magnitude and beta scale
the full genuine M force to beta*(U,-w). With nu the original BC
magnitude, the unchanged true B3 equations and moment about P_AB give

    beta*U=mu*s,
    nu=mu*c+beta*w,
    nu*ell=beta*w.

Thus

    ell=s*w/(c*U+s*w).

Equation (4) and xi<epsilon give ell>1/2-epsilon>29/60.
Therefore

    c*U/(s*w)=(1-ell)/ell<31/29,
    c<(31/29)*(13/60)/(59/60)=403/1711<1/4.

This uses the genuine mean ell; no extreme point was substituted.

## 4. The owned B leaf gives (5) with its full perpendicular mean

Here xi=epsilon, so the actual world x coordinate of P_AB gives

    epsilon*s-w*c=-epsilon.

Together with k=epsilon*c+w*s and c^2+s^2=1, this gives

    w=k,       k*c=epsilon*(1+s).                       (6)

The full B3 equations at the actual North mean give

    c*ell=w*s=k*s.

Consequently the original coordinate t in (4) satisfies

    t=epsilon+ell=k/c=(k^2+epsilon^2)/(2epsilon).         (7)

The point is an actual radial C inner corner, so

    t^2+(1-k)^2=d^2+1/4.                                (8)

Since k<1/5, (8) gives

    t^2<2317/3600<25/36.

If k>=1/6, (7) instead gives t>30*k^2>=5/6. Hence k<1/6.
Using (8) again,

    c^2=k^2/t^2
       <k^2/(1/4+2k-k^2)<1/20<1/16.

The middle function increases on 0<k<=1/6 and equals 1/20 at
the upper endpoint; direct differentiation has positive numerator
k/2+2k^2. Thus c<1/4 in this whole owned-leaf type as well.
All original side-mean endpoints were kept until the full equations
and radial corner forced their strict consequences.

## 5. C's actual center lies between pi/4 and pi/2

The preceding bounds give w<13/60<4/15 in both types. At (4), C
minimizes the actual North coordinate. A shared point cannot be an
outer circle corner, so it is the lower inner corner of this radial
square. Its actual radial direction in the (j,f) frame has positive
coordinates (s0,c0), satisfying

    s0,c0>0,       s0^2+c0^2=1,
    H=d*c0-s0/2,       t=d*s0+c0/2.                     (9)

For precision, the positive North support forces c0>0. If the other
radial coordinate s0 were negative, the inner minimum-North corner
would have t=d*s0-c0/2<0. If s0=0, the whole inner minimum-North
side has |t|<=1/2. Both alternatives contradict (4). Thus (9) is
the actual complete radial orientation, not an assumed C frame.

Since H>11/15, the same elementary estimate as in the radial-boundary
source gives

    s0<5/12,       c0>9/10.                             (10)

The actual C radial direction in world coordinates is therefore

    e_C=s0*j+c0*f
       =(s0*s+c0*c, c0*s-s0*c).

By (5),(10), its horizontal component is strictly between zero and

    5/12+1/4=2/3<1/sqrt(2).

Its vertical component is positive, since s>sqrt(15)/4>3/4 and

    c0*s-s0*c>(9/10)(3/4)-(5/12)(1/4)>0.

C's actual center is (d+1/2)e_C, so its center angle satisfies

    pi/4<theta_C<pi/2.                                 (11)

No C circle weight enters this physical angle conclusion.

## 6. Exact whole-interface contradiction and retained scope

Equations (3),(11) give

    |theta_C-theta_D|<pi/6<2pi/9.

This contradicts the strict physical boundary-center separation in
CENTERED_INNER_ARC.md. The original pair C,D is distinct and physically
boundary; both statements are part of the unchanged component.

The two B leaf types are exhaustive in the full sole-owner chart, and
every original BC North mean was retained. The other mixed labeling,
with D radial and A's owned West leaf, was already excluded by the
actual contact-annulus argument in the all-mask reduction. Thus no
exactly-one-owner mixed physical mask has a horizontal genuine leaf
at that sole owner.

The strict outer-lower A leaf remains a separate domain. All original
degrees, radial forces, both C weights including zero, and the three
arbitrary completion squares remain. No grid, deleted edge, altered
normal, numerical pose, compilation, CI, remote action or shared-metadata
change is used.

