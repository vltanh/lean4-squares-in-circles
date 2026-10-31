# Both D-owned West charts exclude the entire physical-two B mask by hand

Date: October 31, 2026 UTC.

**Status: complete hand physical-mask exclusion.** In the physical-two
West/strict chart, with the strict roof owned by A and the genuine AD
normal owned only by D, the actual exterior B cannot have two physical
circle corners. The result covers both a genuine West DV contact and
a physically shared West DV contact, retaining the entire original
shared mean and either zero individual circle coefficient. It uses
the full A3/D3/V2 data and physical B containment, without an equation
at B, C or N. No generated pose cover is used.

This source does not exclude the complementary physically unique B
feature, and does not change an original-row closure flag.

## 1. A radius-free radial-side lemma

Let d>0, P=(d,1/2), and use actual orthonormal vectors

    h=(cos(alpha),-sin(alpha)), e=J*h,
    0<alpha<pi/2,
    K=P-h+y*e, 0<y<1,
    b=(-M*h+e)/sqrt(1+M^2), w=J*b, M>1.

Suppose that for an angle delta satisfying

    0<delta<=alpha, delta<pi/4,
    M*y=1-(1-y)*tan(delta).                     (1)

Then K cannot be a genuine relative-side-interior point of the
minimum-b side of the radial unit square

    [d,d+1]*b+[-1/2,1/2]*w.                    (2)

### Proof

Set eta=atan(1/M), so 0<eta<pi/4, and psi=alpha+eta.
Thus 0<psi<3*pi/4, and

    b=(-cos(psi),sin(psi)),
    w=(-sin(psi),-cos(psi)).

The exact two projections of the unchanged point K are

    K.b=-d*cos(psi)+(1/2)*sin(psi)
                           +cos(eta)+y*sin(eta),
    K.w=-d*sin(psi)-(1/2)*cos(psi)
                           +sin(eta)-y*cos(eta).

If K belonged to the indicated genuine side in (2), then K.b=d
and K.w>-1/2. The first equation is

    d*(1+cos(psi))
                 =cos(eta)+y*sin(eta)+(1/2)*sin(psi).

Substitute it in the strict second inequality and use
sin(psi)/(1+cos(psi))=tan(psi/2). The half terms cancel exactly,
leaving

    tan(psi/2)*(cos(eta)+y*sin(eta))
                           <sin(eta)-y*cos(eta).       (3)

The left side is positive. Consequently eta-atan(y)>0, and
the quotient of the right side by its positive factor on the
left is tan(eta-atan(y)). Both angles are in (-pi/2,pi/2).
The strict monotonicity of tangent in (3) therefore gives

    alpha<eta-2*atan(y).                       (4)

In particular eta>alpha>=delta. Write a=tan(eta), k=tan(delta),
so 0<k<a<1. Identity (1), with M=1/a, gives exactly

    y=a*(1-k)/(1-a*k).

The denominator is positive, and

    y-(a-k)
       =k*((1-a)+a*(a-k))/(1-a*k)>0.           (5)

On the other hand (4) gives

    y<tan((eta-alpha)/2)
      <=tan((eta-delta)/2)
       <tan(eta-delta)
        =(a-k)/(1+a*k)<a-k.                   (6)

All angles in these comparisons lie strictly between 0 and pi/4.
Equations (5) and (6) contradict each other. This proves the lemma.

## 2. Common actual physical entry

Retain the same original contained, interior-disjoint unit squares
and the already selected common normal certificate. The original
radius window gives

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, 9/10<d<61/60.

The full positive stars are the unloaded A3,D3 and loaded V2,
with unchanged positive magnitudes mu,nu,gamma on AV,DV,AD.
B and C may have arbitrary further positive edges and loads.

The actual physical-two V is

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,1/2-j).

Its two physical circle corners and the entire nonnegative
coefficient interval are retained. Put

    h=(c,-s), e=(s,c), c=cos(alpha), s=sin(alpha),
    A=P-[0,1]*h+[-ell,1-ell]*e,
    0<ell<1, y=1-ell,
    W=P-ell*e, K=P-h+y*e,
    B0=d*s+c/2.

In both charts, the original AB force strictly exposes the actual
A vertex K. The three A contacts P,W,K are distinct genuine
singletons. The existing unchanged common selector therefore makes
B own the actual AB direction b, at a genuine minimum-b
relative-side-interior point K. These are the hand geometric and
owner reductions in Sections 2--4 of
`PHYSICAL_TWO_WEST_STRICT_D_OWNED_GENUINE_ROOF_COMPLETE_EXCLUSION_2026_10_30.md`
and Section 4.1 of
`PHYSICAL_TWO_SHARED_WEST_D_OWNED_FINITE_PLACEMENT_AND_CHANNEL_REDUCTION_2026_10_30.md`.
Only those hand chart reductions are imported; neither source's
generated exclusion is used.

For a contained unit square with two physical circle corners in
this radius window, those corners are adjacent. Indeed opposite
equal-radius corners force the center to be zero, hence all four
corners have radius 1/sqrt(2), which is outside this window.
In an actual own frame, equality of the two adjacent corner radii
forces the transverse center coordinate to vanish. The nonzero
other coordinate determines the outward radial axis.

In particular, if K.b>0, the B center has b-coordinate K.b+1/2>0.
A physical-two B must then have exactly position (2). The possible
radial axes w,-w would give center b-coordinate zero, and -b would
give it negative sign. This is a physical conclusion, independent
of whether either individual circle coefficient is zero.

It remains to establish K.b>0 and (1) in each whole actual chart.

## 3. Physically shared West DV

Here the complete actual chart has

    0<alpha<pi/4, 1/2<j<=1,
    D=[d-1,d] x [-1/2-ell*c,1/2-ell*c].

The original Q remains its entire shared-side mean. The full
unchanged hub and V equations are, with m=mu/gamma and n=nu/gamma,

    m*y=c-s,
    n*(j-1/2)=m*B0,
    n*(1-j+ell*c)=1-ell*s.                   (7)

The unchanged force into B is

    gamma*(-m*c,1+m*s)
       =gamma*c*(-M*h+e),
    M=(m+s)/c.

Using the first equation in (7) gives

    M*y=1-ell*tan(alpha).                    (8)

Since tan(alpha)<1 and y=1-ell, (8) implies M>1. Thus (1)
holds with delta=alpha.

We verify K.b>0 without assuming its physical circle mask.
Since d>1/2 and s+c>1, B0>1/2. The full V equation in (7),
including j=1, consequently gives m<n.

If ell<=1/2, then y>=1/2 and m=(c-s)/y<2, so

    M<(2+1)/c<3*sqrt(2)<6.

If ell>=1/2, the full D equation, with j<=1, gives

    n<1/(ell*c)<=2/c,
    M<(2/c+s)/c<2/c^2+1/c<4+sqrt(2)<6.

In both cases M<6. The fixed scalar P_h=P.h=d*c-s/2 obeys
P_h<d<61/60. Therefore

    K.b=[M*(1-P_h)+B0+y]/sqrt(1+M^2)>0,       (9)

because its numerator is greater than -6/60+1/2=2/5.

If B had two physical circle corners, (9) would force precisely
the radial position (2). The radius-free lemma, using (8),
contradicts its unchanged genuine contact K. This excludes the
entire physical-two B mask in the physically shared West chart.

## 4. Genuine West DV

Retain the full genuine chart, with no endpoint replacement:

    1/2<j<1, pi/4<beta<pi/2,
    nD=(C,S), tD=(-S,C), C=cos(beta), S=sin(beta),
    H=c*S+s*C, k=s*S-c*C,
    H>k>0, H^2+k^2=1,
    pi/2<alpha+beta<3*pi/4,
    D=Q-[0,1]*nD+[0,1]*tD,
    ell=j*S/H in (0,1), v=j*s/H in (0,1), t=1-v.

The full original torque identities are

    mu*y=gamma*(H-k),
    gamma*t=nu*(S-C),
    nu*(j-1/2)=mu*B0.                         (10)

In particular, writing tau=j-1/2, their necessary product equality is

    tau*y*t=(H-k)*(S-C)*B0.                  (11)

Define

    delta=alpha+beta-pi/2 in (0,pi/4),
    epsilon=pi/2-beta in (0,pi/4).

Then alpha=delta+epsilon, H=cos(delta), k=sin(delta),
S=cos(epsilon), C=sin(epsilon). In particular delta<alpha.

### 4.1. A hand whole-domain lower bound alpha>pi/8

Suppose alpha<=pi/8. Both delta and epsilon are then below pi/8.
Since cos(pi/8)-sin(pi/8)>1/2 and cos(pi/8)>9/10,

    H-k>1/2, S-C>1/2, S>9/10.

For completeness, the first strict comparison follows after
squaring from 1-1/sqrt(2)>1/4; the second follows from
cos(pi/8)^2=(2+sqrt(2))/4>81/100. Also B0>1/2, because
d>1/2 and c+s>1 in the assumed angular interval.
Consequently the right side of (11) is greater than 1/8.

But H<=1, y=1-j*S/H<1-(9/10)*j, and 0<t<1 give

    tau*y*t
      <(j-1/2)*(1-(9/10)*j)
       =121/1440-(9/10)*(j-29/36)^2
       <=121/1440<1/8.                        (12)

This contradicts (11). Hence alpha>pi/8 throughout the actual
genuine-West chart. No containment or exterior equation was used
for this angular bound.

### 4.2. The same radial-side contradiction

The unchanged force into B is

    -(mu+gamma*k)*h+gamma*H*e,
    b=(-M*h+e)/sqrt(1+M^2),
    M=(mu/gamma+k)/H.

Using the first equation in (10) yields

    M*y=1-ell*(k/H)=1-ell*tan(delta).         (13)

Since tan(delta)<1, again M>1, and (13) is exactly (1).

The lower angle bound in Section 4.1 gives s>sin(pi/8)>1/3.
The last rational comparison follows from
sin(pi/8)^2=(2-sqrt(2))/4>1/8>1/9, using sqrt(2)<3/2.
Therefore

    P_h=d*c-s/2<d-1/6<17/20<1.

As B0>0 and y>0, the same exact numerator in (9) is strictly
positive. Thus K.b>0, and any physical-two B must have (2).
The radius-free lemma, now with 0<delta<alpha, excludes it.

## 5. Scope and retained data

Both whole D-only West charts have now lost their entire physical-two
B mask by the same hand lemma. No normal is changed, no shared mean
is chosen, and no individual circle coefficient is forced positive.
All actual original units and contacts stay in place. The argument
is valid on the entire original radius window and does not require
the same-nine improvement R>2.

The result uses no balance equation at B, C or N. It therefore
applies to the stated D02.L135 and D02.L1345 features and to any
larger actual positive component carrying the same original full
A3/D3/V2 chart and the unchanged common owner reduction at K.
The remaining physically unique B features require their own
complete hand exclusions.
