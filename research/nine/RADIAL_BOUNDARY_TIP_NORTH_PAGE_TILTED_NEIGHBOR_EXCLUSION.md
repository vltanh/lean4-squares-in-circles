# A radial boundary tip cannot meet the tilted North neighbor

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root
and separate independent review.** This excludes the entire tilted-C
part of the one-owner, radial-D North/North interface. It applies to
both surviving genuine B-leaf types. Every actual side mean and both
original D circle weights, including an individual zero, remain.

Keep the same nine actual units and the positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q_*=1105/256.

A is the sole owner of AB. C has one physical circle corner, whereas
D has two physical circle corners and is therefore an actual radial
S square. We work in the exact retained North/North domains of

- ADJACENT_S_C4_OWNED_TILTED_LEAF_NORTH_CONTACT_REDUCTION.md;
- ADJACENT_S_C4_STRICT_TILTED_ROOT_NORTH_CONTACT_REDUCTION.md.

The local proof below is common to those two complete reductions.
Their literal original-domain substitutions are checked in Section 5.

The actual root A and its unchanged application mean are

    A=[-X,h] times [-v,1-v],
    X=1-h, X^2+v^2=d^2, |h|<=epsilon,
    P_AB=(h,-k), 0<k<v<13/50,
    P_AD=(-t_D,1-v), t_D=X*k/v>1/2.                  (1)

The radial-boundary theorem gives the actual identity

    t_D^2+(1-v)^2=d^2+1/4.                           (2)

B's actual positively oriented axes are

    j=(s,-c), f=(c,s), c,s>0, c^2+s^2=1.

The actual BC normal is f. Write its entire original mean in B's
(j,f) frame as

    P=(t,T), T=1-w.

For the common local argument we need only the necessary bounds

    0<v<1/5, 0<w<3/20,
    c/s<1/4, 0<t<=d.                                (3)

C is tilted at this original North application. No orientation or
equation is assigned to either root by calling C a two-force unit.

Every original cycle edge has an actual side-axis owner by
ADJACENT_S_C4_ONE_OWNER_RADIAL_MASK_ALL_CYCLE_OWNERS.md.
This is the compatible pose-fixed-mean theorem for this mixed mask,
not the unique/unique force-cycle selection. In particular it
retains every original CD mean and does not choose its owner.

## 1. The actual radial D is almost North in B's frame

In world coordinates let the real radial direction of D be

    e_D=(-sigma,chi), sigma,chi>0, sigma^2+chi^2=1.

The complete radial-boundary feature theorem gives

    t_D=d*sigma+chi/2,
    1-v=d*chi-sigma/2.                               (4)

The other inner corner of the same actual D is

    Q_D=(-d*sigma+chi/2,d*chi+sigma/2).

First,

    sigma<1/3, chi>14/15.                            (5)

Otherwise chi<=sqrt(8)/3<17/18, and (4) would imply

    1-v<(61/60)*(17/18)-1/6=857/1080<4/5,

contrary to (3). The chi bound follows by squaring.

In B's actual (j,f) frame put

    eta=sigma*s+chi*c,
    zeta=chi*s-sigma*c.

Thus the radial and transverse axes of D and its other inner corner
are exactly

    e_D=(-eta,zeta),
    n_D=(zeta,eta),
    Q_D=d*e_D+(1/2)*n_D.                             (6)

Equations (3),(5) give zeta>0, eta>0 and

    r=eta/zeta
      =[(sigma/chi)+(c/s)]/[1-(sigma/chi)*(c/s)]
      <[(5/14)+(1/4)]/[1-(5/14)*(1/4)]
      =2/3.                                         (7)

The full original D-to-C feature cover is therefore:

- a strict normal at the fixed other inner corner Q_D, in the
  cone between -e_D and n_D;
- the actual transverse side normal n_D, with actual mean
  Q_D+z*e_D, 0<=z<=1.

The radial inner-face normal is excluded by the genuine physical
boundary-neighbor theorem, and the outer features cannot contain
another boundary body. These are the complete original features
from RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md,
applied to D with its actual positive cycle orientation.

Every normal in this cover has strictly positive j coordinate.
No D circle weight has been removed to obtain the cover.

## 2. The complete actual tilted-C frame

Apply only the local high vertical-port fact in Section 1 of
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md.
Its hypotheses are exactly: a genuine loaded C2, one physical
circle corner, its other neighbor physically boundary, and an
actual incoming North point (t,T), t>0, T>37/50. They hold by
(3). Its proof does not require parallel root frames.

Since C is tilted at this point, its actual full square is

    C=P+[0,1]a0+[0,1]b0,
    a0=(a,b), b0=(-b,a), a,b>0, a^2+b^2=1.

Its one physical circle corner and necessary inequalities are

    Z_C=P+a0=(t+a,T+b),
    t*b-T*a>1/2,
    a/b<1/2, b>8/9.                                 (8)

The opposite circle corner is excluded by the genuine proper
radial point inside this unique-corner C, including zero proper
distance. All tilted frames and their axis limits are accounted
for by the local fact; the axis-owned case is deliberately left
to the separate parallel-C proof.

Let N be the original D-to-C unit normal, with positive magnitude
kappa. C's full equation is

    F_C=nu*(0,1)+kappa*N, nu,kappa>0.

Its original full circle resultant is a positive multiple of Z_C.
By (8),

    Z_C.b0=-t*b+T*a<-1/2,
    (0,1).b0=a>0.

Consequently

    N.b0<0.                                         (9)

This is the entire original C2 equation. The radial D2 equation
has not been replaced by a single-corner equation.

Because CD has an actual side owner, there are now precisely two
possibilities. D ownership is N=n_D. If instead C owns the axis,
the positive j coordinate of N from Section 1 and (9) leave only

    N=-b0.                                          (10)

The other three C axes have either negative j coordinate or
nonnegative b0 component. We keep both owners and their complete
actual mean intervals in the next two sections.

## 3. D-owned CD puts C's actual circle corner beyond R

Suppose N=n_D=(zeta,eta). Equations (7),(8) give

    N.a0>0, N.b0<0.

Thus the actual minimum-N point of C is its vertex P+b0.
It is also the unchanged D-side mean

    P+b0=Q_D+z*e_D, 0<=z<=1.                          (11)

Let q_C be C's genuine positive radial concurrence. The original
BC line is the vertical line through P. At (11), properness gives

    q_C=P+b0+rho*N, rho>=0.

Its horizontal coordinate forces rho=b/zeta. Hence

    q_C=(t,T+a+b*r).

The actual unique-corner conclusion q_C=lambda*Z_C gives
lambda=t/(t+a), and therefore the exact unchanged identity

    t*[b*(1-r)-a]=a*(T+a+b*r).                        (12)

Consider the actual vector from the CD point to the real circle
corner:

    Z_C-(P+b0)=a0-b0.

Its radial and transverse components in D's frame are

    A_r=e_D.(a0-b0)
       =(zeta*a/t)*[T+a+r*(b-t)],

    B_t=n_D.(a0-b0)
       =zeta*[(1+r)*b+(1-r)*a].                       (13)

The first formula follows by substituting (12). Both are strictly
positive. For A_r use

    T-r*t>17/20-(2/3)*(61/60)=31/180>0;

for B_t use 0<r<2/3. Also A_r^2+B_t^2=2, because a0 and b0
are perpendicular unit axes. Therefore A_r+B_t>sqrt(2).

The actual point (11) has D-frame coordinates (d+z,1/2).
Adding the actual vector (13), without changing any mean, gives

    |Z_C|^2-R^2
      =1-2d+2d*A_r+B_t+2z*(d+A_r)+z^2
      >1+sqrt(2)-2d+(2d-1)*A_r
      >11/30.                                       (14)

The last inequality uses sqrt(2)>7/5 and d<61/60.
This contradicts the fact that Z_C is a real circle corner.
The original endpoints z=0 and z=1 were included throughout.

## 4. C-owned CD cannot reach D's actual inner corner

Now suppose N=-b0=(b,-a). Its negative f coordinate prevents
D-side ownership, whose normal n_D has both coordinates positive.
The actual D application is therefore its fixed inner corner Q_D.

The actual minimum-N side of C has b0 coordinate one. Keep its
entire original mean:

    Q_D=P+b0+z*a0, 0<=z<=1.                           (15)

Write the original BC proper radial point as

    q_C=P+u*(0,1)=lambda*Z_C, u>=0.

By (8) and its horizontal coordinate,

    u=(t*b-T*a)/(t+a)>1/[2*(t+a)].

The CD line through (15), parallel to -b0, has fixed a0
coordinate z relative to P. The same actual concurrence thus
gives

    z=b*u.                                          (16)

The actual circle corner has height

    T+b>17/20+8/9>26/15.

Since R^2<=Q_*<40/9, this implies t+a<6/5. Consequently
(8),(16) give

    z>10/27,
    (Q_D)_f-T=a+z*b>80/243.                           (17)

But the original inner D corner has norm

    |Q_D|=sqrt(d^2+1/4)<17/15.

Together with T>17/20 this gives the opposite strict bound

    (Q_D)_f-T<17/60.

The exact reserve is

    80/243-17/60=223/4860>0.

This contradiction includes both possible original side-mean
endpoints; the equations themselves force a strict interior value.
No original mean was selected for convenience.

## 5. Both literal original B-leaf callers satisfy the local hypotheses

We verify (3), keeping the two B leaves separate.

First, (1)--(2) give the exact scalar identity

    k^2=v^2*[1+(2v-3/4)/(d^2-v^2)].                   (18)

For 0<v<13/50, the numerator 2v-3/4 is negative and d>1.
Thus

    k^2>F(v),
    F(v)=v^2*(1/4+2v-v^2)/(1-v^2).                   (19)

F is strictly increasing in this interval. Its positive bracket
has derivative (2+2v^2-3v/2)/(1-v^2)^2>0.
At v=1/5,

    F(1/5)=61/2400>9/400,
    F(1/5)-9/400=7/2400.                             (20)

### 5.1. B has its owned far-axis genuine S leaf

The complete owned-leaf North reduction gives
0<w<3/20, and c/s<1/4 specifically when the actual C is tilted.
It also proves that v>43/240 implies k<3/20.

If v>=1/5, that implication applies, while (19)--(20) give
k^2>9/400, a contradiction. Hence v<1/5.
The actual North mean lies on B's real side [epsilon,d],
so 0<t<=d. These are exactly all four hypotheses in (3).

### 5.2. B has its strict lower-adjacent genuine S leaf

The complete strict-leaf North reduction, including the physical
deep-root capacity exit, gives k<3/20 and c/s<1/4.
Equations (19)--(20) again yield v<1/5.

Its actual B chart and already proved near-root inequality are

    B=[xi,U] times [-w,1-w], U=1+xi,
    U^2+w^2=d^2,
    h=xi*s-w*c, k=xi*c+w*s,
    xi*(1+s)>w*c.

They imply the exact strict inequality

    k-w=c*[xi-w*c/(1+s)]>0.

Thus 0<w<k<3/20. The unchanged actual North mean lies on
the real side [xi,U], with 0<t<=U<d. Again every hypothesis
in (3) holds, with no owned-leaf formula imposed on this
strict-leaf root.

## 6. Exact conclusion

Both possible actual CD owners have been excluded in Sections 3--4.
Section 5 supplies two complete original-domain callers. Therefore
the entire radial-D / unique-C North/North interface with C tilted
at BC is impossible, for either surviving actual genuine B-leaf type.

The C-parallel-to-B alternative remains separate. This source keeps
the full original six-body graph, true A3/B3/C2/D2 degrees,
both D circle weights, every actual mean and all nine physical units.
It does not use a radial-D proper point inside D, a unique-D mask,
a deleted root force, post-extraction normal selection or a new pose.
No numerical search, compilation, CI, remote action or shared
metadata edit is a premise.

