# A radial boundary tip excludes the parallel North neighbor of a strict S root

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root
and separate independent review.** This closes the C-parallel part of
the one-owner, strict-B-leaf, radial-D North/North interface. The
original C2/D2 equations, both physical D circle corners and every
actual contact mean remain.

Keep all nine actual squares and the positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q_*=1105/256.

A alone owns AB. Both real root leaves are strict. C has one
physical circle corner; D has two, so it is its actual radial S
square with both original circle weights, including a possible
individual zero. Use the exact complete North reduction
ADJACENT_S_C4_STRICT_TILTED_ROOT_NORTH_CONTACT_REDUCTION.md:

    A=[-X,h] times [-v,1-v],
    X=1-h, X^2+v^2=d^2, |h|<=epsilon,
    P_AB=(h,-k), 0<k<v<13/50, k<3/20;

    j=(s,-c), f=(c,s), c,s>0, c^2+s^2=1,
    B=[xi,U] times [-w,1-w] in its actual (j,f) frame,
    U=1+xi, U^2+w^2=d^2, 0<xi<epsilon,
    h=xi*s-w*c, k=xi*c+w*s,
    xi*(1+s)>w*c, p=c/s<1/4.

The two original outer normals and their entire actual means are

    AD North, P_AD=(-t_D,1-v), t_D=X*k/v>1/2;
    BC f, P_BC=(t,T), T=1-w,
    t=xi+w/(pU+w)=k/[c+s*w/U], 0<t<=U<d.             (1)

The different owned-B formula t=k/c is not assigned to this strict
leaf. Assume here that C owns f at its actual incoming contact;
thus its actual frame is parallel to B. The other frame is the
separate complete theorem
RADIAL_BOUNDARY_TIP_NORTH_PAGE_TILTED_NEIGHBOR_EXCLUSION.md.

## 1. Exact radial and strict-root identities

The radial-boundary feature theorem gives

    t_D^2+(1-v)^2=d^2+1/4.

Together with the unchanged mean in (1), this gives

    k^2/v^2=1+(2v-3/4)/(d^2-v^2),

    k^2>F(v),
    F(v)=v^2*(1/4+2v-v^2)/(1-v^2).                   (2)

The numerator 2v-3/4 is negative throughout 0<v<13/50, so the
strict inequality follows from d>1 in the displayed direction.
The positive bracket in F has derivative

    (2+2v^2-3v/2)/(1-v^2)^2>0.

Thus F increases on this entire interval. Since

    F(1/5)=61/2400>9/400,

the actual k<3/20 forces v<1/5.

The strict B geometry gives, without a new force equation,

    k-w=c*[xi-wc/(1+s)]>0,

    w^2=k^2+h^2-xi^2>k^2-epsilon^2,
    h+k*p=xi*sqrt(1+p^2),                            (3)

    xi<epsilon-w^2/(2d).

The last bound follows from
U=sqrt(d^2-w^2)<d-w^2/(2d), since w>0. Consequently

    0<w<k<3/20, 0<v<1/5.                            (4)

These identities retain the strict real B leaf and its actual
AB vertex. No owned-leaf equation has been imported.

## 2. The entire original CD owner cover

Let D's real radial direction in world coordinates be

    e_D=(-sigma,chi), sigma,chi>0,
    sigma^2+chi^2=1.

Its actual AD corner and other inner corner are

    t_D=d*sigma+chi/2, 1-v=d*chi-sigma/2,

    Q_D=(-d*sigma+chi/2,d*chi+sigma/2).                (5)

Since v<1/5, equation (5) gives

    sigma<1/3, chi>14/15.                            (6)

Indeed sigma>=1/3 would imply
1-v<(61/60)*(17/18)-1/6=857/1080<4/5,
using sqrt(8)/3<17/18.

In B's actual frame define

    eta=sigma*s+chi*c,
    zeta=chi*s-sigma*c.

Thus eta,zeta>0, eta^2+zeta^2=1, and

    e_D=(-eta,zeta), n_D=(zeta,eta),
    Q_D=d*e_D+(1/2)*n_D.                             (7)

The complete radial-boundary feature theorem leaves exactly
the strict other-inner-corner cone between -e_D and n_D, or
the transverse side n_D with its full mean Q_D+z*e_D,
0<=z<=1. Every such normal has positive j component.
The actual radial inner face cannot support the physical boundary
neighbor C. Outer circle features are likewise excluded by the
same complete physical theorem.

The mixed-mask all-cycle-owner theorem
ADJACENT_S_C4_ONE_OWNER_RADIAL_MASK_ALL_CYCLE_OWNERS.md
supplies an actual owner of CD before extraction. Thus either

- D owns CD with normal n_D and its whole original mean; or
- C owns CD with its positive j axis, and D uses Q_D.

The other C axes have nonpositive j component. No actual mean
or individual D circle weight is changed.

The true unique-corner C2 high-port theorem, applied with its
other neighbor D merely physical boundary, gives the actual
full parallel C and its unique circle corner:

    C=[Z-1,Z] times [T,T+1],
    Z_C=(Z,T+1), Z=sqrt(R^2-(T+1)^2)>1/2.             (8)

Here T>17/20, so the complete local hypotheses of Section 1 of
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md hold.

The estimates in Sections 3--4 below will prove eta<4/5.
Hence zeta+eta/2>1: squaring the positive sides reduces this to
eta*(1-5eta/4)>0.

If D owns CD, C's actual minimum-n_D point is its lower-left
vertex, of height T<1. But the actual D-side mean has height

    d*zeta+eta/2+z*zeta>zeta+eta/2>1.

This excludes every original z in [0,1]. Therefore C owns CD,
and equality of the actual horizontal coordinates at Q_D gives

    Z=1-d*eta+zeta/2.                                (9)

We will show that the real corner (8)--(9) has norm above R.
The actual vertical C-side mean has not been selected or shortened.

## 3. The complete range 0<p<=1/8

By (6),

    eta/zeta
      =[(sigma/chi)+p]/[1-(sigma/chi)*p]
      <[(5/14)+(1/8)]/[1-(5/14)*(1/8)]
      =54/107.

Therefore

    eta<23/50, zeta>22/25.                           (10)

The exact squared comparisons are

    (23/50)^2-(54/107)^2/[1+(54/107)^2]
      =61817/7182500>0,

    1-(23/50)^2-(22/25)^2=7/500>0.

In particular eta<4/5, as needed for the full owner cover.
Equations (4),(8)--(10) yield

    Z>1-(61/60)*(23/50)+(11/25)=2917/3000,
    T+1>37/20.

Consequently the actual circle corner satisfies

    |Z_C|^2>(2917/3000)^2+(37/20)^2
             =Q_*+1854931/36000000.

This is impossible.

## 4. The complete range 1/8<=p<1/4

We first prove the stronger depth bound v<4/25.

Suppose v>=4/25. The actual A radius gives h>-1/240, because

    (241/240)^2-[(61/60)^2-(4/25)^2]
      =163/480000>0.

Equation (2), its monotonicity and the exact comparison

    F(4/25)-(119/1000)^2=86351/609000000>0

give k>119/1000. The original identities (3) then give

    w^2>(119/1000)^2-1/3600>1/73,

where the second reserve is 121277/657000000. Hence

    xi<1/60-30/4453.

But the exact strict-root identity in (3) now has incompatible
bounds. Its left side satisfies

    h+k*p>-1/240+(119/1000)*(1/8)=257/24000.

Its right side satisfies

    xi*sqrt(1+p^2)
      <(1/60-30/4453)*(33/32),

using p<1/4 and sqrt(17)/4<33/32. The left lower bound exceeds
the right upper bound by the exact positive reserve

    257/24000-(1/60-30/4453)*(33/32)
      =100117/213744000.

This contradiction proves v<4/25.

Equation (2) then also gives

    k^2/v^2
      =1-(3/4-2v)/(d^2-v^2)
      <1-(43/100)/(61/60)^2
       =2173/3721<16/25.

The last reserve is 5211/93025. Thus the actual strict-root
inequality w<k supplies

    w<16/125.                                       (11)

The unchanged radial relation (5) now forces

    sigma<11/40, chi>24/25.                          (12)

For the first bound, sigma>=11/40 would give
chi<=sqrt(1479)/40<38459/40000 and hence

    1-v<(61/60)*(38459/40000)-11/80
         =2015999/2400000<21/25,

contrary to v<4/25. The final comparison has reserve 1/2400000;
the square comparison for sqrt(1479)<38459/1000 has reserve
94681/1000000. The second bound in (12) follows by squaring.

Equations (12) and p<1/4 imply

    eta/zeta
      <[(55/192)+(1/4)]/[1-(55/192)*(1/4)]
       =412/713.

Consequently

    eta<101/200, zeta>43/50,                         (13)

with exact squared reserves

    (101/200)^2-(412/713)^2/[1+(412/713)^2]
       =127670713/27124520000>0,

    1-(101/200)^2-(43/50)^2=43/8000>0.

Again eta<4/5, so Section 2's complete owner reduction applies.
Using the actual corner (8)--(9), (11)--(13) give

    Z>1-(61/60)*(101/200)+(43/100)=10999/12000,
    T+1>234/125,

and hence

    |Z_C|^2>(10999/12000)^2+(234/125)^2
             =Q_*+4046797/144000000.

This excludes the whole second range, including its shared
p=1/8 endpoint.

## 5. Exact whole-interface conclusion

The two ranges exhaust the original p=c/s in (0,1/4).
Both actual CD owners were kept with their complete original
means, and both lead to the displayed physical contradictions.
Thus the strict-B-leaf, radial-D, C-parallel North/North
interface is impossible.

Together with the separately reviewed tilted-C theorem, this
provides the complete strict-B radial-D frame join. The actual
strict B mean (1), both D circle weights, true A3/B3/C2/D2
degrees, all genuine leaf data and all nine physical squares
remain throughout. The different unique-D boundary mask is
not claimed excluded by this source.

No sampled pose, shortened equation, one-corner substitution
at D, normal reselection after extraction, compilation, CI,
remote action or shared-metadata edit supplies any premise.
