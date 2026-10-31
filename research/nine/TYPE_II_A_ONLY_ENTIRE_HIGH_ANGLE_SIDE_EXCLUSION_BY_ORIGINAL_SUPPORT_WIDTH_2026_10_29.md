# The entire high-angle A-only side return is impossible

Date: October 29, 2026 UTC. Author: common-selection continuation.

**Status: complete proposed hand theorem, frozen for independent review.**
Every original unique-circle Type II A-only h side return with
alpha+beta>=2pi/3 is impossible. The proof covers every endpoint physical
circle mask, all original force ratios and full contact means at once.
It is a single strict support-width inequality on the entire angle
interval, not a selected pose or a subdivision into endpoint masks.

Combined with the already accepted complete diagonal exclusion, the
original unloaded-N A-only row can survive only when

    pi/2<alpha+beta<2pi/3,
    0<k<1/2, H>sqrt(3)/2.

The whole A-only row is not closed. Its remaining side range, including
both radial and both-unique endpoint alternatives, remains. Loaded N
retains its separate obligation.

The root continuation suggested investigating whether the side budget
excludes a large-k interval. The scalar theorem, concavity argument,
threshold and complete application below were derived here. This topic
suggestion is disclosed for review provenance.

## 1. A continuous scalar support-width theorem

The following theorem does not require a radius, a circle mask or a
choice of force ratio.

**Theorem 1.1.** Suppose

    H>k>0, H^2+k^2=1,
    p=H-k, q=H+k,
    p/q<j<1,
    0<u,t<1,
    1-u=(k+H*j)*(1-t).                         (1)

Define

    v=u/(1-j+j*u),
    r=t/p,
    b0=v/sqrt(1+v^2),
    cY=H/sqrt(1+2*k*r+r^2).                    (2)

If k>=1/2, then

    b0+cY<q.                                   (3)

The statement covers the whole closed lower join k=1/2 and every
0<u,t<1 satisfying (1). No extra relation between u and t is selected.

### 1.1. Immediate strict bounds and the easy branch

Since 0<j,u<1,

    (1-j+j*u)-u=(1-j)*(1-u)>0.

Thus 0<v<1 and b0<1/sqrt(2). Also r>0, so cY<H. If b0<=k,
then b0+cY<k+H=q, which already proves (3). It remains to treat
the entire branch b0>k.

Because H,k,v are positive and H^2=1-k^2, positive squaring gives
the exact equivalence

    b0>k  iff  v>k/H.

Substitute (2). The denominator 1-j+j*u is positive, and
H-k*j>H-k=p>0. Consequently

    u>k*(1-j)/(H-k*j),
    1-u<p/(H-k*j).                              (4)

Combining (4) with the unchanged relation in (1) gives

    t>1-p/F(j),
    F(j)=(H-k*j)*(k+H*j).                       (5)

Both factors of F are positive on the entire interval in (1).

### 1.2. One concavity bound over the full j interval

The quadratic

    F(j)=H*k+(H^2-k^2)*j-H*k*j^2

is strictly concave. Its exact endpoint values on [p/q,1] are

    F(p/q)=1/q^2,
    F(1)=p*q.                                   (6)

For the first equality, H-k*p/q=1/q and k+H*p/q=1/q follow
from H^2+k^2=1. For the second, simply multiply (H-k)(H+k).

When k>=1/2,

    H*(1-2*k^2)<k.                              (7)

Indeed H<1, 0<1-2k^2<=1/2 and k>=1/2. Using
pq=1-2k^2 and q^2=1+2Hk, (7) gives

    p*q^3
      =1-2*k^2+2*H*k*(1-2*k^2)<1.

Hence pq<1/q^2. A concave function on a closed interval is at
least the smaller of its endpoint values, so (6) yields

    F(j)>=p*q.                                  (8)

This is one continuous bound over all j, not an angle mesh or an
assumption that the minimum occurs at the actual original j. The
comparison endpoints are used only to prove (8); the actual j remains
strictly in its original interval.

Equations (5),(8), with p>0, now give

    t>1-1/q,
    r=t/p>(q-1)/(p*q).                          (9)

### 1.3. Uniform rational bounds complete the whole interval

On 1/2<=k<1/sqrt(2), the function
q=sqrt(1-k^2)+k is increasing, because q'=1-k/H>0. Thus

    q>4/3,
    H<7/8,
    p*q<=1/2.                                  (10)

The first two strict comparisons follow from

    q>=(sqrt(3)+1)/2>4/3,
    H<=sqrt(3)/2<7/8.

Their positive squared rational reserves are
3-(5/3)^2=2/9 and (7/8)^2-3/4=1/64.
Equation (9) therefore implies r>2/3. Keeping all original r rather
than assigning its lower comparison value, (2) gives

    1+2*k*r+r^2>1+2/3+4/9=19/9>(7/5)^2,
    cY<(7/8)/(7/5)=5/8.                       (11)

The last squared reserve in (11) is 34/225>0. Also

    b0<1/sqrt(2)<17/24,

since (17/24)^2-1/2=1/576>0. Hence this whole second branch
satisfies

    b0+cY<17/24+5/8=4/3<q.                    (12)

Together with the b0<=k branch, (12) proves Theorem 1.1. Every
inequality is strict where needed at k=1/2. The upper comparison
endpoint H=k is outside the original domain and is not required.

## 2. Literal whole A-only h entry

Use the complete original chart, physical stars and side-return theorem
in

    TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md.

In the original D02.L135 caller retain all six core units
A,V,D,C,N,B and the other three actual squares. Their true stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D are unloaded true3; V,B,C are loaded true2; N is the original
unloaded true2. V has its original unique physical circle corner. The
original common selection and incident-diagonal avoidance remain the
same conditional inputs. No new compatibility claim is made here.

Retain the original orthonormal A frame and angles

    h=(c0,-s), e=(s,c0),
    c0=cos(alpha), s=sin(alpha),
    C=cos(beta), S=sin(beta),
    pi/4<alpha,beta<pi/2,
    pi/2<alpha+beta<3pi/4,
    H=c0*S+s*C,
    k=s*S-c0*C,
    p=H-k>0, q=H+k>1.                          (13)

Thus H>k>0 and H^2+k^2=1. The original full contact coordinates are

    0<omega<1,
    u=1-omega*S/H in (0,1),
    t=1-omega*s/H in (0,1).                     (14)

The complete original hub force and moment equations remain, including

    rho*u=mu*(s-c0),
    nu*t=rho*p,
    (mu/nu)*(1-omega)=S-C,
    mu*East+nu*nD=kappa_V*Z,
    |Z|=R, kappa_V>0.                           (15)

In particular the original cubic

    (1-omega)*(1-omega*s/H)*(1-omega*S/H)
      =p*(s-c0)*(S-C)                           (16)

is still imposed. The larger scalar domain of Theorem 1.1 makes (16)
unnecessary for this particular interval contradiction; no root is
changed or added, and all original configurations still satisfy it.

The actual exterior unit directions and their physical side coordinates
are those proved in the complete input:

    v=s*u/(s-c0+c0*u),
    r=rho/nu=t/p,
    m=(r+k)/H,
    a0=1/sqrt(1+v^2), b0=v/sqrt(1+v^2),
    cX=m/sqrt(1+m^2), cY=1/sqrt(1+m^2),
    b=-a0*h-b0*e, c=-cX*h+cY*e,
    w_B=-b0*h+a0*e, w_C=-cY*h-cX*e.            (17)

B and C genuinely own their original external axes at Q_B and Q_C.
The unchanged shapes, with the original strict side-interior coordinates,
are

    B=Q_B+[0,1]b+[-beta_B,1-beta_B]w_B,
    C=Q_C+[-1,0]c+[-chi_C,1-chi_C]w_C,
    0<beta_B,chi_C<1.                           (18)

For every original side return, with both original contact applications
or full means retained, the accepted whole-domain theorem proves

    x_B=1-beta_B in (0,1), x_C=chi_C in (0,1),
    b0*x_B+cY*x_C<=E,
    E=b0+cY-q>0.                               (19)

This input has no restriction to unique-circle B or C. It retains the
full physical masks, including individual zero circle coefficients,
and both original endpoints' complete force and moment equations. No
support point or mean is selected anew in using (19).

## 3. Exact scalar join, including all angles and force ratios

Set j=c0/s. Since alpha>pi/4, one has 0<j<1. Write
theta=alpha+beta-pi/2 in (0,pi/4), so H=cos(theta), k=sin(theta).
Because beta>pi/4,

    alpha<pi/4+theta.

The cotangent is strictly decreasing on this angle interval, giving

    j>cot(pi/4+theta)=(H-k)/(H+k)=p/q.           (20)

The exact trigonometric identity

    S=s*k+c0*H

gives S/s=k+H*j. Using the actual common omega in (14) therefore
gives exactly

    1-u=(S/s)*(1-t)=(k+H*j)*(1-t).             (21)

This verifies the full coupled relation in Theorem 1.1; u and t have
not been treated as independently selectable variables.

The first definition of v in (17) becomes u/(1-j+j*u), and

    cY=H/sqrt(H^2+(r+k)^2)
       =H/sqrt(1+2*k*r+r^2).                    (22)

All hypotheses and all quantities of Theorem 1.1 now agree with the
original ones. If k>=1/2, its conclusion is b0+cY<q, contradicting
the entire original side budget E>0 in (19). This is an exclusion of
the full original side feature on that whole angle interval, not merely
the absence of one algebraic or selected-normal subcase.

Since sin is strictly increasing on (0,pi/4), k>=1/2 is exactly
alpha+beta>=2pi/3 in this chart. The lower angular equality is covered.

## 4. Whole unloaded-N consequence and precise surviving domain

The accepted complete original diagonal-return theorem already excludes
every diagonal transmission by this same unloaded true2 N, with the same
true degrees, original selected normals, full means and nine physical
squares. It uses no restriction k<1/2. The original two-force theorem
has only side and diagonal transmission.

Consequently **every original D02.L135 A-only h configuration with
alpha+beta>=2pi/3 is excluded**, for all its physical B/C masks and
all original positive magnitudes. The surviving original unloaded-N
A-only feature necessarily has

    pi/2<alpha+beta<2pi/3,
    pi/4<alpha,beta<5pi/12,
    0<k<1/2,
    sqrt(3)/2<H<1,
    (sqrt(3)-1)/2<p<1,
    1<q<(sqrt(3)+1)/2.                         (23)

These bounds follow monotonically from the same original angular chart;
they do not select different endpoint normals or a different stress.
All original full equations, the cubic (16), circle containment, original
applications, true stars, and all nine actual squares remain necessary
on (23). No claim is made that this remaining continuous domain is empty.

In particular this source does not close all radial B endpoints, all
radial C endpoints, or the whole both-unique side alternative. It removes
the same whole high-angle interval from each of them at once. Loaded N
in D02.L1345 does not satisfy the unloaded channel input (19) and is not
assigned it. No whole A-only row, Type II family, physical-two roof
domain, D02 parent, unrestricted n=9 bound or equality classification
is claimed closed.

## 5. Complete inputs and verification boundary

| Complete operative input | SHA256 | Exact use |
| --- | --- | --- |
| TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md | 00e18446bab3fc7b97484fc33d700363ea41f415af5b1746ee4c020c87830033 | Entire original chart, coupled t/u coordinates, true stars, genuine exterior ownership, all physical masks, actual full means and the strict original side budget |
| TYPE_II_A_ONLY_H_OWNER_COMPLETE_DIAGONAL_RETURN_EXCLUSION_BY_ORIGINAL_ENDPOINT_AXES_2026_10_29.md | a38780b72988e3f1628ba751d955bfc8a09e9c06f55764e0699b88506d175eb8 | Entire original diagonal exit and exact side-or-diagonal unloaded-N boundary for the full interval join in Section 4 |

Both complete direct sources were read. The new scalar theorem and its
literal original-family join are proved in full above. The complete
new source requires separate independent review before adoption.

All calculations are exact and continuous. No pose search, angle mesh,
new packing certificate, assigned force ratio, changed selected normal,
replacement mean, altered physical mask, omitted circle term, shortened
star, removed square, Lean/Lake build, CI/workflow, remote write or shared
metadata change was used. No census or completion flag is changed here.
