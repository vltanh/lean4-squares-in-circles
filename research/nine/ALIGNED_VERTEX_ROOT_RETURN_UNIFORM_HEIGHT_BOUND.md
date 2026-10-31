# One uniform height bound for the two remaining aligned-root return charts

Date: October 28, 2026 UTC. Author: root continuation; the original
aligned-root and A-face charts were supplied by roof_resume.

**Status: complete proposed continuous scalar/actual-unit theorem, frozen
for full separate independent review.** The two charts below both force
the actual hub top height g>69/100. A single support quadratic handles
the bounded-slope ranges; the same actual far-circle corner handles the
unbounded-slope ranges. No original family flag is declared closed.

## 1. Complete common hypotheses and the two actual corner charts

Use real numbers with

    0<epsilon<1/60, d=1+epsilon,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<b<353/1000,
    alpha,beta>0, alpha^2+beta^2=1,
    z=(b-beta^2)/(alpha beta)>=1,
    beta b<=epsilon(1+alpha).

Define, without changing the original origin,

    h=alpha epsilon-beta b,
    L=beta epsilon+alpha b,
    A0=1-h,
    delta0=1-alpha+beta z=(b-1+alpha)/alpha,
    s=sqrt(1+z^2), p=1/s, q=z/s,
    m=(-q,p), w=(p,q).

Let delta>0, c=L+delta and g=1-c. Keep a positive original support
slope kappa satisfying all of

    delta<=kappa<4/15,
    kappa<c/A0,
    (A0+c kappa)/sqrt(1+kappa^2)<=d.                 (1)

The actual H is [h-1,h] times [g-1,g]. Require one of the following
two actual physical-circle corner statements, with the same R:

    Upper chart:
      delta>=delta0, u=delta-delta0,
      Z=(h-u/z,g)+m+w,
      |Z|^2=R^2;                                    (2)

    Perpendicular chart:
      0<delta<delta0,
      kappa=delta z/(z-1+delta),
      r=(delta0-delta)/s,
      Z=(h,g)+(1-r)m+w,
      |Z|^2=R^2.                                    (3)

Here Z must be the indicated corner of the original actual boundary
unit A. An abstract chosen point on the circle is not a substitute for
that literal caller. No assertion that a unique corner exists is silently
inferred from the other scalar hypotheses; the exact corner equation in
(2) or (3) is an explicit premise. A graph caller must establish its
whole physical mask before invoking it.

**Theorem.** In both complete charts, g>69/100.

The upper chart includes North HA with its whole original side mean and
also a common-minimum-corner strict HA with u=0, whenever its actual
equations and mask give (2). The perpendicular chart includes the real
side parameter r at A. The theorem does not change an original mean,
normal, coefficient, circle or body.

## 2. Uniform elementary consequences of the actual chart

Since b=beta(beta+alpha z) and z>=1,

    beta b=beta^2(beta+alpha z)>beta^2,
    beta^2<2epsilon<1/30,
    beta<11/60, alpha>49/50,
    -epsilon<=h<epsilon.                            (4)

The last lower bound is precisely the original nearness inequality.
Also delta0=1-alpha+beta z>0. From delta<4/15 and the given b,

    0<c=L+delta
       <353/1000+11/3600+4/15<3/4,
    1/4<g<1.                                       (5)

The relation between the two original vertical quantities is

    delta0-L
       =(beta^2/alpha)(b-1/(1+alpha))-beta epsilon
       >-1/30.                                     (6)

Indeed alpha(1+alpha)>5/3, so
beta^2/[alpha(1+alpha)]<1/50, while
beta epsilon<11/3600<1/300. Their sum is below 1/30.
No small lower bound on b or on an original mean is assumed.

In (3), 0<r<delta0/s<b/(alpha s)<1, and moreover

    r/s<b/[alpha(1+z^2)]
         <353/1960<1/4.                            (7)

In (2), 0<=u<delta<1. These bounds cover the full physical side
intervals needed later; no endpoint is discarded by a choice of mean.

## 3. A reusable support quadratic on whole slope ranges

Cauchy's inequality gives b<=beta sqrt(1+z^2). Expanding directly,
for any 0<k<=1,

    d^2-(1+h)^2-kL^2
      =2epsilon(1-alpha)+(1-k)beta^2 epsilon^2
       +2beta b+2(1-k)alpha beta epsilon b
       -(beta^2+k alpha^2)b^2.                     (8)

Every term except the last is nonnegative. If z<=Zmax and

    k+(1-k)/30<=2/sqrt(1+Zmax^2),                  (9)

then (4), Cauchy and (8) imply

    (1+h)^2+kL^2<=d^2.                             (10)

We use only the following three exact choices, each over the entire
stated interval:

| Whole slope range | k | Upper bound on beta^2+k alpha^2 | Comparison reserve after squaring |
| --- | --- | --- | --- |
| 1<=z<=2 | 7/8 | 211/240 | 4/5-(211/240)^2=1559/57600 |
| 1<=z<=3 | 3/5 | 46/75 | 2/5-(46/75)^2=134/5625 |
| 1<=z<=5 | 1/3 | 16/45 | 2/13-(16/45)^2=722/26325 |

Suppose also t>0 and delta/t<=kappa. The function

    f(v)=(A0+c v)/sqrt(1+v^2)

is increasing on 0<=v<=c/A0, as its derivative has numerator
c-A0 v. By (1),

    A0+c delta/t<=d sqrt(1+delta^2/t^2).

Add 1+h, use (10), and recall c=L+delta. Since 1+h>0,

    2<=sqrt(d^2-kL^2)+d sqrt(1+delta^2/t^2)-c delta/t.

The complete elementary radical bounds sqrt(1-y)<=1-y/2 on
[0,1] and sqrt(1+y)<=1+y/2 on [0,infinity) now give

    4d epsilon
      >=k L^2+(2d/t)L delta
                 +(2d/t-d^2/t^2)delta^2.           (11)

The first radical's argument is nonnegative by (10). No truncated
series or local approximation is being used. This one full-interval
quadratic will control both actual charts.

## 4. The upper chart for every 1<=z<=5

Suppose toward a contradiction that g<=69/100, so c>=31/100.
In (2), delta>=delta0 and (6) give

    L-delta<1/30<c/9,
    0<L/c<5/9.                                     (12)

Use k=1/3 and t=1 in (11); (1) supplies delta<=kappa.
Since d>=1 and 2d-d^2=1-epsilon^2>99/100,

    4d epsilon>=(1/3)L^2+2L delta+(99/100)delta^2.

For x=L/c in [0,5/9], divide by c^2. The resulting polynomial

    (1/3)x^2+2x(1-x)+(99/100)(1-x)^2

is concave, with quadratic coefficient -203/300. Its endpoint
values are 99/100 and 4813/6075, both greater than 3/4.
Thus

    c^2<(16/3)d epsilon<61/675<(31/100)^2,           (13)

contradicting c>=31/100. This excludes the whole bounded-slope
upper chart without using any special actual A side position.

## 5. The upper chart for every z>=5

Continue the same contradiction assumption c>=31/100. By (5), c<1.
Write the actual corner from (2) as

    Z_x=h-(q-p+u/z),
    Z_y=1-c+p+q.

Because q-p=(z-1)/s<(z-1)/z and 0<=u<1,

    0<q-p+u/z<1,
    q-p+u/z<=q-p+c/z.

The second inequality follows from u<delta<c. Therefore

    |Z|^2<=epsilon^2+2epsilon+F(c),
    F(c)=(q-p+c/z)^2+(1-c+p+q)^2.                 (14)

For each fixed z this is a convex quadratic in c. Its maximum on
[31/100,1] occurs at an endpoint. Its exact expansion is

    F(c)=2+(1-c)^2+c^2/z^2
              +2c(q-p)/z+2(1-c)(p+q).

For z>=5, (p+q)=(z+1)/sqrt(1+z^2) is decreasing, and

    p+q<=6/sqrt(26)<59/50,
    0<q-p<1, 1/z<=1/5.

Consequently

    F(31/100)<2+(69/100)^2+(31/100)^2/25
                    +2*(31/100)/5+2*(69/100)*(59/50)
                =529043/125000
                =17/4-2207/125000,
    F(1)<2+1/25+2/5=61/25<17/4.

Thus (14) gives |Z|^2<17/4+2epsilon+epsilon^2<R^2, contradicting
the unchanged actual circle equation. This proves the upper chart over
the entire unbounded interval too, including z=5.

## 6. The perpendicular chart for every 1<z<=2

At z=1 the formula in (3) gives kappa=1, contradicting (1); thus z>1
is derived rather than omitted. In this chart

    delta/kappa=(z-1)/(z-kappa).

That ratio increases separately with z>1 and kappa<1. For z<=2,

    delta/kappa<15/26<3/5.

Use k=7/8 and t=3/5 in (11). Its coefficient bounds are

    2d/t>=10/3,
    2d/t-d^2/t^2>=671/1296>1/2.

Also delta/t<=kappa<c/A0 and A0>59/60 imply

    delta/c<36/59,
    delta/L<36/23.

It follows that

    (7/8)L^2+(10/3)L delta+(1/2)delta^2
        >=(7/8)(L+delta)^2.

To check this without an extremal approximation, subtract the right
side: the result is delta((19/12)L-(3/8)delta), which is positive
under delta/L<36/23<38/9. Hence (11) gives

    c^2<(32/7)d epsilon<122/1575<(7/25)^2.

The final exact reserve is 37/39375. Therefore g>18/25>69/100
on this entire interval, with no physical circle-mask shortcut.

## 7. The perpendicular chart for every 2<=z<=3

Suppose again g<=69/100, so c>=31/100. Expand the original actual
corner in (3):

    |Z|^2=h^2+g^2+2-2r+r^2
          +2h[p-(1-r)q]+2g[(1-r)p+q].              (15)

By (5),(7), 0<g<=69/100 and 0<r<1. The horizontal displacement
p-(1-r)q has absolute value less than one. Moreover
p+q<=3/sqrt(5)<27/20 on this whole interval. If r>=1/20,
then 2r-r^2>=39/400. Dropping only the nonpositive term -2g r p,
equation (15) gives

    |Z|^2<=epsilon^2+2epsilon+(69/100)^2+2
                      +2*(69/100)*(27/20)-39/400
             =epsilon^2+2epsilon+17/4-21/2500
             <R^2.

The actual circle equation therefore forces r<1/20. Since
s<=sqrt(10)<16/5, this yields

    delta0-delta=r s<4/25,
    L-delta<1/30+4/25=29/150<(2/3)c,
    0<L/c<5/6.                                     (16)

The first use of (6) in the second line is in its correct direction:
delta0>L-1/30. The strict last comparison follows from c>=31/100.

For z<=3, the same monotonic ratio as in Section 6 gives
delta/kappa<30/41<3/4. Use k=3/5 and t=3/4 in (11). Then

    2d/t>=8/3,
    2d/t-d^2/t^2>=1769/2025>17/20.

For x=L/c in [0,5/6], the normalized lower quadratic is

    (3/5)x^2+(8/3)x(1-x)+(17/20)(1-x)^2
       =17/20+(29/30)x-(73/60)x^2.

It is concave. Its endpoint values are 17/20 and 1751/2160,
both greater than 4/5; the second has reserve 23/2160. Thus

    c^2<5d epsilon<61/720<(31/100)^2.

The last reserve is 64/5625. This contradicts the same assumption
c>=31/100 throughout the complete middle interval.

## 8. The perpendicular chart for every z>=3

Under the same contradiction assumption, use (15), g>0, 0<r<1
and |p-(1-r)q|<1. Dropping -2r+r^2<=0 and -2g r p<0 gives

    |Z|^2<=epsilon^2+2epsilon+(69/100)^2+2
                                        +2*(69/100)*(p+q).

For z>=3, monotonicity gives p+q<=4/sqrt(10)<19/15. Therefore

    |Z|^2<epsilon^2+2epsilon+17/4-259/10000<R^2.

This is impossible for the same original circle corner. Sections 6--8
cover every z>1, with both shared transition endpoints included. Together
with Sections 4--5 they prove the stated uniform height theorem.

## 9. Literal geometric export and boundary of the assertion

For an actual perpendicular-chart unit

    A=(h,g)-r m+[0,1]m+[0,1]w,

both m,w have positive vertical components, so its full minimum height
is g-r/s>g-1/4 by (7). If its original H-to-A normal is w at the
strict Northeast H vertex (h,g), the already proved strict unit support
span gives min_A x>h-1. Those complete actual extents, the new height
g>69/100 and any unchanged CB point with

    P_x<h-2/3, P_y<49/75

meet the exact-low-port lower-route barrier with ell=2/3, eta=3/4.
The actual A-B-C/H geometry is then impossible. This is a conditional
literal corollary, not a claim that every graph automatically supplies
the displayed whole C cap or the original perpendicular chart.

For the upper chart this source proves only the height statement. A
North HA caller must separately control the actual AB application or
the whole horizontal A extent before using a chord barrier. In particular
this theorem does not assert min_A x>=h-1 merely from g>69/100.

The graph caller must establish the genuine aligned root, actual H
nearness, complete H3 force/torque and HC moment, the original A support
classification and actual circle corner in (2) or (3), and every original
contact coefficient. The source's algebra neither replaces those
obligations nor removes any original force or changes a mean. All nine
actual squares and the original true degrees remain in any literal call.

| Source | SHA256 | Literal use |
| --- | --- | --- |
| HIGH_SQUARE_CHORD_BARRIER_WITH_EXACT_LOW_PORT_CAP.md | 4e04f9fd6e9b3bae2206333817744ae0f3e624819eb6ffd125929b973782b18e | Only Section 9 conditional geometric corollary; the scalar height proof is self-contained |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Only Section 9 actual strict-unit West span at the retained perpendicular HA support |

Root derived the support quadratic, its complete continuous comparisons
and the two height proofs from roof_resume's actual chart. The independent
reviewer supplied no discovery. No numerical pose, sampled parameter,
angle grid, finite exclusion certificate, Lean compilation, CI, workflow,
metadata mutation or remote write is part of this result.
