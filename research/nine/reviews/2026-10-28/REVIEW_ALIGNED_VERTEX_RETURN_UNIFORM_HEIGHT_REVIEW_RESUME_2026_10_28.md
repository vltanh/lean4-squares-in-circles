# Independent review: uniform height for both complete aligned-vertex return charts

Date: October 28, 2026 UTC. Reviewer: review_resume continuation.

## 1. Exact source, full verdict, and literal scope

**PASS.** I read the entire frozen
`ALIGNED_VERTEX_ROOT_RETURN_UNIFORM_HEIGHT_BOUND.md`
and independently rederived the complete support expansion, uniform
quadratic, both whole-chart height arguments, every transition endpoint,
and the conditional perpendicular-chart geometric corollary. I supplied
no discovery contribution to the scalar argument or original roof chart.
No source byte was changed.

The reviewed source is exactly 12,384 bytes, SHA-256

`f7ec694f0f617d772db2d3173d93560690bf3532373aea4a3df47d42d6595b9d`,

with Git blob `49cbcf39f40aba59de3249229324a62e95b33e93`.

The accepted height conclusion is g>69/100 for each of the two
explicit original corner charts, under all the numerical, support and
circle-equality hypotheses printed in Section 1. The indicated Z must
be the actual circle corner of the original unit A. The source does not
derive that complete physical-mask assertion from its other scalar
premises. A graph caller must prove it before applying this theorem.

The perpendicular-chart export supplies the stated whole actual A
extents and invokes the exact-low-port barrier only when its actual
low port and full physical hypotheses are available. For the upper
chart the accepted conclusion here is height alone. No horizontal A
extent or location of the original AB port follows automatically from
that height. This review grants no whole roof or original family flag.

## 2. Exact direct inputs and independence

Both direct input pins match current unchanged bytes:

| Direct input | SHA-256 | Exact operative use |
| --- | --- | --- |
| HIGH_SQUARE_CHORD_BARRIER_WITH_EXACT_LOW_PORT_CAP.md | 4e04f9fd6e9b3bae2206333817744ae0f3e624819eb6ffd125929b973782b18e | Only the conditional whole-unit geometric export after the independent scalar height proof |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual strict West support span at the original perpendicular HA support |

Both complete sources were read in full. The new exact-cap barrier has
its separate complete independent review
`REVIEW_EXACT_LOW_PORT_HIGH_SQUARE_BARRIER_REVIEW_RESUME_2026_10_28.md`,
SHA-256 `86a9bbad75f73add88bb2cb56d8694ef0e3d40690658ca40951f0de6bf6097e5`.
The present scalar height argument is self-contained and does not use
that barrier to infer any of its own numerical premises.

Root derived the scalar estimates from the chart supplied by roof_resume.
This reviewer only audited the frozen result. In particular no proposed
horizontal-port argument, new circle-mask inference, or discovery lemma
from this reviewer is being independently certified here.

## 3. Every common elementary bound, including all signs

The complete hypotheses include

    0<epsilon<1/60, d=1+epsilon,
    R^2=(2+epsilon)^2+1/4<=1105/256,
    0<b<353/1000,
    alpha,beta>0, alpha^2+beta^2=1,
    z=(b-beta^2)/(alpha beta)>=1,
    beta*b<=epsilon*(1+alpha).

The definitions are

    h=alpha*epsilon-beta*b,
    L=beta*epsilon+alpha*b,
    A0=1-h,
    delta0=1-alpha+beta*z=(b-1+alpha)/alpha,
    s=sqrt(1+z^2), p=1/s, q=z/s,
    m=(-q,p), w=(p,q),
    delta>0, c=L+delta, g=1-c.

All original support conditions remain:

    delta<=kappa<4/15,
    kappa<c/A0,
    (A0+c*kappa)/sqrt(1+kappa^2)<=d.

Since b=beta*(beta+alpha*z), z>=1 and alpha+beta>1,
beta*b>beta^2. The given nearness inequality therefore yields

    beta^2<2*epsilon<1/30,
    beta<11/60,
    alpha>49/50,
    -epsilon<=h<epsilon.

The lower h bound is exactly beta*b<=epsilon*(1+alpha), not an
extra assumption. In particular A0>59/60 and 1+h>0, which justify
the support divisions and later square-root substitution.

L is positive. Since delta<4/15,

    0<c<353/1000+11/3600+4/15<3/4,
    1/4<g<1.

The exact difference identity is

    delta0-L
      =(beta^2/alpha)*(b-1/(1+alpha))-beta*epsilon.

Here alpha*(1+alpha)>5/3, so the possible negative first term has
magnitude below 1/50. Also beta*epsilon<11/3600<1/300. Thus

    delta0-L>-1/30.

No lower bound on b, delta or an original side mean was inserted.

For the upper chart, u=delta-delta0 satisfies 0<=u<delta<1.
For the perpendicular chart, 0<delta<delta0 and
r=(delta0-delta)/s give

    0<r<delta0/s<b/(alpha*s)<1,
    r/s<b/[alpha*(1+z^2)]<353/1960<1/4.

These are deductions on the entire stated intervals. The case r=0
is not silently treated as a positive side parameter: delta=delta0
belongs to the separate upper-chart equality case u=0.

## 4. Complete support expansion and the generic quadratic

Cauchy's inequality applied to the actual unit vector (beta,alpha)
gives

    b=beta*(beta+alpha*z)<=beta*sqrt(1+z^2).

For every 0<k<=1, direct expansion of the definitions gives exactly

    d^2-(1+h)^2-k*L^2
      =2*epsilon*(1-alpha)+(1-k)*beta^2*epsilon^2
       +2*beta*b+2*(1-k)*alpha*beta*epsilon*b
       -(beta^2+k*alpha^2)*b^2.

Every term except the final one is nonnegative. If z<=Zmax and

    k+(1-k)/30<=2/sqrt(1+Zmax^2),

then beta^2+k*alpha^2<=k+(1-k)/30<=2/s, whereas
2*beta*b>=2*b^2/s. Thus the negative term is dominated and

    (1+h)^2+k*L^2<=d^2.

This is a whole-range inequality, not an endpoint test substituted
for a varying geometric direction. The three precise choices are:

| Whole z interval | k | Coefficient bound | Exact positive squared reserve |
| --- | --- | --- | --- |
| 1<=z<=2 | 7/8 | 211/240 | 4/5-(211/240)^2=1559/57600 |
| 1<=z<=3 | 3/5 | 46/75 | 2/5-(46/75)^2=134/5625 |
| 1<=z<=5 | 1/3 | 16/45 | 2/13-(16/45)^2=722/26325 |

Now let t>0 with delta/t<=kappa. The actual function

    f(v)=(A0+c*v)/sqrt(1+v^2)

has derivative with numerator c-A0*v and is increasing throughout
0<=v<=c/A0. Since delta/t<=kappa<c/A0, the original support
inequality implies

    A0+c*delta/t<=d*sqrt(1+delta^2/t^2).

Add 1+h and use 1+h>0 together with the support bound just proved:

    2<=sqrt(d^2-k*L^2)+d*sqrt(1+delta^2/t^2)-c*delta/t.

The first radicand is nonnegative by (1+h)^2+kL^2<=d^2.
The inequalities sqrt(1-y)<=1-y/2 on [0,1] and
sqrt(1+y)<=1+y/2 for y>=0 are exact full-domain inequalities.
Substituting them and using c=L+delta yields

    4*d*epsilon
      >=k*L^2+(2*d/t)*L*delta
        +(2*d/t-d^2/t^2)*delta^2.

I independently checked this expansion and every positive denominator.
There is no truncated Taylor estimate or local slope approximation.

## 5. Entire bounded-slope upper chart

The upper chart is

    delta>=delta0, u=delta-delta0,
    Z=(h-u/z,g)+m+w,
    |Z|^2=R^2.

Assume g<=69/100, so c>=31/100. The strict difference bound gives

    L-delta<1/30<c/9,
    0<L/c<5/9.

For every 1<=z<=5, use k=1/3, t=1 in the generic quadratic.
The original delta<=kappa supplies its slope premise. Since d>=1
and 2d-d^2=1-epsilon^2>99/100,

    4*d*epsilon
      >=(1/3)*L^2+2*L*delta+(99/100)*delta^2.

Divide by c^2 and put x=L/c. The normalized lower polynomial is

    (1/3)*x^2+2*x*(1-x)+(99/100)*(1-x)^2.

Its quadratic coefficient is -203/300. It is concave on the entire
closed comparison interval [0,5/9], so its minimum occurs at an
endpoint. The endpoint values are 99/100 and 4813/6075, both
strictly greater than 3/4. Consequently

    c^2<(16/3)*d*epsilon<61/675<(31/100)^2.

This contradicts c>=31/100. Every upper-chart side position in that
whole z range is covered; no circle-mask conclusion was needed to
obtain this bounded-slope contradiction.

## 6. Entire unbounded-slope upper chart and the actual circle corner

For z>=5 retain the same contradiction assumption. The earlier
elementary bound gives c<1. Write the unchanged actual corner as

    Z_x=h-(q-p+u/z),
    Z_y=1-c+p+q.

Because q-p=(z-1)/s<(z-1)/z and 0<=u<1,

    0<q-p+u/z<1.

Also u<delta<c, so this positive horizontal displacement is at most
q-p+c/z. With |h|<=epsilon it follows that

    |Z|^2<=epsilon^2+2*epsilon+F(c),
    F(c)=(q-p+c/z)^2+(1-c+p+q)^2.

For each fixed actual z, F is a convex quadratic in c. Its maximum
on [31/100,1] is attained at an endpoint. Its exact expansion is

    F(c)=2+(1-c)^2+c^2/z^2
          +2*c*(q-p)/z+2*(1-c)*(p+q).

The function (p+q)=(z+1)/sqrt(1+z^2) has derivative with sign
1-z. Hence for every z>=5,

    p+q<=6/sqrt(26)<59/50,
    0<q-p<1,
    1/z<=1/5.

Those whole-range inequalities give

    F(31/100)<529043/125000
                  =17/4-2207/125000,
    F(1)<61/25<17/4.

Thus |Z|^2<17/4+2*epsilon+epsilon^2. The original circle has
R^2=17/4+4*epsilon+epsilon^2 and epsilon>0, contradicting the
explicit actual circle equality. The shared transition z=5 is
included in both valid arguments. All z>=1 in the upper chart are
therefore covered.

## 7. Exact perpendicular ratio and its whole small-slope interval

The perpendicular chart is

    0<delta<delta0,
    kappa=delta*z/(z-1+delta),
    r=(delta0-delta)/s,
    Z=(h,g)+(1-r)*m+w,
    |Z|^2=R^2.

At z=1 its exact formula would give kappa=1, contradicting the
original kappa<4/15. Thus z>1 is derived, not omitted as an open
endpoint. Algebra then gives

    delta/kappa=(z-1)/(z-kappa).

The denominator is positive. The derivatives in z and kappa have
respective positive numerators 1-kappa and z-1, so the ratio
increases separately in both variables.

For 1<z<=2 and kappa<4/15,

    delta/kappa<15/26<3/5.

Thus t=3/5 satisfies delta/t<=kappa, and k=7/8 is available
on the full interval. The generic quadratic has the uniform coefficient
bounds

    2*d/t>=10/3,
    2*d/t-d^2/t^2>=671/1296>1/2.

For the second, the expression decreases throughout 1<=d<=61/60,
so the stated lower endpoint is its value at d=61/60. This is a
continuous coefficient bound, not an unproved extremal substitution.

The same slope premise and actual kappa<c/A0 give

    delta/c<36/59,
    delta/L<36/23.

Subtracting (7/8)(L+delta)^2 from the lower quadratic produces

    delta*((19/12)*L-(3/8)*delta)>0,

because 36/23<38/9. Therefore

    c^2<(32/7)*d*epsilon<122/1575<(7/25)^2.

The final exact reserve is 37/39375. Hence g>18/25>69/100
through this entire interval, including z=2. No far-circle-corner
classification is inferred by this small-slope calculation.

## 8. The middle perpendicular interval first controls the actual side parameter

For every 2<=z<=3, assume again c>=31/100, so
0<g<=69/100 by the already proved common bound. The actual corner
equation expands exactly as

    |Z|^2=h^2+g^2+2-2*r+r^2
      +2*h*[p-(1-r)*q]+2*g*[(1-r)*p+q].

Since 0<r<1, the horizontal displacement lies strictly between
p-q and p, and consequently has absolute value less than one.
The whole interval also satisfies p+q<=3/sqrt(5)<27/20.

If r>=1/20, the increasing function 2r-r^2 on [1/20,1]
gives 2r-r^2>=39/400. Dropping only the nonpositive term
-2*g*r*p and using the complete bounds above yields

    |Z|^2<=epsilon^2+2*epsilon+17/4-21/2500<R^2.

The actual circle equality therefore forces r<1/20. Since
s<=sqrt(10)<16/5,

    delta0-delta=r*s<4/25.

Combining this with delta0>L-1/30, in the stated direction, gives

    L-delta<1/30+4/25=29/150<(2/3)*c,
    0<L/c<5/6.

This uses the actual original side parameter of A. It does not
replace its physical point or set r to a selected value.

## 9. Complete middle perpendicular quadratic contradiction

The exact monotone ratio gives, for every z<=3,

    delta/kappa<30/41<3/4.

Use k=3/5 and t=3/4 in the generic quadratic. The complete
coefficient bounds are

    2*d/t>=8/3,
    2*d/t-d^2/t^2>=1769/2025>17/20.

Again the second coefficient decreases on the whole original d
interval, and its quoted endpoint value is exact. With x=L/c in
[0,5/6], the lower normalized polynomial becomes

    (3/5)*x^2+(8/3)*x*(1-x)+(17/20)*(1-x)^2
      =17/20+(29/30)*x-(73/60)*x^2.

It is concave. Its endpoint values are 17/20 and 1751/2160,
both strictly greater than 4/5; the second reserve is 23/2160.
Thus

    c^2<5*d*epsilon<61/720<(31/100)^2.

The final exact reserve is 64/5625. This contradicts the assumed
c>=31/100 on the entire closed interval 2<=z<=3. Both transition
values are retained.

## 10. Entire unbounded perpendicular interval

For z>=3 under the same contradiction hypothesis, retain the exact
corner expansion, g>0, 0<r<1 and |p-(1-r)q|<1. Dropping only
the negative terms -2r+r^2 and -2grp gives

    |Z|^2<=epsilon^2+2*epsilon+(69/100)^2+2
                                  +2*(69/100)*(p+q).

Monotonicity now gives p+q<=4/sqrt(10)<19/15 throughout the
entire unbounded interval. Therefore

    |Z|^2<epsilon^2+2*epsilon+17/4-259/10000<R^2.

This contradicts the unchanged actual far-circle corner. Together
with the small and middle intervals and the explicit z=1 exclusion,
it proves the entire perpendicular chart. No parameter sample,
orientation mesh or finite geometric exclusion certificate is used.

## 11. Independent exact arithmetic checks

I independently verified the following fourteen fixed rational values
and reserves with exact fraction arithmetic:

| Check | Exact value |
| --- | --- |
| Support coefficient reserve through z=2 | 1559/57600 |
| Support coefficient reserve through z=3 | 134/5625 |
| Support coefficient reserve through z=5 | 722/26325 |
| Upper quadratic at x=5/9 | 4813/6075 |
| Upper far-corner comparison at c=31/100 | 529043/125000 |
| Its reserve below 17/4 | 2207/125000 |
| Small perpendicular delta-squared coefficient | 671/1296 |
| Small perpendicular final height reserve | 37/39375 |
| Middle perpendicular r>=1/20 corner reserve | 21/2500 |
| Middle perpendicular delta-squared coefficient | 1769/2025 |
| Middle normalized quadratic at x=5/6 | 1751/2160 |
| Its reserve above 4/5 | 23/2160 |
| Middle perpendicular final height reserve | 64/5625 |
| Unbounded perpendicular corner reserve | 259/10000 |

These are arithmetic checks of the full hand inequalities and exact
endpoint identities. The proof of monotonicity, concavity, convexity,
all angle ranges, and actual-corner use was supplied independently
above; no numerical pose search or geometric certificate is inferred
from checking these constants.

## 12. Literal perpendicular export and the still-separate upper port obligation

For the actual perpendicular-chart unit

    A=(h,g)-r*m+[0,1]m+[0,1]w,

both own axes have strictly positive vertical components. Its entire
actual minimum height is exactly

    min_A y=g-r/s>g-1/4=g-1+3/4.

If the original H-to-A normal is w at the strict Northeast H vertex
(h,g), the strict support-span lemma applies to the actual minimum-w
point of A. Since w has positive horizontal component, its entire
West extent is strictly less than one, including every actual support
side position. Consequently min_A x>h-1.

The proved height g>69/100, the original h<=epsilon, and an actual
unchanged CB point with P_x<h-2/3 and P_y<49/75 therefore supply
the complete inequalities for the exact-cap lower-route barrier with
ell=2/3 and eta=3/4. Under that barrier's actual unit containment and
physical interior-disjointness hypotheses, the real A-B/H geometry is
impossible. No original point or shared mean is replaced by an auxiliary
chord point.

This is a conditional literal corollary. It does not automatically
establish a whole C cap, actual HA owner, original graph reduction,
or physical A circle mask. Those remain obligations of the final
graph caller. In the upper chart this source proves height only; its
North HA case still requires a separate bound on the original AB
application or complete horizontal A extent. I have not attributed
such a conclusion to this theorem.

All scalar denominators, strict or weak endpoints, and whole-unit
conclusions were checked at their exact stated scope. Every original
unit, true degree, force, normal, circle coefficient, application and
shared mean remains in any literal all-nine-unit application. No
metadata, family flag, mathematical source, commit, remote state,
Lean compilation, CI, workflow or merge was changed by this review.
