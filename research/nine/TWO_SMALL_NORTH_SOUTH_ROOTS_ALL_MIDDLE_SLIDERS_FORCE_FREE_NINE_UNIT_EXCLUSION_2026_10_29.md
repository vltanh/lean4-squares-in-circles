# Two small North/South roots exclude every middle slider

Date: October 29, 2026 UTC. Author: capacity continuation.

**Status: complete new force-free hand theorem, submitted for full independent
review.** This closes the entire remaining middle-slider interval of the
balanced small-root capacity theorem. Its conclusion uses every one of the
nine actual units and is independent of all root degrees and external forces.
It does not assert that every three-genuine-root configuration has two small
North/South root charts.

## 1. Complete statement and the two already available physical inputs

Keep the exact physical hypotheses, radius, six distinct actual units and
two actual root charts of

    BALANCED_MIDDLE_TWO_SMALL_NORTH_SOUTH_ROOTS_FORCE_FREE_NINE_UNIT_EXCLUSION_2026_10_29.md,

except that the middle's transverse interval is now the entire original one:

    Q=1105/256, rho=9/8,
    d=1+epsilon, 0<epsilon<1/60,
    R^2=(d+1)^2+1/4<=Q,

    T=[epsilon,d] x [-b,a], a,b>=0, a+b=1.          (1)

The actual East radial-S leaf L_0 is retained. The other roots and their
distinct actual radial-S leaves satisfy

    H=P_+ +[0,1]f_+ +[0,1]j_+,
    P_+=(epsilon,t_+),
    f_+=(-c_+,-s_+), j_+=(-s_+,c_+),

    K=P_- +[0,1]f_- +[0,1]j_-,
    P_-=(epsilon,-t_-),
    f_-=(-c_-,s_-), j_-=(-s_-,-c_-),

    0<=t_+,t_-<=11epsilon/10,
    0<=s_+,s_-<=9epsilon/4,
    c_+,c_->0, c_+^2+s_+^2=c_-^2+s_-^2=1,

    (e_+)_y>0, (e_-)_y<0,
    |(e_+)_x|,|(e_-)_x|<=3/80.                    (2)

Here the exact real leaf is L(e)=[d,d+1]e+[-1/2,1/2]Je, and the
corresponding actual root has d e as a maximum-e support point. All actual
units are contained in the original disk and have disjoint open interiors.
The original applications and side means are unrestricted by these geometric
charts and are not changed.

**Theorem.** The six actual units T,H,K,L_0,L_+,L_- cannot belong to a
nine-unit collection in the same disk, throughout the full closed slider
domain (1).

If a,b>=1/4, this is precisely the complete balanced theorem, including
either attained endpoint 1/4. It remains to treat a>3/4 or b>3/4; the
two alternatives are exchanged by reflection of all actual data.

For that proof the accepted physical three-near-unit theorem supplies the
following exact statement. In a nine-unit collection with three distinct
units meeting D_(1/60), every other actual unit has a connected open
center component on |z|=rho of length greater than

    phi=acos(9/10).

Among the three completion units beyond three roots and their three real
S leaves, at least two center components have length greater than

    delta=2pi/9.                                   (3)

Their full circle intersections may have other components; those actual
pieces remain present. Only the specified connected component is counted.
The complete source and its full proof were read. Its literal premise is
supplied here by the actual radial segments in each root, which contain
epsilon e and hence meet D_(1/60). There is no new clearance assumption.

In particular ANY TWO of the three completion components have combined
length strictly greater than delta+phi. At most one of the three can fail
the stronger delta bound. This simultaneous count is essential below.

## 2. The actual small chart forces the complete North/South leaf feature

We give the upper-root argument; reflection proves every lower assertion.
Suppress the plus subscripts and put P=(epsilon,t), f=(-c,-s),
j=(-s,c). As in the balanced source,

    |P|^2<=221epsilon^2/100<9epsilon^2/4<1/1600.

The actual upper leaf direction e has e.j>0. Indeed c and e_y are
strictly greater than 79/80, while |s| and |e_x| are at most 3/80,
so e.j>(79/80)^2-(3/80)^2>0.

If e.f>0, its actual unique support vertex would be P+f+j. That
vertex has norm at least sqrt(2)-|P|>sqrt(2)-1/40>61/60>d,
contradicting the actual radial support point d e. If e.f=0, then
e=j and the actual leaf is an owned +j leaf. If e.f<0, its actual
strict support vertex is P+j. These exhaust all support-owner endpoints.

In the actual (j,f) frame write

    h=P.j=-epsilon*s+t*c,
    beta=-P.f=epsilon*c+t*s>0,
    H=[h,1+h]j+[-beta,1-beta]f.                    (4)

For the owned leaf, h=epsilon. For the strict leaf, the unchanged
radial equation |P+j|^2=d^2 gives

    h=epsilon+(epsilon^2-|P|^2)/2.

Consequently the full original feature cover satisfies

    epsilon-(3/2)epsilon^2<=h<=epsilon,
    0<beta<(7/4)epsilon.                           (5)

For the first inequality one actually has the stronger lower bound
epsilon-(121/200)epsilon^2. For the second,

    beta<=epsilon+(99/40)epsilon^2
         <(833/800)epsilon<(7/4)epsilon.

Thus (5) follows directly in the unchanged physical chart. It does not
assign a common orientation to the roots or replace the near vertex by O.

## 3. Each actual western root arc is longer than delta_0

Let

    C_0=11159/13500, delta_0=acos(C_0).

In the actual (j,f) frame the open circle arc

    acos((1+h)/rho)<theta<asin((1-beta)/rho)          (6)

lies in int H. The two far faces give its endpoints. The first coordinate
is at least sqrt(rho^2-1)=sqrt(17)/8>1/2>h; the second is positive
and therefore greater than -beta. All four original face inequalities
are strict. The analogous reflected K arc is also actual.

By (5), the length of (6) is greater than or equal to

    f(epsilon)=asin((1-(7/4)epsilon)/rho)
       -acos((1+epsilon-(3/2)epsilon^2)/rho).

The function decreases on 0<=x<=1/60. In fact

    f'(x)=-(7/4)/sqrt(rho^2-(1-(7/4)x)^2)
       +(1-3x)/sqrt(rho^2-(1+x-(3/2)x^2)^2).

The negative term has magnitude at least
(7/4)/sqrt(rho^2-(233/240)^2); the positive term is at most
1/sqrt(rho^2-(61/60)^2). The first is strictly greater, because

    (49/16)(rho^2-(61/60)^2)
       -(rho^2-(233/240)^2)=5951/15360>0.

All denominators are positive on the full comparison interval. Hence

    length(6)>L_0=asin(233/270)-acos(271/300)>delta_0. (7)

For the last exact comparison, L_0 lies in (0,pi/2), since
(233/270)^2+(271/300)^2>1. The cosine addition formula gives

    cos L_0
      =[sqrt(1366810451)+sqrt(898971551)]/81000
      <(36971+29983)/81000=11159/13500.

The two positive square reserves are 44390 and 8738. This reproduces
the complete continuous small-root arc calculation; no actual root degree,
force, or contact mean is involved.

Both larger arcs in (7) lie in the western real-leaf gap. For completeness
put nu=asin(3/80), phi_+=asin(s_+), phi_-=asin(s_-), and choose
the actual leaf-angle lift

    theta_+ in [pi/2-nu,pi/2+nu],
    theta_- in [3pi/2-nu,3pi/2+nu].

One has nu<3/79<1/25. The H arc begins beyond
pi/2+phi_++acos((1+h)/rho), which is greater than
pi/2+alpha_0, where

    alpha_0=acos(122/135)>pi/8>nu.

It ends before pi+phi_+<pi+nu<theta_-. Thus it lies strictly
between the two real leaf centers. The reflected K arc does too. Actual
interior disjointness from both leaves therefore puts both arcs in the
western gap between their full closed circle arcs. They are mutually
disjoint and occupy total angular measure strictly greater than 2delta_0.

This placement concerns the complete chosen root arcs (6), not just their
centers. No connectedness of either root's remaining circle pieces is
asserted or required.

## 4. A uniform one-completion capacity in the western gap

The real S-leaf halfwidth is exactly

    alpha=min(acos(d/rho),beta_0), beta_0=asin(4/9),
    alpha>alpha_0=acos(122/135).

The western gap length is therefore at most
pi+2nu-2alpha, and is strictly less than pi+2nu-2alpha_0.
After its two actual root arcs from (7), the remaining total angular
measure is strictly less than

    W=pi+2nu-2alpha_0-2delta_0.                    (8)

The following exact comparisons give W<delta+phi:

    alpha_0>53/120,
    delta_0>179/300,
    phi>9/20,
    nu<3/79,
    157/50<pi<22/7.                               (9)

The final pi bounds are weaker than the classical Archimedean bounds.
For the first three, use the alternating-series lower bound

    cos x>=1-x^2/2+x^4/24-x^6/720, 0<=x<=1.

Subtracting the three target cosines gives, respectively,

    at x=53/120, target 122/135:
       724021030871/2149908480000000>0;
    at x=179/300, target 11159/13500:
       325519225255079/524880000000000000>0;
    at x=9/20, target 9/10:
       2288951/5120000000>0.

Cosine is decreasing on [0,pi/2], proving the stated lower-angle
bounds. The nu bound was proved by integrating asin's derivative, as
in the balanced source. Thus

    W<22/7+6/79-53/60-179/150
       =189481/165900
       <1033/900
       =(2/9)(157/50)+9/20<delta+phi.             (10)

The strict central rational reserve is 1403/248850. The estimates are
single exact angle bounds on the whole physical domain, not sampled
orientations.

By (3), any two of the three actual completion center components would
occupy more than delta+phi. Equation (10) makes that impossible in
the western gap. Its completion capacity is at most one even when the
one weaker completion component lies there.

## 5. Every small leaf gap has capacity at most one for the weaker components

The upper East-to-North and lower South-to-East leaf gaps each have
length strictly less than

    pi/2+nu-2alpha_0<pi/4+1/25
       <11/14+1/25=289/350<9/10<2phi.             (11)

Here alpha_0>pi/8, nu<1/25 and pi<22/7 were already established;
the rational reserve 9/10-289/350 is 13/175. Every completion
component is longer than phi. Thus at most one can occupy each small
gap. The argument retains the physical circle pieces outside a chosen
center component and requires no global connectedness of a completing
square's full intersection.

## 6. An unbalanced middle empties one small gap, including the strip-limited leaf

Suppose a>3/4. Put

    lambda=acos(d/rho), beta_a=asin(a/rho),
    beta_* =asin(2/3).

The actual T has a closed circle arc from lambda to beta_a in the
upper-right quadrant. Indeed the actual near first face is strictly
behind that entire arc; the actual top face supplies beta_a; and

    lambda<acos(8/9)<pi/6<beta_*<beta_a.

The East leaf covers from zero to alpha=min(lambda,beta_0). If
alpha=lambda, these two occupied arcs meet. If alpha=beta_0<lambda,
there is a genuine early gap between beta_0 and lambda. That gap is
retained here, not silently filled by T. Its length is less than

    pi/6-beta_0<pi/24<phi,                          (12)

because beta_0>pi/8 and phi>pi/8. These lower-angle comparisons
follow from the usual half-angle formula: cos(pi/8)^2>17/20,
whereas cos(beta_0)^2=65/81<17/20 and cos(phi)^2=81/100<17/20.

After the actual T arc, the remaining upper small-gap interval has
length at most theta_+-alpha-beta_a, and hence less than

    D_*:=pi/2+nu-alpha_0-beta_*<phi.               (13)

The exact final comparison is proved next. If T reaches or passes the
North leaf arc, this latter interval is empty and the conclusion only
strengthens. A connected completion center component cannot cross the
actual closed T arc. It would have to lie entirely in the early interval
of (12) or in the late interval of (13). Neither can hold a component
longer than phi. The upper small gap therefore has capacity zero.

If b>3/4, reflect the entire physical chart and exchange upper and lower
labels. The same proof empties the lower small gap. This covers both
unbalanced slider alternatives without altering either original mean.

### Exact comparison for (13)

Set A_*=alpha_0+beta_*. Since alpha_0<pi/6 and beta_*<pi/4,
one has A_*<5pi/12<pi/2. Also A_*>alpha_0>nu. Hence
D_* lies in (0,pi/2), where sine is increasing. Its exact sine is

    sin D_*
      =[(122sqrt(5)-2sqrt(3341))sqrt(6391)
         +3(sqrt(16705)+244)]/32400.

The first bracket is positive: sqrt(5)>2 and sqrt(3341)<58
give the lower bound 128. Use the exact radical bounds

    sqrt(5)<9/4, sqrt(3341)>289/5,
    sqrt(6391)<80, sqrt(16705)<130.

Their respective squared reserves are 1/16, 4/25, 9 and 195.
Therefore

    sin D_*<[(122(9/4)-2(289/5))80+3(130+244)]/32400
           =6917/16200<43/100<sqrt(19)/10=sin phi.

The final rational and squared reserves are 49/16200 and 51/10000.
Since phi too lies in (0,pi/2), this proves D_*<phi with strict
reserve at every actual leaf-angle and radius endpoint.

## 7. Complete join over the unchanged middle slider

In either unbalanced alternative, the western gap holds at most one
completion center component by Section 4. One small gap is empty by
Section 6, and the other holds at most one by Section 5. All three
completion components cannot be assigned to these actual gaps. This
contradicts the hypothetical nine-unit collection.

The balanced source handles a,b>=1/4. Its complement in the complete
closed domain a,b>=0, a+b=1 is precisely a>3/4 or b>3/4, just
excluded. Thus the theorem of Section 1 is proved for every original
middle slider, including a=0, b=0 and both joins a=1/4 or b=1/4.
Some endpoint charts may already be incompatible with actual contacts;
no such additional incompatibility is needed or assumed here.

The mixed aligned/small-tilted and the two-small-tilted original parallel
triangle branches transfer directly via the physical charts and complete
leaf features in Section 7 of the balanced source. Their original middle
force ratio, outer degrees, private-return stars, all shared means, circle
weights and completing units are arbitrary in this theorem. A North/South
leaf was not substituted for any West-type alternative. Entire original
graph-family closure still requires the other already accepted or newly
reviewed interfaces to exhaust that family's original domain.

## 8. Exact input versions and scope of review

| Complete source | SHA256 | Consumed role |
| --- | --- | --- |
| BALANCED_MIDDLE_TWO_SMALL_NORTH_SOUTH_ROOTS_FORCE_FREE_NINE_UNIT_EXCLUSION_2026_10_29.md | c3978aecc0dbe3f3ff0645f224d7d8e9f18d9353059862d3618deb7ec451afbf | Entire a,b>=1/4 physical theorem and literal aligned/small-tilted chart transfer; this source has been fully independently reviewed by root_triangles and awaits root adoption |
| THREE_NEAR_UNITS_COMPLETION_CENTER_COMPONENT_ARCS_AND_REAL_S_LEAF_BUDGET_2026_10_29.md | fdc1a41c0f405782b2b4f901d45a3c05a6aa56bc9529ea50a48e5a7f14faf9fa | The complete actual nine-unit center-component theorem: every completion component longer than phi and at least two longer than 2pi/9, with disconnected other pieces retained |
| THREE_REAL_S_LEAF_ROOTS_WITH_TWO_EPSILON_VERTICES_NINE_UNIT_EXCLUSION_2026_10_29.md | 3eca9443f10f1bb6b3ccb46f5fad25f64951fa0dd8c1fe87e0aed62d2de8931e | Only provenance for the full one-root continuous arc calculation, reproduced in Sections 2--3; its three-small-root capacity conclusion is not used |

Both immutable pre-existing input files were read completely and their
local bytes verified against the current immutable Git blobs. The full
balanced source was independently reviewed at its exact printed pin.
The new unbalanced proof and whole-slider join require their own full
independent review before adoption.

This theorem is physical and force-free. It needs no common-selection
compatibility premise, stress certificate or graph embedding. Original
graph callers keep all of their own prerequisites; this source does not
repair a missing global extraction argument. No actual unit, selected
normal, mean, original load or true degree was changed. No numerical pose
search, angle mesh, new packing certificate, Lean/Lake build, CI/workflow,
metadata edit, remote mutation or merge was performed.
