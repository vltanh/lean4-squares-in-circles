# Equal-circle heights force a perpendicular adjacent-tip hub near the origin

Date: October 28, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed hand theorem, frozen for a separate full
independent review.** The first theorem is a geometric scalar statement
about two actual points on one circle. The second applies it to an
actual perpendicular contact triangle with a true loaded degree-two
tip. The degrees, loads and all equations of the other two units are
arbitrary and remain unchanged.

This source has no third-hub-neighbor, boundary-path, pocket-capacity
or original graph/load exclusion premise. Its conditional final
consequence concerns three actual units near the origin. Original
completion occupancy must be proved separately before that consequence
can be used.

Put

    Q=1105/256, 2<R<=sqrt(Q).

All geometric data are in the unchanged plane about the original
circle center O.

## 1. A complete equal-circle-height comparison

Let real c,s,C,S,beta,L,H satisfy

    c^2+s^2=C^2+S^2=1,
    0<s<2/5, c>9/10,
    0<=C<S, S>0,
    s/S<=beta<=1.                                    (A)

Define the two points

    Z_1=(L-c-s+beta*C, H+c),
    Z_2=(L+C+S, H+s+(1-beta)*S-C).                    (B)

Suppose both are on the actual circle of radius R and both have
strictly positive second coordinate.

**Theorem A.** Necessarily L>0.

The points need not be square corners for this geometric statement.
No force, circle coefficient, degree, load or contact owner is part
of its hypotheses. The whole closed beta interval in (A), including
beta=s/S, beta=1 and C=0, is retained. The positive-height hypotheses
are actual hypotheses; equal squared norms alone do not supply them.

### 1.1. Reduction to the least permitted beta

Write

    a=c+s-beta*C, b=C+S,
    d_0=c-s+C-(1-beta)*S.

Since C<S and C^2+S^2=1, C<1/sqrt(2)<c. Hence

    0<a<=c+s<sqrt(2), 1<=b<=sqrt(2).                 (C)

Both positive circle heights in (B) are therefore their positive
square roots, and

    d_0=D(L),
    D(z)=sqrt(R^2-(z-a)^2)-sqrt(R^2-(z+b)^2).         (D)

Suppose L<=0. The two square roots remain real and strictly positive
throughout z from L to 0. Indeed their arguments at L are strictly
inside (-R,R) by the actual positive heights, and those at 0 are
strictly inside by (C); each argument is affine in z.

The function

    G(t)=t/sqrt(R^2-t^2)

is strictly increasing on (-R,R). Thus

    D'(z)=G(z+b)-G(z-a)>0

throughout that interval, because a+b>0. Consequently

    d_0<=D(0).                                      (E)

This derivative proof includes a possible negative L+b. It does not
assume the second point lies to the right of the vertical axis.

Now regard beta as a scalar comparison variable at fixed original
c,s,C,S,R. On the interval s/S<=beta<=the original beta, (C) continues
to hold. Differentiating the difference at z=0 gives

    d/dbeta [D(0)-d_0]
      =a*C/sqrt(R^2-a^2)-S<0.                       (F)

For the strict inequality, a<sqrt(2) and R>2 imply
a/sqrt(R^2-a^2)<1, while C<S. If C=0 the derivative is exactly -S.
No new geometric configuration is asserted during this scalar
comparison.

At the lower endpoint beta=s/S put

    a_0=c+s*(1-C/S),
    k_0=c+C-S,
    J=sqrt(R^2-a_0^2)-sqrt(R^2-b^2)-k_0.

Equation (F) shows

    D(0)-d_0<=J.                                    (G)

It remains to prove J<0 on the entire domain (A). This will contradict
(E), including L=0 and the endpoint beta=s/S.

### 1.2. One strict comparison shared by both sign cases

We first prove

    k_0>b-a_0.                                      (H)

The exact difference is

    k_0-(b-a_0)=2*(c-S)+s*(1-C/S).

If S<=c, it is strictly positive because s>0 and C<S.
If S>c, the two unit-circle identities give C<s and

    2*(S-c)=2*(s^2-C^2)/(S+c)
       <(10/9)*s^2<(4/9)*s.

Also C/S<s/c<4/9, so

    s*(1-C/S)>(5/9)*s.

The same difference is then greater than s/9>0. This proves (H)
without a missing S=c endpoint.

### 1.3. The complete case k_0>=0

If a_0>b, the square-root difference defining J is negative, so
J<0 immediately. If a_0=b, (H) gives k_0>0 and again J<0.

If a_0<b, every z between them satisfies

    0<z<sqrt(2), z/sqrt(R^2-z^2)<1.

Integrating the derivative of sqrt(R^2-z^2), or applying the mean
value theorem, gives

    sqrt(R^2-a_0^2)-sqrt(R^2-b^2)<b-a_0<k_0.

Thus J<0 on all of k_0>=0, including k_0=0.

### 1.4. The complete case k_0<0

Put

    d=S-C-c=-k_0>0.

Then S>c>9/10 and

    0<=C<S-c<=1-c<1/10,
    s*(1-C/S)>(8/9)*s.                              (I)

The exact comparison needed below is

    2*C+(17/6)*d
       <=(17/6)*(1-c)-(5/6)*C
       <=(17/6)*s^2/(1+c)
       <(85/57)*s^2
       <(34/57)*s
       <(8/9)*s.                                   (J)

Here the last strict rational reserve is
8/9-34/57=50/171>0. Combining (I)--(J),

    a_0-b=s*(1-C/S)-2*C-d>(11/6)*d>0.               (K)

In particular the entire interval [b,a_0] lies in [1,sqrt(2)).
The actual radius bound gives

    R^2-1<=849/256<121/36,
    121/36-849/256=103/2304>0.

Hence, throughout that interval,

    z/sqrt(R^2-z^2)
       >=1/sqrt(R^2-1)>6/11.

Integrating this strict lower bound and using (K) gives

    sqrt(R^2-b^2)-sqrt(R^2-a_0^2)
       >(6/11)*(a_0-b)>d.

Therefore J<0 in this second complete case as well. Equations
(E)--(G) now contradict L<=0. Theorem A is proved.

## 2. The actual perpendicular contact-triangle theorem

Keep actual pairwise interior-disjoint closed unit squares U,V,W
contained in D_R, with their original physical contact data and full
original equations. The original positive U-to-V and U-to-W normals
are perpendicular own side axes of U. The actual V is a positively
circle-loaded true degree-two body whose only positive pair contacts
are UV and VW. The actual W is physically boundary.

No degree or load restriction is imposed on U or W. Every positive
force in their real stars remains. In particular W need not be a
degree-two body, and no equation at U is used below.

Assume V is nonparallel to U, and its original V-to-W normal is an
own side normal of W but is not an own side normal of V. Normalize
the unchanged geometry by a rotation or reflection about O:

    U=[L-1,L] x [H-1,H],
    n_UV=North, n_UW=East,
    P=(L-p,H),
    e_1=(c,s), e_2=(-s,c), c,s>0,
    V=P+[0,1]e_1+[0,1]e_2.

The unique-adjacent physical mask means that V has exactly one
physical circle corner, namely P+e_2. No selected individual circle
coefficient replaces this physical condition. All original
applications and full shared-side means remain fixed.

**Theorem B.** On the entire stated domain,

    0<L<1/2, 93/200<H<61/60,
    dist(O,U)<1/60,
    every actual U vertex has norm>1/15,
    U is contained in int D_(3/2).                  (L)

In particular U is physically circle-clear. This conclusion is
derived from the actual geometry, not inferred from a zero circle
multiplier or imposed as an additional hypothesis.

For later uses, if two other distinct actual units E,N satisfy

    dist(O,E)<=1/40, dist(O,N)<=1/40,
    every E or N vertex has norm>19/300,             (M)

then the three actual units U,E,N cannot have pairwise disjoint
open interiors. This conditional consequence is proved in Section 6.
It asserts no face allocation or occupancy.

## 3. Complete local entry at the arbitrary-U/W-degree scope

The complete local derivation is reproduced in Appendix A. It is
Sections 2--6 of the frozen adjacent-tip source a1e480, with its
local equations retained. The surrounding all-loaded path hypothesis
is not imported. The following are the only physical inputs used in
that derivation:

- the force-free Southeast normal-cone lemma for two perpendicular
  supports of an actual unit;
- the full all-owner common-point theorem at the true loaded V2
  with the actual physical-boundary neighbor W;
- the complete true V2 force and torque equations and its actual
  unique-circle mask;
- actual U,V,W side/vertex support geometry and circle containment;
- proper concurrence only at the true V2, with its real boundary
  neighbor W.

The appendix does not use an equation of U, does not shorten W's
star, does not require a third hub neighbor, and does not invoke
the old all-loaded path, its endpoint T, a selector, or a pocket
conclusion. Every initial physical W mask, both own-center ties,
the complete original UW mean, the aligned W frame C=0 and the
original W-side endpoint are checked there. Thus its local proof
applies literally to the broadened hypotheses of Theorem B.

For clarity, its complete resulting actual chart is

    M=P+e_1,
    f=(C,S), g=(S,-C), C>=0, S>0,
    W=M+[-beta,1-beta]f+[0,1]g,
    p=c-beta*C, delta=beta*S-s>=0,
    0<p<=c<1, 0<=delta<1,
    M_UW=(L,H-delta_0), 0<=delta_0<=delta,
    delta_0=delta when C>0.

With

    gamma=c*C+s*S,
    eta=c*S-s*C,
    alpha=s/S,
    kappa=c/S,
    tau=1-beta,

the full local proof gives

    gamma^2+eta^2=1, eta>gamma>0,
    alpha<=min(beta,gamma),
    gamma*alpha+eta*kappa=1,
    beta<2/5, beta*gamma<1/4,
    s<2/5, c>9/10.                                 (N)

The condition eta>gamma implies C<S, since
eta-gamma=(c-s)*S-(c+s)*C>0. It also gives c>s.

In V own coordinates the actual sole circle point, and its genuine
positive proper concurrence, satisfy

    Z_V=(-x,y), P=(-x,y-1), M=(1-x,y-1),
    x^2+y^2=R^2,
    q_V=lambda*Z_V,
    0<lambda<1, K=1/(1-lambda)>1,
    x=K*gamma*alpha,
    y=K*(1-gamma*kappa).

The complete continuous comparison in Appendix A proves

    1/2<x<3/4, sqrt(55)/4<y<121/60.                (O)

The actual W mask is forced to its single corner
Z_W=M+tau*f+g, including every original zero individual
coefficient alternative before that physical mask is established.
The exact circle equality yields the comparison scalar

    d_*=F(gamma,tau)
       =(tau^2+tau*gamma+eta)/
                   (2*(1+gamma-tau*eta))
       >sqrt(R^2-1/4)-1>187/200.                   (P)

This is a comparison scalar, not a physical radial parameter.
No upper bound on d_* is assumed. Along eta=sqrt(1-gamma^2),
F increases in tau and decreases in gamma; at fixed gamma,tau
it also increases when eta is enlarged with positive denominator.
The complete derivatives and all continuous bounds underlying
(N)--(P) are included in Appendix A.

Returning to global coordinates gives the exact original U location

    L=c*(1-x)-s*(y-1)-beta*C,
    H=c*(y-1)-s*x.                                  (Q)

Equations (N)--(O) immediately give

    L<1/2,
    H>(9/10)*(17/20)-(2/5)*(3/4)=93/200,
    H<y-1<61/60.                                   (R)

Here sqrt(55)/4>37/20, so y-1>17/20. No sign of L is
assumed in (R).

## 4. The new whole-domain support and origin bound

The actual physical circle corners in global coordinates are exactly

    Z_V=(L-c-s+beta*C,H+c),
    Z_W=(L+C+S,H+s+(1-beta)*S-C).                   (S)

The first height is positive by (R). The second is positive as well:
using C<S and beta<2/5,

    H+s+(1-beta)*S-C
       >H-beta*S>93/200-2/5=13/200>0.               (T)

Thus the positive square-root branch in Theorem A is literal for
both actual circle corners. All its other hypotheses follow from
(N), C<S, and alpha=s/S<=beta. Theorem A proves

    L>0.                                            (U)

Together with (R) this proves the first two coordinate bounds in
(L). The actual horizontal interval of U contains zero in its
interior, and H>0. Therefore its exact distance to O is

    dist(O,U)=max(H-1,0)<1/60.                       (V)

This argument covers the whole original aligned UW mean interval.
Neither delta_0 nor any original force/application is moved. It
also includes every continuous parameter value permitted by the
actual physical mask, without selecting a sample or a smaller
orientation subdomain.

## 5. A stronger whole side bound keeps every vertex away from O

First sharpen (N) to

    beta*gamma<1/5.                                 (W)

Suppose beta*gamma>=1/5. Since beta<2/5, gamma>1/2.
If gamma<=3/5, then beta>=1/3 and tau<=2/3. The complete
monotonicities in (P), and sqrt(3)/2<7/8, give

    d_*<=F(1/2,2/3)<119/132<187/200.

The final strict reserve is 221/6600. If gamma>=3/5, then
gamma<1/sqrt(2)<4/5 gives beta>1/4 and tau<3/4. Hence

    d_*<F(3/5,3/4)=29/32<187/200.

The final reserve is 23/800. These two closed ranges cover every
gamma>1/2 and include their common endpoint. Both contradict (P).
Thus (W) is proved on the full domain.

Since C=c*gamma-s*eta and eta,s>0, it follows that

    beta*C<c/5.                                    (X)

Both left vertices of U have absolute first coordinate 1-L>1/2.
Both upper vertices have second coordinate H>93/200. Only the
lower-right vertex Q_U=(L,H-1) remains.

Its displacement from the actual circle corner in (S) is

    Z_V-Q_U=(-c-s+beta*C,c+1).

Equation (X) gives

    |Z_V-Q_U|^2>((4/5)*c+s)^2+(c+1)^2>116/25.       (Y)

For the second inequality, its exact difference from 116/25 is

    s*[(8/5)*c-s*(16/25+2/(1+c))].

The bracket is greater than

    (8/5)*(9/10)-(2/5)*(16/25+2)=48/125>0.

Thus (Y) is strict even as the tilt tends to zero. The actual
triangle inequality and R<25/12 now give

    |Q_U|>=|Z_V-Q_U|-|Z_V|
       >2sqrt(29)/5-25/12>1/15.                    (Z)

The last comparison is exact:

    (2sqrt(29)/5)^2-(43/20)^2=7/400>0,
    43/20-25/12=1/15.

Every actual U vertex has therefore been covered, proving the
vertex assertion in (L).

For every point (u,v) of U the coordinate bounds already proved
give |u|<1 and |v|<61/60. Consequently

    u^2+v^2<1+(61/60)^2=7321/3600<9/4.

Thus U is contained in the open 3/2 disk, proving the final
assertion of Theorem B and its physical circle-clear consequence.

## 6. The degree-free conditional three-unit consequence

Suppose two other actual units E,N satisfy (M). Theorem B gives

    dist(O,U)<1/60<13/300,
    every U vertex norm>1/15>19/300.

Apply the complete unequal near-origin angular-budget theorem741
to the unchanged units U,E,N at test radius 19/300. Their normalized
distance bounds are 13/19,15/38,15/38. The exact comparison is

    cos(2acos(15/38))=-497/722,
    cos(pi-acos(13/19))=-494/722.

The strict reserve 3/722 forces the three actual open-interior
angular measures to exceed a full turn, contradicting disjoint
open interiors. That theorem includes O outside a unit, on its
boundary, or in its interior, and both closed 1/40 distance endpoints.

This proves the conditional consequence of Theorem B. No original
central or channel occupancy has been inferred here. Any original
caller must establish its own complete face allocation and provide
the two real units E,N at their actual scopes.

## 7. Exact inputs, proof provenance and verification boundary

| Complete source or review | SHA256 | Exact operative use |
| --- | --- | --- |
| PERPENDICULAR_HUB_W_OWNED_ADJACENT_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | a1e480fc3b636f5ccbba676336be93ea997a4ec3b99a9b98b8983ef19e848165 | Only its complete local Sections 2--6, reproduced in Appendix A and applied at their actual arbitrary-U/W-degree scope; no old path or pocket conclusion |
| REVIEW_PERPENDICULAR_W_OWNED_ADJACENT_CIRCLE_POCKET_CYCLES_2026_10_28.md | e944147021a28a810e261917f8c3de375b96c6236e81b6fe2a736170ad3593c8 | Complete separate independent audit of a1e480, including full local owner/mask/mean and continuous scalar cover |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Only Section 2, the force-free perpendicular-neighbor Southeast normal cone |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Complete all-owner P not in physical-boundary W at the true loaded V2, with arbitrary U/W degrees and all means |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Only complete Lemma 2.1, positive proper concurrence at the true loaded V2 with actual boundary neighbor W |
| UNEQUAL_NEAR_ORIGIN_UNIT_ANGULAR_BUDGET.md | 741ff2415b91fa8d490c601185994b7d947e000003c1ca702e423677eea3684e | Complete conditional three-actual-unit contradiction, including every origin location and closed distance endpoint |

The entire old source and its entire independent review were read
for this continuation, not merely the displayed excerpts. The new
equal-circle-height comparison, the stronger beta*gamma bound, all
four vertex bounds, and the arbitrary-U/W-degree and conditional
exports above require a fresh full independent review.

Roof continuation assisted as a discovery collaborator. It first
developed separate large-gamma bounds, which are not operative here,
then checked the entire new circle-root comparison including both
k_0 signs, C=0, the full beta interval, radical domains and the
actual positive-height guard before freezing. That contribution
is not represented as an independent review. Review-resume, which
supplied none of this discovery, is the separate requested reviewer.

Only exact rational arithmetic was used to check the displayed
transcriptions and reserves. There was no pose sampling, angle mesh,
numerical packing exclusion, normal reselection, mean substitution,
force deletion, artificial degree-two neighbor, removed physical
corner, Lean/Lake operation, build, CI/workflow, remote write,
commit, shared metadata edit or original flag/count change.

## Appendix A. Complete local derivation at the broadened degree scope

The following is the entire local argument from a1e480 Sections
2--6. Its equation numbers are retained within this appendix.
Only heading prefixes are changed. The arbitrary U/W degrees of
Theorem B are sufficient at every step, as itemized in Section 3
above. No U3 equation, T endpoint or boundary-path conclusion
appears in this appendix.

### A.2. Complete actual W-owned chart, including aligned means

Rotate and, if necessary, reflect the entire physical data about the unchanged origin so that U-to-V is North and U-to-W is East. Write

    U=[L-1,L] x [H-1,H],
    P=(L-p,H), 0<=p<=1,
    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (1)

The actual UV intersection is the singleton P, the bottom vertex of the nonparallel V.

The force-free perpendicular-neighbor direction lemma places the original V-to-W normal in the closed Southeast cone. The all-owner common-point theorem at true loaded V2 with physical-boundary W gives P not in W, since R^2>4>13/4.

The Southeast normal has negative e_2 component. Its e_1 component cannot vanish because it is not a V own axis. A negative e_1 component would expose P itself, contradicting P not in W. Thus the unchanged actual VW point is

    M=P+e_1.                                        (2)

Name W's inward normal and side tangent as

    g=(S,-C), f=(C,S),
    C>=0, S>0, C^2+S^2=1.

The endpoint S=0 would have negative e_1 component and is impossible. If C>0, W has a unique left vertex Q_W. If C=0, let Q_W be its lower-left corner. The entire actual square and the unchanged VW point are

    W=Q_W+[0,1]f+[0,1]g,
    M=Q_W+beta*f, 0<=beta<=1.                       (3)

Its UW support is x=L, while M has height H+s. The actual original UW application is at height at most H. Consequently

    Q_W=(L,H-delta),
    p=c-beta*C,
    delta=beta*S-s>=0.                              (4)

Hence beta>0. The strict positive e_1 component of g gives

    eta=c*S-s*C>0,
    C<c, S>s,
    0<p<=c<1, 0<=delta<1, 0<beta<=1.                (5)

The equality p=c is retained when C=0.

For C>0 the original UW application is Q_W. For C=0, the lower-left point Q_W itself lies on the U right side, since its height H+s-beta is above H-1. The actual original UW mean is, in every case,

    M_UW=(L,H-delta_0), 0<=delta_0<=delta,            (6)

where delta_0=delta if C>0. No force equation replaces an aligned mean by Q_W.

Set

    gamma=c*C+s*S>0,
    gamma^2+eta^2=1,
    r=C/S>=0,
    alpha=s/S=gamma-r*eta,
    kappa=c/S=eta+r*gamma,
    tau=1-beta in [0,1).                            (7)

Then

    alpha>0, alpha<=beta, alpha<=gamma,
    gamma*alpha+eta*kappa=1,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.                            (8)

These identities include the whole aligned frame C=0 and the actual W-side endpoint beta=1.

### A.3. Full V2 equations on the unique-adjacent physical mask

Let mu,nu>0 be the unchanged UV and VW magnitudes. The full outward circle resultant is

    F_V=mu*North-nu*g,
    F_V.e_2=mu*c+nu*gamma>0.                        (9)

Thus P.e_2>=-1/2. Equality would make P or M a physical circle corner, because the other own center coordinate is nonzero when R>2. A containing-circle point cannot belong to two interior-disjoint contained units: their open inward right-angle sectors would both have to fit into the same strict inward radial half-plane. Hence P.e_2>-1/2.

In the present physical mask P.e_1<-1/2. Write the actual corner, points and sole full circle resultant as

    Z_V=(-x,y), P=(-x,y-1), M=(1-x,y-1),
    x>1/2, y>1/2,
    F_V=Lambda*Z_V, Lambda>0.                       (10)

The pair lines meet at the actual concurrence

    q_V=P+(gamma/S)*North
       =(-x+gamma*alpha,y-1+gamma*kappa).            (11)

Indeed (q_V-M).f=0. The full all-mask proper-concurrence lemma, applicable because W is a physical boundary neighbor of true V2, gives q_V=lambda*Z_V with lambda>0. The first component yields

    (1-lambda)*x=gamma*alpha>0.

Thus lambda<1 and K=1/(1-lambda)>1. The unchanged equations give

    x=K*gamma*alpha,
    y=K*(1-gamma*kappa).                            (12)

There is no assumption that a concurrence of some other unit lies inside it.

Dotting the original full (9) with f gives F_V.f=mu*S>0. On the other hand, (8),(12) give

    Z_V.f=K*(eta-gamma).

Therefore

    eta>gamma>0, gamma<1/sqrt(2).                   (13)

Also kappa-alpha=eta-gamma+r*(eta+gamma)>0, so c>s. Since

    gamma*(alpha+kappa)
      =gamma*(gamma+eta+r*(gamma-eta))
      <=gamma*(gamma+eta)<1,

equation (12) gives

    y>x.                                           (14)

A useful exact form of the same unchanged equation is

    x/y=gamma*eta*alpha/
             (eta-gamma+gamma^2*alpha)
        <=gamma^2/(1-gamma*eta).                    (15)

The inequality uses alpha<=gamma and the strict positivity of eta-gamma. It retains the aligned equality alpha=gamma.

### A.4. Every physical W mask is forced to one actual corner

Use W own coordinates. Put

    h=eta-gamma>0,
    j=eta+gamma<sqrt(2),
    v=eta*x+gamma*y>0.

Then

    Z_V.f=K*h, Z_V.g=-v,
    M.f=(K-1)*h=:m>0,
    M.g=j-v=:z.

The W center coordinates are m+1/2-beta and z+1/2.

First suppose z+1/2<=0. Then v>=j+1/2. Since eta>gamma and y>x,

    v=eta*x+gamma*y < j*(x+y)/2.

Consequently

    x+y>2+1/j>2+1/sqrt(2)>27/10>R+1/2.

Here R<25/12. Thus

    |M|^2=R^2+2-2(x+y)<(R-1)^2.

Every maximum-norm W corner lies on its minimum-g side. Its only two candidates are Q_W and M+tau*f. The first belongs to U, so it is not a containing-circle point. The second is strictly inside D_R because |M|<R-1 and tau<1. This contradicts physical boundary status, including the zero g-center tie. Hence z+1/2>0.

Now suppose m+1/2-beta<=0. Then m<=beta-1/2<=1/2, so

    K*h=m+h<3/2,
    v=sqrt(R^2-(K*h)^2)>sqrt(7)/2>5/4.

It follows that

    1/2<z+1=j+1-v<5/4,
    -1<m-beta<=-1/2.

The actual maximum-norm corner on the minimum-f, maximum-g side is Q_W+g. Its squared norm is strictly less than

    1+25/16=41/16<4<R^2.

That contradicts boundary status, including a zero f-center tie. Both own center coordinates of W are therefore strictly positive.

Thus the unique actual W circle corner is

    Z_W=M+tau*f+g=Z_V+(A_1,-B_1),                  (16)
    A_1=1+eta+tau*gamma,
    B_1=1+gamma-tau*eta.

Here

    A_1>B_1>0, A_1<1+sqrt(2)<5/2.

The exact unchanged circle equation is

    2*A_1*x+2*B_1*y=A_1^2+B_1^2=:N.               (17)

No W equation or load has been discarded. This section covers all initially possible W physical masks and every side parameter endpoint.

### A.5. A comparison scalar and two whole-domain side-parameter bounds

On the line (17), y decreases with x with slope -A_1/B_1. Its squared norm decreases strictly while y>x>0. At the diagonal endpoint x=y, its squared norm is

    N^2/[2*(A_1+B_1)^2] <= A_1^2/2 <25/8<4.

The actual point has x>1/2, y>x and squared norm R^2>4. Moving left along the same line to x=1/2 therefore gives a point (1/2,1+d_*) of strictly greater norm. Expanding (17) at that endpoint gives

    d_*=F(gamma,tau)
       :=(tau^2+tau*gamma+eta)/
              (2*(1+gamma-tau*eta))
        >sqrt(R^2-1/4)-1>187/200.                  (18)

This is only a scalar comparison. No physical radial square or new circle application has been inserted. In particular no upper bound on d_* is assumed.

On 0<gamma<1, 0<=tau<=1, F is strictly increasing in tau and strictly decreasing in gamma, with eta=sqrt(1-gamma^2). Its tau derivative has positive numerator

    (2tau+gamma)*(1+gamma-tau*eta)
        +eta*(tau^2+tau*gamma+eta).

Multiplying its gamma derivative numerator by eta gives

    tau*(1-tau)*eta-(1+tau^2)-(1+tau^3)*gamma<0.      (19)

If eta is enlarged independently at fixed gamma,tau, with positive denominator, F increases as well.

We claim

    beta<2/5.                                       (20)

Otherwise tau<=3/5. If gamma>=3/8, monotonicity and sqrt(55)/8<149/160 give

    d_*<=F(3/8,3/5)<1213/1306<187/200,

contrary to (18); the final reserve is 811/130600. Thus gamma<3/8. But (15) then gives

    x/y<9/40,
    x<(9/40)*(25/12)=15/32<1/2,

again a contradiction. This proves (20) on the entire domain.

Next,

    beta*gamma<1/4.                                 (21)

Otherwise gamma>5/8 by (20), beta>=1/4, and tau<=3/4. Using sqrt(39)/8<25/32 gives

    d_*<F(5/8,3/4)<116/133<9/10,

contrary to (18). The last reserve is 37/1330.

The useful consequences, valid for every aligned mean and every actual W-side endpoint, are

    s=alpha*S<2/5, c>9/10,
    beta*C=beta*(c*gamma-s*eta)<c/4.                (22)

### A.6. A uniform bound x<3/4 on the full continuous domain

Suppose, for contradiction, that x>=3/4. Then y<R<25/12 gives

    t=x/y>9/25=:t_0.

Solving (15)'s equality before its final inequality yields

    alpha=t*(eta-gamma)/
                 (gamma*(eta-t*gamma)).

The denominator is positive because t<1 and eta>gamma. This expression increases in t. Hence, with

    a(gamma)=t_0*(eta-gamma)/
                    (gamma*(eta-t_0*gamma)),

we have alpha>a(gamma), beta>=alpha and

    tau<1-a(gamma).                                 (23)

We also have gamma>9/20. If gamma<=9/20, the function gamma*sqrt(1-gamma^2) is increasing on this interval and is below 81/200; thus (15) would give

    t<81/238<9/25,

with reserve 117/5950.

The following three intervals are exhaustive.

#### A.6.1. The whole interval 9/20<gamma<=1/2

Put z=gamma/eta. Then z<=1/sqrt(3)<7/12 and 1/gamma>=2. Consequently

    a(gamma)>2*t_0*(1-7/12)/(1-t_0*(7/12))
            =30/79>3/8.

Thus tau<5/8. Monotonicity, and eta at gamma=9/20 being below 9/10, give

    d_*<F(9/20,5/8)<503/568<187/200.

The final reserve is 351/7100. This is impossible.

#### A.6.2. The whole interval 1/2<=gamma<=9/16

We prove that

    G(gamma)=F(gamma,1-a(gamma))

is increasing throughout this interval, and then bound its upper endpoint.

In terms of z=gamma/eta,

    a=t_0*sqrt(1+z^2)*(1-z)/(z*(1-t_0*z)),
    -a_z=a*[1/(z*(1+z^2))
                +(1-t_0)/((1-z)*(1-t_0*z))].        (24)

On the entire interval,

    4/7<z<7/10,
    1/4<a<2/5,
    3/5<tau_*=1-a<3/4,
    13/16<eta<7/8.                                 (25)

For the bounds on a: z<11/16 and 1/gamma>=16/9 give a>80/301>1/4. Formula (24) shows a decreases with z, hence with gamma; at the lower endpoint z>4/7 and 1/gamma=2 give a<54/139<2/5.

Equation (24) gives the strict derivative bound

    (tau_*)_z
      >(1/4)*(20/21+784/417)>7/10.                  (26)

For the first term use z*(1+z^2)<(7/10)*(3/2)=21/20. For the second use
(1-z)*(1-t_0*z)<(3/7)*(139/175)=417/1225.
The last reserve in (26) is 79/9730.

Write D=1+gamma-tau_* eta and N_*=tau_*^2+tau_* gamma+eta. The positive tau derivative numerator is

    T_*=(2tau_*+gamma)*D+eta*N_*
       >(17/10)*(27/32)
          +(13/16)*(9/25+3/10+13/16)
        =16837/6400>13/5.                          (27)

The reserve is 197/6400. The magnitude M_* of the negative gamma derivative numerator after multiplication by eta satisfies

    M_*=(1+tau_*^2)+(1+tau_*^3)*gamma
             -tau_*(1-tau_*)*eta
        <=2419/1024.                               (28)

Since gamma_z=eta^3 and eta^2<=3/4, the derivative of G with respect to z has the same sign as

    (tau_*)_z*T_*-eta^2*M_*
      >(7/10)*(13/5)-(3/4)*(2419/1024)
       =4943/102400>0.                             (29)

Thus G increases on the whole interval.

At gamma=9/16, z=9/sqrt(175)<109/160, so

    a>816/3019>27/100.

The latter reserve is 87/301900. Also eta<53/64. Therefore (23) and the monotonicities give

    d_*<G(9/16)
       <F(9/16,73/100)
       <141732/153275<187/200.                     (30)

The final reserve is 12641/1226200. This contradicts (18).

#### A.6.3. The whole interval gamma>=9/16

Let y_0 be the line (17)'s height at x=3/4:

    y_0=(N-(3/2)*A_1)/(2*B_1).

Since the actual x>=3/4 and y>x, norm monotonicity along this line gives

    R^2<=9/16+y_0^2.                               (31)

At fixed gamma, y_0 increases in tau. Its derivative numerator is

    -eta*tau^2+2*(1+gamma)*tau
                  +(1/2)*(1+gamma-eta)>0.

Thus

    y_0<=5/4+eta/[2*(1+gamma-eta)].

This last expression decreases with gamma; the derivative of eta/(1+gamma-eta) is
-(1+gamma)/(eta*(1+gamma-eta)^2)<0.
At gamma=9/16, eta<53/64 gives

    y_0<5/4+53/94=341/188.

Consequently

    R^2<9/16+(341/188)^2
       =4-2607/17672<4,

contradicting the radius lower bound.

All three intervals are impossible. We have proved the whole-domain result

    1/2<x<3/4,
    sqrt(55)/4<y<121/60.                            (32)

The upper y bound follows from x>1/2 and Q: the squared reserve
(121/60)^2-(Q-1/4) is 31/57600.

