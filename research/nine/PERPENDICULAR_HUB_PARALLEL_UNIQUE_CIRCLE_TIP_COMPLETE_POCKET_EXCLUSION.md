# Complete perpendicular-hub exclusion for a parallel unique-circle tip

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed hand theorem for the whole parallel-V unique-physical-circle feature, submitted for independent review.** Every actual VW return owner and the whole original UV shared mean are retained. The proof includes a weak support-endpoint extension of the wide inner-arc lemma, needed when the actual T port lies exactly on the closing cap line.

Put Q=1105/256 and work in 2<R<=sqrt(Q).

## 1. Complete original setting and theorem

Retain the same nine actual contained unit squares and their common previously selected physical certificate, including the strict point-contact normal convention. The entire positive component consists of an unloaded true-degree-three U, the positively loaded path

    V,W,B_3,...,B_(k-1),T, 3<=k<=6,

and exactly the three original spokes UV,UW,UT. Its actual outer-face order is U,V,W,...,T,U. V,T have their true loaded degree two; W has true loaded degree three; all other path units retain degree two. Every original force, torque, normal, positive magnitude, actual side mean, physical circle corner, individual zero coefficient and completing square remains.

Assume the original U-to-V and U-to-W normals are perpendicular own side axes of U. Assume V is parallel to U and has exactly one physical circle corner. No VW owner, W/T mask or contact-mean restriction is added.

**Theorem.** This entire original feature is impossible in D02.L01345. In every remaining nonparallel-W case below the actual closing pocket through U has capacity at most one; the parallel-W case is covered by the already complete adjacent shared-contact theorem. Every branch retains the complete central and three-extra allocation.

The proof is about the selected original certificate. It does not reselect an extracted normal or treat an endpoint-valued shared mean as a physical singleton.

## 2. Full parallel-W exit and unique V mask

Rotate and, if necessary, reflect all actual data about O so the original U-to-V and U-to-W normals are North and East. Write

    U=[L-1,L] x [H-1,H].                              (1)

For parallel U,V, an original North normal cannot be the retained normal of an isolated vertex/vertex contact: the selected strict point-contact convention puts such a normal inside both vertex cones, whereas North is their side-axis boundary. Thus the actual UV intersection has positive length, with its full original mean retained. If W is also parallel to U, the identical argument for the original East normal gives positive shared UW length. These are the two adjacent U faces. The complete adjacent shared-triangle D02 theorem excludes that whole original feature, with all masks and mean endpoints. No new selection is performed.

It remains to take W nonparallel to U. The force-free perpendicular-neighbor direction lemma puts the original V-to-W normal m in the closed Southeast quadrant. V's complete force equation is

    F_V=mu*North-nu*m, mu,nu>0,
    (F_V)_x<=0, (F_V)_y>0.                            (2)

Because V has one physical corner and positive total circle load, its resultant is a positive multiple of that corner. A unique farthest corner of a parallel square has both own coordinates of absolute value strictly greater than 1/2. Equation (2) therefore makes that corner strictly Northwest. Write

    Z_V=(-x,y), x>1/2, y>1/2,
    V=[-x,1-x] x [y-1,y],
    x^2+y^2=R^2,
    F_V=Lambda*Z_V, Lambda>0,
    H=y-1.                                          (3)

In particular m=(u,-v) with u>0,v>=0. The South endpoint is impossible in (2).

W's original minimum-x support is its unique vertex Q_W=(L,q), with H-1<=q<=H. If v>0, m exposes V's lower-right vertex. If v=0, the VW minimum-x point is Q_W; since it belongs to V, its height is at least H, while its UW height is at most H. Thus again the actual VW point is the singleton

    M=(1-x,y-1).                                    (4)

This proves the singleton premise also for the East return, rather than replacing a shared VW mean by a point.

## 3. The actual UV mean forces y>x and a whole normal-angle bound

Let the unchanged original UV mean be P=(p,H). Since P lies in V's bottom side,

    D=(1-x)-p in [0,1].

The complete common-point theorem applies to true loaded V2 and physical-boundary W, giving P not in W. Because M belongs to W, D is strictly positive.

Taking the complete V torque about the actual M, using (2),(3), gives

    mu*D=Lambda*(y-x).                               (5)

Indeed det(M,Z_V)=y-x and both original VW contributions are at M. Hence

    y>x>1/2, y>sqrt(2).                              (6)

The two force components give nu*u=Lambda*x and mu=Lambda*(y-x*v/u). Dividing (5) only by this positive original magnitude yields

    D=(y-x)/(y-x*v/u)<=1,
    0<=v/u<=1.                                       (7)

Every original UV mean, including both endpoints of its actual shared segment, remains. Equation (5) is not a fixed-tip selector invocation.

## 4. Exhaustive actual W support and the far side endpoint

Name W's actual inward axes at Q_W by

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1,
    W=Q_W+[0,1]f+[0,1]g.

Since m.g=u*S+v*C>0, an actual minimum-m point of W has g-coordinate zero. The unchanged point (4) therefore has the exhaustive form

    M=Q_W+beta*f, 0<=beta<=1,
    L=1-x-beta*C,
    q=y-1-beta*S.                                   (8)

The endpoints cover free vertex returns as well as any retained owned normal at an endpoint. A side-interior beta forces the original m to equal g; it is not a changed normal.

We first exclude beta=1 on the whole domain (6). Then W=M+[-1,0]f+[0,1]g. Its two corners M and Q_W=M-f are shared physical points with V and U, so both lie strictly inside D_R: a containing-circle point cannot be shared by two contained units with disjoint open interiors.

For each of the other two actual corners, write it as (-x+A,y-B). Its squared deficit is

    R^2-|(-x+A,y-B)|^2=2Ax+2By-A^2-B^2.              (9)

For fixed R and positive A,B, the expression Ax+B*sqrt(R^2-x^2) is concave in x on [1/2,R/sqrt(2)]. Its minimum occurs at an endpoint. Put a_0=sqrt(15)/2>3/2. At x=1/2 the circle height is at least a_0; at the other endpoint both coordinates are at least sqrt(2).

For M+g one has A=1+S, B=1+C. Half the deficit at the first endpoint is at least

    a_0-1-S/2+(a_0-1)C>a_0-3/2>0.

At the diagonal endpoint it is at least

    (2+S+C)*sqrt(2)-3/2-S-C
      =1/2+(sqrt(2)-1)*(2+S+C)>0.

For Q_W+g=M-f+g one has A=1+S-C>0, B=1+S+C>0. Half the deficit at the first endpoint is at least

    (a_0-3/2)*(1+S)+(a_0-1/2)*C>0,

and at the diagonal endpoint at least 2*(1+S)*(sqrt(2)-1)>0. Concavity proves both strict deficits on the entire actual domain. All four W corners are therefore strictly inside the circle, contradicting its physical boundary status.

This is a force-free whole-interval endpoint argument, not a selected W circle mask. It uses no upper bound on a comparison parameter.

## 5. The near side endpoint beta=0 forces x<1 directly

If beta=0, W=M+[0,1]f+[0,1]g and L=1-x. Suppose x>=1. Equation (6) gives y>x>=1. Since (x^2-1)(y^2-1)>=0,

    x+y>=1+sqrt(R^2-1).

Consequently

    |M|^2=R^2+2-2(x+y)
       <=(sqrt(R^2-1)-1)^2<1,                       (10)

because R^2<=Q<5 and R>=2. Thus M, M+f and M+g all lie strictly inside D_R, using |M|+1<2<R for the latter two.

The remaining corner is M+f+g=(-x+A,y-B), where

    A=1+C+S>0, B=1+C-S>0,
    A^2+B^2=2(A+B).

Its exact deficit (9) is

    2A*(x-1)+2B*(y-1)>0.

This too is strictly inside, contradicting physical boundary contact. Hence

    1/2<x<1                                          (11)

throughout the whole beta=0 domain, without imposing a W mask or return owner. The actual T port will have a=x in Section 7; that equality is retained explicitly.

## 6. Every interior side contact has x<1 and beta*C<1/4

Now take 0<beta<1 and put tau=1-beta in (0,1). The actual side-interior normal is m=g, so (7) gives C<=S. Set gamma=C, eta=S, h=eta-gamma>=0 and j=eta+gamma<=sqrt(2). In W coordinates define

    m_f=M.f=gamma*(1-x)+eta*(y-1)>0,
    v_0=eta*x+gamma*y>0,
    z=M.g=j-v_0,
    Z_V.f=m_f+h, Z_V.g=-v_0.                        (12)

The strict first inequality follows from y>sqrt(2)>1 when x<=1; when x>1 it follows from eta>=gamma and y>x. The equality gamma=eta is included.

The actual W center coordinates are m_f+1/2-beta and z+1/2. If z+1/2<=0, then v_0>=j+1/2. Since eta>=gamma and y>x,

    v_0<=j*(x+y)/2,
    x+y>=2+1/j>=2+1/sqrt(2)>R+1/2.

The last strict comparison uses R<25/12. Thus |M|<R-1. The only possible farthest corners on the minimum-g side are Q_W, which is shared with U and not a circle point, and M+tau*f, whose norm is below R. This excludes the alleged g-center sign, including its zero tie.

If m_f+1/2-beta<=0, then m_f<=beta-1/2<1/2 and

    0<Z_V.f=m_f+h<3/2,
    v_0=sqrt(R^2-(Z_V.f)^2)>sqrt(7)/2>5/4.

The already positive g-center and j<3/2 give

    1/2<z+1<5/4,
    -1<m_f-beta<=-1/2.

The farthest candidate Q_W+g then has squared norm below 1+25/16=41/16<4<R^2, impossible, including the f-center tie.

Both own center coordinates of W are positive. Its unique physical circle corner is therefore

    Z_W=M+tau*f+g=Z_V+(A_1,-B_1),
    A_1=1+eta+tau*gamma,
    B_1=1+gamma-tau*eta>0,
    A_1>B_1,
    2A_1*x+2B_1*y=A_1^2+B_1^2=:N.                 (13)

The strict A_1>B_1 follows even when eta=gamma, because tau>0. This mask forcing is the direct complete parallel-frame version of the adjacent-mask calculation; no tilted V force ratio is used.

The line in (13) has height at x=1 equal to

    y_1=1-(1-tau^2)/(2B_1)<1.

Since its height decreases with x and the actual y>x, it follows that x<1. The full open coordinate interval (11) is now proved in this case too.

Moving left on the same line from the actual x>1/2 to x=1/2 strictly increases squared norm: its derivative is 2*(x-(A_1/B_1)y)<0 throughout y>x. The height at x=1/2 is 1+d_*, with

    d_*=F(gamma,tau)
       =(tau^2+tau*gamma+eta)/[2*(1+gamma-tau*eta)]
        >sqrt(R^2-1/4)-1>187/200>11/12.             (14)

There is no asserted upper bound on d_* and no physical radial square is substituted.

Sections 4--5 of RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md give a purely algebraic implication for this exact F: if beta=1-tau and beta*gamma>=1/4, its three complete gamma intervals give F<11/12. Apply that proved scalar implication to (14), not the other theorem's physical radial-square premise. This yields

    beta*C<1/4.                                     (15)

All original beta, frame and physical-mask endpoints were either included above or excluded on their whole actual domains.

## 7. A proved weak support-endpoint extension of the wide matching theorem

The wide adjacent-circle matching theorem remains valid if its actual port premise a>x is weakened to a>=x, with all its other premises unchanged. Here is the complete check of the one altered argument; every subsequent scalar and routing premise is the same.

For a proposed T circle corner with Z_x>=-x, one now has w_x=(Z-P)_x>=0 rather than strictly positive. Its strict Southwest minimum-support direction still gives w_y<=0. Therefore the coordinate bounds become

    -x<=Z_x<=sqrt(2)-x,
    y-2-sqrt(2)<=Z_y<=b<y-1.

If x>=sqrt(2)/2, then |Z_x|<=x while |Z_y|<y because y>sqrt(3)>1+sqrt(2)/2. The norm contradiction remains strict. If x<sqrt(2)/2, the possibly weak coordinate bounds give

    |Z|^2-R^2
      <=8+4sqrt(2)-2sqrt(2)*x-(4+2sqrt(2))*y
       <4/5-(3/5)*sqrt(2)<-1/25.

Here y>9/5 and x>=1/2 supply the same strict final reserve as in the original source. Thus every actual T circle corner is still strictly left of x=-x.

All later arguments in that source use a>=x>=1/2, not a strict positive gap: the center's first-coordinate bound is still strict because sigma<17/24; on the short x interval |b|<1/4 and the upper bound a<=x+41/100 still put |P|<r_0; when b<0, |b|/a<1/5 still follows from b>-1/10 and a>=1/2. The two height/left-face derivative comparisons do not otherwise use a. The conditional capacity corollary depends only on the actual cap and angular-routing premises.

Consequently all conclusions of that complete theorem and its conditional capacity corollary hold at a=x as well, with no perturbation or limiting packing. This is a direct weak-endpoint proof.

## 8. Actual T support and all matching hypotheses

In both remaining beta cases, the complete original U force equation has positive North and East terms, so its original U-to-T normal n is strictly Southwest. Its actual application is U's unique southwest vertex:

    P_T=(-a,b), a=x+beta*C>=x,
    b=y-2,
    0<=beta*C<1/4.                                  (16)

No original UV mean is substituted in this equation. At beta=0 the equality a=x is exactly the endpoint proved in Section 7.

Equations (11),(3) give sqrt(3)<y<121/60. Hence the entire wide matching theorem's remaining port premises hold:

    y-2<=b<min(y-1,37/150).

On its short interval x<=9/16, (16) gives a<x+1/4<x+41/100. All original physical T masks and zero-weight corners remain. The wide theorem and Section 7 now prove that every T physical circle corner lies in x<-x, that its center angle theta_T has the lift in (90,270) degrees with theta_T<230 degrees, and that an actual radius-9/8 point of int V has angle phi with

    theta_T<phi+100 degrees.                         (17)

The actual cap and angular-routing premises needed for capacity are proved next; they are not inferred from (17).

## 9. Complete occupied cap and the true T2 angular routing

The actual VW moment is

    det(M,m)=-(1-x)*v-(y-1)*u<0,                    (18)

because x<1, y>sqrt(3)>1 and u>0. Thus the actual loaded boundary path is clockwise by the degree-free boundary-pair moment theorem and its angular-neighbor order. Its closing gap through U is counterclockwise from V to T.

Use Z_V=(-x,y), then V's actual left side down to P_V=(-x,y-1), then U's top boundary left to its northwest corner, then U's left boundary down to P_T, then a path inside T to its gap-facing circle corner Z_T. The possible zero-length top step at beta=0 is simply omitted. All these actual pieces lie in x<=-x, and all physical T circle corners lie strictly left of that line by Section 8.

The complete U3 touching-return theorem makes T closed-disjoint from V and W. U intersects T only at P_T by its strict support. V's left-side piece and U's top-left boundary meet only at P_V; this remains true when the top step has length zero. The chosen crosscut is simple.

The actual closing circle arc from Z_V to Z_T is the left cap arc, because the loaded path occupies the complementary clockwise order and every T circle corner is in the open left cap. U is strictly circle-clear. Its maximum absolute horizontal coordinate is a=x+beta*C<5/4. Its maximum absolute vertical coordinate is y-1<61/60, since sqrt(3)<y<121/60. Thus every U point has squared norm below

    25/16+(61/60)^2<4<R^2.

The bounded region is consequently in x<=-x. Homotoping the original center/contact crosscut to this occupied path stays inside the unchanged closed U,V,T union. The geometric UV junction moves to its actual left extreme only in that barrier; its original mean remains in every original equation. Every compact subset of an extra's open interior avoids the closed union, so winding is unchanged. Closure retains the whole extra at weak contacts or zero-weight junctions. Hence

    every whole pocket extra E lies in {X:X_x<=-x}.  (19)

For the angular upper bound, the true T2 torque and its actual counterclockwise boundary-predecessor moment give det(P_T,n)>0. Proper concurrence with that physical boundary predecessor gives q_T=P_T+ell*n=lambda_T*F_T, with ell>=0 and lambda_T>0, retaining every T mask. P_T and n are in the open left half-plane; the determinant sign orders n counterclockwise from P_T. Thus arg(P_T)<=arg(F_T)<theta_T+15 degrees. Every physical T circle corner has that same strict upper bound.

The occupied V/U pieces increase in argument: their determinant signs are x>0 on V's downward side, y-1>0 on the leftward top step if nondegenerate, and a>0 on U's downward left side. Their angle never exceeds arg(P_T). Both ends of the chosen T segment are between arg(Z_V) and theta_T+15 degrees; the lower bound for its circle endpoint follows from its position in the left cap. This cone has aperture below pi because arg(Z_V)>90 degrees and theta_T+15<245 degrees.

The actual closing circle arc and crosscut lie in that pointed cone, whose two half-planes therefore contain the bounded region. Every actual extra center satisfies

    arg(Z_V)<=theta_E<=theta_T+15 degrees.           (20)

Equations (19),(20) are precisely the actual routing premises of the wide matching capacity corollary. It gives closing-pocket capacity at most one, using the actual V point (17) and strict centered-arc gaps 20,40,40 degrees. No W3 or internal path equation is shortened and no concurrence is presumed to lie inside a physical two-circle T.

## 10. Complete original D02 feature join and remaining boundary

Use the original rim 01,12,23,34,45,50, chord 02 and loads {0,1,3,4,5}, with U=2,V=1,W=0,T=3 and path (1,0,5,4,3). The same-nine analytic lower-radius theorem supplies R>2. The original degrees U3,V2,W3,5_2,4_2,T2 and all three additional squares remain.

The parallel-W branch was the entire already excluded adjacent-shared feature. For every nonparallel W, the whole support classification gives beta=0, beta=1 or a side interior. The far endpoint is impossible; both other cases have the exact actual closing capacity just proved. The central union has capacity one and every direct boundary-pair exterior pocket is empty, so all three original extras cannot fit in total capacity two. This proves the entire parallel-V unique-circle feature, for every return owner and original UV mean.

Together with the separately accepted parallel physical-two-circle proof, no physical V mask remains in the parallel-V perpendicular-hub interface. The nonparallel circle masks and other original U-normal interfaces retain their separate proof obligations; this source does not itself mark the entire D02 row closed.

## 11. Exact operative inputs

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Existing strict point-normal convention and original full force/torque/mean equations |
| RECOVERED_ADJACENT_SHARED_HUB_BOUNDARY_TRIANGLE_D02_FULL_FEATURE_EXCLUSION.md | 44b78ba21f68b23387aeb30a5b5fb3c0ea2bea352c538a4782ebdf382f30ce88 | Entire original both-parallel shared UV/UW adjacent-face branch |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2 only, force-free whole Southeast neighbor-normal cone |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Actual original UV mean is not in physical-boundary W, at true V2 |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 | Only the printed pure F monotonicity and three-interval scalar implication, not its physical radial-chart premise |
| ADJACENT_CIRCLE_TIP_WIDE_LEFT_CAP_INNER_ARC_MATCHING.md | 14ca7fbac82fb74b698ab17df01eb1783ce558e75fa8b5a528bbb8fb7bba76c1 | Complete actual V/T matching and conditional capacity; the weak a=x endpoint is proved directly in Section 7 above |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Full U3 and actual VW make T closed-disjoint from V,W |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 | Lemma 1.1 only, actual boundary-pair moment signs |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | True T2 proper concurrence with actual boundary predecessor and all physical masks |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e | Section 2 only, full physical corner/resultant cone |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Actual loaded path direction and order |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Actual physical circle-corner order and empty direct pockets |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 | Entire central free-union capacity one |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual compatible embedding and weak-junction allocation |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, loads, degrees and three extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine original R<=2 exit |

The parallel W-mask calculation was informed by the separately complete adjacent-mask proof a1e480fc; all its new parallel and equality hypotheses, actual corner comparisons and scalar joins are proved directly above. No tilted V force ratio, inside-concurrence assertion, unproved comparison-radius upper bound or missing W equation is imported.

No sampled pose, numerical optimization, finite orientation grid, computational exclusion packet, new normal selection, force deletion, changed original mean, artificial degree-two neighbor, Lean compilation, CI, workflow or merge was used.
