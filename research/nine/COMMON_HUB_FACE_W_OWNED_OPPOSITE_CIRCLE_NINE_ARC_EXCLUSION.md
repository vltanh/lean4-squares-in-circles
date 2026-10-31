# A W-owned common-face return with the tip's opposite circle corner leaves no nine-unit completion

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed whole-feature hand exclusion, submitted for root and separate independent review.** The theorem covers every frame and physical circle mask of W, including the aligned W and every actual UW mean. Its explicit additional premise is that V has a unique physical circle corner opposite its actual UV vertex. The adjacent-circle and physical two-circle alternatives at V remain separate. No original fine or coarse gate is closed here.

The proof uses a central one-eighth disk and all eight actual inner arcs. It does not require a central-face capacity assignment or an auxiliary drawing of the completion units.

## 1. Complete original component and exact feature

Keep the same nine actual closed unit squares with pairwise disjoint open interiors, the unchanged circle origin, and the entire original selected physical certificate in

    2<R<=sqrt(Q), Q=1105/256,
    d=sqrt(R^2-1/4)-1<61/60.

Suppose a complete positive component consists of one unloaded U and k positively loaded boundary units, 3<=k<=5, with precisely the positive boundary path

    V,W,B_3,...,B_(k-1),T

and the original three spokes UV,UW,UT. For k=3 the path is V,W,T. The actual outer-face order is U,V,W,...,T,U. The true degrees are U3,V2,T2,W3, with every other path unit of degree two. All other physical units, extra zero-weight contacts and full circle masks remain.

Assume the original U-to-V and U-to-W normals are the same own side axis of U. Assume V is nonparallel to U, and the actual VW contact is a singleton consisting of a V vertex and a point in the relative interior of a W side, with its original normal owned by W.

Finally assume V has exactly one physical circle corner, and it is the vertex opposite its actual UV vertex. This is a physical-mask/corner premise, not a statement about which individual circle weights happen to be positive.

**Theorem.** This entire actual feature is impossible in the nine-square packing.

The literal D02.L01345 substitution has k=5, U=2,V=1,W=0,B_3=5,B_4=4,T=3. All original loaded W3 forces, all original side means and the three arbitrary extra squares are retained.

## 2. The actual common-face chart, all W frames and all initial moments

Rotate about O so the common U side is x=a and U is on its left. The actual UV point is the unique minimum-x vertex

    P=(a,t),
    V=P+[0,1]e_1+[0,1]e_2,
    e_1=(c,-s), e_2=(s,c),
    c,s>0, c^2+s^2=1.                               (1)

The minimum-x support set of W cannot contain P. The inward tangent sector of nonparallel V at P contains East openly, whereas a unit W on the same right side and containing P would overlap that sector. This whole W support therefore lies strictly above or below P. Reflect all original data to place it below P.

Every actual UW mean then has height z<t. The full U force equation gives

    n_UT=West, mu_T=mu_V+mu_W,
    P_T=(a-1,h),

and its unchanged complete torque equation is

    mu_T*h=mu_V*t+mu_W*z.                            (2)

The occupied U boundary arc from the V port to the T port contains the lower UW port. It runs clockwise down the right side and around the bottom to the left side. The actual boundary path consequently has clockwise circle order. This is exactly the distinct-port order and endpoint-moment implication in Section 1 of GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md; no quarter-disk or capacity conclusion of that source is needed.

The two true endpoint torque equations and the degree-free boundary-pair moment theorem give

    t>0, h>0.

Equation (2), with mu_W>0 and z<t, further gives

    0<h<t.                                         (3)

The contained T center/support bound gives 1-a<=d, so initially

    a>=1-d>-1/60.                                  (4)

No claim that U contains O has been used.

### 2.1. Complete W-owned physical feature cover

If W is not parallel to U, write its actual axes from its unique left vertex P_W as

    f=(C,S), g=(S,-C), C,S>0, C^2+S^2=1.

If W is parallel to U, use C=1,S=0 and let P_W be its upper-left corner. Its entire minimum-x side lies below P, so this corner is below P as well. The original UW mean remains anywhere in its actual intersection with U; it is not replaced by P_W in any equation.

Because W owns its VW side normal, the physical triangle owned-axis rule at W gives n_VW dot East>=0. For nonparallel W, only f or g among its inward axes have nonnegative x component. In the aligned W case the additional North endpoint is impossible: W's minimum-North side lies below P, whereas V's maximum-North vertex is above P. The limiting East alternative cannot put W beyond V's maximum x while W still has minimum x=a.

The choice n_VW=f is impossible. W's minimum-f side lies at or below its left vertex. V's maximum-f support includes its e_2 side direction: its exposed vertex is either its upper vertex, whose height is above P, or its right vertex, whose x coordinate is greater than a+1. Neither can lie on W's actual minimum-f side, whose height is below P and whose x coordinates are at most a+1. The actual VW contact is a V vertex, so no side-interior V exception is introduced.

Therefore the unchanged normal is

    n_VW=g=(S,-C).

Put

    gamma=C*c-S*s, eta=C*s+S*c,
    gamma^2+eta^2=1.

Its V-own components are (eta,-gamma). Since the actual contact strictly exposes a V vertex and is not a V-owned side, gamma is nonzero. If gamma<0, V's exposed right vertex has x>a+1, again beyond W's minimum-g side. Thus gamma>0 and the actual VW point is exactly

    M=P+e_1=(a+c,t-s).                              (5)

The original W side is P_W+[0,1]f, and M is in its strict relative interior. Hence

    alpha=c/C in (0,1),
    M=P_W+alpha*f,
    P_W=(a,t-delta), delta=s+c*S/C.                 (6)

For nonparallel W, P_W is the actual UW singleton. For parallel W the original UW mean is below or at P_W; since U's right side also contains P at the strictly greater height t, that same U side contains P_W. Thus in both whole frame cases

    0<delta<=1, P and P_W belong to the actual U side. (7)

No original mean was changed in (2).

Define further

    r=S/C>=0, kappa=s/C>0, tau=1-alpha in (0,1).
    l=c-s*r=gamma/C>0.

The exact useful identities are

    alpha=gamma+r*eta,
    kappa=eta-r*gamma,
    alpha^2+kappa^2=1+r^2,
    gamma<=alpha<=2*gamma.                          (8)

The last upper bound follows from delta=eta/C<=1, which implies r*eta<=gamma. These identities include C=1,S=0.

### 2.2. The actual V concurrence and opposite circle corner

The UV line is horizontal through P. Its intersection with the original VW line through M in direction g is exactly

    q_V=P+l*East.

In V's own coordinates, q_V-P=(l*c,l*s). Both entries are strictly between zero and one, since l<=c and c,s>0. Thus q_V belongs to int V. The actual loaded V2 with physical boundary neighbor W also satisfies the complete proper-concurrence lemma. Its unique physical circle corner is

    Z_V=P+e_1+e_2=(a+c+s,t+c-s),

and

    q_V=lambda*Z_V, 0<lambda<1.                     (9)

The strict lambda upper bound also follows from q_V in int V and |Z_V|=R. Taking the y component, with t>0, gives c>s. Therefore

    alpha>kappa, alpha>1/sqrt(2)>7/10,
    kappa<1, r<kappa, tau<3/10.                     (10)

Here r<kappa follows from alpha<1 and alpha^2+kappa^2=1+r^2. No unknown W circle corner has yet been selected.

## 3. The complete physical circle mask of W is forced

We prove that W has precisely its right vertex on the circle. All other physical W-mask alternatives are included in this proof.

Use W's orthonormal frame f,g about the unchanged origin. Write

    m_f=M.f, m_g=M.g, b=kappa-gamma.

From (9),

    m_g=kappa+(b/eta)*m_f,
    Z_V=(m_f+eta)f + ((b/eta)*(m_f+eta))g.            (11)

The scalar m_f is positive, because (1-lambda)*m_f=lambda*eta and eta>0.

First we prove m_f>1/2. Directly from the global coordinates of q_V,

    m_f=gamma+C*a+S*t>gamma-1/60.                   (12)

If gamma>=31/60, this is already greater than 1/2.

For the remaining gamma<=31/60, (8),(10) give gamma>7/20. Put L=sqrt(eta^2+b^2). Equation (11) gives

    m_f=R*eta/L-eta.

If gamma<=1/2, then 0<kappa<1 implies |b|<1-gamma. Consequently

    eta^2/L^2>(1+gamma)/2>27/40>16/25.

If 1/2<=gamma<=31/60, then |b|<gamma, so L<1 and

    eta/L>eta>=sqrt(2639)/60>4/5.

Thus in either remaining case m_f>8/5-eta>=3/5. Together with (12),

    m_f>1/2.                                       (13)

The f-coordinate of W's center is m_f+1/2-alpha>1-alpha>0. Its physical circle corners can therefore occur only on its maximum-f side: the top vertex M+tau*f or the right vertex M+tau*f+g.

The top vertex is strictly inside the circle. To see this using all actual parameters, put X=P.e_1+1 and Y=P.e_2+1, the own coordinates of Z_V. The positive radial relation (9) gives

    (1-lambda)X=1-gamma*alpha,
    (1-lambda)Y=1-gamma*kappa.

Since alpha>kappa, 0<X/Y<1 and Y>R/sqrt(2)>sqrt(2)>7/5. The W top vertex has V-own coordinates

    (X+tau*gamma, Y-(1-tau*eta)).

Its squared-radius deficit is

    2Y*(1-tau*eta-(X/Y)*tau*gamma)
       -[(tau*gamma)^2+(1-tau*eta)^2]
    >2*(7/5)*(1-(3/10)*(3/2))-(1+9/100)
     =9/20>0.                                      (14)

We used tau<3/10, gamma+eta<=sqrt(2)<3/2, and only positive factors. Therefore the actual right vertex is the unique physical W circle corner:

    Z_W=P_W+f+g=(a+C+S,t-delta+S-C).                (15)

This rules out the two-circle W mask by geometry, including a second corner with zero individual circle coefficient. No W force equation or corner coefficient was used.

## 4. W's whole top support is strictly below O

Let H=1+gamma and set

    E=H*(1-kappa)-eta*tau.

Using |Z_W|^2=|Z_V|^2 and (11), direct expansion gives

    m_f=eta*(H*kappa+tau^2/2)/E.                    (16)

Since m_f>0 and the numerator is positive, E>0. These divisions therefore have proved signs.

Let y_top be the y coordinate of W's top vertex M+tau*f. Its coordinate in the original global frame and (11) give

    y_top/C=(alpha-kappa)*m_f/eta+r*tau-kappa.

Substituting (16) and expanding yields exactly

    E*y_top/C
      =tau*[(kappa-r)*(kappa-1-gamma)
               +tau*(2*gamma-alpha-kappa)/2].        (17)

For transparency, the identity uses alpha=gamma+r*eta, kappa=eta-r*gamma and gamma^2+eta^2=1. Also

    tau*(1+alpha)=(kappa-r)*(kappa+r).

Put L_0=kappa-r>0. Because kappa<1, gamma<=alpha and gamma>=alpha/2, the bracket in (17) satisfies

    bracket < -L_0*gamma+tau*(alpha-kappa)/2
            = L_0*[-gamma+
                   (kappa+r)*(alpha-kappa)/(2*(1+alpha))]
            < L_0*[-gamma+kappa*(alpha-kappa)/(1+alpha)]
            <=L_0*[-alpha/2+alpha^2/(4*(1+alpha))]
             <0.

The penultimate line uses kappa*(alpha-kappa)<=alpha^2/4. Every denominator is positive. Thus

    y_top<0.                                       (18)

In particular the whole actual W lies strictly below the horizontal axis, and its original left support point or side is below that axis. The aligned W endpoint r=0 was retained throughout.

## 5. Broad port bounds put the actual hub around the one-eighth disk

We prove the strict whole-domain bounds

    3/10<a<2/3, t>1/8, t-delta<-1/8.                (19)

### 5.1. The horizontal support lies between 3/10 and 2/3

The actual circle vertices (9),(15) have positive x coordinates by (4), with the V vertex above O and the W vertex below O. Their vertical separation is

    (Z_V)_y-(Z_W)_y
      =delta+c-s+C-S
      =C*(1+alpha)-S*(1-alpha)<2.

Both x coordinates are at most a+sqrt(2). If a+sqrt(2)<=sqrt(R^2-1), each circle vertex would have absolute y coordinate at least one, contradicting that strict separation. Therefore

    a>sqrt(R^2-1)-sqrt(2)>sqrt(3)-sqrt(2)>3/10.

The last comparison follows from sqrt(2)<3/2: 91/100>(3/5)*sqrt(2).

The actual opposite-vertex vector Z_V-P has norm sqrt(2), and (9) writes it as

    Z_V-P=A*P+B*East, A=(1-lambda)/lambda>0,
    B=l/lambda>0.

Since P.East=a>0, the exact cone identity

    (P.(Z_V-P))^2-a^2*|Z_V-P|^2
       =t^2*(A^2*|P|^2+2*A*B*a)>=0

gives

    R^2>=a^2+t^2+2+2*sqrt(2)*a>(a+sqrt(2))^2.       (20)

This is the squared vertex argument from the general port-gap theorem; here the opposite corner is an explicit premise, so no |t|<1/2 premise is needed to identify it. Both dot products whose positive square roots are taken are positive.

Consequently a<R-sqrt(2)<=sqrt(Q)-sqrt(2)<2/3. For the last comparison, sqrt(2)>140/99 gives

    (sqrt(2)+2/3)^2>1286/297>Q.

### 5.2. The upper UV port has t>1/8

Suppose t<=1/8. Put D=c-s>0 and g_0=s*(1+r)=c+s-l. The y equation in (9) gives exactly

    t=D*(a+l)/g_0.

From delta<=1 and c>s,

    r<=(1-s)/c,
    g_0<=1,
    l>=c/(1+s)>=sqrt(2)-1>2/5.

Using a>3/10 yields D<5/28. If s<=61/100, then c>79/100 and D>9/50>5/28, a contradiction. Hence

    s>61/100, c<4/5,
    r<=c/(1+s)<1/2,
    C>2/sqrt(5)>143/160,
    c>1/sqrt(2)>70/99.

The positive and negative circle heights then satisfy

    (Z_V)_y=t+D<17/56,

    -(Z_W)_y
       =s+C-r*(C-c)-t
       >61/100+(70/99+143/160)/2-1/8
        =203609/158400.

Here C>c follows from alpha<1. The lower height bound uses r<1/2 and C-c>0.

The W circle x coordinate is at least a+1, and the V circle x coordinate is at most a+sqrt(2). Therefore

    |Z_W|^2-|Z_V|^2
      >(203609/158400)^2-(17/56)^2-1-2*a*(sqrt(2)-1)
      >(203609/158400)^2-(17/56)^2-14/9
       =5616819169/1229437440000>0.

The second line uses a<2/3 and sqrt(2)-1<5/12. This contradicts their equal actual circle radii. Thus t>1/8.

### 5.3. The lower W port lies below -1/8

Suppose t-delta>=-1/8. Equation (18) says

    y_top=t-delta+S<0,

so S<1/8 and C+S<9/8. The W circle height is negative with absolute value

    C-S-(t-delta)<=C-S+1/8<=9/8.

Since R>2, its positive x coordinate satisfies

    a+C+S>sqrt(175)/8>13/8,

hence a>1/2. On the other hand, (15) gives

    R^2<=(a+C+S)^2+(C-S+1/8)^2.

Subtracting (a+sqrt(2))^2, and using C^2+S^2=1, the right side minus that quantity equals

    2*a*(C+S-sqrt(2))+(C-S)/4+1/64
       <-11/40+1/4+1/64=-3/320.

We used a>1/2, C+S<9/8, sqrt(2)>7/5 and C-S<=1. This contradicts (20). Therefore t-delta<-1/8, completing (19).

### 5.4. The entire actual U and every original mean are retained

Write the actual U as [a-1,a] times [b,b+1]. Its right side contains P at height t and P_W at height t-delta, even for aligned W, as proved in Section 2. Thus

    b<=t-delta<-1/8, b+1>=t>1/8.

Together with 3/10<a<2/3, these inequalities put the entire closed disk D_(1/8) strictly inside the actual U. Since every other original closed unit has disjoint open interior from U, compactness gives

    dist(O,E)>1/8

for every one of the other eight actual squares.

One also has b>=t-1>-7/8 and b+1<=t-delta+1<7/8. All actual U points therefore have |x|<7/10 and |y|<7/8, giving

    |x|^2+|y|^2<2009/1600<2025/1600=(9/8)^2.

So U lies strictly inside the radius-9/8 circle. These are consequences of the unchanged geometry; U has not been centered or slid.

## 6. The opposite endpoint T has its center in the upper-left quadrant, with both physical masks

Put u=1-a, so 1/3<u<7/10. The original UT port is (-u,h), with h>0 by (3), and the inward normal into T is West.

The full loaded T2 equation, with its actual boundary-path predecessor as physical boundary neighbor, gives the proper concurrence

    q_T=(-u-rho,h), rho>=0,

as a positive multiple of its whole circle resultant. No claim that a two-circle concurrence belongs to T is made.

For the unique physical T corner, the proper lemma gives q_T=lambda_T Z_T with 0<lambda_T<=1. Reflect x solely for this local calculation, making the actual inward normal East and the port (u,h). If that normal is an own T axis, the rectangle's farthest vertical coordinate must be positive by h=lambda_T*(Z_T)_y>0. Its actual center consequently has positive y; uniqueness excludes equality.

If it is not an own T axis, write its inward axes from the port as (c_T,s_T),(s_T,-c_T), with c_T,s_T>0. The lower adjacent corner cannot be Z_T because its y coordinate is less than h>0, contradicting the positive proper multiple with lambda_T<=1. The shared port itself cannot be a circle corner. For the opposite corner, h=lambda_T*(h+s_T-c_T) forces s_T-c_T>=0, and the center height is at least h>0.

In the remaining upper-adjacent case, containment of its adjacent opposite corner forces

    u*s_T-h*c_T<=-1/2.

Hence h>1/(2*c_T), and the actual center height is

    h+(s_T-c_T)/2>0.

This covers every unique-circle T feature.

For two physical T corners, its actual radial S form has center (d+1/2)e. In the reflected coordinates T lies wholly in x>=u>0, so e_x>0. If its center height were nonpositive and e_y<0, its unique minimum-x vertex would have height

    -d*|e_y|-e_x/2<0,

contrary to h>0. If e_y=0, its minimum-x side has u=d, impossible because u<7/10<d. The full two-circle mask therefore also has positive center height. Both individual zero-weight endpoints remain included.

Returning to the original coordinates, T's maximum x is a-1, so

    (c_T)_x=a-1-width_T(East)/2<0, (c_T)_y>0.

The actual V center has positive x and y by a>0, t>0 and c>s. W's center has positive x and negative y by a>0 and (18). Thus V and T are in the two upper quadrants, and the actual path begins clockwise from V to W.

## 7. The whole upper endpoint gap is less than 157.5 degrees

Write the actual endpoint center directions as

    arg(c_V)=alpha_0 in (0,pi/2),
    arg(c_T)=pi-beta_0, beta_0 in (0,pi/2).

Their upper closing gap is pi-(alpha_0+beta_0). Every boundary center has radius at least R-1/sqrt(2)>31/24. The actual opposite support faces give

    (c_V)_x-(c_T)_x
       =1+[width_V(East)+width_T(East)]/2
       <=1+sqrt(2)<29/12.                           (21)

If the closing gap were at least 7*pi/8, then alpha_0+beta_0<=pi/8. Therefore

    (c_V)_x-(c_T)_x
       >(31/24)*(cos(alpha_0)+cos(beta_0))
       >=(31/24)*(1+cos(alpha_0+beta_0))
       >=(31/24)*(1+cos(pi/8))
       >(31/24)*(19/10)=589/240>29/12.

The elementary cosine-sum inequality follows from its half-angle identity. Also cos(pi/8)>9/10 follows by squaring cos(pi/8)=sqrt(2+sqrt(2))/2. The final reserve is 3/80. This contradicts (21), proving

    arg(c_T)-arg(c_V)<7*pi/8=157.5 degrees.          (22)

No orientation or force equation at T was simplified to obtain (21).

## 8. All eight actual inner arcs give the contradiction

By Section 5, each of the eight units other than U has distance greater than 1/8 from O. The complete theorem FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md gives a connected open-interior arc on the radius-9/8 circle of length strictly greater than 40 degrees, containing the actual center direction. These eight arcs are pairwise disjoint.

Each boundary path unit also satisfies the centered-forty theorem: its closed arc from twenty degrees before to twenty degrees after its center direction lies in its open interior. Every physical boundary contact has minor center gap less than 72 degrees.

It follows that no other one of the eight center directions can lie on the short arc of a boundary contact. Otherwise its connected inner arc, disjoint from the two boundary squares' closed centered arcs, would be confined to the intervening angular interval of length less than

    72-20-20=32 degrees,

contrary to its strictly greater forty-degree length. This argument applies to every other actual unit, whether or not it has a positive force in the component. It uses actual inner arcs, not a guessed center location of an extra square.

Thus the k boundary-path centers are successive members of the circular order of all eight arcs. A simple path of distinct consecutive members cannot reverse direction. It begins clockwise from V to W by Section 6, so the entire path proceeds clockwise. Every one of the remaining 8-k>=3 inner arcs is consequently in the upper closing gap from V counterclockwise to T.

The endpoint squares already occupy their closed twenty-degree half-arcs into this gap. By (22), the available interval between these two endpoint half-arcs has length strictly below

    157.5-20-20=117.5 degrees.

Three disjoint open arcs of length strictly greater than forty degrees require a total length strictly greater than 120 degrees. This is impossible.

All additional physical units were retained simultaneously. The proof assigns none to a guessed polygon, moves no actual contact crosscut and does not need a separate assertion about an extra unit's center being in a central or exterior face.

## 9. Literal D02 caller, exact dependencies and remaining feature boundary

For M6.B6.HEXAGON.D02.L01345, use the original path

    V,W,B_3,B_4,T=1,0,5,4,3, U=2.

The original graph is the rim 0--1--2--3--4--5--0 with the single chord02, and the positive load set is {0,1,3,4,5}. The exact degrees U3,V2,W3,5_2,4_2,T2 match Section 1. The three actual extras remain. Every graph-preserving reflected image is handled by reflecting all physical data together.

The accepted common-face owner normal form supplies a W-owned side-interior return throughout the remaining nonparallel same-U-axis feature. This manuscript excludes the whole subdomain in which V has a unique physical circle corner opposite its actual UV vertex. It includes every W orientation, all original UW means, every T mask and all three-extra placements. It does not exclude V's adjacent unique-circle or two-physical-corner alternatives, other U-axis interfaces, or the whole D02 graph/load row.

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| SAME_HUB_FACE_BOUNDARY_TRIANGLE_TIP_RETURN_OWNER_NORMAL_FORM.md | 5f70175b10e068bdaddcd135fdf0cf70ad48d5f256d4ca18b86e616cc3fd7eb6 | Literal selected W-owned side-interior return in the original same-axis caller |
| GENERAL_SINGLE_HUB_BOUNDARY_PATH_POCKET.md | 958bb122342783a824d023c221ccc2c93a68300b00b0ffc3496c25ad394aec84 | Only the actual occupied-arc order, endpoint moment signs and complete endpoint degrees; its pocket-capacity conclusion is not used |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual W-owned triangle-axis sign in the complete physical chart |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Full local proper concurrence at the actual loaded V2 and T2, each with a physical boundary neighbor |
| POSITIVE_RADIAL_CONCURRENCE_PORT_GAP_DICHOTOMY.md | c4bdf0659d6a4d05728f6b5526143c91e1124f15642c1cc5060c202a6cc02935 | Provenance of the squared opposite-vertex identity, fully reproduced after the opposite-circle premise is established |
| FORTY_DEGREE_NINE_EIGHTHS_ARC_OUTSIDE_ONE_EIGHTH.md | 5c0da36441613ccf2e3ce75a669ca1b212589788442e56b007a33a32d5131517 | Connected >40-degree actual inner arc for every one of the eight unchanged units outside the proved one-eighth disk |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 | Closed centered forty-degree arcs at the physical boundary path units |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Boundary contact center gap <72 degrees, unchanged circle order and geometric center radii |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph, load mask, degrees and retained all-nine domain |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 entry for the original caller |

Every displayed inequality is continuous over its entire parameter domain. Exact rational computations check arithmetic transcriptions only. There is no pose search, angle mesh, numerical exclusion packet, replacement mean, deleted force, false transmitter, Lean compilation, CI, ledger mutation or remote action. No original checkbox is changed.

