# A mixed common-boundary-side opposite-circle tip forces the whole quarter disk into the actual hub

Date: October 28, 2026 UTC. Authors: root continuation (uniform scalar bounds and all four hub margins), with cycles continuation (complete common-side chart, unique-circle equations and W-mask derivation).

**Status: complete proposed uniform local hand theorem and original D02 feature exclusion, submitted for full separate independent review.** Every actual frame and closed W-side parameter is retained. The proof derives the entire physical W mask, then proves all four hub margins by continuous scalar estimates. The final contradiction treats all eight other original units at once.

Put Q_*=1105/256 and work in the closed window

    2<=R<=sqrt(Q_*).

## 1. Complete unchanged local statement

Retain actual pairwise interior-disjoint contained closed unit squares U,V,W,T, the unchanged circle origin, and their full original physical force and torque equations. Assume:

* U is unloaded and its entire positive pair neighborhood is V,W,T.
* V is positively circle-loaded and its entire positive pair neighborhood is U,W.
* W is physically boundary. Its degree, load, physical circle mask, other original forces and means are unrestricted.
* The original U-to-V normal is an own side axis of U. After a rotation and, if necessary, reflection of all actual data about O, it is North.
* The original U-to-W and V-to-W normals are the same unit vector m, strictly Northeast in that U frame.
* V is nonparallel to U and its unique physical circle corner is opposite its actual UV application.

The third unit T needs no circle load, physical-boundary premise or two-force equation in the local result. Every original mean, individual circle coefficient, other force and completing square remains. Equality of the two normals into W is an unchanged feature hypothesis, not a normal-selection operation.

**Local theorem.** The closed origin-centered disk D_(1/4) lies in the open interior of the actual U.

**Same-nine consequence.** This entire original feature is impossible in a nine-square packing in the stated radius window. Every one of the eight other actual units would contain an open radius-5/4 arc longer than pi/4, with all eight arcs disjoint.

## 2. Complete actual common-side chart and the full U3 equation

Write the actual U and its UV application as

    U=[L-1,L] x [H-1,H],
    P=(L-D,H), 0<=D<=1,
    Q=(L,H),
    m=(b,a), a,b>0, a^2+b^2=1,
    w=a/b.

Because V is nonparallel, P is its unique bottom vertex. Its inward axes and complete square are

    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (1)

The original strict Northeast UW normal exposes Q. Both original normals into W are m, so its minimum-m support value agrees at Q and the actual VW application. In particular the actual V point P+e_1 gives

    b*c+a*s<=b*D<=b.

If b*s-c*a<=0, then w>=s/c and D>=c+w*s>=1/c>1, impossible. Thus

    gamma=b*s-c*a>0,
    eta=b*c+a*s>0,
    gamma^2+eta^2=1.

The V-own components of m are (eta,-gamma), so the actual VW point is necessarily

    M=P+e_1,
    D=c+w*s.                                       (2)

The points Q,M are distinct, with height difference s>0. They lie on the same actual minimum-m face of W, which therefore is an actual side. Its unit tangent is f=(-a,b), and

    M-Q=(s/b)*f.

The entire actual W and both points consequently have the form

    alpha=s/b<=beta<=1,
    tau=1-beta in [0,1-alpha],
    W=M+[-beta,1-beta]f+[0,1]m,
    Q=M-alpha*f.                                   (3)

In particular the lower W corner need not be Q. No equation substitutes one for the other. All allowed side endpoints are retained.

Let mu,omega,zeta>0 be the original UV,UW,UT magnitudes. Full unloaded U force gives

    mu*North+omega*m+zeta*n_T=0.

Thus the original UT normal is strictly Southwest, and its actual U application is the southwest vertex P_T=(L-1,H-1). Full torque about that vertex is

    mu*(1-D)+omega*(a-b)=0.                         (4)

If D=1, (4) would force a=b and then (2) would give D=c+s>1. Hence

    0<D<1,
    b>a,
    0<w<(1-c)/s=s/(1+c).                            (5)

From alpha<=1 also b>=s, a<=c, w<=c/s. In the V frame,

    f=(gamma,eta), m=(eta,-gamma).

This full chart is the same mask-independent calculation printed in Sections 1--2 of the separately reviewed common-side source. It has been reproduced here because the present local theorem does not assume that source's boundary-path or physical-mask conclusion.

## 3. The unchanged unique V2 equations fix the circle direction

The actual unique corner is Z=P+e_1+e_2. Write its V-own coordinates as

    Z=(X,Y), X,Y>1/2,
    X^2+Y^2=R^2,
    P=(X-1,Y-1), M=(X,Y-1).

These strict coordinate inequalities are exactly physical uniqueness. The full circle resultant is Lambda*Z with Lambda>0, and the complete true V2 equation is

    F_V=mu*North-nu*m, nu>0.                        (6)

The two original pair lines meet at

    q_V=P+(gamma/b)*North.

Indeed (q_V-M).f=0. The full true-V2 proper-concurrence lemma applies because its other actual neighbor W is physical boundary. In the unique mask q_V=lambda*Z with 0<lambda<=1. Put kappa=c/b. Its first own component gives

    (1-lambda)X=1-gamma*alpha=c*(c+w*s)=cD>0.

Therefore lambda<1 and K=1/(1-lambda)>1. The exact components are

    X=K*cD,
    Y=K*(1-c*s+c^2*w),
    Z_global=K*(c-s,c*(1+w)).                       (7)

The full resultant in (6) has negative global first coordinate -nu*b. Hence c<s. The difference of the own coordinates is

    Y-X=K*(s-c)*(s-c*w)>0.

Here s-c*w>0 follows from (5), or from w<=c/s and c<s. Consequently

    c<1/sqrt(2)<s,
    Y>X>1/2,
    Y>sqrt(2)>7/5,
    X<R/sqrt(2)<3/2,
    0<=tau<=1-s/b<=1-s<3/10.                       (8)

The actual hub coordinates are

    L=D-(K-1)*(s-c),
    H=K*c*(1+w)-s-c=s*(X-1)+c*(Y-1).               (9)

One further exact identity, using gamma*alpha+eta*kappa=1, is

    Z.f=K*eta,
    M.f=(K-1)*eta>0.                               (10)

Only the full true V2 and U3 equations have been used. No equation at W or T has been shortened.

## 4. Every initial physical W mask is forced

The two actual minimum-m corners are M-beta*f and M+tau*f. For the first, (10) gives

    |M-beta*f|^2<|M|^2+1=R^2-2Y+2<R^2.

For the second, its exact radius deficit is

    2Y*(1-tau*eta)-2tau*gamma*X
       -(1-2tau*eta+tau^2).

Using X<Y, gamma+eta<3/2 and (8), this is strictly greater than

    2Y*[1-tau*(gamma+eta)]-1-tau^2>9/20.

Both actual corners are strictly inside the circle. If W's m-center coordinate were nonpositive, a farthest corner would lie on this minimum-m side, including the center tie. This contradicts W's physical boundary status. Thus its m-center coordinate is positive.

Suppose its f-center coordinate is nonpositive. Then M.f<=beta-1/2<=1/2, so Z.f=M.f+eta<3/2. Since |Z|=R>=2,

    |Z.m|>sqrt(7)/2>5/4.

If Z.m>0, W's maximum m-coordinate is Z.m+gamma+1>9/4>R, contradicting containment. If Z.m<0, this maximum coordinate is strictly between 1/2 and 3/4: the lower bound is the already proved positive m-center sign, and the upper bound follows from gamma<1. Its minimum f-coordinate M.f-beta is in (-1,-1/2]. The remaining farthest candidate therefore has squared norm below

    1+9/16=25/16<4,

again impossible. This includes the f-center tie.

Both center coordinates are positive. Thus W has the unique actual circle corner

    Z_W=M+tau*f+m=Z+(u,-v),
    u=eta+tau*gamma>0,
    v=1+gamma-tau*eta>0.                            (11)

The exact identity u^2+v^2=2v+tau^2 and the equal actual circle radii give

    Y=1+qX+t,
    q=u/v>0,
    t=tau^2/(2v)>=0.                               (12)

Every original physical W mask, every individual zero coefficient and beta=1 were retained before this mask was derived. The lower corner in this argument was not assumed to be Q.

## 5. One complete continuous bound: c>9/20

Suppose c<=9/20. Then s>89/100. Since a<=c and b>=s,

    gamma>=s^2-c^2>=119/200,
    eta<=2c*s<81/100,
    tau<11/100.

For the eta comparison, the function c*sqrt(1-a^2)+s*a increases for 0<=a<=c because s>c. Its maximum is 2cs, which increases with c<1/sqrt(2). At c=9/20 its square is below (81/100)^2. All these comparisons cover the whole continuous interval.

Consequently u<23/25, v>3/2, q<46/75 and t<1/200. The exact ratio from (7) is

    Y/X=1+(s-c)*(s-c*w)/(cD).

Here s-c>11/25, s-c*w>=(1-2c^2)/s>=119/200 and cD<=2c^2<=81/200. Thus

    Y/X>1+1309/2025>41/25.

The final reserve is 13/2025. Inserting this ratio in (12) gives

    X<603/616,
    Y<24723/15400.

Their squared sum is below 4 by 55078823/118580000, contradicting R>=2. Therefore

    9/20<c<1/sqrt(2),
    1/sqrt(2)<s<9/10,
    c+s>67/50.                                     (13)

For the sum, c+sqrt(1-c^2) increases below 1/sqrt(2), and at c=9/20 its second term is greater than 89/100.

## 6. Two full-domain lower bounds for X

Put c=cos(theta), s=sin(theta), with 45<theta<90 degrees, and a=sin(phi), b=cos(phi). The actual inequality w<s/(1+c)=tan(theta/2) gives phi<theta/2. Since gamma=sin(theta-phi),

    gamma^2>(1-c)/2.

From c<1/sqrt(2)<71/100 it follows that gamma>19/50 and eta<37/40. The latter squared reserve is 1/40000. Using tau<3/10,

    20u-19v
      =(20+19tau)*eta+(20tau-19)*gamma-19
      <(257/10)*(37/40)-13*(19/50)-19
       =-67/400.

Hence q<19/20. Also v>441/400, so t<2/49<1/24. If X<=4/5, (12) would give Y<1081/600 and

    R^2<4-41039/360000,

impossible. Thus X>4/5 on the entire actual domain.

On the entire subdomain c<=3/5, one has s>=4/5, gamma>sqrt(1/5)>11/25, eta<9/10 and tau<=1/5. Therefore

    5u-4v<(29/5)*(9/10)-3*(11/25)-4=-1/10.

Now q<4/5, v>63/50 and t<1/63<1/60. If X<=9/10, (12) would give Y<521/300 and

    R^2<4-15659/90000,

again impossible. We have proved the uniform bounds

    X>4/5;
    X>9/10 whenever c<=3/5.                         (14)

## 7. Both actual vertical hub margins

For fixed actual R,c,s, the function

    h_R(x)=s*(x-1)+c*(sqrt(R^2-x^2)-1)

is concave. The actual H=h_R(X), with X<R/sqrt(2). Its minimum on any interval [x_0,R/sqrt(2)] is at an endpoint. Each endpoint value increases with R>=2.

If 9/20<c<=3/5, use x_0=9/10. Since sqrt(4-81/100)>89/50,

    h_R(9/10)>-9/100+(9/20)*(39/50)=261/1000.

At the diagonal endpoint,

    h_R(R/sqrt(2))=(s+c)*(R/sqrt(2)-1)>67/125,

using (13) and sqrt(2)-1>2/5. Hence H>261/1000.

If c>=3/5, use x_0=4/5. Here s<=4/5 and sqrt(4-16/25)>9/5, so

    h_R(4/5)>-(4/5)*(1/5)+(3/5)*(4/5)=8/25.

The same diagonal lower bound applies. The two closed c intervals cover the entire actual domain. In particular

    H>261/1000>1/4.                                 (15)

For the upper bound, the actual global circle height is H+s+c<=R. Since sqrt(Q_*)<25/12, (13) gives

    H<25/12-67/50=223/300<3/4.                      (16)

The strict lower and upper reserves beyond the required margins are 11/1000 and 1/150.

## 8. Exact two-circle chord data for the horizontal margins

In the original U frame, (7),(11) are

    Z_V=(L-S_0,H+s+c),
    Z_W=(L+E,H+F),
    S_0=s*(1+w),
    E=b-w*s-tau*a,
    F=s+a+tau*b.

Set

    A=S_0+E=s+b-tau*a>0,
    B=(s+c)-F=c-a-tau*b>=0.                        (17)

To check the weak sign, tau*b<=b-s, so

    B>=c+s-a-b>=0.

The last inequality follows because a<=c<1/sqrt(2) and the function t+sqrt(1-t^2) increases below 1/sqrt(2). Also

    E>=b-a>0,
    S_0<=s+c<sqrt(2).

Both actual circle heights are positive by (15). Equality of their norms yields exactly

    L=(S_0-E)/2 + (B/A)*[(Z_V)_y+(Z_W)_y]/2.        (18)

All zero B endpoints are retained. These are actual circles of the unchanged units, not an auxiliary placement.

## 9. A single convex comparison proves L<3/4

The average of the two actual heights is at most R. Thus (18) gives

    L<=G(tau)
      :=(s-b+2s*w+tau*a)/2
          +R*(c-a-tau*b)/(s+b-tau*a).

For fixed actual c,s,a,b,R, direct differentiation gives

    G'(tau)=a/2-R*(1+gamma)/(s+b-tau*a)^2<0.

Indeed its denominator is below 4, R>=2, gamma>0 and a<1. This derivative is valid over the whole enlarged interval from zero to the actual tau; no actual square or original mean is changed. Therefore L<=G(0).

Now put c=sin(psi), s=cos(psi), a=sin(phi), b=cos(phi), with

    0<=phi<=psi<45 degrees.

The upper comparison is

    G(0)=(s-cos(phi))/2+s*tan(phi)
                       +R*tan((psi-phi)/2).

Its second derivative in phi, with radians understood, is

    cos(phi)/2
      +2s*sec(phi)^2*tan(phi)
      +(R/2)*sec((psi-phi)/2)^2*tan((psi-phi)/2)>0.

Hence its maximum on [0,psi] is at an endpoint. At phi=psi its value is c<3/4. At phi=0 it is

    (s-1)/2+R*c/(s+1)
       =(cos(psi)-1)/2+R*tan(psi/2).

This increases with psi because its derivative is
(-sin(psi)+R*sec(psi/2)^2)/2>0. Using psi<45 degrees and R<25/12, its value is less than

    (28sqrt(2)-31)/12<3/4,

where the last strict comparison is sqrt(2)<10/7. Thus

    L<3/4.                                          (19)

This whole-angle convex argument covers every actual a and tau. It does not assume that the extrema define realizable equilibrium configurations.

## 10. A low-L assumption reduces to one complete scalar inequality

Suppose L<=1/4. Define, with the same fixed actual frame and tau,

    Dcal(l,R)=sqrt(R^2-(l-S_0)^2)
                  -sqrt(R^2-(l+E)^2).

The actual positive heights give Dcal(L,R)=B. Its derivative in l is positive because z/sqrt(R^2-z^2) strictly increases and l+E>l-S_0. Both root arguments remain strictly inside (-R,R) when l increases to 1/4: they are inside at the actual endpoint, while at 1/4 one has

    -sqrt(2)+1/4<1/4-S_0<0,
    1/4<1/4+E<=5/4<2<=R.

The intervening arguments are affine. Therefore B<=Dcal(1/4,R).

If |1/4-S_0|>1/4+E, the latter difference is negative, contradicting B>=0. Otherwise Dcal(1/4,R) decreases weakly with R, including the equality of absolute values. Thus

    0<=Dcal(1/4,2)-B.                               (20)

For fixed actual c,s,a,b, differentiate the right side with respect to tau. With z=1/4+E, one has 1/4<z<=5/4 and

    d/dtau [Dcal(1/4,2)-B]
       =b-a*z/sqrt(4-z^2)
       >=b-a*(5/sqrt(39))>0.

Here b>a and 5/sqrt(39)<1. The entire enlarged tau interval ends at tau_*=1-s/b, which is nonnegative by (3). At that endpoint E=b-a and B=c+s-a-b. Consequently (20) implies

    J(phi)>=0,                                      (21)

where c=sin(psi),s=cos(psi),a=sin(phi),b=cos(phi), 0<=phi<=psi<45 degrees, and

    J(phi)=sqrt(4-[s*(1+tan(phi))-1/4]^2)
             -sqrt(4-[1/4+cos(phi)-sin(phi)]^2)
             -(c+s-sin(phi)-cos(phi)).               (22)

This is only an algebraic enlargement of an inequality at fixed actual c,s. No actual W contact, beta, original mean or force is moved.

The next two sections prove J(phi)<0 throughout the entire interval with one uniform strict reserve.

## 11. A full initial bound: J(0)<-9/1000

At phi=0,

    J(0)=sqrt(4-(s-1/4)^2)-sqrt(39)/4-(c+s-1).

Regard this as a function of psi with c=sin(psi),s=cos(psi). By (13), psi lies between asin(9/20) and 45 degrees. Write r_1=sqrt(4-(s-1/4)^2). Its second derivative is

    c+s + s*(s-1/4)/r_1 - 4c^2/r_1^3>0.

Indeed r_1>7/4, c^2<=1/2 and c+s>1, so the magnitude of the last term is below 128/343<1. The function is convex, and its maximum is at one of the two comparison endpoints.

At c=9/20, s=sqrt(319)/20>893/1000, with squared reserve 51/1000000. Therefore r_1<947/500, with squared reserve 137/200000. Also sqrt(39)/4>39/25. Hence

    J(0)<947/500-39/25-343/1000=-9/1000.

At c=s=1/sqrt(2), one has r_1<39/20 and c+s>7/5. Thus

    J(0)<39/20-39/25-2/5=-1/100.

The first root comparison has reserve 1/200; the bound sqrt(39)/4>39/25 has squared reserve 39/10000. Both endpoints are strict, so throughout the complete actual c interval

    J(0)<-9/1000.                                    (23)

## 12. One continuous curvature bound gives J(phi)<-71/40000

Fix actual c,s. Put

    v=s*(1+tan(phi))-1/4,
    k=cos(phi)-sin(phi),
    z=1/4+k,
    r_1=sqrt(4-v^2), r_2=sqrt(4-z^2).

On 0<=phi<=psi<45 degrees all these roots are positive, v>0 and 0<k<=1. Also sin(phi)+cos(phi)>=1. Differentiating (22) twice gives

    J''(phi)=-(sin(phi)+cos(phi))
       -2s*sec(phi)^2*tan(phi)*v/r_1
       -4s^2*sec(phi)^4/r_1^3
       -z*k/r_2
       +4*(sin(phi)+cos(phi))^2/r_2^3.              (24)

We give a complete algebraic bound for its only positive term:

    4*(2-k^2)/(4-(k+1/4)^2)^(3/2)<9/8
    for every 0<=k<=1.                              (25)

For u=z^2/4<1, the function (1-u)^(3/2) has positive third derivative. Its second Taylor polynomial at zero is therefore a lower bound. Consequently

    r_2^3>=8-3z^2+(3/16)z^4=:D_0>0.

The desired numerator comparison follows from the exact polynomial

    9D_0-32*(2-k^2)
      =(27/16)*(k^4+k^3)+(721/128)*k^2
                            -(3429/256)*k+25883/4096.

For every k>=0, convexity of k^3 and k^4 gives their tangent lower bounds at k=2/3:

    k^3+k^4 >= (68/27)*k-32/27.

Substitution gives the quadratic lower bound

    (721/128)*k^2-(2341/256)*k+17691/4096.

Its minimum on the entire real line is

    1794649/2953216>0.

Thus 9D_0>32*(2-k^2), proving (25) without a mesh or an omitted extremum.

In (24), the first term is at most -1. The third term is strictly less than -1/4, since s^2>1/2, sec(phi)>=1 and r_1<2. The second and fourth terms are nonpositive. Equation (25) therefore proves the uniform continuous curvature bound

    J''(phi)<-1/8.                                  (26)

At zero,

    J'(0)=1-s*(s-1/4)/sqrt(4-(s-1/4)^2)-5/sqrt(39)
          <1-63/400-4/5=17/400.

Here s>7/10, s-1/4>9/20, the first denominator is below 2, and 5/sqrt(39)>4/5. Integrating (26) and using (23), for every phi in the entire interval,

    J(phi)<-9/1000+(17/400)*phi-phi^2/16
           <=-9/1000+289/40000
            =-71/40000<0.                           (27)

At phi=0, (23) gives the same strict conclusion directly. The maximum of the quadratic is a purely algebraic bound on all real phi; all derivatives above use radians.

Equation (27) contradicts (21). Hence the alleged L<=1/4 domain is impossible, and

    L>1/4.                                          (28)

## 13. Complete local conclusion and all eight other original units

Equations (15),(16),(19),(28) give

    1/4<L<3/4,
    1/4<H<3/4.

Since the actual U is [L-1,L] x [H-1,H], the entire closed D_(1/4) lies in int U. Every other actual closed square misses int U; otherwise approximating its boundary point by its own interior would produce overlap of the two open interiors. Each such compact square therefore has distance strictly greater than 1/4 from O.

For any one of those squares E, choose a nearest point p. Convexity gives p dot (z-p)>=0 for every z in E, by the one-sided derivative of squared norm along its segments. Thus E lies in the actual half-plane

    (p/|p|) dot z>=|p|>1/4.

The full-Q force-free cap-arc theorem supplies an actual open radius-5/4 arc of length strictly greater than pi/4 inside int E. It applies to every orientation, load and physical circle mask.

In a nine-square packing there are eight such unchanged units. Their eight open arcs are pairwise disjoint by interior-disjointness of the actual squares. Their total length is strictly greater than 2pi, a contradiction. This proves the entire stated feature without omitting a central or exterior extra and without needing a separate pocket allocation.

## 14. Literal original D02 use and exact remaining scope

For M6.B6.HEXAGON.D02.L01345, retain the rim 01,12,23,34,45,50, the original positive chord 02 and loads {0,1,3,4,5}. Put U=2,V=1,W=0,T=3. U is truly unloaded degree three, V truly loaded degree two and W truly loaded degree three. The full remaining boundary path, all three extras and every original force remain.

Whenever UV is a U axis, UW is strict in the adjacent U vertex cone, the original UW/VW normals agree, V is nonparallel, and its unique physical circle corner is opposite UV, every local hypothesis above is literal after a symmetry of the complete actual data. The same-nine analytic input gives R>2 within the theorem's closed R>=2 domain. The entire feature is impossible.

The local quarter-disk theorem has broader scope: W has arbitrary true degree/load beyond physical boundary status, and the true third U neighbor T need not be boundary. Its use elsewhere still requires the exact complete U3, true loaded V2 and original support hypotheses. It never permits deleting an extra positive force.

The complete adjacent-unique and physical-two masks under the same common-side feature have a separate pocket theorem. A full union needs to retain that theorem's original component and all-extra routing. The parallel V alternative also needs its own physical support check. Neither the full D02 row nor a coarse parent is declared closed by this manuscript alone.

## 15. Exact operative inputs and verification boundary

| Source | SHA256 | Exact operative use |
| --- | --- | --- |
| MIXED_HUB_AXIS_SAME_BOUNDARY_SIDE_ADJACENT_OR_RADIAL_TIP_POCKET_CAPACITY_ONE.md | 94f9d4850e408c3b076605f8738126d32dd3856899ba3fe330d132b8d029ccb0 | Sections 1--2 only: mask-independent actual chart and full U3 identity, reproduced locally above without assuming its path/mask conclusion |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Lemma 2.1 only at true V2 with actual boundary neighbor W; unique physical mask gives positive inside concurrence |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force/torque, physical support, original means and radial circle resultant |
| GENERAL_SIDE_CHANNEL_CAP_INNER_ARC.md | f76d76ef2feccc80098fb6d10d6316af4e393d3ae34d4953846dd27b80c137cb | Force-free whole-Q cap-arc theorem for every actual square strictly beyond a quarter-height support |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal unchanged D02 graph, loads, true degrees and all three extras |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine exclusion of R<=2 for the original caller only |

The complete W-mask proof and all new continuous scalar comparisons are printed above. Exact fraction arithmetic checked the displayed polynomial identities and strict reserves only. The former working note with only vertical margins is superseded by this complete proof, not adopted as an exclusion source.

No pose sample, orientation grid, computational exclusion packet, normal reselection, changed original application or mean, force deletion, false lower-degree unit, Lean compilation, CI, workflow, remote write or ledger mutation was used.

