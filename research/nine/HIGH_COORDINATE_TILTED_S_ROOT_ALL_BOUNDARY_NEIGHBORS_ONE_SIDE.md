# Every boundary neighbor of a high-coordinate tilted S root lies on one strict radial side

Date: October 28, 2026. Author: house.

**Status: complete new force-free physical theorem, frozen for separate full review. No original graph, load row or ledger is closed by this manuscript alone.**

All actual squares, their original contacts, shared-side means, physical circle masks and possible individual zero circle coefficients remain. The theorem uses no force or torque equation at the root, leaf or neighbor. It enlarges the earlier shallow-root one-sided screen to the whole closed coordinate range U>=4/5, and includes the closed radius endpoint R=2.

## 1. Exact physical statement

Let actual interior-disjoint closed unit squares be contained in the origin-centered circle of radius

    2<=R<=sqrt(Q),       Q=1105/256,
    d=sqrt(R^2-1/4)-1.

Suppose two of them have the genuine tilted S-root geometry

    A=[U-1,U] times [V-1,V],
    U>=4/5,       U>=V>0,       U^2+V^2=d^2,
    P=(U,V),       e=P/d,       f=Je=(-V,U)/d,
    L=P+[0,1]e+[-1/2,1/2]f.                         (1)

The actual square L is kept as an occupied square. Its outer two corners are on the original containing circle. Let T be any other actual physical circle-touching unit which touches A.

**Theorem.** Every physical circle corner Z of T satisfies

    f.Z<0.                                           (2)

Every actual common separating normal and application is included. The neighbor may own a side, expose a vertex, be parallel to A, or have any original shared-side mean. Its positive degree and total circle load are arbitrary. A circle corner with zero individual coefficient is still covered by (2).

The root itself is strictly tilted: V>0 in (1). An aligned S root with an arbitrary independent side slider is not silently represented by setting V=0. The proof below does include every aligned or tilted frame of T.

## 2. Uniform exact bounds and the inaccessible northwest vertex

Write

    a=U-1,       alpha=U/d,       beta=V/d,
    eta=V/U=beta/alpha,       r=R-sqrt(2).

The radius interval gives

    14/15<d<61/60,       R>d+1,
    a>=-1/5,       U>V>0.                            (3)

For the first lower bound,
(29/15)^2<15/4, with reserve 11/900. For the upper bound,
d<=sqrt(1041)/16-1<61/60. Since d/sqrt(2)<4/5, the equality U=V cannot occur in (1).

We will use the strictly stronger ratio bound

    R/d>51/25.                                       (4)

Indeed

    R^2-(51d/25)^2
       =2d+5/4-(1976/625)d^2.

The expression is decreasing on [14/15,61/60], and its value at 61/60 is 8701/562500>0.

The two convenient ranges for eta are

    d>=1: eta<4/5;
    d<=1: eta<=3/4.                                  (5)

For the first, eta^2<=d^2/(4/5)^2-1
<1417/2304<16/25, with the final cross-multiplied reserve 1439. The second follows from d^2<=1 and U^2>=16/25.

Every point p in a physical boundary unit satisfies |p|>=r: compare p with one of its actual radius-R corners and use the unit diameter sqrt(2).

The actual northwest A vertex N=(a,V) is strictly inside that forbidden point disk:

    |N|^2=d^2+1-2U<=d^2-3/5<r^2.                   (6)

Here

    r^2-(d^2-3/5)
       =2d+77/20-2sqrt(2)R>0.

Both compared quantities are positive. The squared difference is

    (2d+77/20)^2-8R^2
       =1929/400-(3/5)d-4d^2
       >281/3600>0.

Consequently no actual physical boundary unit can contain N. No force or normal assumption is part of this fact.

The leaf point P belongs to no third actual unit. At P the root occupies its southwest right-angle tangent sector, while L occupies the half-plane directed along the strictly northeast vector e. The two remaining connected tangent gaps have angles strictly below pi/2. A unit square's tangent sector at a contained point has angle at least pi/2 and cannot fit in either gap. This excludes P for every third unit, including side endpoints and coincident application means.

## 3. A small north-contact interval is entirely inaccessible

The following interval calculation will be used in the complete leaf-separator cover.

Suppose a north contact Q=(q,V) satisfies

    a<=q<=U-d/(2V).                                  (7)

This interval is empty unless beta>=1/2. If beta>=1/2, put

    q_0=U-d/(2V).

In the leaf frame the endpoint Q_0=(q_0,V) is

    Q_0=(d-1/(2eta))e+(1/2)f.                         (8)

Its radial coefficient is positive: beta>=1/2 gives
eta>=1/sqrt(3), so 1/(2eta)<=sqrt(3)/2<7/8<d.

We prove |Q_0|<r. If d>=1, (5) gives

    |Q_0|^2<=(d-5/8)^2+1/4.

The exact difference from r^2 is

    (13/4)d+167/64-2sqrt(2)R(d),
    R(d)=sqrt((d+1)^2+1/4).

Its derivative is strictly larger than 13/4-2sqrt(2)>0. At d=1 its positivity follows by squaring the two positive quantities, with reserve

    (375/64)^2-8R(1)^2=1361/4096>0.                  (9)

If d<=1, (5) instead gives

    |Q_0|^2<=(d-2/3)^2+1/4.

The corresponding difference is

    (10/3)d+23/9-2sqrt(2)R(d).

Its derivative is strictly larger than 10/3-2sqrt(2)>0. At d=14/15 the exact squared reserve is

    (17/3)^2-8R(14/15)^2=47/225>0.                   (10)

Thus both complete d ranges give |Q_0|<r. The squared norm of (q,V) is convex in q. Its value at the other endpoint q=a is strictly below r^2 by (6). Hence every point in the entire closed interval (7) has norm strictly below r.

**North-interval conclusion.** No actual physical boundary unit can contain any point in (7). This includes beta=1/2, when the interval has only its northwest endpoint.

## 4. The complete north-neighbor theorem: aligned T

Suppose T touches A across the north own normal. Its actual minimum y is V.

First let T own this minimum side. Then it is aligned with A and has the exact form

    T=[z,z+1] times [V,V+1].

Its bottom side physically intersects [a,U] times {V}; no midpoint or endpoint application is selected in place of an original mean.

Avoiding the real leaf forces

    z+1<=U.                                          (11)

Otherwise at height V+xi for sufficiently small xi>0, L's inner edge is at x=U-(V/U)xi<U and its open horizontal section extends to the right of U. The open interval (z,z+1) meets that section because z<=U<z+1, contradicting disjoint interiors. This also treats z=U by taking xi>0.

Equation (11) gives z<=U-1=a. Since the bottom side still meets the actual root top side, z+1>=a. Thus N=(a,V) belongs to T, contrary to (6). This excludes the whole aligned T case with every original shared mean.

## 5. The complete north-neighbor theorem: exact separating-axis cover

Otherwise T has a unique bottom vertex Q=(q,V), and the full actual frame is

    T=Q+[0,1]u+[0,1]v,
    u=(c,s),       v=(-s,c),
    c,s>0,       c^2+s^2=1,
    a<=q<=U.                                         (12)

Put

    g=U-q in[0,1],
    K=e.u=alpha*c+beta*s>0,
    S=f.u=alpha*s-beta*c,
    S_-=max(-S,0).

Then K^2+S^2=1. All T orientations in (12) are retained.

For two rectangles with disjoint open interiors, the separating-axis theorem supplies a common non-strict separation parallel to a side of at least one rectangle. This includes a point contact, side endpoint and whole shared segment. One elementary proof is to form their Minkowski difference: its polygonal sides are parallel to sides of the two original rectangles, and an outside or boundary translation is separated by one of those side normals.

Orient such a normal w from T toward L. The actual support inequality is

    g*w_x >= max(w.u,0)+max(w.v,0)
                   -min(w.e,0)+(1/2)|w.f|.           (13)

Each right side for the eight possible own-axis normals is strictly positive. Therefore w_x>0. The four possible normals are precisely e,-f,u,-v; all their x components are strictly positive. Formula (13) gives the exhaustive alternatives

    w=e:   g>=g_e=(K+S_-)/alpha;
    w=-f:  g>=g_f=(S_-+1/2)/beta;
    w=u:   g>=g_u=(1+|S|/2)/c;
    w=-v:  g>=g_v=(S_-+K/2)/s.                       (14)

These are necessary inequalities from actual avoidance of the occupied L. No new physical contact with L, selected stress or altered normal is introduced.

The u alternative is impossible, since g_u>=1/c>1.

The -f alternative gives g>=1/(2beta)=d/(2V), so its actual Q belongs to the forbidden interval (7).

If S<0, then K-S>1, so g_e>1/alpha>1 and the e alternative is impossible. Also

    2beta(-S+K/2)-s=-(alpha+2beta)S>0,

using s=alpha*S+beta*K. Thus g_v>1/(2beta), and the -v alternative is again excluded by (7). This exhausts the whole S<0 range.

It remains S>=0. The only surviving possibilities in (14) are e and -v, and

    g_e=K/alpha=c+eta*s,
    g_v=K/(2s),
    g_v/g_e=alpha/(2s).                              (15)

We now treat their entire common envelope, including equality.

## 6. The small-s north envelope

Suppose S>=0 and 0<s<=alpha/2. Equation (15) gives

    q<=q_e:=U-g_e.

For a fixed actual T frame, the squared norm of each of its four corners is a convex function of q. The lower endpoint q=a puts Q=N, so every corner then has norm at most |N|+sqrt(2)<R by (6).

If q_e<a there is no actual q. Otherwise it remains to bound the four corners at q=q_e. The corner E=Q+u has

    e.E=d,       f.E=xi:=s/alpha in(0,1/2].

Thus E=d*e+xi*f. Also

    Q.u=q*c+V*s >= a*c >=-1/5.

Consequently adding u strictly increases squared norm, both at Q and at Q+v. It suffices to bound E and E+v.

The first has norm squared d^2+xi^2<=d^2+1/4<R^2. Since e.v=-S and f.v=K, the second has exact deficit

    R^2-|E+v|^2
       =2d+1/4-xi^2+2d*S-2xi*K
       >=2d-1>0.                                    (16)

Every corner is therefore strictly inside the circle at both endpoints of the whole q interval. Convexity proves the same for every actual q. This excludes the complete small-s envelope.

## 7. The remaining north envelope and its exact scalar deficit

Suppose S>=0 and s>=alpha/2. Now (15) gives

    q<=q_v:=U-g_v.

Again the q=a endpoint is strictly internal by (6), and q_v<a leaves no actual q. At q=q_v put

    t_0=alpha/(2s) in(0,1],
    tau=1-t_0 in[0,1),
    E=P+(1/2)f=Q+t_0*u.

The two corners which can maximize the norm are therefore

    Q+u=E+tau*u,       Q+u+v=E+tau*u+v.              (17)

The other two are smaller because Q.u>=-1/5, exactly as in Section 6.

For the first corner in (17),

    R^2-|E+tau*u|^2
       =2d+1-tau^2-2d*K*tau-S*tau
       >=(2d+1)(1-tau)-tau^2.

Both ranges in (5) have eta<=4/5. Consequently
S+eta*K<=sqrt(1+eta^2)<=sqrt(41)/5<13/10, so
tau<8/13. The displayed deficit is therefore strictly larger than

    (43/15)(5/13)-64/169=367/507>0.                  (18)

For the opposite corner the exact deficit is

    D(d,K,S,tau)
       :=2d(1+S-tau*K)-K-tau*S-tau^2.                (19)

We prove D>0 on the entire actual range, not merely at selected orientations.

Since s=alpha*S+beta*K,

    tau=1-1/[2(S+eta*K)].

The quantity D is increasing in d and decreasing in tau on K,S>=0, K^2+S^2=1, 0<=tau<1: its respective derivatives are

    2(1+S-tau*K)>0,
    -2d*K-S-2tau<0.

For an upper comparison eta<=E_0, put

    w=S+E_0*K,       tau_0=1-1/(2w).

Both choices E_0=4/5 and E_0=3/4 have w>=E_0>1/2 on the entire closed quarter circle. Hence 0<tau_0<1 and tau<=tau_0.

### 7.1. The whole d>=1 range

Use d_0=1 and E_0=4/5. Let t=tan(gamma/2) in[0,1], where K=cos(gamma), S=sin(gamma). Then

    K=(1-t^2)/(1+t^2),       S=2t/(1+t^2),
    w=(4+10t-4t^2)/(5(1+t^2)).

Expansion of the exact rational expression gives

    25(1+t^2)^3 * 4w^2 * D(1,K,S,tau_0)
      = N_1(t),

    N_1(t)=7-32t+477t^2+2864t^3
                         +285t^4-1232t^5+231t^6.     (20)

For 0<=t<=1, t^5<=t^3. Therefore

    N_1(t)
      >=477(t-16/477)^2+3083/477
                     +1632t^3+285t^4+231t^6
      >0.                                            (21)

All multiplying factors in (20) are positive. Thus D(1,K,S,tau_0)>0, and the full monotonic comparison gives D(d,K,S,tau)>0.

### 7.2. The whole d<=1 range

Use d_0=14/15 and E_0=3/4. The same half-angle parameter gives

    w=(3+8t-3t^2)/(4(1+t^2)),

and the exact expansion is

    16(1+t^2)^3 * 15 * 4w^2
                     * D(14/15,K,S,tau_0)
      = N_0(t),

    N_0(t)=72-392t+2736t^2+25136t^3
                         +4040t^4-10408t^5+1728t^6.  (22)

Again t^5<=t^3 gives

    N_0(t)
      >=2736(t-49/684)^2+9911/171
                     +14728t^3+4040t^4+1728t^6
      >0.                                            (23)

This proves D>0 throughout the low d range as well. The comparison includes d=1 in either proof, S=0, the half-angle endpoint t=1, and tau=0. The actual inequalities are strict at every retained endpoint.

Equations (18)--(23) put every corner at q=q_v strictly inside the containing circle. Convexity in q and the already checked q=a endpoint then exclude every actual q in the whole large-s envelope.

Sections 4--7 prove the complete force-free result:

    no physical boundary neighbor of A can use the North own normal.
                                                               (24)

## 8. West, Southwest, South and Southeast: all actual circle corners are below f=0

Let p=(a,y) be an actual West-side application belonging to a physical boundary neighbor. If f.p>=0, then

    Va/U<=y<=V.

Since |a|<U, this implies |y|<=V and |p|^2<=a^2+V^2<r^2 by (6), a contradiction. Hence f.p<0.

If a circle corner Z of that neighbor had f.Z>=0, resolving p in the e,f frame gives

    |Z-p|^2>=min(|R*e-p|^2,|-R*e-p|^2).             (25)

Both distances are already larger than sqrt(2) in their horizontal coordinate alone:

    R*alpha-a=U(R/d-1)+1>229/125,
    R*alpha+a=U(R/d+1)-1>179/125>sqrt(2).             (26)

The last squared reserve is 791/15625>0. This contradicts the unit diameter. Thus every West neighbor circle corner has f.Z<0. The Southwest endpoint is included.

Now let p=(x,V-1) be any actual South-side point, a<=x<=U. Then

    d*(f.p)=-V*x+U(V-1)<=V-U<0.

For a proposed Z with f.Z>=0, the lower bound in (25) becomes

    F(x)=R^2+x^2+(V-1)^2
                  -(2R/d)|U*x+V(V-1)|.              (27)

On the branch where the expression inside the absolute value is nonnegative, F'(x)=2x-2R*alpha<0. On its nonpositive branch, F'(x)=2x+2R*alpha>0, because x>=-1/5 and R*alpha>8/5. Therefore the minimum on [a,U] is at one of its two outer endpoints, not at a sign-change point.

At the southeast endpoint (U,V-1), its radial projection is positive and the exact lower bound is

    (R-d)^2+1+2V(R/d-1)>2.                            (28)

At the southwest endpoint (U-1,V-1), put W=U+V. If its radial projection d-W/d is nonnegative, the lower bound is

    (R-d)^2+2+2W(R/d-1)>2.                            (29)

If that projection is nonpositive, it is instead

    2+(R+d)[R+d-2W/d]>2.                              (30)

For (30), W<=sqrt(2)d and R+d>44/15>2sqrt(2). All inequalities in (28)--(30) are strict because R>d+1. Thus every actual South application, including both endpoints, contradicts the unit diameter if f.Z>=0.

The same southeast or southwest vertex calculations apply to any strict normal exposing that vertex. No side ownership of T was assumed in (25)--(30).

## 9. The whole East-normal case is screened by the occupied leaf

We use only the following complete physical angular fact from the pinned sources in Section 11:

    no circle corner of a boundary unit different from L lies
    on the closed minor containing-circle arc between L's two corners.
                                                               (31)

For precision, distinct physical boundary centers are separated by more than 2pi/9. Each physical circle corner differs from its own center direction by less than pi/9. The real L center is on the e ray, so every circle corner of any other physical boundary unit has angular distance greater than pi/9 from e. Both L corners have distance less than pi/9 from e. This proves (31), with every physical mask and zero individual coefficient included.

Suppose an actual East-normal neighbor T contains an actual contact p=(U,y), y<=V, and has a circle corner Z with f.Z>=0. It lies wholly in x>=U. The point p cannot be P by Section 2, so y<V, f.p<0 and e.p<d.

If f.Z=0, its x coordinate forces Z=R*e, contrary to (31). Hence f.Z>0. If e.Z>d+1, the exact equation

    (e.Z)^2+(f.Z)^2=R^2=(d+1)^2+1/4

puts Z strictly between the two leaf corners on their minor arc, again contrary to (31). Thus e.Z<=d+1.

The segment [p,Z] belongs to T and crosses f=0 at a point q=t*e. Since every point of T has x>=U, t>=d. Since e.p<d and e.Z<=d+1, the interior crossing has t<d+1. If t=d, it is the unshareable actual P. If d<t<d+1, q belongs to int(L). A closed point of T in the open L forces open-interior overlap, because interior T points approach it. Both alternatives contradict the actual packing.

Thus every circle corner in the entire East-normal case also has f.Z<0. No force, degree or fixed application on that side was used.

## 10. Exhaustive physical join and retained limits

Choose any original actual common separating normal at A--T. Its complete feature cover is:

- positive y component and negative x component: the ineligible northwest vertex N;
- positive y component and positive x component: the unshareable leaf vertex P;
- the North axis: excluded in full by Sections 4--7;
- the West or South axis, or either strict lower vertex cone: every physical circle corner satisfies (2), by Section 8;
- the East axis: every physical circle corner satisfies (2), by Section 9.

These alternatives exhaust all own normal cones and their axis endpoints. They prove (2) for every actual physical boundary neighbor T other than L.

The theorem is independent of the root's true degree. It does not turn an H4 star into an H3 star, require a loaded neighbor, remove an original pair or circle force, choose a new shared-side mean, or apply unique-corner concurrence to a two-corner mask. The radial leaf itself is used as the actual occupied unit throughout.

This source has no original-family conclusion. A later caller must establish the full physical boundary-access order and the complete loaded set before using the one-sided corners in a component force sum. In particular an aligned S root with a free side slider, a tilted root with U<4/5, and a path whose intermediate load status is not known remain outside the local statement (1).

## 11. Complete operative inputs and provenance

The sole imported physical ingredients are the two angular facts used in Section 9.

| Source | SHA256 | Exact operative scope |
| --- | --- | --- |
| CENTERED_INNER_ARC.md | fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5 | Complete strict separation greater than 2pi/9 of any two actual physical boundary-center directions. |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | Complete Lemma 2.1: every physical circle corner lies strictly within pi/9 of its actual center direction. No pocket theorem is imported. |

The angular consequence (31) is also explicitly reconstructed in Section 1 of S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, current SHA256
70a3488bb613b1ce1cb4ac778d6f2b2acb2e04bae226741a0665378d096e28ec. Its connected-neighbor or component force theorem is not used here.

The earlier SHALLOW_TILTED_S_ROOT_BOUNDARY_NEIGHBORS_ONE_SIDE.md, current SHA256
c8e399293ee684fa21a4d5028dc56ab9234007db2b7e1b3a35ad9e214efc45a3, proved the narrower U>=1-epsilon chart. The earlier S_LEAF_ROOT_HIGH_COORDINATE_NORTH_SCREEN_EXCLUSION.md, current SHA256
acec45db3253b2be2c6b68a85714313da572a8a858e9921431a745cafd889a83, proved a North screen with the additional V<9/20 premise, followed by a separate true-degree-three caller. Neither older caller is imported. The northwest-point reserve (6) is reproduced from that source, and root separately suggested its use as the lower-q endpoint during this investigation.

The new complete separating-axis cover, both full continuous North inequalities, the degree-free South/West distance bounds and the East occupied-leaf crossing argument are printed above. They use no sampled pose, numerical-angle grid, new computational geometry certificate, Lean operation, CI, remote mutation or ledger edit.

