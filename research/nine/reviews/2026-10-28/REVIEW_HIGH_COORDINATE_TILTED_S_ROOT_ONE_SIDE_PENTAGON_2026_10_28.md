# Independent review: every boundary neighbor of a high-coordinate tilted S root lies on one strict radial side

Date: October 28, 2026. Reviewer: pentagon.

**Verdict: full independent PASS, with no source repair requested.** This review concerns the complete force-free local theorem at the exact source bytes below. It does not close an original graph, load row, completion family, or ledger flag.

## 1. Exact target, read scope, and independence

Target:

- HIGH_COORDINATE_TILTED_S_ROOT_ALL_BOUNDARY_NEIGHBORS_ONE_SIDE.md
- SHA256: 96b83e1c002cf7b2535be832e9187b7220597b57b764820305d19705690c72f9
- Exact byte length: 20,217.

I read the entire target, independently rederived its geometric support cover and continuous inequalities, and read both complete operative source files. Their current exact pins are:

| Operative source | SHA256 | Scope used in the target and checked here |
| --- | --- | --- |
| CENTERED_INNER_ARC.md | fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5 | The full closed centered inner arc and its strict greater-than-40-degree separation consequence for two actual boundary-square centers. |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b | The self-contained proof of Lemma 2.1, placing every physical circle corner strictly within 20 degrees of its actual square center. No triangle-hole or exterior-pocket conclusion is imported. |

The current target and both operative pins were checked against actual filesystem bytes. The two older S-root screens and S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md listed by the author are provenance only; this review does not transfer an older caller or an older theorem's additional premises.

I did not contribute to discovery of the new theorem, its separating-axis cover, either polynomial comparison, or its side cases. The author's disclosed use of root's northwest-point suggestion remains disclosed. My earlier authorship of other arc or pocket manuscripts has no operative role here: neither direct input above is authored by me, and neither of my later strengthened arc theorems is needed.

The independent audit uses continuous hand inequalities and exact rational polynomial arithmetic. No pose sample, interval grid, numerical optimization, Lean operation, CI, remote write, or ledger mutation was performed.

## 2. The precise physical domain

The theorem retains the actual occupied root and leaf

    A=[U-1,U] x [V-1,V],
    U>=4/5, U>=V>0, U^2+V^2=d^2,
    d=sqrt(R^2-1/4)-1, 2<=R<=sqrt(1105/256),
    P=(U,V), e=P/d, f=Je,
    L=P+[0,1]e+[-1/2,1/2]f.

The two outer leaf corners are the actual radius-R corners. For every other actual physical boundary unit T touching A, the conclusion covers **every physical circle corner** Z of T:

    f.Z<0.

There is no force, load, degree, uniqueness-of-corner, or concurrence assumption. In particular a zero coefficient at a physical circle corner does not remove that corner from the conclusion. Any original shared-side mean stays on its actual common segment; the proof never chooses a new mean.

The restrictions are substantive. V>0 is needed for the strict tilted leaf geometry and the unshareable P sector. The theorem does not treat an aligned root with a free slider by setting V=0. The neighbor T may nevertheless be aligned, tilted, side-owning, vertex-owning, or shared with A at any original endpoint.

## 3. Uniform bounds and the two inaccessible vertices

The source's exact radius bounds are valid at both containing-radius endpoints:

    14/15<d<61/60, R>d+1, U>V>0, a=U-1>=-1/5.

The strict upper d comparison has squared reserve 31/57600. The lower comparison has reserve 11/900. Also

    (4/5)^2-(61/60)^2/2=887/7200>0,

so U=V is genuinely impossible rather than an omitted diagonal endpoint.

I checked

    R^2-(51d/25)^2=2d+5/4-(1976/625)d^2.

Its derivative is negative on the entire d interval, and its upper-end value is 8701/562500. Thus R/d>51/25 is strict even when R=2 or U=4/5. The two eta=V/U bounds are correct: eta<4/5 for d>=1 and eta<=3/4 for d<=1. At d=1 either later comparison can be used.

Every point of a unit with an actual radius-R corner has norm at least R-sqrt(2), solely by the diameter bound. The northwest root point N=(a,V) violates this necessary condition:

    |N|^2<=d^2-3/5<(R-sqrt(2))^2.

The last comparison uses two positive quantities before squaring; its exact difference reduces to a decreasing quadratic with strict lower reserve 281/3600 at d=61/60. This excludes N from the entire closed T, not merely from the interior or from an application chosen by a force equation.

The leaf point P is also unavailable to every third square. At P, A occupies the southwest right-angle tangent sector and L occupies the inward northeast half-plane. Because both coordinates of e are strictly positive, each remaining connected tangent gap has aperture strictly less than pi/2. The tangent sector of a third square at any contained point has aperture at least pi/2 and is connected, so it cannot fit. This handles a third square's vertex, side interior, side endpoint, and all coincident application choices.

## 4. The entire forbidden North interval

I rederived the auxiliary interval

    a<=q<=U-d/(2V).

It is nonempty exactly when beta=V/d>=1/2. Its right endpoint in the leaf frame is

    Q_0=(d-1/(2eta))e+(1/2)f.

The first coefficient is positive: beta>=1/2 implies eta>=1/sqrt(3), while sqrt(3)/2<7/8<d. Therefore increasing the lower bound on 1/(2eta) gives the claimed upper norm bounds with the correct direction.

For d>=1 the comparison is

    |Q_0|^2<=(d-5/8)^2+1/4.

Its deficit from (R-sqrt(2))^2 increases with d and is positive at d=1 with squared reserve 1361/4096.

For d<=1 the comparison is

    |Q_0|^2<=(d-2/3)^2+1/4.

Its deficit also increases with d and is positive already at d=14/15 with squared reserve 47/225. The derivative bounds use R'(d)<1 and the strict inequalities 13/4>2sqrt(2), 10/3>2sqrt(2).

The other interval endpoint is N. Convexity of q^2+V^2 therefore excludes every point of the entire closed interval. The beta=1/2 singleton endpoint is N itself and is retained.

## 5. Exhaustive actual North geometry

### 5.1. Parallel and shared North contacts

If T has an actual minimum horizontal side at height V, it has the complete aligned form

    [z,z+1] x [V,V+1].

Physical intersection with the root top requires its bottom interval to meet [a,U]. If z+1>U, the real leaf's small positive-height open horizontal sections overlap T: the leaf's inner edge is left of U and its open section extends to the right of U. This includes z=U. Consequently avoidance forces z+1<=U.

Since z<=a and z+1>=a, T contains N, which has already been excluded. No mean on the actual bottom common side has been altered. Equality at the side interval endpoints does not escape the argument.

### 5.2. Oblique North contacts and the full separator cover

All remaining North neighbors have a unique bottom vertex Q=(q,V) and can be written

    T=Q+[0,1]u+[0,1]v,
    u=(c,s), v=(-s,c), c,s>0, c^2+s^2=1.

This covers all nonaligned square orientations above the North support. Put g=U-q in [0,1],

    K=e.u>0, S=f.u, S_-=max(-S,0).

I independently derived the support inequality for an actual separator w directed from T toward the occupied L:

    g*w_x >= max(w.u,0)+max(w.v,0)
                 -min(w.e,0)+(1/2)|w.f|.

The separating-axis theorem applies to actual disjoint open rectangles even at point contact or a shared side. The right side is strictly positive for each candidate own-axis normal, so w_x must be positive. The full list is exactly e,-f,u,-v. Their respective necessary lower bounds on g are

    (K+S_-)/alpha,
    (S_-+1/2)/beta,
    (1+|S|/2)/c,
    (S_-+K/2)/s.

No geometric contact with L is assumed or created by using this necessary separator.

The u case exceeds one. The -f case enters the forbidden North interval. If S<0, the e case exceeds one because K-S>1, and the -v case enters that same forbidden interval by the exact identity

    2beta(-S+K/2)-s=-(alpha+2beta)S>0.

Thus the entire S<0 range is excluded. In the remaining S>=0 range the two possible thresholds have ratio alpha/(2s). Choosing their minimum gives the correct enlarged common envelope; it does not discard the possibility of either separator.

## 6. The two continuous North envelopes

For fixed frame u,v, every corner's squared norm is a convex function of q. The common lower endpoint q=a places Q at N, so each comparison corner has norm at most |N|+sqrt(2)<R. This scalar endpoint is valid without requiring that the comparison pose itself be a packing. If the upper q endpoint is below a, the actual interval is empty.

For 0<s<=alpha/2, the upper endpoint is q_e=U-K/alpha. There

    E=Q+u=d*e+xi*f, xi=s/alpha in(0,1/2].

Since Q.u>=-1/5, adding u strictly increases squared norm at Q and Q+v. Therefore E and E+v exhaust the potentially largest corners. Their deficits are positive, including xi=1/2:

    |E|^2<=d^2+1/4<R^2,
    R^2-|E+v|^2>=2d-1>0.

For s>=alpha/2, the upper endpoint is q_v=U-K/(2s). With

    t_0=alpha/(2s), tau=1-t_0,
    E=P+(1/2)f=Q+t_0*u,

the only possible farthest corners are E+tau*u and E+tau*u+v. The first has deficit strictly greater than 367/507 using tau<8/13. The latter has exact deficit

    D=2d(1+S-tau*K)-K-tau*S-tau^2.

I checked both monotonicity signs over the full enlarged quarter circle: D is strictly increasing in d and strictly decreasing in tau. With eta<=E_0,

    w=S+E_0*K, tau_0=1-1/(2w),

we have w>=E_0>1/2 and tau<=tau_0. Thus the comparison never reverses sign or uses a negative denominator.

For d>=1, compare at d=1,E_0=4/5. For d<=1, compare at d=14/15,E_0=3/4. After K=(1-t^2)/(1+t^2), S=2t/(1+t^2), both exact polynomial identities (20) and (22) were independently re-expanded coefficient by coefficient; all seven residual coefficients in each identity are zero.

The continuous positivity arguments are valid on the entire closed t interval [0,1]:

    N_1 >=477(t-16/477)^2+3083/477
                  +1632t^3+285t^4+231t^6>0,

    N_0 >=2736(t-49/684)^2+9911/171
                  +14728t^3+4040t^4+1728t^6>0.

The replacement of the negative t^5 term by the corresponding negative t^3 term has the correct direction because t^5<=t^3. Every multiplier used to recover D is positive. The comparisons cover S=0, the small/large-envelope equality, tau=0, d=1, and the enlarged half-angle endpoint t=1. Every actual North orientation is consequently excluded.

## 7. West, lower vertices, and South

For an actual West-side point p=(a,y), the supposition f.p>=0 forces

    Va/U<=y<=V.

Since |a|<U, this gives |y|<=V and |p|<=|N|<R-sqrt(2), a contradiction. Thus f.p<0.

For any p with f.p<0, the maximum of p.Z over the radius-R upper f-semicircle occurs at one of its two radial endpoints. Hence a proposed circle corner with f.Z>=0 satisfies the exact lower bound

    |Z-p|^2>=min(|R*e-p|^2,|-R*e-p|^2).

For West points, each endpoint distance already exceeds the unit diameter in its horizontal coordinate:

    R*alpha-a>229/125,
    R*alpha+a>179/125>sqrt(2).

This is a statement about all physical corners and does not require a corner-force sign.

For a South point p=(x,V-1), the source correctly gives f.p<0 for the entire closed side. The relevant distance function is

    F(x)=R^2+x^2+(V-1)^2
                   -(2R/d)|Ux+V(V-1)|.

On the negative-sign branch its derivative is positive; on the positive-sign branch its derivative is negative. A zero of the expression inside the absolute value is therefore a possible peak, not a missing minimum. The minimum on [a,U] is at one of the two outer endpoints.

At the southeast endpoint the radial projection is positive. This follows explicitly from V<=d/sqrt(2) and d>14/15>1/sqrt(2). The source's displayed deficit is consequently the correct branch. At the southwest endpoint both possible radial signs are separately checked. All three resulting expressions are strictly greater than two, using R-d>1 and

    R+d>44/15>2sqrt(2).

The strict southwest and southeast normal cones use those same actual vertices, so they require no separate side-ownership assumption. The West/South axis endpoints and all side means remain included.

## 8. East and the actual occupied leaf

I checked the only imported angular step at its full physical scope. Our containing-radius interval is contained in the declared interval of both sources. CENTERED_INNER_ARC proves actual center separation strictly greater than 40 degrees; Lemma 2.1 of CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS bounds every physical circle corner's angle from its own center strictly below 20 degrees.

The real L center lies on e. By the circle-angle triangle inequality, every physical corner of any other boundary unit is more than 20 degrees from e. Both L circle corners are within 20 degrees of e. Thus no such other corner belongs to the closed minor leaf arc. The argument includes both-corner physical masks and zero individual weights.

For an East neighbor, T is wholly in x>=U and contains its actual application p=(U,y), y<V. Therefore f.p<0 and e.p<d. If a proposed corner has f.Z=0, its x coordinate forces Z=R*e, on the forbidden leaf arc. If f.Z>0 and e.Z>d+1, the circle equation puts Z strictly inside that same minor arc. Thus a remaining proposed corner must satisfy e.Z<=d+1.

The actual segment [p,Z] stays inside T. Its interior crossing of f=0 is q=t*e with d<=t<d+1. At t=d it is the unshareable P; for d<t<d+1 it lies in the open occupied L. A point of closed T in open L implies an intersection of the two open interiors, since interior points of T approach that point. This justifies the closed-set endpoint handling in the crossing argument.

No independent leaf position, fictitious contact, or altered force application is used.

## 9. Exact arithmetic audit

The audit reproduced both degree-six identities with zero coefficient remainder. It also checked the following 27 strictly positive rational comparisons, together with the two exact threshold identities used in (26):

| Comparison | Exact positive reserve or value |
| --- | --- |
| Lower d bound | 11/900 |
| Upper d bound | 31/57600 |
| Exclusion of U=V | 887/7200 |
| R/d comparison endpoint | 8701/562500 |
| Magnitude proving negative derivative of ratio comparison | 36578/9375 |
| High-range eta comparison | 1439/57600 |
| Northwest-point squared comparison | 281/3600 |
| sqrt(3)/2<7/8 | 1/64 |
| High-d North endpoint comparison | 1361/4096 |
| Low-d North endpoint comparison | 47/225 |
| 13/4>2sqrt(2), squared | 41/16 |
| 10/3>2sqrt(2), squared | 28/9 |
| sqrt(41)/5<13/10, squared | 1/20 |
| First large-s corner deficit | 367/507 |
| High polynomial square-completion constant | 3083/477 |
| Low polynomial square-completion constant | 9911/171 |
| High polynomial remaining cubic coefficient | 1632 |
| Low polynomial remaining cubic coefficient | 14728 |
| West distance threshold above sqrt(2), squared | 791/15625 |
| 44/15>2sqrt(2), squared | 136/225 |
| Imported centered-arc radius upper comparison | 9/4096 |
| Imported centered-arc center lower comparison | 41/1600 |
| Imported cos(20-degree) triple-angle comparison | 17/1024 |
| Imported sin(20-degree) squared triple-angle comparison | 320041 |
| Imported centered-arc cubic lower reserve | 117/40960 |
| Imported corner-angle radius polynomial endpoint | 331/800 |
| Imported arctan(1/3)<20-degree squared comparison | 74/81 |

The two threshold identities are

    (4/5)(51/25-1)+1=229/125,
    (4/5)(51/25+1)-1=179/125.

The physical strictness in (26) comes from R/d>51/25, not from pretending either threshold identity is strict.

## 10. Exhaustiveness and adoption scope

The complete normal-cone cover at A is sound:

- strict northwest exposes N and is impossible;
- strict northeast exposes the unshareable P and is impossible;
- North is entirely excluded by the aligned and oblique arguments;
- West, South, and both strict lower vertex cones force every physical T corner below f=0;
- East forces the same conclusion by the occupied leaf.

All own-axis boundaries are explicitly retained. The proof is independent of the true root degree and of all neighbor degrees. It removes no force, replaces no original mean, and does not apply a unique-corner result to a two-corner mask.

**Final review determination:** the complete local theorem at SHA256 96b83e1c002cf7b2535be832e9187b7220597b57b764820305d19705690c72f9 is valid as stated, without repair. A later original-family application must still establish that its actual tilted S root has U>=4/5 and identify its full loaded set and boundary-access order before summing the one-sided circle resultants. This review grants no independent original-family or ledger closure.

