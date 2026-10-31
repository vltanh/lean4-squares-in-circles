# A negative left support and a vertically spanning common neighbor exclude a loaded boundary tip

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete new local hand theorem and exact low-radius aligned-fan interface join, frozen for independent review.** The local theorem has no upper radius bound, no equation or degree premise at the root or common neighbor, and no radial-leaf premise. It uses the true loaded degree-two equation only at the displayed boundary tip. Every actual support owner, shared-side mean, physical circle mask and individual zero coefficient remains.

The original application covers the entire low-radius aligned inner-fan interface in which the original root normals toward its two boundary pages are North and South and its normal toward their common neighbor is West. It does not exclude the other low-radius strict-root-vertex interfaces, and assigns no original-row credit.

## 1. Complete local statement

Let H,K,V be three distinct actual closed unit squares with pairwise disjoint open interiors, all contained in the original origin-centered disk D_R, where

    R>=2.

Use an actual own frame of H about the unchanged circle origin and suppose

    H=[epsilon,epsilon+1] times [-b,a],
    -1/15<epsilon<0,
    a+b=1,       0<a<=2/3.                            (1)

Thus b>=1/3. K physically touches H with the actual H-to-K normal West. In particular

    max_K x=epsilon.

Suppose K reaches the level of H's lower side:

    min_K y<=-b.                                     (2)

V has true positive degree two, with its entire original positive pair neighborhood exactly H,K and positive total circle coefficient. Its original H-to-V normal is North, so

    min_V y=a,

and its actual HV application or shared mean belongs to H's upper side. The original KV normal and its actual aggregate application are unrestricted.

**Theorem.** These data are impossible if V physically touches the containing circle.

No force equation at H or K is used. Their degrees and circle loads may be arbitrary. The entire local theorem is valid at R=2 and throughout R>2, without an upper bound. The negative sign of epsilon is an explicit hypothesis; epsilon=0 is not silently included.

## 2. All parallel endpoints are excluded with their actual means

### 2.1. V parallel to H

Write

    V=[z,z+1] times [a,a+1].

Its actual H contact gives z+1>=epsilon, while its actual K contact gives z<=epsilon. Therefore

    epsilon-1<=z<=epsilon.

Every actual V corner satisfies

    |x|<16/15,       0<y<=5/3.

Its squared norm is strictly below

    (16/15)^2+(5/3)^2=881/225<4<=R^2,                (3)

with exact reserve 4-881/225=19/225. Thus V cannot physically touch the circle. All original shared-side means and both endpoints are included.

### 2.2. K parallel to H, with V nonparallel

The actual K has horizontal interval [epsilon-1,epsilon]. Its contact with V is at a height at least a. Combining this with (2), the unit vertical width and a+b=1 forces

    K=[epsilon-1,epsilon] times [-b,a].

The unique minimum-y V vertex is its original HV application Q=(x,a), with epsilon<=x<=epsilon+1. Every KV contact must have height a, so it must also be Q. Since K lies in x<=epsilon, necessarily

    Q=(epsilon,a).                                   (4)

At K's upper-right vertex the actual K-to-V supporting normal n has

    n_x>=0,       n_y>=0.

Keep the two original positive V magnitudes mu at HV and nu at KV. The full V force vector from its circle coefficients is

    F_V=mu*North+nu*n.

Thus (F_V)_x>=0 and (F_V)_y>0. Both original pair applications are exactly Q. Since every individual circle force has zero origin moment, the complete V origin-moment equation requires

    0=det(Q,F_V)=epsilon*(F_V)_y-a*(F_V)_x<0,          (5)

using epsilon<0 and a>0. This contradiction retains every possible physical circle mask and zero corner coefficient. It does not need distinct applications, a proper-concurrence theorem or a newly chosen support normal.

The common-application endpoint (4) is therefore excluded. Both K and V are genuinely tilted in every remaining configuration.

## 3. The full tilted frames and original return mean

Write the actual K frame as

    K=P+[0,1]u_K+[0,1]v_K,
    P=(epsilon,t),
    u_K=(-c,s),       v_K=(-s,-c),
    c,s>0,       c^2+s^2=1.                          (6)

P is its unique maximum-x vertex and its actual H-contact point, so -b<=t<=a. The lower reach (2) gives

    t-c<=-b,
    t<=c-b<a,
    a-t>=1-c>0.                                     (7)

The actual tilted V frame is

    V=Q+[0,1]u+[0,1]v,
    Q=(x,a),
    u=(p,q),       v=(-q,p),
    p,q>0,       p^2+q^2=1,
    epsilon<=x<=epsilon+1.                           (8)

Unlike the high-radius kernel, this proof does not assume x>epsilon or that H's upper-left point is too close to O to belong to a boundary unit. The endpoint x=epsilon is retained.

Let n be the unchanged actual K-to-V separating unit normal and M its original common application or full side mean. Then

    M_y>=a,       M_x<epsilon<=x,
    n.(Q-M)>=0.                                     (9)

The strict horizontal inequality follows because K's only point with x=epsilon is P, whose height t is strictly below a by (7). This is an actual geometric statement about the whole support point, not a selection of a different mean.

We prove that

    n_x>0,       n_y>0.                              (10)

If n_x<0, the last inequality in (9) forces n_y<0. But both components of the actual center difference from K to V are strictly positive:

    (c_V)_x>=x-1/2>=epsilon-1/2>(c_K)_x,
    (c_V)_y>=a+1/2,
    (c_K)_y=t+(s-c)/2<=(c+s)/2-b,
    (c_V-c_K)_y>=3/2-(c+s)/2>0.                     (11)

An actual supporting normal has positive center gap, equal to the sum of the two positive support halfwidths. Both negative components of n would instead give a negative dot product with this center difference. Therefore n_x>=0.

If n_y<=0, then n.u_K<0. K's maximum-n support is on P+[0,1]v_K, whose height is at most t<a, contrary to (9). Hence n_y>0. If n_x=0, n is North and V's unique minimum-n point is Q, again contradicting M_x<x. This proves (10).

Now n.v_K<0 and n.u>0. The unchanged actual common point has the exact forms

    M=P+tau*u_K=Q+lambda*v,
    0<tau<=1,       0<lambda<=1,
    n_u:=n.u>0,       n_v:=n.v<=0.                   (12)

When n_v<0, lambda=1. When n_v=0, all possible actual side-interior means and its endpoint lambda=1 remain. The endpoint lambda=0 was excluded by M_x<x, not by a new normal convention. Likewise tau=1 remains. The proof does not impose that either mean is a midpoint.

Equating the actual coordinates in (12) gives

    x-epsilon=lambda*q-tau*c>=0,
    a-t=tau*s-lambda*p>=1-c.                        (13)

## 4. One strict elementary inequality controls both the frame and the far corner

The depth inequality in (13), tau>0, s<1 and c<=1 give

    lambda*p<=c+tau*s-1
                <c+tau-1
                <=tau*c.                            (14)

The final inequality is equivalent to (1-c)(1-tau)>=0. In particular (13)--(14) imply

    lambda*q>=tau*c>lambda*p,
    q>p.                                             (15)

They also give the stronger actual adjacent-corner bound

    x+p
      =epsilon+lambda*q-tau*c+p
      <epsilon+lambda*(q-p)+p
      <=epsilon+q<epsilon+1<1.                       (16)

The lower bound is x+p>=epsilon+p>epsilon>-1/15. Thus

    |x+p|<1,
    0<a+q<5/3.                                      (17)

These inequalities keep x=epsilon, tau=1, lambda=1 and every intermediate original side mean. They are exact whole-frame statements. No angle subdivision or curvature estimate is needed.

## 5. Full V2 force and torque select only a geometrically impossible circle corner

Let mu,nu>0 be the original HV and KV magnitudes. The true loaded V equation is

    F_V=2 sum_(Z on V) lambda_Z Z
       =mu*North+nu*n.

Its own components in the positively oriented frame u,v are

    F_u=mu*q+nu*n_u>0,
    F_v=mu*p+nu*n_v.                                 (18)

### 5.1. Every unique physical circle mask

A unique physical circle corner on V's minimum-u face would have u-coordinate less than -1/2. Its positive total circle coefficient would then give F_u<0, contradicting (18). The unique circle corner is therefore Q+u or Q+u+v.

For the opposite possibility Z=Q+u+v, the full original torque about Q, with the actual second point M=Q+lambda*v, yields

    0=F_v-F_u+lambda*nu*n_u
      =mu*(p-q)+nu*[n_v-(1-lambda)*n_u]<0,            (19)

using (12),(15). This contradiction uses the real two-force equation only at V. No equation at K or H, concurrence assertion, or boundary status for K has been introduced.

Thus a unique physical circle corner must be Q+u.

### 5.2. Every physical two-corner mask and zero coefficient

At R>=2, a contained boundary unit has either one physical circle corner or two adjacent physical circle corners. Equal farthest-corner norms in the latter case put its center on one of its own axes. Four physical circle corners would instead force R=1/sqrt(2).

The negative-u and negative-v pairs include Q, which is also in H. Two distinct contained packing units cannot share a containing-circle point: at such a point each contains a short inward radial segment in its open interior. Thus both of those physical masks are impossible regardless of the weights.

For the positive-v physical pair, write

    d_R=sqrt(R^2-1/4)-1>1/2.

Its exact lower vertex is Q=d_R*v-(1/2)u. Consequently

    Q_x=-d_R*q-p/2
           <-(p+q)/2<-1/2<epsilon,

contrary to (8). The only remaining two-corner mask is the positive-u pair, which includes Q+u.

Therefore, in every physical mask still possible after the genuine equations,

    Z=Q+u

is an actual circle corner, even if its individual coefficient is zero in the physical-two case.

But (17) puts it strictly inside radius two:

    |Z|^2=(x+p)^2+(a+q)^2
             <1+25/9=34/9<4<=R^2.                  (20)

The exact reserve 4-34/9 is 2/9. This contradiction proves the complete local theorem for every original mask and mean, at every R>=2.

## 6. Precise relation to the earlier high-radius kernel

The earlier ALIGNED_S_ROOT_COMMON_BOUNDARY_PAGES_HIGH_RADIUS_FAN_EXCLUSION.md, SHA256 e36fc1969d34b58813e07fc8a66266ba7ed6b7a15f25a63ffd084fed09609a91, proves a different closed high-radius theorem with epsilon>=0. Its circle-annulus entry excludes its parallel-K coincident upper port and then bounds a whole adjacent-circle expression by a continuous curvature argument.

The present theorem retains a strictly negative epsilon. Its parallel-K endpoint is removed by the exact full moment (5), rather than by an annulus estimate. Its tilted argument starts from the actual strict inequality M_x<epsilon, which remains true at x=epsilon. The stronger depth consequence (14) yields the direct corner box (17).

This is a separate new proof at a separate stated support-sign domain. It does not alter the frozen high-radius source, transfer its hypotheses to a low radius, or include epsilon=0 by continuity. The high-radius source covers that critical endpoint in the original fan application.

## 7. The full low-height physical screen at its closed zero endpoint

For the literal genuine-S caller in Section 8, use only the complete physical top-contact theorem in Sections 1--5 of C6_NEXT_INTACT_ROOT_GENUINE_CYCLE_ALIGNED_S_LEAF_EXCLUSION.md. Its printed domain is

    2<=R<=sqrt(17)/2,
    d_R=sqrt(R^2-1/4)-1,
    0<h<=1/3,
    H=[d_R-1,d_R] times [h-1,h],
    L=[d_R,d_R+1] times [-1/2,1/2].

Every other actual unit above y=h that touches H's top side is strictly inside D_R. This physical theorem has no force or degree premise at H or that unit. Its later intact-root five-force and cycle arguments are not used.

The same fully printed physical inequalities cover h=0 as well. Here is the exact closed-endpoint check, so no force or physical-pose continuity is assumed. Put Delta=1/2-h. The endpoint has Delta=1/2; the real-leaf crossing cover still consists of

    t<Delta: x<=d_R-r,
    t>=Delta: x<=d_R-Delta*r/t,

for the actual two inward axes (r,t),(-t,r), r,t>0. The horizontal-side case only changes its nonnegative minimum height from h>0 to h=0; its norm upper bound remains 656/225<4. The first three vertex bounds in that source's Section 4 use only 0<=h<=1/3, and their strict comparisons remain unchanged.

For the last corner, the lower-x endpoint bound remains 26/225<(7/20)^2. In the t<Delta branch its upper-endpoint coordinates have 0<d_R-t<=1 and

    h+r+t<1+h+Delta=3/2,

exactly as before. In the t>=Delta branch, all uses of Delta are weak inequalities Delta<=t, Delta>=1/6, Delta<=1/2. The squared-coordinate comparison to Delta=1/6 is unchanged. Its entire Section 5 polynomial proof depends only on the closed comparison range 1/6<=t<=1, with all four strictly positive exact interval identities retained.

Thus all four actual corners are still strictly inside D_R at h=0. This establishes precisely the needed closed physical export

    0<=h<=1/3.                                      (21)

No new Bernstein coefficients or numerical certificate are introduced, and no later root equation is carried to an endpoint.

## 8. Entire original low-radius North/West/South common-page interface

Return to actual units H,L,K,V,W in the same selected certificate. Suppose L is a genuine S leaf at an aligned H, both V,W are physical boundary neighbors of H, and both physically touch K by their original positive edges. Assume the actual original support interface, after possibly reflecting the whole chart, is

    n_HK=West,
    n_HV=North,
    n_HW=South,

with V of true loaded degree two and entire neighborhood H,K. All actual forces at H,K,W remain; no degree bound there is required for this interface theorem.

Take the strict low radius range

    2<=R<sqrt(17)/2.

The actual unchanged leaf and root have

    L=[d_R,d_R+1] times [-1/2,1/2],
    H=[epsilon,epsilon+1] times [-b,a],
    epsilon=d_R-1,
    a+b=1,       0<=a,b<=1.

The radius gives

    -1/15<epsilon<0.

If a<=1/3, the complete closed physical export (21) excludes the actual upper boundary V directly. If b<=1/3, its reflection excludes the actual lower boundary W. Thus every possible configuration in this entire interface must have

    1/3<a,b<2/3.                                    (22)

K lies to the left of H by its actual West support. Its actual contact with W, which lies below y=-b, proves min_K y<=-b. Every premise of the new local theorem is now literal, and it excludes V.

This proves the entire low-radius North/West/South common-page interface, including all original root sliders before (22), all parallel and tilted return units, all physical masks and zero coefficients, and all actual side means. The two extreme slider endpoints a=0 or b=0 are covered by (21). The critical radius R=sqrt(17)/2 is not assigned negative epsilon; it belongs to the separate high-radius theorem.

### 8.1. Literal fan-inner 134.S mapping

Use the exact original edges

    J1, J2, J3, J4, 12, 23, 34, 2L,

with block loads 1,3,4 and genuine S leaf at root 2. Put

    H=2, K=J, {V,W}={1,3},

reflecting the whole frame so the true loaded degree-two page 1 is V above H when this original normal interface occurs. The original J1 and J3 edges give both actual K/page contacts. The true degrees remain

    deg(2)=deg(J)=4, deg(3)=3,
    deg(1)=deg(4)=2, deg(L)=1.

All J4 and 34 forces and the three other actual squares remain. Only the genuine V2 equation at body 1 is used by the kernel. The whole low-radius aligned North/West/South feature of M6.B5L.FAN.INNER.L134.S is therefore excluded.

The separately accepted high-radius theorem excludes all high-radius aligned fan features, and the separately accepted tilted theorem excludes every strictly tilted fan root. This manuscript does not declare the remaining low-radius strict-Northwest/Southwest page features impossible. Their actual force and physical contact domains remain.

### 8.2. Other exact callers

The local theorem may be applied whenever an actual left common neighbor has the full lower reach (2), independently of its degree or load. A house-hub caller must prove that reach from its actual original geometry. The house TCB graph has no BD edge, so its southern root neighbor does not automatically provide a contact with D. No such missing edge, physical return or degree reduction is inserted here.

## 9. Complete operative inputs and exact scope

| Source | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full actual V2 force and torque, physical support normals, and unchanged aggregate means. The local proof makes no new normal selection. |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Only its force-free fact that distinct contained squares cannot share a containing-circle point. No planar or root-degree conclusion is used in the new local kernel. |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Only the literal genuine aligned S-leaf and root chart in Section 8. |
| C6_NEXT_INTACT_ROOT_GENUINE_CYCLE_ALIGNED_S_LEAF_EXCLUSION.md | 6a1a37c6ed825ef1cea0bebf503e894e3ca9d4777fe23e3cf508b188e4898aa5 | Complete force-free Sections 1--5 top-contact screen only; Section 7 here explicitly checks its closed h=0 extension. None of that source's intact-root degree-five or genuine-cycle conclusions is imported. |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal fan-inner 134 graph, loads, all true degrees, and retained leaf/extras; the explicit missing house BD edge distinction. |

The local proof in Sections 1--5 is fully printed and has no upper radius bound. The physical low-height source is used only in the separate actual-leaf caller. The high-radius and tilted companions are mentioned solely to state the live original scope and are not mathematical inputs to this local proof.

The new negative-support endpoint moment, actual strict M_x inequality, uniform depth estimate (14), full physical-mask cover, closed low-height export and literal original join require their own complete independent review. No original fine row or parent graph is credited before that review or by this partial family join.

No numerical pose, sampled orientation, new computational geometric certificate, moved unit, dropped force, changed normal or mean, Lean compilation, CI, merge, remote action or ledger edit was used.

