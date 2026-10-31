# A B-owned lower-root chart has no vertical return with K-owned central contact

Date: October 27, 2026.  
Author: topology_final.  
Original comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

**Status: complete new analytic candidate on the explicit entire lower-root chart, pending full independent review.** This manuscript covers both physical types of vertical BK, both genuine H leaves, every HC direction and physical type, every CK owner and actual mean, and the aligned height endpoint. It uses no K2 equation, no H3 equation, no chosen shared mean, and no computational packet.

The file is freshly saved after the workspace rollback. It is not a claimed exact restoration of a missing earlier source. The new local proof is complete under the explicit chart in Section 1. Its join from the original graph still needs recovery, or a separately reviewed replacement, of the missing earlier lower-root and physical-C-mask artifacts listed in Section 16.

## 1. Entire original chart and precise theorem

Retain the original nine-unit S/S hub-tip graph

    HK, HB, BK, HC, CK, HL_H, BL_B,

with true H4/K3/B3/C2, two distinct occupied genuine radial S leaves, positive K and C circle loads, all original positive pair forces, actual selected normals, actual singleton applications, all physical shared-side means and their endpoints, and the three other physical units. No body, force, or mask is deleted. The containing-circle origin is unchanged.

The whole earlier B-owned lower-root normal form supplies the following explicit chart. The theorem below may also be read directly as a local theorem with all these stated premises, without pretending that the missing original artifact has been restored:

\[
 \begin{gathered}
 d=1+\delta,\quad 0<\delta<1/60,\quad
 R^2=(d+1)^2+1/4,\quad 17/4<R^2\le1105/256,\quad R<25/12,\\
 B=[h_B,h_B+1]\times[-b,1-b],\quad
 p_B=(1+h_B,-b),\quad(1+h_B)^2+b^2=d^2,\\
 |h_B|\le\delta,\quad0<b<31/120,\quad
 P=P_{HB}=(h_B,-t),\quad0<t<b,\quad\sigma=t/b\in(0,1),\\
 u=(-\alpha,\beta),\quad v=(-\beta,-\alpha),\quad
 \alpha,\beta>0,\quad\alpha^2+\beta^2=1,\quad
 H=P+[0,1]u+[0,1]v.
 \end{gathered}
 \tag{1}
\]

HB is the actual singleton owned only by B. Its H-to-B normal is E_1, P is the strict rightmost H vertex and a relative-interior B-side point. The genuine B leaf has the displayed actual radial application p_B. The whole central normal form makes HK a physical singleton between distinct H/K side frames. The earlier whole C-mask theorem makes C physically unique, with its actual positive circle load. K only needs to be physically circle-touching here; no uniqueness of its mask is used in the new proof.

Define the actual H-frame scalars

\[
 x=P\cdot v=-\beta h_B+\alpha t,\qquad
 A=-P\cdot u=\alpha h_B+\beta t,\qquad X=1+x.
 \tag{2}
\]

The full genuine H leaf cover is exactly

| Actual H leaf | Its unchanged radial data |
|---|---|
| Vertex | \(p_H=P+v=Xv-Au\), \(X^2+A^2=d^2\), \(A>0\) |
| Aligned | actual direction v and actual radial mean \(dv\), \(x=\delta\), \(0\le A<31/120\) |

The original root strip gives x<=delta. The vertex row has A<31/120 as well; all its actual poses remain. No vertex identity is imposed on the aligned row.

Assume the actual BK normal from B to K is E_2. This is the entire vertical BK feature. The physical selected convention makes it B-owned, either singleton or shared with its full real mean. Assume K alone owns the actual HK singleton. C has the original true positive pair degree two and the physical boundary neighbor K, with the unchanged force and moment laws.

**Theorem 1.1.** This entire explicit feature is impossible.

The proof below preserves the original H4/K3/B3/C2 equations. It uses H4 only at the genuine aligned A=0 endpoint, B3 to identify the actual vertical BK mean, and the true C2 at the page. The arbitrary K3 is never replaced by a smaller force law.

## 2. Both real leaves put the reflected root strictly to the left

The two actual radii in the vertex row give the exact identity

\[
 2(1+\beta)h_B=2\alpha t+t^2-b^2,
\]

and consequently

\[
 (1+\beta)x=\alpha t+\frac\beta2(b^2-t^2)>0.
 \tag{3}
\]

For the aligned row x=delta>0 directly. Thus, before any further central or page split,

\[
 0<x\le\delta<1/60,\quad 0\le A<31/120,
 \quad G=1-A\in(89/120,1].
 \tag{4}
\]

Use only the origin-preserving orthogonal map

\[
 F(q)=(-v\cdot q,\ u\cdot q).
\]

In these reflected H coordinates put h=-x. Then

\[
 H=[h-1,h]\times[-A,G],\quad
 P=(h,-A),\quad W=P+u=(h,G),\quad -1/60<h<0.
 \tag{5}
\]

The actual H leaf is (-X,-A) in the vertex row, and (-d,0) in the aligned row. The actual H-to-B normal becomes (beta,-alpha). The actual vertical B-to-K normal becomes (alpha,beta). This is a change of orthonormal axes, not a translation of the disk or any change in force applications.

## 3. The full actual vertical BK mean and central geometry

Write the actual positive HB and BK magnitudes as mu and nu_B. In the original global B frame, the complete B3 equation with the genuine radial B leaf gives

\[
 \nu_B=\frac{\mu b}{1+h_B}.
\]

Its origin moment, at the actual HB point (h_B,-t) and the actual BK point Q=(q,1-b), gives

\[
 \nu_B q=\mu t,\qquad
 q=\sigma(1+h_B).
 \tag{6}
\]

This is the unchanged actual mean if BK is shared. Its physical membership in B gives h_B<=q<=h_B+1. Put

\[
 a_Q=q-h_B=\sigma-h_B(1-\sigma),\qquad
 D_B=1-b+t.
 \tag{7}
\]

Then 0<=a_Q<1 and 0<D_B<1. All K points have original global height at least 1-b>89/120 because BK is vertical and physically separating.

K ownership of HK and distinct H/K frames make its actual application a strict H vertex. The vertices P and P+v have negative global height, so K cannot contain them. The opposite vertex P+u+v cannot be the HK application either. Its strict H outward normal has positive u and v components. The B-to-H normal is -E_1=alpha*u+beta*v. The complete support-span lemma at the K contact then gives

\[
 \min_K(-E_1)\cdot z>
 (-E_1)\cdot(P+u+v)-1
 =(-E_1)\cdot P+\alpha+\beta-1
 >\max_B(-E_1)\cdot z.
 \tag{8}
\]

This contradicts physical BK. The actual central application is therefore exactly W=P+u. Its normal is strict in the corresponding H vertex cone, so its original global height component is positive.

### 3.1. Singleton BK

The actual Q is a strict minimum-height vertex of K. In the original global B axes write its whole physical frame as

\[
 e=(-c_0,s_0),\quad f=(s_0,c_0),\quad
 c_0,s_0>0,\quad c_0^2+s_0^2=1,
 \quad K=Q+[0,1]e+[0,1]f.
 \tag{9}
\]

The positive global height of the HK normal leaves only e or f as its K-owned axis. It cannot be e: K's whole minimum-e side has x-coordinate at least q>=h_B, while W_x=h_B-alpha<h_B. Thus its actual normal is f and

\[
 W=Q+\ell e,\quad0<\ell<1,\qquad
 \ell c_0=\alpha+a_Q,
 \quad\ell s_0=b-t-(1-\beta)>0.
 \tag{10}
\]

After the orthogonal map (5), this is

\[
 m=(-c,s),\quad n_K=(s,c),\quad c,s>0,\quad c^2+s^2=1,
 \quad K=W+[-\ell,1-\ell]m+[0,1]n_K,
 \tag{11}
\]

where

\[
 c=\beta c_0-\alpha s_0>0,
 \quad s=\alpha c_0+\beta s_0>0,
 \quad Q=W-\ell m.
 \tag{12}
\]

Strict positivity of c is the actual H support sign at W. The central force normal remains n_K.

### 3.2. Shared BK, with its entire actual mean

K has the actual B frame, with bottom side at height 1-b. A K-owned central axis with positive global height can only be E_2. Thus W is a relative-interior point of that same actual K bottom side. In the reflected chart (11) now has

\[
 c=\beta,\quad s=\alpha,\quad0<\ell<1.
 \tag{13}
\]

The actual mean Q and W obey

\[
 Q=W-rm,\qquad r=a_Q+\alpha>0,
 \qquad0<r\le\ell<1.
 \tag{14}
\]

Both Q and W lie on the same physical K side; this proves the non-strict r<=ell endpoint without fixing Q. The exact vertical relation b-t=1-beta is retained when needed, although no later bound requires substituting a chosen mean.

In both physical BK types the entire actual central chart is (11), with an actual Q=W-rm and 0<r<=ell<1. The singleton has r=ell. K remains arbitrary in force degree and circle mask.

## 4. Positive physical circle heights on the whole K-C page

K contains the actual point W=(h,G), |h|<1/60 and G>0. If a physical K circle corner z had z_y<=0, then

\[
 |z-W|^2\ge(R-|h|)^2+G^2>
 (2-1/60)^2>2,
\]

contradicting the unit-square diameter. Every physical K circle corner therefore has positive reflected height.

Use only physical Sections 1--2 of the complete original connected-boundary-neighbor theorem. H has its genuine occupied radial S leaf. K and C are physical boundary neighbors of H, different from that leaf, joined by the actual CK edge. Their physical circle corners all lie on one common strict side of the real H leaf line, and each has angular distance greater than pi/9 from the genuine leaf center direction. The later global load-balance theorem is not applied: the separate genuine B leaf and every original load remain.

For the aligned H leaf, whose reflected direction is west, the positive K circle height fixes that common side and immediately gives positive C circle height.

For the vertex H leaf use the actual perpendicular functional

\[
 \Phi(z)=-A z_x+X z_y,
 \quad X^2+A^2=d^2,
 \quad X>1.
\]

If a K circle corner with positive height had Phi<=0, its horizontal coordinate would be positive and satisfy

\[
 z_x\ge RX/d>120/61>\sqrt2.
\]

The same K contains W with negative horizontal coordinate h. Their actual distance would exceed sqrt(2), impossible. Thus Phi is positive on the whole K mask and therefore on the whole connected C mask. A C circle point of nonpositive height with Phi>0 would lie strictly between the west axis and the real southwest H leaf direction. Its angular distance from that leaf would be at most

\[
 \arctan(A/X)<\arctan(31/120)
 <\arctan(4/15)<\pi/12<\pi/9,
\]

contradicting the same physical corner separation. The exact tangent comparison uses (26/15)^2-3=1/225>0.

Both genuine leaf rows consequently give positive physical C circle height. Its actual unique loaded C2 concurrence is a positive radial point, so it too has positive height. If the actual H-to-C normal had negative height, its H application would lie on the bottom side at height -A<=0; its entire proper incoming ray would then have nonpositive height. Hence

\[
                         (n_{HC})_y\ge0.
 \tag{15}
\]

Only the genuine C2 law has been used. No concurrence is assigned to H4 or K3.

## 5. The entire actual HC direction cover

The two negative or positive horizontal axes are H-owned directions under the original selected-contact convention. The negative axis is impossible: H owns it in the physical H-K-C triangle, while its dot product with the actual central normal n_K=(s,c) is -s<0.

The positive horizontal axis is impossible by an actual occupied triangle. The three points P=(h,-A), W=(h,G), Q=W-rm are actual applications. Their segments P-W, W-Q and Q-P lie respectively in H, K and B. The triangle has vertical base length one and horizontal width rc<1, hence area rc/2<1/2. Any positive-length shared HC on H's right side contains a relative-interior point of P-W; a singleton H-owned contact is already such a point. C lies to the right of that side, so its open interior locally enters the triangle. Its open interior cannot cross any segment of the triangle boundary, since every boundary point belongs to H, B or K and entering an open neighborhood of such a point would overlap that physical square. The connected open interior of C must lie entirely inside the triangle. A unit square cannot fit in area less than one. This contradiction keeps the actual shared BK mean Q, including its physical side endpoint.

A strictly northeast HC normal would apply at W. No third unit can contain W: at this actual K-owned singleton, K has a half-plane tangent sector and H has a right-angle tangent sector strictly inside its opposite half-plane. The two remaining tangent gaps each have angle strictly less than pi/2. The tangent sector of any unit containing W has angle at least pi/2. This is a local physical exclusion, independent of an absent application-separation artifact.

Together with (15), the only remaining actual HC features are

* the H-owned top normal E_2, with either physical HC type and its actual mean;
* a strictly northwest normal at the opposite upper H vertex F=(h-1,G).

No perimeter or central normal is reselected in this cover.

## 6. The whole top HC page, including A=0

First take the genuine aligned endpoint A=0, G=1. The real H leaf force is horizontal west and has zero origin moment. Let mu>0 be HB's magnitude, tau_K>0 the actual HK magnitude, and omega>0 the actual HC magnitude. If HC is the top page, write its unchanged mean as T=(xi,1), xi<=h<0. The full H4 height and origin moment equations are

\[
 -\mu\alpha+\tau_K c+\omega=0,
 \qquad
 -\mu\alpha h+\tau_K(hc-s)+\omega\xi=0.
 \tag{16}
\]

Eliminating only the first displayed term yields

\[
                   -\tau_K s+\omega(\xi-h)=0.
\]

Its left side is strictly negative because s>0 and xi<=h. This excludes the entire top page at that aligned endpoint, with every original mean and all four H forces kept.

For A>0, G<1. Apply the complete accepted high-corner top-page theorem to the actual chart (11), with

\[
 R_0=W,\quad U=n_K,\quad V=-m,
 \quad a_0=1-\ell\in(0,1),\quad N=n_K.
 \tag{17}
\]

Then K=W+[0,1]U+[-a_0,1-a_0]V, N dot U=1 and N dot V=0. All height and h premises hold by (4)--(5); the actual unique loaded true-C2 and physical boundary K premises are unchanged. That complete theorem covers both HC physical types, all shared means and all actual CK owners. Its fixed-singleton selection is the same original common certificate. Thus the whole top HC page is excluded for A>0 as well.

The exact source is `HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md` at 580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b, with its full separate acceptance at 4b39a8e97f4714a8cb37f91665edb3e3069d2a0ecde9d0b0f19c884f362daa14. This is a whole local theorem, not a sampled angle restriction.

## 7. The entire opposite-upper HC owner cover

The remaining northwest HC is a singleton at F=(h-1,G)=(-X,G). It cannot be H-owned because its normal is strictly oblique to H's frame.

If CK is singleton too, the two actual C applications are distinct. Otherwise the exact genuine C2 coincident-star calculation leaves the radial-D inner vertex. Since K is a physical boundary neighbor, equality in the unit diameter bound would force its circle point to be the same containing-circle point as C's, impossible. The original compatible fixed-singleton selector therefore gives actual owners for both contacts. HC can only be C-owned.

If CK is physically shared, HC can be C-owned or free. In the free alternative its actual point F is a vertex of C, and its actual normal is strict in both vertex cones. The complete accepted `HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md` applies directly to (11), h<0, 89/120<G<=1, and the original unique loaded C2. It covers all four shared translations, the full free normal and every actual CK mean, and needs no K force equation or unique K mask. It therefore excludes the entire free-HC/shared-CK feature.

The only remaining branch is C-owned HC. Its entire analysis below permits either initial CK type and every original CK mean.

## 8. Signed C coordinates and one whole circle budget for both H leaves

Write the actual C-owned incoming side frame and actual HC position as

\[
 n=(-u_0,v_0),\quad w=(v_0,u_0),\quad
 u_0,v_0>0,\quad u_0^2+v_0^2=1,
 \quad C=F+[0,1]n+[-\lambda,1-\lambda]w,
 \quad0<\lambda<1.
 \tag{18}
\]

Keep the initially signed coordinate

\[
 a=F\cdot n=Xu_0+Gv_0>0,
 \qquad B_0=-F\cdot w=Xv_0-Gu_0.
\]

The true C2 proper ray is q_C=F+ell_C*n=r_C*z_C in C, r_C>0. Physical uniqueness makes B_0 nonzero and fixes the sign of the circle's transverse coordinate. If B_0<0, then

\[
 a-X=v_0[G-Xv_0/(1+u_0)]>0.
\]

The actual point F+n belongs to C. Put E_H=0 in the vertex H row and E_H=A^2 in the aligned H row, so

\[
 X^2+A^2=d^2+E_H.
 \tag{19}
\]

Its squared-radius excess is exactly

\[
 |F+n|^2-R^2=E_H+3/4-2A+2(a-d)>1/6.
 \tag{20}
\]

Here X>1, d-X<1/60, A<31/120 and a>X; even the weaker original d-X<1/30 gives the displayed strict reserve. This contradicts containment. Thus B_0>0 and the actual unique C circle is

\[
 z_C=F+n-\lambda w,
 \quad z_C\cdot n=a+1,
 \quad z_C\cdot w=-B_0-\lambda,
 \quad a<d<61/60.
 \tag{21}
\]

The complete uniform estimates are

\[
 B_0>83/120,\quad u_0<1/3,\quad v_0>14/15,
 \quad a-G>(4/5)u_0.
 \tag{22}
\]

Indeed B_0^2=d^2+E_H+1-2A-a^2>1-2A>29/60>(83/120)^2. The function a(u)=Xu+Gsqrt(1-u^2) increases up to the actual u because its derivative has the sign of B_0. At u=1/3 its value exceeds 1/3+(89/120)(14/15)=923/900>61/60. This proves u_0<1/3. Finally

\[
 a-G=u_0[X-G u_0/(1+v_0)]>(24/29)u_0>(4/5)u_0.
\]

The actual circle equation gives the exact two-row budget

\[
 \lambda^2+2B_0\lambda+2(a-G)
       =2d-11/4+4A-E_H
       <4A-43/60<19/60.
 \tag{23}
\]

It follows, on the whole actual branch, that

\[
 A>43/240,\quad \lambda<1/5,\quad
 u_0<(5/2)(A-43/240)<19/96<1/5,
 \quad v_0>49/50.
 \tag{24}
\]

For lambda use `(1/5)^2+(83/60)(1/5)=19/60`. For v_0 the exact squared reserve is `1-(19/96)^2-(49/50)^2=2471/5760000>0`. The aligned branch's extra negative term -A^2 in (23) is kept; it is only relaxed in the displayed strict upper bound. Thus A=0 is already impossible in this page, independent of the top-page endpoint argument.

## 9. Both actual root leaves force alpha<1/10

This consequence is independent of BK's physical type or any central angle. The exact inverse H/B-frame identities are

\[
 h_B=-\beta x+\alpha A,
 \qquad t=\alpha x+\beta A,
 \qquad h_B^2+t^2=x^2+A^2.
 \tag{25}
\]

Since b>t, the actual B radius and (19) give

\[
 d^2=(1+h_B)^2+b^2>
 1-2\beta x+2\alpha A+x^2+A^2,
\]

and comparison with `d^2=(1+x)^2+A^2-E_H` yields

\[
 \alpha A<(1+\beta)x-E_H/2\le2\delta<1/30.
 \tag{26}
\]

Together with A>43/240 this already gives alpha<8/43<1/5 and beta>4/5>delta. The function `x^2-2beta*x` is therefore decreasing on the entire actual interval 0<x<=delta. Substitute its lower endpoint value at x=delta in the preceding necessary B-radius inequality to obtain

\[
 A^2+2\alpha A<2\delta(1+\beta)<1/15.
 \tag{27}
\]

The function `1/(30A)-A/2` is strictly decreasing for A>0. Hence

\[
 \alpha<\frac1{30A}-\frac A2
 <\frac8{43}-\frac{43}{480}
 =\frac{1991}{20640}<\frac1{10},
 \qquad\beta>99/100.
 \tag{28}
\]

Both genuine H leaves were retained through E_H, and the genuine B leaf was used only through its original radius and original b>t. No fictitious H vertex or root concurrence was introduced.

The same actual data now give

\[
 \sigma=\frac tb>
 \frac{(99/100)(43/240)}{31/120}
 =\frac{4257}{6200},\quad
 a_Q>\frac{4257}{6200}-\frac1{60}>\frac23,
 \quad b-t<\frac{1943}{24000}<\frac1{12}.
 \tag{29}
\]

The exact margins for the last two comparisons are 61/18600 and 19/8000. They hold for the unchanged vertical BK mean, even before its singleton/shared type is specified.

## 10. The entire vertical K central frame is almost upright

For singleton BK use precisely the actual two components in (10). Equation (29) gives

\[
 \ell c_0=\alpha+a_Q>2/3,
 \quad0<\ell s_0=b-t-(1-\beta)<1/12.
\]

Thus s_0/c_0<1/8, so c_0>sqrt(64/65)>99/100 and s_0<1/8. Substituting the unchanged reflected frame (12) yields

\[
 \begin{split}
 c&> (99/100)^2-(1/10)(1/8)
      =2419/2500>24/25,\\
 s&<1/10+1/8=9/40.
 \end{split}
 \tag{30}
\]

For shared BK, (13) gives the stronger c=beta>99/100 and s=alpha<1/10. Therefore the same whole bounds (30) hold for both actual physical types, including the full shared mean.

Relative to the actual C frame put

\[
 D=v_0c-u_0s=n\cdot n_K,\qquad
 J=v_0s+u_0c=n\cdot m,
 \qquad D^2+J^2=1.
 \tag{31}
\]

All divided quantities below are strictly positive. From (24) and (30),

\[
 D>(49/50)(24/25)-(1/5)(9/40)
       =4479/5000>17/20,
 \quad0<J<s+u_0<17/40,
 \quad\boxed{J/D<1/2}.
 \tag{32}
\]

No K circle corner has been chosen or identified to obtain this bound. In particular the proof allows the physical K circle to lie on either side of its central transverse coordinate, which is necessary in this vertical-return feature.

## 11. Every K-owned CK is impossible

If CK is singleton, its actual C application differs from HC. Coincidence is impossible already at the relative-interior C-owned HC side with the genuine nonparallel C2 proper ray. The existing compatible fixed-point selection therefore gives a side owner. If CK is shared, it is also C-owned and is covered in the next section without applying a selector to its mean.

Suppose K alone owns CK, and write its actual C-to-K normal as r. The H-K-C triangle at the K-owned central side gives r dot n_K>=0. The K-axis cover is exactly m,-m,n_K. At C, its owned CH axis is -n, so the same physical triangle rule gives r dot n<=0. Since J>0 and D>0 in (31)--(32), this excludes m and n_K, leaving only

\[
                         r=-m.
\]

Its actual C support is the minimum-n, maximum-w corner

\[
 Z=F+(1-\lambda)w.
\]

The genuine incoming proper coefficient and radial coefficient are

\[
 \ell_C=\frac{B_0-a\lambda}{B_0+\lambda},
 \qquad r_C=\frac{B_0}{B_0+\lambda}.
 \tag{33}
\]

The unchanged proper outgoing ray in direction `-m=-J*n+D*w` gives

\[
 \ell_C=(1-\lambda)J/D,
 \quad B_0=a\lambda+(1-\lambda)(J/D)(B_0+\lambda).
 \tag{34}
\]

Using the whole bound J/D<1/2, lambda<1/5 and a<61/60,

\[
 B_0<a\lambda+\tfrac12(B_0+\lambda),
 \quad B_0<(2a+1)\lambda<91/150<83/120.
 \tag{35}
\]

This contradicts (22), with exact final gap 17/200. The complete original K side interval and all positive magnitudes were retained; no K force equation was needed.

## 12. Every C-owned CK and shared CK is impossible

Let omega,gamma>0 be the actual HC,CK magnitudes. The complete C2 force is

\[
 \kappa_C z_C=\omega n-\gamma r.
 \tag{36}
\]

Its w projection, using (21), gives r dot w>0. If C owns CK, its only compatible side axis is therefore r=w. This includes every possible positive shared CK.

Now w dot m=-D<0 and w dot n_K=J>0. Thus K's actual minimum-w support is the single actual vertex

\[
 Z=W+z m,\qquad z=1-\ell\in(0,1).
\]

It cannot support a shared segment, so any physically shared CK has already failed this consequence. Retain the unchanged actual C-side position, relaxing its strict singleton endpoints only outward:

\[
 Z=F+(1-\lambda)w+\rho n,\qquad0\le\rho\le1.
\]

Projection of the same actual point gives exactly

\[
 1-\lambda=v_0-zD,
 \quad\rho=zJ-u_0,
 \quad zD=\lambda-(1-v_0)<\lambda.
 \tag{37}
\]

Consequently, with all actual means fixed,

\[
 \rho<zJ<\lambda J/D<\lambda/2<1/10.
 \tag{38}
\]

The proper outgoing line is parallel to w, so its actual n coordinate is the actual rho: ell_C=rho. Equation (33) therefore gives

\[
 B_0=a\lambda+\rho(B_0+\lambda)
 <a\lambda+\tfrac1{10}(B_0+\lambda).
\]

It follows that

\[
 (9/10)B_0<(a+1/10)\lambda<67/300,
 \quad B_0<67/270<83/120,
 \tag{39}
\]

with exact final gap 479/1080. This contradicts (22) and excludes the entire C-owned CK feature. A negative geometric rho would already contradict physical membership; no such value is silently admitted as a replacement mean.

## 13. Exhaustive feature conclusion

The entire vertical BK cover consists of its strict singleton vertex or its full shared side. Section 3 derived the same actual central H vertex and the whole K-owned central chart for both. It did not assume a K mask or remove a K force.

The physical connected-page sign and actual H/K/B triangle leave only the top HC page or the opposite-upper northwest page. Section 6 excludes both physical top-page types at every genuine H height, with the real A=0 aligned endpoint treated by full H4. Section 7 excludes every free HC/shared-CK far-page feature using the complete accepted local helper. Sections 8--12 exclude all remaining C-owned HC, every CK owner and both initial CK physical types in one uniform analytic angle and true-C2 argument.

This proves Theorem 1.1 on the entire explicit chart. Both real H leaf equations and the actual B leaf were used at their stated scopes. Every original mean, mask, positive weight, true degree, physical extra and upper-radius endpoint is retained. There is no new computational certificate.

This is the vertical-BK/K-owned-HK feature of the B-owned HB domain. It does not relabel a continuous subfeature as a separate original gate. An original whole-owner or full hub-tip assembly must still recover and pin its complete earlier prerequisites and the independent acceptance of this new source.

## 14. Required independent review and algebra boundary

The independent reader must check the whole original chart, both actual BK physical forms, the origin-preserving reflection and its true side offset, all HC directions, the physical occupied-triangle argument, the genuine A=0 H4 endpoint, the entire shared-free far-page transfer, the signed C circle derivation, both H-leaf terms E_H, the complete B/H radius monotonicity, every actual side projection and both true-C2 owner contradictions.

The proof is analytic on whole intervals. Exact identity and rational checks accompanying review are validation of the displayed mathematics, not interval boxes, pose samples or a computational packet. No Lean compilation, build, CI, ledger, or remote edit is part of this source.

The separate author record `check_b_owned_vertical_return_identities.py`, SHA256 d7dead5b7622a8eed64958e19456b94edb3597ef0aaebd35c2145777372f9bcd, verifies twenty-nine complete polynomial or coordinate identities and thirty-eight exact rational values or reserves using only sparse polynomials and Fraction arithmetic. These include the two genuine root radii, the actual reflection, the full A=0 H4 cancellation, the signed C coordinates, both E_H budgets, the actual proper-ray and support projections, and every final scalar gap. All ten present source pins and both complete local review pins below were checked separately. This author validation does not replace the required full independent original-domain review.

## 15. Present exact complete sources and accepted local transfers

These present sources supply all geometric lemmas and new local transfers used after the explicit chart (1)--(2):

| Complete source | SHA256 | Exact scope |
|---|---|---|
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Strict singleton convention; original full H4/B3/C2/K3 forces and actual means |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Whole physical support-span lemma and every actual triangle owner sign |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Genuine unique loaded true-C2 proper ray with physical boundary neighbor K |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing selector only for distinct fixed actual singleton applications; no variable-mean choice |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Physical unique-circle own coordinates and impossibility of a shared circle point |
| S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md | 70a3488bb613b1ce1cb4ac778d6f2b2acb2e04bae226741a0665378d096e28ec | Only physical Sections 1--2: common page side and circle-corner angular separation; its later global force theorem is not used |
| SS_HUB_TIP_CENTRAL_SINGLETON_DISTINCT_FRAME_NORMAL_FORM.md | 89ff6eee18061f7ef57fea5acd8da87ce42ff3c24185d478da113c181e77fae0 | Whole actual central singleton and distinct H/K frames, as stated in the original chart |
| HIGH_CORNER_CENTRAL_TOP_PAGE_EXCLUSION.md | 580c065de7812c889f91d0e06e7319a3126134b31b8bd31c2044960b7819083b | Complete top page at A>0, with actual a_0=1-ell and all means retained |
| HIGH_CORNER_FREE_OPPOSITE_PAGE_SHARED_RETURN_EXCLUSION.md | 7df434664a33019260a1b5b41983989a536f223edca4702cfed9a91786bb4f9e | Entire actual free far-HC/shared-CK feature, including G=1 and arbitrary K degree/mask |
| FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md | a33b15a4a3e7894c256ee1877edfb47f6241fd208558765267113e56e12a1b4e | Complete original graph, positive loads, true degrees and all nine physical units |

The complete separate local acceptance of the top-page source is `REVIEW_HIGH_CORNER_CENTRAL_TOP_PAGE_CERT_INDEPENDENT_2026_10_27.md`, SHA256 4b39a8e97f4714a8cb37f91665edb3e3069d2a0ecde9d0b0f19c884f362daa14. The complete separate local acceptance of the free-opposite/shared-return helper is `REVIEW_HIGH_CORNER_FREE_OPPOSITE_SHARED_RETURN_ROOTED_INDEPENDENT_2026_10_27.md`, SHA256 e0096519f88fcd14f664fef5b493d8bd689c885faf1cbc5e503bcfd8f5d71e2f. Both complete sources and reviews were read and their present bytes verified. Neither prior review substitutes for the full independent review of the current whole vertical feature.

## 16. Original caller and missing-artifact boundary

The missing original lower-root source is `SS_HUB_TIP_B_OWNED_SINGLETON_LOWER_H_LEAF_NORMAL_FORM.md`, preserved SHA256 3ad155e266b71e0c2e91ca67be9328a04e204ede77289a375fbd01c77f48653f, with its earlier full acceptance at 88e86b3a87562aa6f44d2e4453bc8e10dc18fedfaedd24b8b64c0f14c6c8572d. Its precise needed contract is stated in full in (1)--(2), the genuine two-row table, the strict selected central convention, and the original C-mask premise.

The earlier whole singleton positive-tip source at d563e080a5d3d8fb42f2e47fc4e646fb935285ff6d5d8b2a72e8f62c307c8229, and the whole C physical-uniqueness source at 2bf0e377d1c17d28c7e49742b418ea6a60a8b9fbe7dad56249e73cf0e96a8d9b, are also not declared restored merely from their remembered hashes. Their complete original joins remain publication obligations. The exact x>0 consequence needed here has been reproduced in Section 2 rather than imported from a missing later caller. The exact actual HK/HC separation needed here has been proved physically in Section 5, without invoking a missing separation file.

The complete new geometric and force proof under the explicit premises is written above. Original assembly must distinguish its mathematical acceptance from recovery of every earlier artifact. No old source bytes or old hashes are rewritten by this manuscript, and no missing file is fabricated as an exact restoration.
