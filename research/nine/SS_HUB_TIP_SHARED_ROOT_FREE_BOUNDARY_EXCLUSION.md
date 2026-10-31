# The shared-root/free-boundary S/S hub-tip diamond has no positive selected core

Date: October 26, 2026.

**Status: complete whole-feature hand candidate, pending fresh full independent review.** The proof first gives a full physical reduction to a narrow stacked configuration, retaining every original H4/K3 force. A final nontrivial finite determinant at the two coincident physical hub ports excludes that entire configuration. No sampled orientations or scalar certificate packet is used.

## 1. Original domain and result

Retain the actual positive graph
\[
                    HK,HB,HC,KB,KC,HL_H,BL_B.
 \tag{1}
\]
The true degrees are H4,K3,B3,C2, the genuine leaves \(L_H,L_B\) are S, and the block loads are exactly the original positive loads at K,C. All nine physical units and all three arbitrary completion units remain.

Use
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \epsilon=\max(d-1,0)<\frac1{60},\qquad
 \frac9{10}<d<\frac{61}{60}.
 \tag{2}
\]
Assume HB is a genuine positive-length shared side and BK is a free vertex/vertex singleton. Its actual mean on HB may be either endpoint.

**Theorem 1.1.** One common compatible pre-extraction certificate excludes this entire original feature family.

The new common selection used first is
S_ROOT_BOUNDARY_FREE_NORMAL_SIDE_BIAS_SELECTION.md,
SHA256
48bc30d65e1581f4dc84ac0143b76482738dd46901e9f5384b66f94b34de8343.
Its open side-bias restrictions have a complete matched-junction and prior-choice compatibility proof. Later restrictions below are finite open-dense exclusions inside those intervals.

## 2. The whole shared-root chart, without a chosen mean

Both genuine S roots meet \(D_\epsilon\). Orient the actual B-to-H shared normal upward. The physical H-B-K triangle and this B side axis make the free B-to-K normal have positive vertical component. Reflect horizontally so it is
\[
                          n_{BK}=(-u,v),\qquad u,v>0.
\]
The full true B3 force equation makes its actual radial leaf application strictly rightward and downward. Write
\[
                 p_B=(A,-b),\qquad A,b>0,\qquad A^2+b^2=d^2.
\]
The physical B and the full shared H slider are therefore
\[
 \begin{split}
 B&=[A-1,A]\times[-b,1-b],\\
 H&=[A-1+\sigma,A+\sigma]\times[1-b,2-b],
                       \qquad -1<\sigma<1,\\
 P=B\cap K&=(A-1,1-b).
 \end{split}
 \tag{3}
\]
The actual HB support height satisfies \(|1-b|\le\epsilon\).

If \(d\le1\), this last inequality gives b=1 and
\(d^2=1+A^2>1\), impossible. Thus \(d>1\), and
\[
            |1-b|\le d-1,\qquad A^2\le4(d-1)<\frac1{15},
                       \qquad 0<A<\frac4{15}.
 \tag{4}
\]
All leaf and shared means are still their original values.

## 3. The entire nonzero slider is excluded; K lies strictly west

If \(\sigma<0\), P lies in the relative interior of H's bottom side. H occupies the upper tangent half-plane and B the southeast quadrant there. A further unit K would have to occupy exactly the southwest quadrant. A strict northwest B-to-K normal cannot be minimum support at P on that quadrant, because it has negative dot product with the downward inward axis. This contradicts the actual free normal.

Suppose \(\sigma>0\). At P the B sector is southeast. Any K tangent quadrant disjoint from it is either wholly in the upper half-plane or wholly in the left half-plane, with their common boundary cases included. In the left alternative the whole K has \(x\le A-1\), whereas the whole H has \(x\ge A-1+\sigma>A-1\); their physical contact is impossible. Thus K lies wholly above B's top line \(y=1-b\).

The side-bias theorem applies to the actual true B3 root, its near-origin H neighbor, and physical boundary K. Its actual B-to-H axis is upward, and K lies beyond that same B side. The theorem excludes this complete free-BK alternative. Hence \(\sigma>0\) is impossible as well.

It follows that
\[
                         \sigma=0.
 \tag{5}
\]
At P the H northeast and B southeast tangent quadrants fill the right half-plane. The whole K lies west of their common vertical side. If K were the aligned northwest quadrant, it would lie above B's top side and be excluded by the same side-bias theorem. If it were the aligned southwest quadrant, BK would share a whole side rather than be a free singleton.

Thus K is strictly oblique, with its unique rightmost vertex P and exact axes
\[
             u_K=(-c,s),\qquad v_K=(-s,-c),\qquad
             c,s>0,\qquad c^2+s^2=1,
\]
\[
                        K=P+[0,1]u_K+[0,1]v_K.
 \tag{6}
\]
The entire physical strict common-normal interval on BK is
\[
                  n_{BK}=(-u,v),\qquad
                         0<\frac vu<\frac sc.
 \tag{7}
\]
Indeed its dot product with \(u_K\) is positive automatically, while strict minimum support on the other inward axis is \(us-vc>0\).

The unique near-origin B side at P is its top side. The physical-cone conclusion of the side-bias theorem says that (7) cannot contain a ratio greater than one. Therefore \(s\le c\).

Equality would give \(c=s=1/\sqrt2\), and K's opposite corner would have first coordinate \(A-1-\sqrt2\). By (4),
\[
  |z|\ge1-A+\sqrt2>
       \frac{11}{15}+\frac75
        =\frac{32}{15}>\frac{25}{12}>R,
\]
contradicting containment. The middle reserve is \(1/20\). Consequently
\[
                                 c>s>0.
 \tag{8}
\]
In particular both HK and BK are genuine singleton contacts at P, and the actual H-to-K normal is strictly southwest. All four actual H forces remain.

## 4. The other genuine S leaf forces exact stacked root heights

The H chart is now
\[
                    H=[A-1,A]\times[1-b,2-b].
\]
Its genuine S leaf has radial support d. We cover every actual vertex or side support.

Its northeast vertex has squared norm \(A^2+(2-b)^2\). Equality with \(d^2=A^2+b^2\) gives b=1.

Its northwest vertex has squared norm exceeding \(d^2\) by
\[
             5-2A-4b>
                  5-\frac8{15}-\frac{61}{15}
                    =\frac25>0.
\]
Its southeast vertex has squared norm \(d^2+1-2b<d^2\), because \(b\ge1-(d-1)>59/60\). At the southwest vertex, a radial outward support requires \(b>1\); then its squared norm differs from \(d^2\) by \(2-2A-2b<0\). If \(b\le1\), its nonnegative vertical coordinate is incompatible with a strictly southwest radial direction. These vertices cannot supply the other genuine leaf.

The right, left and lower side supports are respectively A, \(1-A\), and \(b-1\), all strictly below d. The sole remaining side possibility is a vertical upper S leaf with \(2-b=d\), retaining its complete horizontal mean.

That side possibility is impossible by the unchanged H4 force equation. Its leaf has zero horizontal component, its HB force is downward, and its actual HK normal is strictly southwest. Thus its HC normal must have strictly positive horizontal component. There are only three such H support features:

* the right axis, which contradicts the nonobtuse triangle-side rule with the strictly southwest HK normal in the physical H-K-C triangle;
* a strict northeast normal at \((A,d)\), which lies in the relative interior of the actual vertical S leaf's inner side, since \(A<4/15<1/2\). The leaf and H leave only a southeast quadrant for any further unit, forcing a right-axis shared contact rather than the proposed strict normal;
* a strict southeast normal at \((A,1-b)\), whose radius is below \(3/10<r\), because
\[
 A^2+(1-b)^2<
       \frac{16}{225}+\frac1{3600}
          =\frac{257}{3600}<\frac9{100}.
\]
Such a point cannot belong to the physical boundary unit C.

The full vertical-leaf chart is therefore excluded, including its actual side mean endpoints. The northeast vertex case is the only one left. Put
\[
                         a=1-A.
\]
The complete actual physical roots and leaf applications are now
\[
 \begin{gathered}
 B=[-a,A]\times[-1,0],\qquad
 H=[-a,A]\times[0,1],\\
 p_B=(A,-1),\qquad p_H=(A,1),\qquad
 d^2=1+A^2,\qquad P=(-a,0),\\
 K=P+[0,1](-c,s)+[0,1](-s,-c),\qquad c>s>0.
 \end{gathered}
 \tag{9}
\]
Both actual leaves are the genuine radial S squares in these directions. There was no deletion of HC, HK or any circle force to reach (9).

## 5. K is physically unique, and its complete tilt interval is small

The opposite K corner
\[
                     z_K=(-a-c-s,s-c)
 \tag{10}
\]
is strictly farther from O than all three other K corners. Compared with the two adjacent corners, its squared-norm differences are
\(1+2as>0\) and \(1+2ac>0\); compared with P the difference is
\(2+2a(c+s)>0\). Thus z_K is K's unique physical circle corner.

Combining its norm with (2),(9) gives
\[
 R^2=a^2+2a(c+s)+2=(d+1)^2+\frac14,\qquad
              a(c+s)=d+A-\frac38.
 \tag{11}
\]
The complete parameter ranges imply
\[
 \frac{43}{240}<A<\frac{11}{60},\qquad
             a>\frac{49}{60},\qquad
                1<c+s<\frac{99}{98},\qquad
                         0<s<\frac1{60}.
 \tag{12}
\]
Here \(A^2=d^2-1<(61/60)^2-1=121/3600\). Since \(c+s>1\), (11) gives \(d+2A>11/8\), and hence \(A>43/240\). Also
\[
 c+s-1=\frac{d+2A-11/8}{a}
       <\frac{1/120}{49/60}=\frac1{98}.
\]
Therefore
\[
 cs=\frac{(c+s)^2-1}{2}<\frac{197}{19208}.
\]
Since \(c>1/\sqrt2>2/3\), this gives
\[
 s<\frac{591}{38416}<\frac1{60}.
\]
These estimates cover the entire continuous interval, not selected poses.

## 6. The complete H/C support cover

At H, the actual HK normal is strict southwest at P. The physical H-K-C triangle excludes the positive horizontal and positive vertical H side axes by their negative dot products with that normal.

The H bottom side is the full shared H/B side. Its relative interior is locally covered by the two opposite half-planes of H and B, so no further unit can meet it. Its right endpoint \((A,0)\) has radius below r. At its left endpoint P, the two right quadrants of H,B and the strictly oblique west quadrant of K leave two sectors each strictly smaller than \(\pi/2\), so no further unit can contain P.

A strict northeast HC point would be the actual leaf application \((A,1)\); H and its tilted actual S leaf leave no sector of width \(\pi/2\) for C. Strict southeast and southwest contacts have already been excluded at \((A,0)\) and P.

Thus precisely the following H/C possibilities remain:
\[
 \begin{array}{c|c}
 \text{H-owned left axis}&P_C=(-a,Y),\quad0<Y\le1,\\
 \text{strict northwest H normal}&Q=(-a,1).
 \end{array}
 \tag{13}
\]
Every contact owner and mean is still present within this cover.

## 7. C's physical two-corner mask is impossible

A physical two-corner C is a radial S square. Its inner vertices have norm squared \(d^2+1/4\), its inner face has radius at most that value, its tangential faces have radial coordinate at least d, and its circle corners cannot be shared.

### 7.1. A strict northwest H contact

At \(Q=(-a,1)\),
\[
                   |Q|^2-(d^2+\tfrac14)
                           =\frac34-2A>\frac{23}{60}>0.
 \tag{14}
\]
Hence Q cannot be an inner vertex or inner-face point of a physical S unit. It cannot be a circle vertex or outer-face point either, the latter having radial coordinate \(d+1>|Q|\).

If C owns a tangential side at Q, write its inward side normal from H as \(n=(-w,z)\), \(w,z>0\). Its radial direction is either \((z,w)\) or \((-z,-w)\). Their scalar products with Q are respectively \(-az+w<1<d\) and \(az-w<a<1<d\). Neither reaches C's necessary radial coordinate d. Thus every physical S feature at Q is excluded.

### 7.2. An H-owned left side

Now C has maximum x-coordinate \(-a\). A radial S unit aligned with H could have this maximum only among \(d+1,-d,1/2\), none equal to \(-a\in(-1,0)\). Thus its H contact is its unique rightmost inner vertex \(P_C=(-a,Y)\).

Its two inward axes have negative horizontal components. The radial axis pointing downward would make the vertex height negative, contrary to (13). The actual radial direction e_C is therefore northwest, and
\[
 Y=\sqrt{\tfrac14+2A},\qquad
 e_C=\frac{(-da-Y/2,\ dY-a/2)}{d^2+1/4}.
 \tag{15}
\]
The second coordinate is positive: \(d>a\) and \(Y^2=d^2+1/4-a^2\) imply \(dY>a/2\).

Let \(\phi_C\) be its center angle above the negative horizontal axis. Then
\[
                 \tan\phi_C=\frac{dY-a/2}{da+Y/2}.
\]
The ratio increases with d,Y and decreases with a. In (12),
\(d<61/60,\ a>49/60,\ Y<79/100\); the last inequality follows from
\(Y^2<37/60<(79/100)^2\). Consequently
\[
          0<\tan\phi_C<
               \frac{7107}{22055}<\frac13.
 \tag{16}
\]

The actual K center lies below the negative horizontal axis, with angle \(\phi_K\) satisfying
\[
 0<\tan\phi_K=\frac{c-s}{2a+c+s}<\frac{30}{79}.
 \tag{17}
\]
Thus the two boundary-center directions have separation
\[
 \phi_C+\phi_K
    <\arctan\frac13+\arctan\frac{30}{79}
     =\arctan\frac{169}{207}
       <\arctan\frac56<\frac{2\pi}{9}.
 \tag{18}
\]
The penultimate rational reserve is \(7/414>0\). To check the last angle exactly, put \(\theta=\arctan(5/6)\). Then
\(\pi/6<\theta<\pi/4\) and
\(\tan(3\theta)=-415/234<-\sqrt3=\tan(2\pi/3)\);
the squared reserve is \(7957/54756>0\). Monotonicity on the negative tangent branch gives \(3\theta<2\pi/3\).

Equation (18) contradicts strict \(2\pi/9\) separation of physical boundary centers. This excludes the last S alternative. Since C is physically boundary, it has exactly one physical circle corner.

No circle-weight ratio was assumed in excluding its two-corner mask.

## 8. HC cannot be shared

The only possible shared HC normal in (13) is the H left axis. Then
\[
                     C=[-a-1,-a]\times[q,q+1],
\]
where the open vertical interval intersects \((0,1)\).

For every height strictly between 0 and s, the open K interior meets the strip \(-a-1<x<-a\), as seen directly along its upper edge
\(P+[0,1](-c,s)\), with \(0<c<1\). To avoid interior overlap with K, C's open vertical interval must avoid \((0,s)\). Positive shared H/C length rules out \(q+1\le0\), so \(q\ge s\).

Its actual upper-left corner therefore has squared norm at least
\((a+1)^2+(s+1)^2\). Subtracting the exact K radius from (11) gives
\[
  (a+1)^2+(s+1)^2-R^2
     =2a(1-c-s)+s^2+2s
       >s^2+2As>0,
 \tag{19}
\]
because \(c<1\). This violates containment. HC is a singleton.

## 9. CK cannot be shared: all four K-side orientations

Use the actual K axes \(u_K=(-c,s)\), \(v_K=(-s,-c)\) from (9). A positive-length shared CK side makes the C frame parallel to K. Its real tangential slider is \(-1<\tau<1\). Every orientation follows.

* Beyond K's \(+u_K\) side:
\[
 C=P+[1,2]u_K+[\tau,\tau+1]v_K.
\]
Its maximum x-coordinate is
\(-a-c-\tau s<-a-c+s<-a\), so it cannot touch H.

* Beyond K's \(+v_K\) side:
\[
 C=P+[\tau,\tau+1]u_K+[1,2]v_K.
\]
Reaching H requires its maximum x-coordinate \(-a-\tau c-s\) to be at least \(-a\), hence \(\tau\le-s/c<0\). Its maximum y-coordinate is then
\((\tau+1)s-c<s-c<0\), so it again cannot touch H.

* Beyond K's \(-u_K\) side:
\[
 C=P+[-1,0]u_K+[\tau,\tau+1]v_K.
\]
For \(\tau>0\), its maximum height is \(-\tau c<0\), impossible for H contact. For \(\tau\le0\), C contains P and extends there in the strict southeast direction \(-u_K=(c,-s)\), overlapping the actual B southeast quadrant. At \(\tau=0\) the same overlap occurs at the C vertex; for \(\tau<0\) it occurs along its side-interior support.

* Beyond K's \(-v_K\) side:
\[
 C=P+[\tau,\tau+1]u_K+[-1,0]v_K.
\]
For \(\tau\le0\), C contains P and extends in the strict northeast direction \(-v_K=(s,c)\), overlapping H. For \(\tau>0\), the H northwest corner \(Q=P+(0,1)\) has K-frame coordinates \((s,-c)\). If \(\tau<s\), Q is in the open interior of C, forcing overlap with H. If \(\tau>s\), the u_K support intervals of H and C are strictly separated. Their required physical contact therefore forces \(\tau=s\).

In this last equality case C contains the actual corner
\(Z=P+(1+s)u_K-v_K\). Compared with K's circle corner
\(z_K=P+u_K+v_K\),
\[
             |Z|^2-|z_K|^2
                   =s\bigl[2+s+2a(c-2)\bigr]>0.
 \tag{20}
\]
Indeed \(a<1,c<2\) make the bracket greater than
\(2c+s-2=s(1-2s/(1+c))>0\), since \(c>s\) and \(1>s\).
This last shared-side chart also violates containment.

The four cases retain the entire open length condition and every actual shared mean. Hence CK is a singleton.

## 10. C now supplies two fixed side-owned normals

C is an actual positive loaded degree-two body with one physical circle corner, and both HC,CK intersections are singletons.

Their applications are distinct. Every possible HC point in (13) has first coordinate \(-a\) and positive height. K attains first coordinate \(-a\) only at P, whose height is zero. Thus no HC point belongs to K.

GENERAL_FIXED_TIP_NORMAL_SELECTION.md therefore makes both actual C incident normals side-owned in the same compatible selection. They are fixed physical axes, not selected values of unknown means. Write
\[
       n=n_{HC}\quad\hbox{from H to C},\qquad
       g=n_{KC}\quad\hbox{from K to C},
\]
and let Q_C be the actual fixed CK point.

The true C2 loaded-body theorem with its physical boundary neighbor K makes n,g nonparallel. The original H4 and K3 equations have not been changed.

## 11. Coincident K ports fix all loads up to scale

Let z_C be C's unique physical circle corner. Normalize its positive actual circle resultant to z_C. Since n,g are fixed and nonparallel, its actual unchanged equation determines unique fixed scalars
\[
                           z_C=\alpha n+\beta g.
 \tag{21}
\]
In any eventual positive candidate \(\alpha,\beta>0\). Otherwise that physical owner assignment cannot occur.

All HK and BK forces act at the same physical point P. Summing their actual terms in K's force and origin-moment equations, without changing the forces at H or B, gives
\[
          \kappa\,\det(P,z_K)
                         =\beta\,\det(Q_C-P,g),
 \tag{22}
\]
where \(\kappa z_K\) is the original K circle resultant in this normalization. The denominator is
\[
                           \det(P,z_K)=a(c-s)>0.
 \tag{23}
\]
Thus \(\kappa\) is fixed by the physical geometry and the two owned C normals. A nonpositive computed value cannot occur in this positive-load domain.

The complete original component force sum is
\[
                \lambda_H p_H+\lambda_B p_B
                         +\kappa z_K+z_C=0.
 \tag{24}
\]
The two actual leaf directions are independent:
\(\det(p_H,p_B)=-2A\ne0\). Hence their two positive actual coefficients
\(\lambda_H,\lambda_B\) are also fixed by the physical data. Again, assignments giving nonpositive coefficients cannot occur.

Equations (21)--(24) use every actual force and real point. They do not treat the two root neighbors as one invented unit or assert that K is physically degree two. In particular their individual forces remain in the next two original root equations.

This argument gives a reusable conditional implication: in a four-body block with two real pair forces coincident at a loaded hub, a fixed nonparallel opposite tip and nonzero \(\det(P,z_K)\) fix the hub load; independent real leaf rays then fix both leaf loads. The precise original hypotheses are all verified here.

## 12. A nontrivial finite restriction excludes the remaining free pair

Write the two actual free normals at P as
\[
 n_{BK}=(-u,v),\qquad n_{HK}=(-u',-v'),\qquad
                      u,v,u',v'>0.
\]
Let \(\mu>0\) be the original HB magnitude. Define the fixed physical constants
\[
 D=\lambda_H A+\alpha n_x,\qquad
 E=\lambda_H+\alpha n_y-\lambda_B.
\]
The true H4 horizontal equation and true B3 horizontal equation give
\[
                     \nu_{HK}u'=D>0,\qquad
                     \nu_{BK}u=\lambda_B A>0.
 \tag{25}
\]
If \(D\le0\), that owner assignment is incompatible with the original positive HK force and needs no generic exclusion.

The two vertical equations give
\[
 \begin{split}
 \mu&=\lambda_B-\lambda_B A\,\frac vu,\\
 \mu&=\lambda_H+\alpha n_y-D\,\frac{v'}{u'}.
 \end{split}
\]
Therefore every remaining positive candidate requires
\[
            D\,\frac{v'}{u'}-\lambda_B A\,\frac vu=E.
 \tag{26}
\]
All three coefficients in this relation are fixed physical data from Sections 10--11. The full actual HB mean has not been chosen and does not enter it.

The two singleton edges HK and BK are at the same physical three-unit junction, but their strict normal parameters are independent in the original construction. A fourth unit at P would require all four frames to agree, impossible for the strictly oblique K. No matched opposite-pair parameter identifies these two normals.

The original strict intervals have
\[
                0<\frac vu<\frac sc,\qquad
                0<\frac{v'}{u'}<\frac cs.
\]
The earlier side-bias selection may restrict the second to its nonempty subinterval \(v'/u'>1\); since \(c>s\), this still has positive length. The first interval has no ratio greater than one and remains nonempty. All prior finite determinant exclusions may be imposed inside these open domains.

Prelist every physical assignment of the six original roles, their actual genuine S leaves, physical unique corners, singleton points and both possible side-axis owners at C's two edges. The list is finite. For each assignment with the required positive constants, (26) is a nontrivial analytic restriction on the independent free parameters: holding \(v/u\) fixed, its coefficient of \(v'/u'\) is the fixed number \(D>0\). It cannot hold on an open interval.

Avoid these finitely many conditions simultaneously before extraction, inside the existing nonempty open domains. Equivalently multiply (26) by \(u u'>0\) to obtain an explicit nonzero polynomial condition in the two strict unit normals. The choices are compatible with the earlier fixed-tip, side-bias and matched-junction selections. They use no unknown force coefficient or mean; all normalized coefficients were computed from the fixed physical owner assignment.

Uncrossing preserves the surviving singleton normals and creates only shared-side atoms. Thinning deletes atoms. Every possible eventual physical tuple and side owner was prelisted. The original positive equations would force the forbidden (26) if any shared-HB/free-BK candidate survived. This proves Theorem 1.1.

## 13. Whole-interface consequence and remaining original scope

The reviewed S_ROOT_TRIANGLE_NEAR_ORIGIN_CONTACT_SIDE_OWNERSHIP.md already excludes every free HB contact in the original S/S hub-tip diamond. If HB is singleton, the reviewed fixed-nonleaf S-root selector at the true B3 excludes a free BK contact as well. The present theorem excludes the complementary case of genuinely shared HB and free BK.

Consequently one common compatible certificate has
\[
               \boxed{\text{both HB and BK have actual side owners}}
 \tag{27}
\]
throughout the entire original
M6.B4L2.DIAMOND.HUB_TIP.LKC.SS domain.

This does not identify a side-owned singleton with a shared side, nor does it close every remaining owner/owner, central-HK or C-mask chart of that original gate. The displayed stacked geometry is an intermediate consequence only in the proposed free-BK feature; it has now been excluded by its full original equations. It is not asserted for the surviving owner/owner features.

## 14. Exact frozen inputs and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| S_ROOT_BOUNDARY_FREE_NORMAL_SIDE_BIAS_SELECTION.md | 48bc30d65e1581f4dc84ac0143b76482738dd46901e9f5384b66f94b34de8343 | Whole physical free-cone restriction and its compatible open choice |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | Genuine S supports and actual near-origin points |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Actual side-axis signs in both physical triangles |
| CENTERED_INNER_ARC.md | fac240eca4ad3254ba4aafd8c915f9771f7eeb3acea57bd2ee3ddd4eab0ba2e5 | Physical boundary-center angular separation |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | The proved unique C mask and two distinct singleton ports give owned normals |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | True C2 nonparallelity with its actual boundary neighbor K |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Independent three-junction parameters, finite preselection and preservation |
| S_ROOT_TRIANGLE_NEAR_ORIGIN_CONTACT_SIDE_OWNERSHIP.md | 51dc1e532e3663d7637c3d22a7053d5b2e8e024d076706f5bbd793f8cc3e42be | Entire free-HB exclusion for the final two-interface consequence |
| S_LEAF_ROOT_FIXED_NONLEAF_CONTACT_SELECTION.md | 499e6d42632a811bcb7bef6596b8585c11fbb5f59f36551d02fd05c080387a43 | Singleton HB/free BK complement for that same consequence |

Original accepted inputs are compared at
26d9e3042b733ff0796876a4607a7d834f4b630a; new sources are pinned separately.

All physical circle masks, individual zero weights, all means and all original degrees were retained until eliminated by the displayed whole-domain arguments. The proof introduces no numerical exclusion certificate, orientation grid, new graph ID, checklist count, force deletion, post-extraction normal change, Lean run, CI workflow, ledger edit or remote mutation.

