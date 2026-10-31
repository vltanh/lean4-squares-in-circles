# A hub-owned triangle normal forces an opposite end, with a complete D02 double-axis exclusion

Date: October 28, 2026 UTC. Author: cycles continuation.

**Status: complete proposed radius-free local theorem and literal original-feature join, submitted for independent review.** All original contact means, positive force coefficients and physical masks remain. The local implication has no circle-radius or neighbor-degree premise.

## 1. Entire local physical and algebraic scope

Let U,V,W,T be distinct actual unit squares with pairwise disjoint open interiors. Retain actual nonempty contacts U-V, U-W, U-T, and V-W. The V-W contact need not carry positive stress.

Let n,m,t be unchanged unit common separating normals directed respectively from U into V,W,T. Suppose the actual positive coefficients mu,nu,tau satisfy

    mu*n+nu*m+tau*t=0,
    mu>0, nu>0, tau>0.                                (1)

In a physical-stress application, (1) is the complete original force equation of an unloaded true-degree-three U. The abstract implication below needs exactly the displayed balance, but it does not license omitting an additional nonzero force at a caller.

Assume n is an actual own side axis of U.

**Theorem 1.** The original third normal satisfies

    n.t<0.                                             (2)

**Theorem 2.** If t is also an actual own side axis of U, then

    t=-n, m=n, tau=mu+nu.                              (3)

Both conclusions retain every original force and physical contact. They cover singleton and shared-side contacts, including original endpoint-valued or variable aggregate means. The statement is about the actual retained normals, not a choice of replacement separating axes.

The degrees, circle loads, circle masks and other forces at V,W,T are arbitrary. No force or torque equation at those three squares is used. The location of the containing-circle origin, if there is one, is irrelevant.

## 2. Complete proof of the original axis propagation

The actual triangle U,V,W and the original U-owned axis n satisfy

    n.m>=0                                             (4)

by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md. That radius-free geometric theorem permits every original contact point and shared-side mean and any actual common normal m. It does not require m to be an axis of U or W.

Take the dot product of the complete balance (1) with n. Since |n|=1,

    tau*(n.t)=-mu-nu*(n.m)<0.

The strict inequality follows from mu>0, nu>0 and (4). Dividing only by the positive original tau proves (2).

Now suppose t is also an own side axis of the same unit square U. Its four possible unit axis directions relative to n are

    n, -n, Jn, -Jn.

Only -n has negative dot product with n. Thus (2) forces t=-n.

Project (1) onto Jn. Both n and t=-n have zero projection, so nu*(m.Jn)=0. The actual nu is strictly positive, hence m.Jn=0. Since m is a unit vector, m is n or -n. Equation (4) excludes -n. Therefore m=n. Substitution back into the unchanged vector equation gives tau=mu+nu. This proves all of (3).

Every original moment equation remains satisfied at the original applications. None was replaced or required in the argument. In particular no endpoint of a genuine side mean was promoted to the original force application.

## 3. Complete physical interpretation of the axis premise

Under the established physical contact construction, an own-axis U normal can arise from a singleton contact against the relative interior of a U side, or from a positive-length shared side with parallel actual frames and the original aggregate mean. A shared-side mean may itself be at a vertex; that does not change its physical shared-feature type.

The theorems do not need this classification as an extra assumption: any actual retained U-axis normals satisfy their conclusions. In particular all mean endpoints and all aligned-frame limits already covered by the physical stress construction remain.

The strict vertex/vertex convention is not used to infer a side owner. No generic normal is changed after the force coefficients have been obtained.

## 4. Literal whole double-endpoint-axis exclusion for D02.L01345

Retain the unchanged nine-square packing and the original row

    M6.B6.HEXAGON.D02.L01345.

Its rim is 01,12,23,34,45,50, its single positive chord is 02, and its positive circle-load set is {0,1,3,4,5}. Put

    U=2, V=1, W=0, T=3.

The actual positive neighborhoods are:

| Body | Entire positive pair neighborhood | Degree | Circle load |
| --- | --- | --- | --- |
| U=2 | 1,0,3 | 3 | zero |
| V=1 | 0,2 | 2 | positive |
| W=0 | 1,5,2 | 3 | positive |
| T=3 | 2,4 | 2 | positive |
| 5 | 4,0 | 2 | positive |
| 4 | 3,5 | 2 | positive |

The actual V-W contact is the unchanged positive rim edge 10. Thus the hypotheses of Theorems 1 and 2 are literal for the entire original U3 equation.

Assume the original U-to-V and U-to-T normals, namely those on edges 21 and 23, are both actual own side axes of U. No singleton or positive-shared-length restriction is imposed on either physical contact.

Theorem 2 proves that the original U-to-W normal on chord 20 is exactly the same U axis as the original U-to-V normal:

    n_20=n_21.

Apply the complete reconstructed theorem RECOVERED_SAME_AXIS_HUB_BOUNDARY_TRIANGLE_D02_FULL_FEATURE_EXCLUSION.md at precisely this original same-U-axis feature. Its theorem covers the entire parallel and nonparallel V frame split, every original V-W owner, every W and T physical circle mask, every original U-W shared mean, and all three unchanged additional squares. No narrower positive-shared-only premise is being substituted.

That accepted whole-feature theorem gives a contradiction. Therefore:

**Corollary.** The entire original D02.L01345 domain in which both endpoint normals 2-to-1 and 2-to-3 are own axes of 2 is impossible throughout the declared nine-square radius window.

This includes both original singleton/shared contact choices and all physical endpoint masks. The apparent adjacent-axis possibility is excluded directly by (2); the opposite-axis possibility propagates to the full same-axis triangle contradiction. No separate numerical angle or mean case remains.

## 5. Consequences and exact remaining boundary

The radius-free Theorem 1 also says that whenever U owns the U-V contact in such an actual touching triangle, every balanced third contact points strictly toward U's opposite n face. If that third normal is oblique, (2) remains a necessary condition, not a full geometric exclusion.

The D02 corollary is a complete original endpoint-axis feature. It does not claim that all D02 endpoints are axes, and it does not remove a tip-owned or a genuinely free endpoint from the original physical cover. It therefore gives no whole D02-row or coarse-cell credit by itself.

Combined with the complete both-tip-owned endpoint pocket theorem, the two uniform results remove the two homogeneous endpoint-owner classes. Mixed hub-axis/tip-owned endpoints and actual surviving free-normal features retain their original obligations. This sentence is a description of the remaining original domain, not a new case ledger.

## 6. Exact operative sources

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Radius-free n.m>=0 for the full actual U,V,W triangle, with original U-owned n and arbitrary original m |
| RECOVERED_SAME_AXIS_HUB_BOUNDARY_TRIANGLE_D02_FULL_FEATURE_EXCLUSION.md | f5847537dd854c738c06bb6637d86380ddafad2e5411844c866871dc4b7c7525 | Entire original D02 feature with unchanged U-to-V and U-to-W normals equal to one U side axis |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original chord, load mask, outer order, true degrees and three completing squares |
| TIP_OWNED_HUB_BOUNDARY_PATH_ENDPOINTS_POCKET_CAPACITY_ONE.md | 82692b55bbf1ab90baaa485c0de45a83d68a745d7991a408e27a3a3bf7060732 | Only the final description of the separately complete homogeneous tip-owned endpoint class; not used to prove Theorems 1, 2 or the double-axis corollary |

The local proofs above use no circle radius at all. The literal D02 join uses the exact radius and same-nine scope of its complete same-axis dependency, including that dependency's independent lower-radius exit.

No positive edge, physical contact, original magnitude, normal, side mean, physical circle corner or additional square is deleted or altered. No numerical pose, finite mesh, computational exclusion certificate, Lean compilation, CI, remote write or ledger mutation is used.

