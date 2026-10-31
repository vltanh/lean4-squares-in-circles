# Root review: complete negative-concurrence reduction for intact-root simple cycles

Date: October 27, 2026.

Reviewer: root, separately from c6_next and global_next.

**Decision: ACCEPT both complete stated theorems, with the explicit nonparallel-endpoint condition on the auxiliary polygon.** No whole surviving cycle is excluded by this reduction.

## 1. Exact source and complete read

Accepted source:

    C6_NEXT_INTACT_ROOT_SIMPLE_CYCLE_NEGATIVE_CONCURRENCE.md
    SHA256 5e49f162076ce7e699e5013e8e5d6354e907a343bcc4520aa08f1beef78fda42.

Separate complete independent review:

    REVIEW_INTACT_ROOT_CYCLE_NEGATIVE_CONCURRENCE_GLOBAL_NEXT_2026_10_27.md
    SHA256 52165c83ba86707f50ce8715ce1a55c7d16eefd62535a3de8a8631794d6bcb25.

I read both in full. The complete local parallel-star/channel extraction, actual annular order, conditional loaded2 concurrence and full endpoint circle-mask inputs were just root-audited in

    REVIEW_INTACT_ROOT_CYCLE_OPPOSITE_PARALLEL_ROOT_2026_10_27.md
    SHA256 cbf0ac0f1bf28a9f0872503af70e1636714f0f0915673ebb45ad397f7c0f15e3.

The genuine unit-bypass theorem, the full intact-root normal form 103a0f4c, degree-free moment theorem 8def789e, and equal-parallel exclusion 0d534b23 retain their already accepted scopes. The new proof imports only the local parts of fc07a3b7 that precede its opposite-parallel root specialization. It does not apply a full-component degree-two theorem to E.

## 2. Original moments and the complete private endpoint cover

In the actual cycle E-T_1-...-T_m-E with m≥4, all private vertices retain their true positive degree two. The full normal form makes both E neighbors A,C loaded and E physically clear with O in its open interior. A private edge has nonzero origin moment, and the unchanged private torque equations propagate the common directed value k. Orientation gives det(p_A,u)=k>0 and det(p_C,v)=−k. The private force sum is exactly M=u+v, with c_E·M<0. The two separately accepted whole parallel-interface exclusions make u,v nonparallel.

Only two private loads would leave at least two actual unloaded transmitters on the private A-C path. Their reserve would be at least two, but the actual unit E touches both endpoints and bounds that reserve by sqrt(2). Thus at least three private loads occur. This does not create a physical A-C contact or use E as a transmitter.

Every interior private loaded star is nonparallel by the complete local S/D and channel-reserve cover. Its two nearest loaded endpoints are distinct and reached without crossing E. Each endpoint A,C remains either nonparallel with positive weakly proper concurrence, or radial S with its two original nonzero inner-side moments. Radial D has zero moment and is excluded explicitly. No individual S mean is moved to a midpoint.

## 3. Actual private order and outside-root corner placement

Consecutive nonparallel loaded concurrences satisfy q_next−q=L f with L>0 and det(q,f)=k. The direct-edge zero-coefficient case would identify distinct actual boundary resultant directions and is impossible by the full disjoint corner intervals. Hence every consecutive resultant determinant is positive. At a radial-S first or last endpoint, its original private port lies on the appropriate strict transverse side of its radial axis; the adjacent interior proper concurrence gives the same determinant sign. This includes either or both S endpoints.

The physical cycle and its actual exterior circle spokes give its private resultants either clockwise or counterclockwise order. At least two consecutive clockwise gaps would exceed pi and have disjoint total greater than 2pi, so the actual order is counterclockwise. Its lifted endpoint directions are 0 and gamma, with 0<gamma<2pi and every private consecutive gap below pi.

Each intact tip's actual E edge followed by a circle spoke places all of its physical circle corners in the complementary open arc (gamma,2pi). The genuine optional S/D leaf has the same placement. The disjoint full corner intervals make this strict relative to the endpoint resultants, including zero individual weights. These are exactly the remaining positive circle atoms of the original E component, so their actual sum obeys F_out+M=0. No circle load is created at E.

## 4. Long and antipodal endpoint arcs

At nonparallel A, q_A=p_A+alpha u with alpha≥0. Open origin containment gives p_A·u>0, while det(q_A,u)=k>0. Therefore the u direction makes an angle beta_A strictly between zero and pi/2 from the A resultant. At C the direction of v is gamma−beta_C, with beta_C in the same interval. An S endpoint has beta=0 exactly. These conclusions include zero proper lengths.

Put delta=gamma−beta_A−beta_C. If gamma>pi, then 0<delta<2pi. If delta≥pi, the cone from v to the next lift of u has width at most pi and contains every outside circle atom strictly inside. Its bisector has nonnegative projection on u,v and strictly positive projection on the actual outside atoms. The intact tips have positive total load, so the full component equation cannot hold. Thus 0<delta<pi and det(u,v)>0.

If gamma=pi, delta=pi could occur only with both endpoints S. Then u+v is axial, whereas an interior positive private load and all other private loads lie in the same upper half-plane, making M have positive transverse component. This is impossible. Again det(u,v)>0.

The original root-line intersection q satisfies det(q,M)=0, hence q=tM. Its first moment gives k=−t det(u,v). Therefore t<0 in both arc cases, without any root-port properness premise.

## 5. Short endpoint arcs and the complete projection argument

When 0<gamma<pi, M lies strictly inside the positive cone of the endpoint resultants. If A is S and delta≤0, u,v instead have their positive sum at or below the first endpoint ray, a contradiction. The reflected argument handles C of type S, including both endpoints S. Thus det(u,v)>0 and t<0 throughout those cases.

With both endpoints nonparallel, the actual positive radial vectors q_A,q_C are independent and the full private sum can be written M=A_0 q_A+B_0 q_C with A_0,B_0>0. Write q_A=q+a u and q_C=q+b v with initially arbitrary a,b. Comparison in the independent u,v basis gives

    A_0 a = B_0 b = 1 − t(A_0+B_0).

Neither coefficient can vanish, since that would identify q_A,q_C. Thus they have the same strict sign. If both were negative, endpoint properness would put q strictly on two actual outward normal rays of the convex E. For any p+lambda n on such a strict ray, the displayed squared-distance identity proves that p is its unique nearest point in E, including a vertex or side endpoint. The two ports would coincide, and two nonparallel rays from that point cannot meet again. Therefore a,b>0.

Direct expansion gives

    det(q_A,q_C) = [t(a+b)+ab] det(u,v).

The left side is positive in the short arc. If t≥0, the nonzero moment forces t>0 and det(u,v)<0, while the bracket is positive. This contradiction proves t<0 in the last case. Consequently every original endpoint alternative satisfies q=−sigma M, sigma>0, and c_E·q>0.

## 6. Exact auxiliary-polygon scope

Assume now that both endpoint stars are nonparallel, as Theorem 2 requires. All private loaded stars are then nonparallel. In the short-arc case a,b>0 was proved above. In the long or antipodal case q=sigma F_out lies strictly in the complementary arc, whose width is at most pi. The two endpoint determinants and the moment identities again give a,b>0. For a short arc, q opposite the strict M cone has angle in (pi,pi+gamma), and its two closing gaps are also strictly below pi.

The ordered vertices q,q_A,...,q_C therefore have one circular radial order, all successive angular gaps in (0,pi), and strictly positive coefficients along their actual directed force lines. Each edge advances inside its own angular sector; the sectors' open interiors are disjoint. The polygon is simple and winds once about O.

At a private vertex the unchanged true force equation F_j=f_−−f_+ and q_j=t_j F_j give det(f_−,f_+)=k/t_j>0. At q, the incoming direction is −v and the outgoing direction u, with determinant det(u,v)>0. Thus every turn of the simple polygon is strictly left and it is strictly convex, with O in its interior.

The actual E ports are not assigned nonnegative distances from q. The proof does not put E inside this polygon or identify the polygon with an empty physical face. This distinction is necessary: the result is an auxiliary force-line geometry theorem, and the radial-S endpoint alternatives are outside its polygon conclusion.

## 7. Acceptance and remaining obligations

Both complete theorems are accepted at the frozen source pin. All original C5 private-load orbits and all C6/C7 channel and endpoint masks remain covered, including the genuine optional E leaf. Every actual force, application mean, circle mask, individual zero weight, true degree and physical zero-stress contact remains intact.

The original geometric root interface still needs a complete exclusion. No physical capacity, whole-cycle closure, unrestricted inequality or equality classification follows from the negative concurrence or convex auxiliary polygon alone. The older global prerequisites and Lean integration remain separate. No source header, ledger, remote branch, Lean file or workflow was changed.
