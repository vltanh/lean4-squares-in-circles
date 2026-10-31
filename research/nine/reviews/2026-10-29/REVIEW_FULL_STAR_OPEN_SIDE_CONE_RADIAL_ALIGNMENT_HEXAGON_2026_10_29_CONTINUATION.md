# Independent full review: one open side cone forces a loaded full star to be physically radial

Date: October 29, 2026 UTC. Reviewer: hexagon continuation.

**Verdict: PASS for the complete printed theorem and both full-star consequences.** This is a full independent mathematical review of the root-authored arbitrary-degree, no-axis-premise strengthening. The reviewer authored the earlier two-force endpoint lemma that motivated it, but did not propose or develop this generalization. The entire new source, including all physical masks, every sign of every incoming term, and all actual shared means, has been read and checked. No original checkbox or count is changed by this review.

## 1. Exact frozen object and physical convention

The reviewed source is the complete file

`LOADED_FULL_STAR_OPEN_SIDE_CONE_FORCES_PHYSICAL_RADIAL_ALIGNMENT_2026_10_29.md`

read from `/workspace/scratch/f6ccb6b18452/pr11-continuation/research/nine`.

| Object | Bytes | SHA256 |
| --- | ---: | --- |
| Full new source | 8711 | `dcbd7f5339899052dd8237858778c0bfb53c7a2f087a44d6edcd7db3a6c96952` |
| `PHYSICAL_CONTACT_STRESS.md` | 17993 | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |

The latter physical source has been read in the ongoing continuation and its exact force/torque equation was reread for this review. Its circle forces are positive radial atoms, while the pair terms point outward from the actual square at actual supporting applications. With an incoming direction n_i, the actual outward pair term is therefore -mu_i n_i. Absorbing the common factor two into the nonnegative circle coefficients gives precisely the new source's equations

    F = sum_j c_j Z_j = sum_i mu_i n_i,
    sum_i det(P_i,-mu_i n_i) = 0.

Every original positive pair term is retained. The arbitrary-degree quantifier concerns the entire star, not a selected subset. The applications are actual minimum supports in the original square, and an own-axis direction retains its complete original shared-side mean interval.

The full new proof is elementary after this convention. It uses no prior special selection theorem, no concurrence result, no shape of an adjacent graph, and no numerical packing certificate. The earlier two-force source is discovery provenance rather than an imported mathematical premise.

## 2. Complete physical-circle classification and the empty-star endpoint

Write the actual square as

    C = x e + y f + [-1/2,1/2]e + [-1/2,1/2]f.

Its corner squared norms are sums of two independent own-coordinate squares. When both x and y are nonzero each coordinate has a unique farthest endpoint, so there is one farthest corner. When exactly one center coordinate is zero its two endpoints tie and the other coordinate has a unique farthest endpoint, giving precisely two adjacent farthest corners. When both center coordinates vanish all four corners have squared norm 1/2.

Positive circle load supplies an actual circle corner and hence makes the maximum corner norm equal to R. Every farthest corner is therefore a physical circle corner, independently of whether its original individual coefficient vanishes. Conversely, any point of a side interior has strictly smaller squared norm than the larger of its endpoints, by strict convexity of the squared norm on a nondegenerate segment. Thus there is no missing side-interior physical circle mask.

The explicit hypothesis R>1/sqrt(2) excludes the four-corner mask. In each remaining mask all physical circle corners lie in a common strict radial half-plane: for a two-corner mask its nonzero center coordinate gives the corresponding common radial sign, and for one corner this is immediate. A positive-total nonnegative combination of these actual corners cannot vanish. Consequently the source correctly excludes a star with no positive pair terms before using a strict sum inequality. There is no vacuous application of its cone condition to an empty set.

For every retained positive pair term the hypothesis a_i>|b_i| implies a_i>0. Since the set of positive terms is nonempty and all mu_i>0,

    F.e = sum_i mu_i a_i
        > sum_i mu_i |b_i|
        >= |sum_i mu_i b_i| = |F.f|.

The strict first inequality remains strict with any finite degree, including a star containing some exactly axial incoming terms. No angular averaging or individual circle-weight sign beyond nonnegativity is used.

## 3. Full unique-corner torque audit

Suppose that C has exactly one physical circle corner Z. The total positive circle load then gives F=c_0 Z for c_0>0. The source first treats the exact endpoint F.f=0. That would force Z.f=0. Because Z is a corner, the other endpoint of its unit own-coordinate interval differs by exactly one and has absolute coordinate one; the corner with that endpoint and Z's same e-coordinate has strictly larger norm. Thus this endpoint cannot be discarded by assuming a nonzero transverse resultant; it is actually excluded.

After a common reflection one may assume F.f>0. The reflection reverses the sign of the determinant convention if the ordered axes become negatively oriented, but it multiplies every term of the zero-torque equation by the same sign. The source's use of the reflected ordinary coordinate determinant is therefore valid. Since F.e>0, the actual Z has both coordinates positive. Unique farthest-coordinate maximization forces Z to be the upper-right corner of the actual square

    C=[u,u+1] x [v,v+1],  Z=(u+1,v+1).

The minimum support for a_i>0 has the following complete alternatives. I recomputed their determinants directly:

| Original transverse sign | Actual minimum application | P_i-Z | det(P_i-Z,-mu_i n_i) |
| --- | --- | --- | --- |
| b_i>0 | (u,v) | (-1,-1) | mu_i(b_i-a_i)<0 |
| b_i<0 | (u,v+1) | (-1,0) | mu_i b_i<0 |
| b_i=0 | (u,t_i), v<=t_i<=v+1 | (-1,t_i-v-1) | mu_i a_i(t_i-v-1)<=0 |

The source writes the last row as mu_i(t_i-v-1). Here a_i=1 under the repository's unit-normal convention, so the expressions agree. Even without normal normalization the extra factor a_i>0 would leave its sign unchanged. The two oblique rows and both endpoints of the axial mean interval are all covered.

Every term is nonpositive. Since F.f=sum_i mu_i b_i>0, at least one original b_i is strictly positive, and its first-row moment is strictly negative. This establishes strict total negative pair torque with no assumption that all transverse signs agree. Negative and zero transverse terms strengthen or preserve the contradiction rather than constituting omitted cases.

The original torque about O can be moved to Z using the complete force equation. More explicitly,

    sum_i det(P_i-Z,-mu_i n_i)
      + sum_j det(Z_j-Z,c_j Z_j)
    = total torque about O
      - det(Z, sum_i(-mu_i n_i)+F)
    = 0.

With a unique physical corner, every circle atom is at Z and the second sum is zero. The strictly negative first sum is therefore impossible. The F.f<0 case is the complete reflected calculation, reversing all signs together. This proves exclusion of the unique physical mask for the full actual star at every finite positive degree, with no force deleted.

## 4. Full radial direction and position audit

Only a two-adjacent-corner mask remains. Put A=sqrt(R^2-1/4). The radius hypothesis gives A>1/2.

If the center's e-coordinate vanished, the two physical corners would be +/-e/2+sigma A f. For their unchanged nonnegative coefficients, with positive total c_tot,

    |F.f|=A c_tot > c_tot/2 >= |F.e|.

This contradicts the already proved strict cone inequality. Either one of the two original circle coefficients may be zero, and the argument remains strict because A>1/2 and c_tot>0. Thus the center's f-coordinate vanishes instead.

The actual physical corners then have the form sigma A e +/- f/2. The positive sign of F.e forces sigma=+1. Hence the complete actual square is exactly

    C=[A-1,A]e+[-1/2,1/2]f.

This checks the full positional conclusion, rather than only its mask or the direction of its circle resultant. No false equal-weight conclusion appears: the two original coefficients remain free subject to the full original equations.

The source also allows 1/sqrt(2)<R<sqrt(5)/2, where d=A-1 is negative. That causes no problem for the principal mask and position theorem. Its later no-axis corollary has the separately stated stronger radius guard d>=0.

## 5. Both exact full-star consequences

In the forced radial frame, the two physical circle corners are (A,+/-1/2). Thus

    F.e=A(c_++c_-),
    F.f=(c_+-c_-)/2,

and nonnegativity gives |F.f|<=F.e/(2A). Equality corresponds to one coefficient being zero and is retained. This is a bound on the complete resultant only; it imposes no such individual bound on any pair direction.

For d=A-1, actual minimum supports give

    b_i>0: P_i=(d,-1/2),
    b_i<0: P_i=(d,+1/2),
    b_i=0: P_i=(d,t_i), -1/2<=t_i<=1/2.

Direct determinants in the original center-torque equation are respectively

    -mu_i(d b_i+a_i/2),
    -mu_i(d b_i-a_i/2),
    +mu_i a_i t_i.

Multiplying the complete zero sum by -1 gives exactly equation (5) of the reviewed source. In particular the signs of the last-row mean terms are correct. When R>=sqrt(5)/2, one has d>=0. If every b_i is strictly positive, every displayed summand in source equation (5) is strictly positive because a_i>0. If every b_i is strictly negative, every summand is strictly negative. Either whole no-axis feature is impossible, including the critical d=0 endpoint.

An actual axis term has a freely retained mean t_i and can contribute either sign. The source explicitly stops the same-sign no-axis corollary at that boundary; it does not silently drop axis terms or specialize their means. Mixed transverse signs remain covered by the main radial theorem and exact torque identity, but not by that extra exclusion.

For the earlier two-force caller, one incoming vector is e and the other is a unit vector n satisfying n.e>1/sqrt(2). Squaring and using unit length gives n.e>|n.f|, so every positive term of that actual two-force star meets the present cone hypothesis. This recovers the old endpoint mask exclusion and strengthens it to the exact radial direction. It does not require or manufacture a new contact at a higher-degree endpoint.

## 6. Scope, endpoints and adoption boundary

The strict open-cone condition is essential for this argument: at a 45-degree boundary the first unique-corner determinant may be zero. The source leaves that domain explicitly outside its theorem. Likewise the four-corner radius R=1/sqrt(2) is outside the stated radius interval. All attained endpoints that are inside the printed statement are retained: an axial pair normal, an endpoint shared-side mean, a zero individual circle coefficient, d=0 in the no-axis consequence, and either transverse resultant sign.

The theorem requires no equation at any neighbor, no contact among the neighbors, no positive graph embedding, and no fixed total number of bodies. These are substantive valid enlargements beyond the earlier true-two endpoint lemma. Any application to a particular nine-square graph must nevertheless verify the incoming open-cone inequality for every positive term of the actual loaded star. A partial cone formed by selecting two terms of a larger star is insufficient.

No whole original graph/load row is closed by this review alone. The exact reviewed object can be adopted as an arbitrary-degree radial-mask and exact-torque theorem at its printed scope, subject to the parent's usual preservation of its full source and this independent review. No Lean, Lake, CI, sampled pose, numerical angle search, or packing optimizer was run. Only complete hand geometry and exact source-identity checks were used.
