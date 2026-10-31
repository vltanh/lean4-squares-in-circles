# Independent review: the entire radial top-boundary exclusion

Date: October 27, 2026.  
Reviewer: rooted_final_review.  
Verdict: **PASS for the complete frozen local theorem and the exact original applications stated in its Section 9. No correction requested.**

## 1. Exact target, scope, and independence

I read and reconstructed all ten sections of

    SMALL_SIDE_RADIAL_TOP_BOUNDARY_EXCLUSION.md
    SHA256 64ef75b5e3c944314a3a1c2795abc8aaea84084104cf160d369e1305873311fb
    18,226 bytes.

The whole physical theorem is accepted, including its closed central endpoint. It excludes three interior-disjoint unit squares H,K,C in the actual containing disk when

    R^2=(d+1)^2+1/4,       1<=d<61/60,
    H=[h-1,h] x [G-1,G],  -1/60<=h<=0,
    K=(h,z)+[0,1](c,s)+[0,1](s,-c),
    c,s>0, c^2+s^2=1,     0<=z<=G<=1,

K is physically circle-touching, C is physically circle-touching at two corners, all three pair contacts are physically present, and the actual H-to-C normal is E2. No force equation, degree, positive mask coefficient, ownership of K-C, strict central side position, or generic normal choice is required.

I contributed no proof argument to this source. During coordination I informed the author that a separate free-central caller needed the closed endpoint z=G; the author independently supplied and proved the theorem with that endpoint. I independently reviewed a separate small-side disk theorem earlier, but that theorem is not a logical input here. I also authored the separate recovered positive-B-concurrence result; it is not an input to this local physical proof. The original application in the reviewed manuscript explicitly retains its own positive/nonparallel antecedents.

This is a complete non-contributor mathematical review, independent of the author's checker and independent of the separate cert_final_review reconstruction. I did not run or import the author's exact checker or infer acceptance from the other review. I reconstructed the complete geometric cover and made a separate sparse-polynomial/Fraction record from the displayed formulas.

## 2. Complete direct reads and exact pins

I read the entire three present foundational sources, not only the cited statements. I also read the complete eight-section fresh normal form and its complete acceptance, and verified the origin-preserving map in the caller directly.

| Exact source | Verified SHA256 | Actual logical scope checked |
| --- | --- | --- |
| SMALL_SIDE_RADIAL_TOP_BOUNDARY_EXCLUSION.md | 64ef75b5e3c944314a3a1c2795abc8aaea84084104cf160d369e1305873311fb | All ten target sections |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual physical supports, unchanged selected normals and whole means; no selection is invoked by the target |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Entire source read; physical circle-point exclusion, inner-face bound, and exhaustive two-circle-corner classification used independently of its cycle force arguments |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete radius-free physical three-contact theorem, including arbitrary side applications and equality of the two normal projections |
| POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md | 93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce | Entire normal form; actual H-owned singleton-central and top-page chart used only with its full stated antecedents |
| REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md | 705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d | Complete existing acceptance of that exact normal form |

All six pins match actual present bytes. The physical theorem does not depend on any missing older global C-mask artifact, older positive-concurrence manuscript, or older central-contact reduction.

## 3. The K radius and complete two-corner classification

For T=(h,z), direct expansion gives

    |T+(c,s)|^2=h^2+z^2+1+2hc+2zs,
    |T+(s,-c)|^2=h^2+z^2+1+2hs-2zc.

The three nonopposite corners are bounded by 1+1/3600, 4+1/3600, and 2+1/3600. All are strictly below 17/4, including the largest reserve 899/3600. Strict convexity of squared norm on every nonconstant side excludes a separate circle contact in a side interior. Thus the actual K circle point must be its opposite corner

    Z_K=(h+c+s,z+s-c).

No K mask was assumed to reach this conclusion. I expanded the whole actual norm and obtained

    R^2=E+2+z^2+2z(s-c),
    E=h[h+2(c+s)]<=0.

The bracket is strictly positive because c+s>1 and h>=-1/60. This sign covers h=0 without introducing strictness. The alternative s<=c gives R^2<=3. With s>c, the entire z<=4/5 range gives R^2<=106/25, below 17/4 by 1/100. Therefore

    s>c,       4/5<z<=G<=1.

The physical classification of C was also reconstructed. At any containing-circle corner, its two orthogonal inward side coordinates a,b are at least 1/2, from containment of the adjacent corners. A second equal-radius adjacent corner requires the corresponding coordinate to be exactly 1/2. An equal-radius opposite corner would require a+b=1, hence a=b=1/2 and radius squared 1/2, outside the domain. Three or four circle corners are excluded by the same observation. Consequently the complete possible physical two-corner form is

    C=[d,d+1]e+[-1/2,1/2]f,

with orthonormal e,f and actual circle corners (d+1)e±f/2. This is a classification of physical corners; no individual force weight is assumed positive.

The average circle point has positive height, so e_y>0. If e_x>0, the unique minimum-height C vertex has positive x, whereas every point of the actual H top has x<=h<=0. This eliminates that whole sign. It leaves the vertical axis endpoint or the stated negative-x radial orientation.

## 4. The entire d=G=1 axis endpoint

When e_x=0, the exact radial form gives min-height C=d. Contact with the actual H top and 1<=d,G<=1 therefore force d=G=1 and

    C=[-1/2,1/2] x [1,2].

This is not discarded as a degenerate angle. Put F=(h+1/2,5/4), L=5/4-z. Its exact K own coordinates are

    A=c/2+Ls,       B=s/2-Lc,
    1/4<=L<9/20.

I reconstructed both coordinates and their inverse map. We have A>0, B>(s-c)/2>0, B<1/2, and

    A^2<=1/4+L^2<181/400<1.

Thus F lies in the open interior of K. For h<0 it also lies in the open interior of C. At h=0 it lies on the right edge of C, and a sufficiently small displacement F-epsilon E1 remains in the open K interior and enters the open C interior. The entire h=0 endpoint is therefore excluded as well. The negative endpoint h=-1/60 is harmless: F_x=29/60 is still strictly inside C's horizontal interval.

No force, strict central position, or C/K frame relation enters this endpoint argument.

## 5. The actual negative-x C chart and full side/corner cover

The remaining orientation is exactly

    e=(-q,p), f=(p,q), p,q>0, p^2+q^2=1,
    T_C=(-dq-p/2,dp-q/2),
    G=dp-q/2,
    V=(p/2-dq,G+q).

The first inner vertex T_C is the unique minimum-height C vertex and therefore the actual H-C contact. The previously arbitrary H-C physical intersection/mean has become singleton by actual geometry, rather than by choosing a mean. From G>4/5 and d<61/60,

    p>48/61,       (T_C)_x<-24/61<-1/60<=h.

The final strict comparison has reserve 1379/3660.

I reconstructed the complete physical triangle rule used for the two outward sides. If one normal is an actual side axis and has negative dot product with the other actual normal at the same square, the second application lies on the opposite side of that square. The corresponding neighbor has positive span in the first normal strictly less than one, while the first neighbor starts at the far support level. At a vertex this follows from the two orthogonal inward axes; at a side point it follows from the inward normal and full unit tangent interval. The result excludes physical contact between the two neighbors, for every actual point or mean. It does not assume a stress cycle, true degree two, or strict positivity of a missing force.

I also reconstructed the inner-face argument with its complete side slider. A neighbor at P=d e+t f, |t|<=1/2, with maximum e support d has its entire e interval in [d-sqrt(2),d], contained in [-d,d] for d>=1. Its entire f interval is in [t-1,t+1], hence [-3/2,3/2]. At a vertex the two orthogonal inward axes have opposite f signs and each transverse component at most one. At a side point the full actual side interval has length one. The whole neighboring square therefore has norm squared at most d^2+9/4, below the actual R^2 by 2d-1>=1. A physical boundary unit K cannot be such a neighbor.

Finally, a circle point Z is unshareable. Each contained-square inward axis v_i satisfies Z·v_i<=-1/2. Therefore the actual vector -Z points strictly into both inward quadrants if two squares shared Z, giving open interior overlap. This physical proof includes all possible side frames and does not use a mask weight.

These three facts give the following exhaustive boundary cover of C:

| Actual C boundary part | Complete reason it cannot meet K |
| --- | --- |
| Relative interior of the outer e side | Actual C-to-H normal -E2 has dot product -p<0 with the owned e axis, contradicting the physical triangle rule |
| Relative interior of the positive f side | Dot product f·(-E2)=-q<0 gives the same contradiction |
| Entire negative f side, including T_C | Its maximum x is (T_C)_x<h, below the actual minimum x of K |
| Relative interior of the inner e side | Full neighbor radius bound d^2+9/4<R^2 |
| Both outer vertices | They are actual circle points and cannot be shared |
| Remaining inner vertex V | Retained |

Thus the actual nonempty K-C contact is exactly {V}. No side owner is inferred or needed at this point. A free contact and every admissible common normal at V remain.

## 6. Complete K support signs, including free theta=1

Every nonzero outward normal w of C at V belongs to the cone generated by -e=(q,-p) and f=(p,q), whose two x components are strictly positive. Hence w_x>0 for every actual common normal.

Writing A_w=w·(c,s) and B_w=w·(s,-c), the full inverse coordinate identity is

    w_x=c A_w+s B_w.

I checked all sign combinations. Positive/positive gives T; positive/negative gives T+b; positive/zero gives the full T+[0,1]b side. All have height at most z<V_y=G+q. Negative/negative and their single-zero limits give w_x<=0. Zero/positive leaves T+[0,1]a, and negative/positive leaves its far endpoint T+a. Both coefficients zero would be the forbidden zero normal.

This exhausts all actual support faces and yields

    V=T+theta a,       0<theta<=1.

The strict lower bound follows from V_y>z. The upper endpoint remains closed and includes the entire free K-vertex alternative. Consequently

    theta c=V_x-h,       c>=V_x-h>=V_x.

There is no hidden assumption that K owns K-C or that V lies in the relative interior of its side.

## 7. Both continuous scalar estimates

The C-angle estimate is uniform. If q>=1/3, then p<=sqrt(8/9)<17/18. Together with d<61/60 and G=dp-q/2 this gives

    G<857/1080<4/5,

where the last reserve is 7/1080. Therefore 0<q<1/3. The exact comparison sqrt(1-q^2)<1-q^2/2 follows by squaring the positive right side; its squared excess is q^4/4. The function 1+q-q^2/2 is increasing throughout that whole interval. Hence p+q<23/18.

Direct reconstruction of the actual C coordinates gives

    G-V_x=(d-1/2)(p+q)
         <(31/60)(23/18)=713/1080<2/3.

The final reserve is again 7/1080. Combining with the actual K support inequality gives

    c>G-2/3>2/15.

Set t=G-2/3, so 2/15<t<=1/3. The function sqrt(1-c^2)-c is strictly decreasing throughout the positive quadrant. Thus

    s-c<sqrt(1-t^2)-t.

The original full K radius and z<=G now give

    R^2<=2+G^2+2G(s-c)
       <F(t),
    F(t)=22/9-t^2+2(t+2/3)sqrt(1-t^2).

The first inequality retains equality at h=0,z=G. The second remains strict there because the actual support/contact angle bound is strict; no step silently replaces z<=G by z<G.

I independently differentiated the entire radical expression and obtained

    F'(t)=2[1-2t^2-(2/3)t-t sqrt(1-t^2)]/sqrt(1-t^2).

The denominator is positive on the complete closed interval. Its numerator is bounded below by

    1-2/9-2/9-1/3=2/9>0.

Thus F increases over the whole domain. At the upper endpoint,

    F(1/3)=7/3+2sqrt(8/9)<38/9<17/4.

The two exact reserves are (17/18)^2-8/9=1/324 and 17/4-38/9=1/36. This contradicts the actual radius lower bound, with every physical angle and side application retained. There is no subdivision or sampled pose in either scalar step.

## 8. Exact original application and the free-central endpoint

The complete normal form at 93cbef18 supplies, under its explicit positive/nonparallel B and singleton-HK antecedents, the actual H-owned-central chart

    H=[x,x+1]v+[-y,G]u,
    0<x<=delta<1/60,       89/120<G<1,
    P_HK=xv+zu,           0<z<G,
    n_HK=-v.

The origin-preserving map P -> (-P·v,P·u) sends it exactly to H=[h-1,h] x [G-1,G] with h=-x<0, and its actual K support point to (h,z). The existing side-interior singleton implies a strict minimum-x K vertex; no K frame alignment is imposed. Its orthogonal inward axes have strictly positive x coordinates and may therefore be labelled (c,s),(s,-c) with c,s>0. The actual H-owned top-HC alternative becomes E2 and min-height C=G. All three real contacts remain present.

Therefore the entire physical two-circle-corner C mask is excluded in that original feature. The conclusion concerns physical corners, including either individual force weight being zero. It changes no original H4/K3/B3/C2 equation, actual application, or occupied leaf. A packing completion with all nine units would still contain these impossible three actual units.

The target also correctly states its broader application boundary: a separately proved free-central chart with the same strict minimum-x K vertex at (h,G) satisfies the theorem with z=G. I independently checked every place where this equality could matter. The vertex classification still gives z>4/5; V_y=G+q remains strictly above z; theta=1 stays allowed; the first radius comparison may be equality but the angle comparison is strict. The vertical radial-C endpoint d=G=1 is handled physically before the final scalar step. Thus no new endpoint premise is needed by that caller.

The local result does not prove positive/nonparallelity, an original HK-singleton reduction, or an arbitrary free-contact support chart. Those antecedents must be supplied by their own actual source. It does not recover any absent old manuscript or by itself close a whole original graph label. This scope matches the source exactly.

## 9. Independent exact record and final acceptance

My separately written audit is

    recovery_2026_10_27/rooted_radial_top_boundary_audit.py
    SHA256 2527c543cafccc3ea18665d9b3645564de753dfbe47007ed1f043ab24c504abb

with report

    recovery_2026_10_27/rooted_radial_top_boundary_audit.json
    SHA256 205681afb2e2a0fd7916d5eba872c72a0212a4295c060d9833da9a2528a550ba.

It passes **21 complete coordinate, norm, support, or cleared-radical identities; 24 exact rational values and reserves; and all six target/input/review pins.** The independent record includes both K adjacent corners, its entire opposite-circle identity, the axis-endpoint fixed point and inverse coordinates, both inner and both outer C vertices, the whole inner-face gap, both K support-coordinate inverses, the exact G-V_x comparison, the full radical derivative, and the actual radius-to-comparison difference.

The exact record verifies the written algebra; the full continuous physical proof and original application were reconstructed separately above. This is not a computational exclusion certificate and adds no leaf boxes or finite pose covering. No Lean, CI, ledger or remote action was performed. The frozen source remains unchanged.

**Final verdict: complete independent non-contributor PASS for the whole local theorem, all closed endpoints and every actual contact type, together with the exact original application stated in the source.**
