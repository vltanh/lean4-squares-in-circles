# Independent entry review: perpendicular W-owned physical-two-circle pocket

Date: October 28, 2026 UTC. Reviewer: cycles continuation.

**PASS for Sections 2--3 of the repaired source, including both literal imported premises, the entire actual contact chart, all original UW means, and the complete physical V circle mask.** This is a focused independent entry review. It does not replace the separate full review of the new capacity, scalar, routing, and original-family arguments in Sections 4--14.

## 1. Exact reviewed bytes and independence

| Source | SHA256 | Scope read and checked |
|---|---|---|
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 | Full statement and Sections 2--3, with all later uses of the repaired p bound checked |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Sections 1--2: the force-free geometric normal-direction lemma only |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Entire source read; exact application at true loaded V2 and physical-boundary W checked |
| REVIEW_LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_PENTAGON_2026_10_28.md | 14053d3894f36653357e0210a2ae9ee8c83c578dddfb2a59a180bdccdf008e42 | Entire independent review read, including both imported local geometric inputs and all physical shared-side cases |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Operative simultaneous force/torque equations, radial circle atoms, and preservation of original side means |

I did not supply the preliminary perpendicular W-owned chart or the V two-circle inequality. Their independent verification is the purpose of this note. I authored earlier local lemmas used by the already accepted common-point theorem. Accordingly, this note checks the common-point theorem's literal application and relies on the separate complete pentagon review for independence of that theorem's entire dependency chain; it does not count my rereading of my own earlier inputs as a new independent review.

The initial target c0f6c7c951535fe662d20657b680ba11eb93d25d0e7311d6028f7485cc384edf printed the strict bound p<c in equation (6). I found that this fails at the explicitly retained aligned endpoint C=0, where equation (5) gives p=c. The author repaired precisely that bound to

    0<p<=c<1.

The repaired bytes above are the review target. Every downstream use needs only 0<p<1 or 1-p=1-c+beta*C>0, so the repair changes no subsequent argument or feature scope. In particular the aligned endpoint has not been removed.

## 2. Literal imports and full actual side chart

The U normals are original perpendicular own axes. A common global rotation and possible reflection therefore puts them North and East without moving the circle origin. With

    U=[L-1,L] x [H-1,H],

nonparallel V has a unique bottom vertex P=(L-p,H), and its inward axes are exactly

    e_1=(c,s), e_2=(-s,c), c,s>0, c^2+s^2=1.

Thus the physical UV intersection is a singleton, not a chosen point of a variable shared side.

Apply the geometric part of the bowtie source with its A=U, B=W, C=V. That part uses only three actual unit squares, their three physical contacts, and the two perpendicular U supports. It does not use the bowtie theorem's loaded-degree-two requirement at both neighbors or its radius hypothesis. Its conclusion puts W-to-V in the closed northwest cone, hence the original V-to-W normal in the closed southeast cone. Its proof explicitly covers arbitrary original application means and common triple junctions.

The common-point theorem applies separately: V is true loaded degree two with complete positive pair neighborhood {U,W}, W is physically on the circle, and R^2>4>13/4. It uses no U or W degree truncation. Therefore the original P does not belong to W. This is the full theorem's actual conclusion, not an inferred absence of all other physical triple points.

Any unit southeast normal has strictly negative e_2 component. Its e_1 component cannot be zero because the stated return normal is not a V own axis. A negative e_1 component would uniquely expose P on V and put P in W. Hence it is positive and the actual VW application is the unique V vertex M=P+e_1.

Because W owns that unchanged normal, its chart can be written

    g=(S,-C), f=(C,S),
    S>0, C>=0, C^2+S^2=1,
    W=Q_W+[0,1]f+[0,1]g,
    M=Q_W+beta*f, 0<=beta<=1.

The omitted southeast-cone endpoint S=0 would have negative e_1 component and is indeed impossible. The endpoint C=0 is retained.

For C>0, both W axes have positive horizontal component, so Q_W is its unique left vertex. Its UW support is therefore Q_W on x=L, and its height is at most H. For C=0, Q_W is the lower endpoint of W's vertical left side; the original UW mean at height at most H again implies Q_W,y<=H. Equating the actual M coordinates gives

    Q_W=(L,H-delta),
    p=c-beta*C,
    delta=beta*S-s>=0.

Since s>0, beta>0. The positive e_1 component of g is eta=c*S-s*C. Comparing the unit first-quadrant frames gives C<c and S>s. Consequently

    p>=c-C>0, p<=c<1,
    delta<=S-s<1,
    0<beta<=1.

Every claim remains valid at beta=1 and C=0.

At C>0 the original UW application is Q_W. At C=0 its actual common segment has heights exactly from H-delta to H: Q_W,y=H+s-beta>H-1, while Q_W,y+1>H. Thus the full original mean is

    M_UW=(L,H-delta_0), 0<=delta_0<=delta.

Setting delta_0=delta only in the genuine singleton case is correct. The argument does not replace the original variable mean by Q_W in an equilibrium equation.

The identities for gamma, eta, r, alpha and kappa follow by dot products of the unchanged orthonormal frames:

    gamma=c*C+s*S>0,
    eta=c*S-s*C>0,
    r=C/S>=0,
    alpha=s/S=gamma-r*eta,
    kappa=c/S=eta+r*gamma,
    gamma^2+eta^2=1,
    gamma*alpha+eta*kappa=1,
    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.

The support inequality beta*S>=s gives alpha<=beta; r*eta>=0 gives alpha<=gamma. Both weak endpoints are intentional, including alpha=gamma when C=0.

## 3. Complete physical V mask

Use the original positive pair magnitudes mu and nu. The physical stress equations give the full outward circle resultant

    F_V=mu*North-nu*g,
    F_V.e_2=mu*c+nu*gamma>0.

If B_V=P.e_2<-1/2, all farthest V corners have e_2 coordinate B_V<0. No nonzero positive total circle load on those corners can have the displayed positive component. Hence B_V>=-1/2.

At equality B_V=-1/2, the first own center coordinate cannot also vanish, since that would put the farthest radius at sqrt(1/2), contrary to R>2. A positive first center coordinate makes M=P+e_1 a physical circle corner; a negative one makes P such a corner. Either would be a shared containing-circle point. At such a point both incident square side directions have strictly negative inward radial projection. Each square's open right-angle tangent sector therefore lies strictly inside the same open inward semicircle; two such sectors cannot have disjoint interiors. This excludes both alternatives and proves B_V>-1/2.

With two physical circle corners and R>2, exactly one own center coordinate is zero. The second is now strictly positive, so it must be the first coordinate that vanishes. Thus the actual physical V is precisely

    V=[-1/2,1/2]e_1+[d,d+1]e_2,
    d=sqrt(R^2-1/4)-1,
    P=(-1/2,d), M=(1/2,d)

in V coordinates. This is a conclusion about its whole physical mask, independent of which individual outer-corner coefficients vanish.

The strict radius comparisons in (12) are correct:

    15/4-(387/200)^2=231/40000>0,

and the squared radius at d=61/60 exceeds 1105/256 by 31/57600. Therefore

    187/200<d<61/60.

The actual pair force lines have intersection

    q_V=P+(gamma/S)*North
       =(-1/2+gamma*alpha,d+gamma*kappa)

in V coordinates, because (q_V-M).f=-gamma+(gamma/S)S=0. Both pair-force moments vanish about q_V. Every circle atom is radial about the unchanged origin, so the full torque equation gives det(q_V,F_V)=0. Both e_2 coordinates are strictly positive; hence q_V is a positive multiple of F_V. This does not require q_V to lie in V and does not import a unique-circle-mask concurrence lemma.

Normalize only the positive total circle coefficient:

    F_V=Lambda*(xi,d+1),
    Lambda>0, -1/2<=xi<=1/2.

The nonnegative original weights on both actual circle corners give precisely this closed interval, with both endpoints retained. Parallelism yields

    (-1/2+gamma*alpha)/(d+gamma*kappa)=xi/(d+1).

All denominators are positive. Using only xi>=-1/2 and multiplying gives

    2(d+1)(-1/2+gamma*alpha)>=-d-gamma*kappa,
    gamma*[2(d+1)*alpha+kappa]>=1.

This is equation (14) on the complete physical-two-circle-mask domain.

## 4. Decision and exact limit of this review

The repaired Sections 2--3 give the claimed entry for every original W side application, including beta=1, aligned C=0, the full delta_0 interval, and both individual V circle-weight endpoints. The imported normal-direction and common-point results have exactly their required physical premises.

This focused independent PASS should be paired with the separately authored full review of the later pocket argument. It supplies no extra whole-family or coarse-gate credit by itself and makes no claim to have independently re-proved Sections 4--14 here. No normal was reselected, no force or body was deleted, no shared mean was changed, and no Lean compilation, CI, pose search, or numerical exclusion certificate was used.

