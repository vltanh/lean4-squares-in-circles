# A nonparallel boundary tip at perpendicular hub axes has no surviving free return

Date: October 28, 2026 UTC. Author: house continuation.

**Status: complete proposed hand owner-class exclusion, submitted for full root and separate independent review.** The unique physical-circle mask uses the already common simultaneous fixed-tip selection at two proved distinct fixed points. The entire physical two-circle mask is excluded by a new actual-geometry argument. No new normal is selected and no W3 equation is shortened.

Together with the accepted whole V-owned exclusion, this leaves only the actual W-owned return when the original V is nonparallel to U. It does not close the entire perpendicular branch or original D02 row.

## 1. Exact local setting and original selection

Put Q=1105/256 and work in

    2<R<=sqrt(Q).

Keep distinct actual closed unit squares U,V,W, contained in the unchanged disk D_R with pairwise disjoint open interiors and physical contacts UV,UW,VW. The original U-to-V and U-to-W normals are perpendicular own side axes of U.

V is nonparallel to U, has positive total circle load, and has its complete positive pair neighborhood exactly U,W. W physically touches the containing circle, with arbitrary degree, load, physical circle mask and all its other original forces retained. U's degree and load are arbitrary in the local result.

Retain the common previously selected physical certificate, including its strict free point-normal convention and simultaneous fixed-tip selection. All actual original applications and side means, their endpoints, positive magnitudes, physical circle corners, individual zero weights and every other physical unit remain.

**Theorem.** The actual VW contact cannot be a point-only vertex/vertex contact with a free original normal.

The physical-two-mask argument in Sections 3 through 6 does not use the fixed-tip selection. The unique-mask argument uses that already accepted selection before multipliers, not a reselection of an extracted normal.

## 2. Complete perpendicular direction and distinct fixed points

Rotate or reflect all physical data about the circle origin so that U-to-V is North and U-to-W is East. Write

    U=[L-1,L] x [H-1,H],
    P=(L-p,H), 0<=p<=1.

Since V is nonparallel to U, its actual UV intersection is the singleton P, its unique bottom vertex. Its inward axes are

    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (1)

Only the force-free geometric direction lemma of BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md, Section 2, is used. It gives the complete Southeast sign restriction for the original V-to-W normal:

    n_VW=(u,-v), u,v>=0, u^2+v^2=1.                (2)

That direction lemma covers every original U mean and a possible triple contact; it does not require W to be a loaded degree-two tip.

The complete common-point theorem for a true loaded V2 with a physical-boundary neighbor applies, since R^2>4>13/4. It gives

    P does not belong to W.                         (3)

In particular the original UV and VW applications are distinct. No original shared-side mean is replaced in applying that theorem.

Suppose now that VW were a free point-only vertex/vertex contact. Its normal is strict in both actual vertex cones. In V's frame,

    n_VW.e_2=-s*u-c*v<0.

Its e_1 component is nonzero because the normal is free. If that component were negative, the actual V support would be P, contradicting (3). Hence it is positive and the actual common point is necessarily

    M=P+e_1.                                       (4)

Both original pair applications P,M are fixed physical singleton points, and they are distinct.

If V has a unique physical circle corner, GENERAL_FIXED_TIP_NORMAL_SELECTION.md applies to these exact two fixed points in the already common certificate. It excludes a free normal on either incident edge. Its coincident radial-D exception is unavailable by (3), and no variable side mean is being treated as fixed. This proves the theorem for the entire unique physical-circle mask.

It remains to exclude the full physical two-circle mask without the selector.

## 3. The full V2 force fixes the only possible physical two-circle mask

Write the actual own coordinates of P as

    A=P.e_1, B=P.e_2.

Let mu,nu>0 be the original UV,VW pair magnitudes. V's full outward circle resultant F is

    F=mu*North-nu*n_VW,
    F.e_2=mu*c+nu*(s*u+c*v)>0.                     (5)

This is V's true two-force equation with its complete circle resultant. No equation at W or U is used.

If B<-1/2, every physical circle corner of V has negative e_2 coordinate B, so every nonzero positive circle resultant has negative e_2 component. Equation (5) therefore gives B>=-1/2.

If B=-1/2 and V has two physical circle corners, its first center coordinate A+1/2 is nonzero, since otherwise its farthest radius would be sqrt(1/2)<R. If A+1/2>0, the actual corner M=P+e_1 is a physical circle point. If A+1/2<0, P is a physical circle point. Both alternatives are impossible because M is shared with W and P is shared with U.

For completeness, a containing-circle point cannot be shared by two interior-disjoint contained unit squares: both inward own axes at such a corner have strictly negative dot product with the circle radius, placing each open right-angle tangent sector inside the same open inward radial half-plane. Two such angle-pi/2 sectors cannot have disjoint interiors there. This is geometric and does not require positive weight at the shared circle point.

Thus B>-1/2. A unit at R>2 can have two physical farthest corners only when exactly one own center coordinate is zero. Its positive second center coordinate therefore forces

    A=-1/2,
    B=d=sqrt(R^2-1/4)-1>1/2,
    P=-e_1/2+d*e_2,
    M=e_1/2+d*e_2,
    V=[-1/2,1/2]e_1+[d,d+1]e_2.                  (6)

Both physical outer circle corners remain, together with every permitted individual zero coefficient. No equal-weight or one-positive-corner hypothesis has been imposed.

## 4. The entire physical free-return geometry at W

First suppose W is nonparallel to U. Let Q_W=(L,H-delta) be its unique left vertex, which is its unchanged original UW point, with 0<=delta<=1. Write its actual inward axes as

    f=(C,S), g=(S,-C),
    C,S>0, C^2+S^2=1.

The actual M from (4) has height H+s>H>=Q_W.y. It therefore cannot be W's left or lower vertex.

It cannot be W's rightmost vertex either. At M the inward V axes are -e_1 and e_2, and their open cone contains West. At W's rightmost vertex its inward axes would be -f,-g, whose open cone also contains West. The two actual open tangent sectors would overlap. Thus a physical free contact there is impossible.

The only remaining W vertex is its upper vertex, giving

    M=Q_W+f.

Their coordinates imply

    C=c-p<=c,
    S=s+delta>=s.                                  (7)

If equality C=c occurred, then S=s, p=delta=0, f=e_1 and g=-e_2. The actual V and W would share their entire side P--M, contradicting the point-only premise. Therefore C<c and S>s.

Now suppose W is aligned with U. Its vertices have x coordinates L or L+1. But M_x=L-p+c<L+1, so M_x=L. Its height is greater than H, whereas the actual UW mean has height at most H. Thus M must be W's upper-left vertex. Set

    C=0, S=1, f=North, g=East,
    Q_W=M-f.

The original UW mean remains unchanged. Its existence gives Q_W.y<=H, and Q_W.y=H+s-1>H-1, so this actual corner Q_W belongs to the original U side as a geometric fact. No equation is evaluated at Q_W instead of the original mean.

In every W frame, therefore,

    W=M+[-1,0]f+[0,1]g,
    0<=C<c, S>s,
    gamma=c*C+s*S>0,
    eta=c*S-s*C>0,
    gamma^2+eta^2=1.                               (8)

The same actual V-own coordinates give

    f=gamma*e_1+eta*e_2,
    g=eta*e_1-gamma*e_2.

All aligned-frame and original UW mean possibilities have been retained.

## 5. Every actual W corner is strictly inside the containing circle

Using (6),(8), W's actual center has f coordinate

    c_W.f=M.f-1/2
         =d*eta-(1-gamma)/2>0.                      (9)

Indeed eta>1-gamma for gamma,eta>0 with gamma^2+eta^2=1, and d>1/2. Thus both minimum-f W corners are strictly closer to O than their corresponding maximum-f corners.

The two maximum-f corners are exactly M and M+g. Their V-own coordinates are

    M=(1/2,d),
    M+g=(1/2+eta,d-gamma).

They satisfy the strict comparisons

    R^2-|M|^2=2d+1>0,
    R^2-|M+g|^2=2d*(1+gamma)-eta>0.                (10)

The second follows from 2d>1 and 1+gamma>eta. Equations (9)--(10) therefore put all four actual W vertices strictly inside D_R, contradicting its physical boundary contact.

This contradiction uses the entire physical two-circle mask of V and the actual shape of W, not any chosen positive circle coefficient or any shortened W force equation. It treats the complete original free-return geometry at once.

## 6. Exhaustion of masks and selected original owners

At R>2 every physical boundary unit has either one circle corner or two adjacent circle corners: the farthest-corner formula in its own frame gives a tie on exactly one coordinate, unless its center is O and its farthest radius is sqrt(1/2). The latter is outside the current range.

Section 2 excludes the unique physical mask at the exact distinct-fixed-point selector scope. Sections 3 through 5 exclude the full physical-two mask geometrically. These exhaust V's physical circle domain, proving the theorem.

For the same actual perpendicular U-axis feature with V nonparallel, the separately accepted theorem

PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_OWNED_RETURN_QUARTER_DISK_EXCLUSION.md

excludes the complete V-owned original VW normal, including positive-length shared contacts and every original mean endpoint, inside the same nine packing.

Consequently the complete remaining original normal feature has

    V nonparallel to U;
    VW a singleton at the actual V vertex M=P+e_1;
    the original VW normal owned by W;
    M in the relative interior of an actual W side.

No new normal is selected. Positive-length shared VW contacts are already V-owned and covered by the separate theorem. Point-only vertex/vertex contacts are the actual free strict-cone case just excluded. V-side-interior/W-vertex contacts are V-owned. These physical contact types exhaust the original selected interface.

This is an owner-domain reduction, not a proof that the remaining W-owned feature is impossible. A V parallel to U is also outside the present statement.

## 7. Literal D02.L01345 join and retained original data

For the original rim

    01,12,23,34,45,50

with its unchanged positive chord02 and complete positive circle-load set {0,1,3,4,5}, use

    U=2, V=1, W=0, T=3,
    boundary path 1,0,5,4,3.

The true degrees are U3,V2,W3,5_2,4_2,T2. The same-nine analytic radius entry supplies R>2 and all three arbitrary completion units remain.

Whenever the original U-to-V and U-to-W normals are perpendicular U side axes and V is nonparallel to U, every premise of the theorem is literal. Its selected unique-mask invocation uses only the pre-existing common certificate and the two proved distinct physical singleton applications. Its two-circle invocation retains both V physical corners and every individual zero weight.

Thus the entire original free-return subdomain is excluded. The complete V-owned theorem then leaves only the stated actual W-owned singleton feature in the nonparallel V branch. W retains all three original forces and its full circle system; none is discarded to imitate a loaded tip.

No whole D02 load row, parent or coarse gate is closed by this reduction. The remaining W-owned geometry and the original parallel-V branch still require complete exits.

## 8. Exact sources and verification boundary

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Section 2's force-free perpendicular-support direction lemma only; no two-tip force theorem is applied to W3 |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Complete original P not in W, with all means and no hub owner or degree premise |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Existing common selection for the physical-unique V2 mask at the two actual distinct singleton points P,M |
| PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_OWNED_RETURN_QUARTER_DISK_EXCLUSION.md | 8f564d6904cc8744175ec1664a88cbf84f51d74d146d4536a647662aac8a1487 | Accepted complete V-owned feature, only in the Section 6 selected-owner and same-nine join |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original D02 graph, load mask and true degrees |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Same-nine R>2 entry retaining every completing unit |

The new physical-two-circle and actual W-corner arguments are printed in full. No pose search, numerical angle mesh, computational exclusion packet, changed mean, altered selected normal, fake lower-degree body, Lean compilation, CI, workflow, ledger mutation or remote action is used.

