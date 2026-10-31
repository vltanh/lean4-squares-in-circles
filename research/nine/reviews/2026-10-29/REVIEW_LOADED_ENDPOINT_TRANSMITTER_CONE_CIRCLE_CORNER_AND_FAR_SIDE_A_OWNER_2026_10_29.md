# Independent review: loaded-endpoint cone, physical corner and complete far-side reduction

Date: October 29, 2026 UTC. Reviewer: Type II A-owner continuation.

**Verdict: PASS at the stated complete generic and necessary-reduction
scope.** I read the entire new source and every complete direct input,
reconstructed both endpoint alternatives including coincident actual
applications, checked both physical-circle masks and every individual
zero coefficient, and re-derived the complete far-side application.
The source leaves its final circle-cap inequality explicitly open.

The reviewer did not contribute to the new loaded-endpoint theorem,
its physical-mask lemma, its outward-corner comparison, or the far-side
application. I authored the older A-only support-cone and diagonal
sources used as inputs in its scope discussion; those inputs have their
own separate independent reviews. This review does not replace those
reviews or claim fresh independence for their original proofs.

## 1. Exact frozen source and full input reads

Reviewed source:

    LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md
    SHA256 d2420066a74cb41cc080f34be8be3b4538d6b66912f0dfed48bf9d23b0573198

Complete direct inputs read and checked:

| Source | SHA256 | Exact reviewed use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original endpoint/N force, moment and actual support conventions |
| NONPARALLEL_TWO_APPLICATION_LOADED_STAR_HAS_PROPER_CONCURRENCE.md | 4aeba77a0f964597a40ce290f4a0f9d6d7dc802f83a024f3497cfdb6bb97359d | Only the complete nonparallel, distinct-application proper-ray theorem, retaining the possible exterior two-corner concurrence |
| LOADED_PARALLEL_FULL_STAR_WITH_DISTINCT_NEIGHBORS_FORCES_RADIAL_S_2026_10_29.md | f0e7b44a8d7e0eff5654384bf20bb5a99c3809d57a92bbb16afba6ee7ac1c96c | Entire parallel-star conclusion without application distinctness, with both physical circle weights and opposite-sign forces handled |
| UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md | f4f2f293e038ea9f42dc8572cb8f216c9b9718a8fb14c4ac215232efcaf34e3c | Whole original far-return chart, strict acute cone, q>0, k>1/2, actual B owner and side remainder |
| NONACUTE_SUPPORT_CONE_DIAGONAL_BRIDGE_GAP_AND_COMPLETE_A_ONLY_CONE_REDUCTION_2026_10_29.md | 6c07437cf008c1d9c5f89532d1ba080cfed4cc7fdea5e5b332317ae0be44c7e1 | Only the complete original A-only strict-cone entry, with no acute premise |
| TYPE_II_A_ONLY_H_OWNER_COMPLETE_DIAGONAL_RETURN_EXCLUSION_BY_ORIGINAL_ENDPOINT_AXES_2026_10_29.md | a38780b72988e3f1628ba751d955bfc8a09e9c06f55764e0699b88506d175eb8 | Only the exact original A-only diagonal exit and its retained loaded endpoint stars |

All hashes were checked against the local full sources. The old inputs
remain at their accepted original scopes. In particular no generic
boundary-neighbor theorem has been used at B or C, whose other actual
neighbors need not be boundary units.

## 2. Exact direction signs and complete loaded-endpoint alternatives

At the actual N, full force and moment give the unchanged positive
common magnitude gamma and T-U=ell*d, with ell=1 or sqrt(2).
The inward direction into B from N is d, so B's original outward
pair normals are -b and -d. The inward direction into C from N
is -d, so C's original outward pair normals are c and d.
Consequently the displayed complete circle-force equations

    G_B=p_B*b+gamma*d,
    G_C=-p_C*c-gamma*d

have the correct signs and retain every original endpoint term.

If B's two normal lines are parallel, the complete parallel-star
input applies because B has two distinct actual positive neighbors.
It permits coincident original means. It excludes the opposite-sign
case and proves both normals are the same, hence d=b, with the full
radial S physical mask and equal positive weights. At C, the same
argument gives d=c. Both parallel alternatives cannot occur at once
because b,c are nonparallel. No finite concurrence has been assigned
to either parallel case.

In the finite/finite case, I independently reconstructed

    q_B=Q_B+ell_B*b=T+alpha*d,
    q_C=Q_C-ell_C*c=U-beta*d,
    ell_B,ell_C,alpha,beta>=0.

For each endpoint with two distinct actual applications these are
exactly the signs of its full proper-ray theorem. In a physical
two-circle mask, the concurrence may be outside the square; the new
proof never uses inside membership. If its actual applications
coincide, setting its two ray lengths to zero makes both equalities
literal. This is a separate direct treatment of coincidence, not an
application of the distinct-point theorem outside its domain.

Subtracting gives

    (ell+alpha+beta)*d
       =Delta+ell_B*b+ell_C*c.

The assumed strict positive-cone representation of Delta makes both
right-hand coefficients positive, while the left scalar is positive
because ell>0. This proves the whole strict-cone consequence without
an acute assumption. The parallel/nonparallel tests exhaust all
endpoint normal pairs. Endpoint directions d=b and d=c have exactly
their stated parallel types, since a strict combination of two
nonparallel directions cannot be either endpoint ray.

## 3. The physical-mask corner lemma retains all zero coefficients

I checked the entire argument in actual own coordinates. If the center's
f coordinate x were negative, all farthest corners would use the -f
sign and have f coordinate x-1/2<0. Every actual circle corner is
farthest by containment. Thus the positive weighted sum of all original
circle terms would have negative f component, contradicting G.f>=0.
This proves x>=0. Likewise G.w<=0 implies the center's w coordinate
is nonpositive.

The +f/-w corner is therefore farthest in both coordinates. A positive
total circle weight guarantees at least one physical corner has radius
R, so every tied farthest corner, including the selected one, has radius
R. This includes a zero center coordinate, two adjacent physical
circle corners, either zero individual corner coefficient, and a zero
resultant component. The conclusion is about actual physical circle
membership; it does not incorrectly infer a positive coefficient at
that particular corner.

No radius interval, degree equation or separate neighbor assumption is
needed for this lemma. The later loaded2 application supplies its signs
from the full circle vector, not from one arbitrarily retained atom.

## 4. Outward comparison and every equality endpoint

At an actual circle corner Z, its actual adjacent vertex Z+w lies in
the disk. Thus 2(Z-O).w+1<=0. Direct expansion for delta>=0 gives

    |Z-O-delta*w|^2
       =R^2-2delta*(Z-O).w+delta^2
       >=R^2+delta+delta^2.

The comparison point need not lie in a square; no physical realizability
or contact interpretation is used for it. If an independent argument
proves its norm at most R, the nonnegative right-hand excess forces
delta=0 and equality of the norm. This exact weak endpoint is valid,
and the strict-cap contradiction is immediate.

## 5. The complete owned-side application

For the actual chart

    B=Q_B+[0,1]b+[-(1-beta),beta]w,
    0<beta<1,

the strict signs d.b>0,d.w<0 force the actual minimum-d support
T=Q_B+beta*w. This is an original support conclusion, not a choice
of T. Since the actual U is in C and Q_C is a maximum-c support,

    Delta.c+beta*w.c=d.c+(U-Q_C).c<=1.

With w.c<0 this proves beta>=beta0 as stated. Its original strict
upper endpoint gives beta0<1, and beta0>=1 therefore excludes the
whole feature directly.

The full B circle force has positive b component and negative w
component. The physical-mask lemma makes

    Z_B=Q_B+b-(1-beta)w

an actual circle corner, including every original physical weight mask.
Its inward own edge is w, and the comparison point is exactly
Y=Z_B-(beta-beta0)w. The previous outward comparison gives all of
the stated quadratic lower bound with the original beta retained.

If |Y-O|<=R, both beta=beta0 and |Y-O|=R follow. The support chain
then has equality: d.c=1 and (U-Q_C).c=0. Unit lengths imply d=c.
Keeping the full original C2, its two actual outward directions are
both c, so its radial S conclusion follows from the complete parallel
theorem. No circle load at C has been discarded to obtain the equality
case.

## 6. The far-return application covers every remaining side direction

The companion far-return proof supplies the complete original strict
acute cone, k>1/2, and the actual B-owned support f. It also retains
C as the original loaded true2 with its full D mean and physical mask.
Its diagonal alternative is already excluded, so the actual N is side
with the unit point difference required in Section 5.

In the B-parallel alternative d=f, both Q_B,T lie on B's same actual
minimum-f side. Therefore (Q_B-T).n<=beta_B*a, while the actual C
maximum-n support gives (U-Q_C).n<=0. I obtain exactly

    1+k=Delta.n<=beta_B*a+b0
                    <a+b0<=sqrt(2)<3/2<1+k.

This excludes the entire B-parallel side alternative, including all
its original physical S placements and means.

In every other side alternative, d is either strictly in cone(f,n)
or equals n at the C-parallel endpoint. Because f.n=b0>0, both
alternatives have d.f>0. With w_B=Jf, one has f.w_B=0 and
n.w_B=-a<0, so the positive n coefficient makes d.w_B<0.
Thus all three signs in the generic owned-side theorem hold on the
whole remaining domain. Its exact beta0 is k/a; no smaller angle or
force-ratio subset is used.

The displayed original-coordinate simplification is exact:

    Q_B+(k/a)w_B=P-M*d0,
    M=(1+ell)/H=sqrt((1+ell)^2+(1+q)^2),
    Y=P-M*d0+f-w_B.

The necessary inequality on this single point is consequently valid
for every remaining side mean. The paper does not claim that it has
proved the required opposite cap on Y or that every corner of a
hypothetical comparison square is inside the disk.

At the weak equality endpoint, d=n makes C physical radial S with
inward radial direction -n. Its true maximum-n support is
1-sqrt(R^2-1/4). Equating this with the retained original P.n-1
gives P.n=2-sqrt(R^2-1/4), exactly as stated. This is an implication
of its full loaded star, not an assumed saturation of the earlier cap.

## 7. Exact limits and adoption boundary

The general cone theorem also applies to the entire original A-only
strict-cone row. The source correctly avoids inferring d.b>0 from
non-acute cone membership alone. Its A-only discussion claims only
the actual cone and full radial parallel alternatives; a caller of
the circle-corner reduction must still supply all necessary signs.

The source contains a complete general result and a complete necessary
far-side reduction. The strict norm cap on its comparison point is
still open. It claims no whole far-return or A-only side exclusion,
loaded-N exclusion, full D02 closure, global sharp radius theorem or
equality classification. Every original unit, degree, full stress,
mean, physical mask and individual zero coefficient remains.

No changes were required. This independent review used exact equations
and complete physical feature covers; no pose search, angle mesh,
packing certificate, numerical corner sampling, changed normal,
replacement mean, metadata mutation, remote write, Lean/Lake build,
CI/workflow or merge was used.

