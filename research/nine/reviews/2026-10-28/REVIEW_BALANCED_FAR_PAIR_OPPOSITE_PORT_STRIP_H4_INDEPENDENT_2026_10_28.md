# Independent review of the balanced far-pair and opposite-port strip reductions

Date: October 28, 2026 UTC. Reviewer: h4_review continuation.

**Verdict: PASS at the complete stated scopes of Sections 1--6.**
This is an independent full review of the frozen source below. The
reviewer did not author it, contribute its estimates, or edit it before
review. Subsequent attempts to extend it are separate from this verdict.
No complete original H4 family, graph parent, or coarse cell closes.

## 1. Exact reviewed source and direct dependencies

| Source | SHA256 |
| --- | --- |
| BALANCED_BOUNDARY_FAR_PAIR_AND_OPPOSITE_PORT_ORIGIN_STRIP.md | 72a915beaee37b435d993c6e77bd9833d717479b7b07ac014783d764cffa8605 |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c |
| INNER_PENTAGON_FOUR_SPOKE_NO_CHORD_OCCUPIED_POCKETS_AND_LONG_PORT_REDUCTION.md | ad0a8e658d303d7527a383c4688fa4bfdae1a04f46cecfb59c424cc4028e02a6 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| FIXED_SINGLETON_THREE_FORCE_OFF_LINE_NORMAL_SELECTION_AND_H4_OWNED_END_REDUCTION.md | d5e02f317ecbfdbd3d948fd27f5f78d6eda8803fb679c435ef3101780e1f47b1 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |

All eight direct dependency pins match the current local bytes. I read
the complete new source and its operative older arguments: the entire
balanced-three metric and four-boundary-path proofs, the complete
fixed-return geometry and fixed-singleton selection proof, the original
H4 pocket/load join, the degree-free boundary-edge moment lemma, the
all-mask true-degree-two concurrence lemma, and the physical embedding
construction. Existing accepted transitive inputs retain their own
review records; this record does not claim a new global prerequisite
audit or a replay of unrelated historical certificates.

## 2. Complete three-load far-endpoint argument

The inherited center bounds m<|c|<M and open pi/12 resultant deviations
apply to every physical circle mask with positive total circle weight.
The center separation argument proves the resultant directions have
the actual circular center order and all consecutive directed center
gaps are strictly below 7*pi/6. It needs no local pair-degree equation.

The actual touching pair has center distance at most sqrt(2). Its
minor angle g obeys cos(g)>9/25 because both center radii exceed 5/4.
The shorter BC arc cannot contain E: its complementary consecutive
gap would exceed 2*pi-theta>7*pi/6. Thus it really is one consecutive
gap, rather than an arbitrarily selected angular interval.

If both minor E endpoint angles were at most alpha=pi-theta/2,
a corresponding major consecutive gap would be at least
pi+theta/2>7*pi/6; equality at pi is also excluded. All three gaps
would consequently be their minor gaps and sum to less than
theta+2*alpha=2*pi, a contradiction. The strict far-pair conclusion
is valid for the entire original window. It explicitly requires
balance of exactly the stated three actual resultants; no fourth
positive load is removed.

## 3. Full port-strip theorem and support criterion

At the weak outside alternative O_x>=P_C,x, the center-to-point
half-diagonal bound gives c_C,x<=sigma. The actual outward projection
of the other center and the full port distance sqrt(2) give
c_E,x<-sqrt(2). The angular distances from East and West therefore
give angle(C,E)<pi-u+v, with u>v>0. In particular the comparison
angle belongs to (0,pi), where cosine is strictly decreasing.

I rederived the exact cosine expression and checked every rational
comparison:

    (m^2-1/2)*(M^2-2) = 537257/1620000,
    (173/300)^2 - (m^2-1/2)*(M^2-2) = 1465/1620000,
    m*M = 1729/900,
    17*1729^2 - 25*1419^2 = 481472.

All quantities squared in the radical comparisons are positive.
Thus cos(angle)>-1419/1729>cos(alpha). Reflection handles the other
weak outside alternative, including equality of the origin projection
with either port. The conclusion is the strict open port strip.

For the support criterion, n.(c_K-P) is the actual support half-width
and is at least 1/2, while |c_K-P|<=1/sqrt(2). Its perpendicular
component has magnitude at most 1/2, so the center displacement makes
at most pi/4 with n. The strict n.d>1/sqrt(2) hypothesis then makes
the center displacement have strictly positive d projection. This
covers all actual minimum-support points and all genuine side means;
no support point is replaced and no external ownership is needed.

## 4. Exact full-force H4 substitutions

The reviewed fixed-port source uses the actual H4 and D3 equations.
Its D-frame vectors become

    f_C = (2*eta+gamma*b, gamma*b)/sqrt(2),
    f_E = (-(2*eta+gamma*a), gamma*a)/sqrt(2)

in the displayed orthonormal port-chord frame. Positivity of eta,
gamma,a,b proves their strict outward pi/4 bounds. The Section 3
criterion applies to the actual minimum supports on C and E before
the optional external-owner selection is invoked.

In L0124, all four actual loaded bodies E,A,B,C form the unchanged
boundary path, and their full force sum is zero. The complete path
theorem gives the minor C/E angle greater than 5*pi/6>alpha. Thus
the whole H-owned-HD feature satisfies the strip conclusion.

In L124, the three positive loads are exactly B,C,E, and BC is an
actual contact. The far-pair alternative may choose CE or BE.
Reflection exchanges the two original unloaded ends and the two
adjacent loaded bodies. The manuscript correctly requires that the
chosen far end itself be H-owned. It does not transfer ownership from
the other end or silently cover the entire original load family.

The true degrees remain H4, A/B/C/D each three and E two. In L0124,
A is loaded; in L124, A is unloaded but remains degree three. No
third force at C is deleted in either application.

## 5. Genuine E2 moment and full physical mask

Section 5 adds the explicit premise that A physically touches the
circle. Positive circle weight at A is not required. The compatible
rim embedding and the actual lower D arc give the same boundary order
for E--A. The degree-free physical boundary-edge lemma therefore
gives det(Z,g)>0 for the unchanged EA mean and normal. Its use is
legitimate at a physically boundary zero-load A as well.

The original full E2 moment is exactly

    |f_E|*det(P_E,n_E) = lambda*det(Z,g)>0.

With P_E=(-L,h), n_E=(-c,s), and c>s>0, its left determinant is
c*h-s*L. It follows that h>(s/c)*L>0. No torque sign or proper
concurrence is inferred at C3. The body A being physically clear in
L124 is expressly excluded from this part of the theorem.

Section 6 uses the already compatible selected-certificate conclusion
that DE is externally E-owned; it does not reselect a current normal.
The full original side parameter is rho in (0,1). The true E2 lemma
applies because A is its actual physical boundary neighbor. Its sign
convention gives q=P_E+ell*n_E with ell>=0 and q=tau*F_E, tau>0.
An assertion that q belongs to a two-circle-corner square is neither
needed nor made.

The n-coordinate of the actual center is N+1/2>0. The negative
k-coordinate of F_E forces the center's k-coordinate to be nonpositive.
The complete actual mask is therefore

    Z_E=K+rho>=1/2,
    R^2=(N+1)^2+Z_E^2.

The strict case has one physical circle corner. At equality both outer
n-face corners remain physical and the negative-k corner has positive
weight; the other coefficient is retained, whether zero or positive.
The displayed center formulas prove its strict upper-left quadrant.
The same quadrant for F_E follows directly from q=(-L-ell*c,h+ell*s).

## 6. Scope and acceptance boundary

No source correction was required for this verdict. These are complete
uniform necessary reductions, not a claim of a complete mixed C3/E2
pocket capacity. The non-H-owned original features, the far-end/owner
conjunction in L124, and its physically clear A refinement are still
separate obligations. Both original H4 load families remain open.

All nine actual units, true degrees, original forces and moments,
normals, physical masks, individual zero coefficients and full actual
means remain. Exact arithmetic above checks printed comparisons; it
is not a pose cover or a computational exclusion certificate. No Lean
compilation, CI, workflow dispatch, shared-ledger edit, commit or
remote write was performed for this review.
