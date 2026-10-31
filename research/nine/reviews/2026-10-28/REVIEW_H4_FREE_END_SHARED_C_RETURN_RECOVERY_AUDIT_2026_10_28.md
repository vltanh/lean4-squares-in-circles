# Independent review of the free-HD shared-CD pentagon exit

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the entire free-HD, positive-length CD interface in
the stated four-physical-boundary domain.** The original coincident
s=r=0 application is included. Both auxiliary supports are actual points
of the unchanged C and E and enter no original force or torque equation.
The other free-HD features and L124's physically clear A mask remain.

## 1. Exact object, original scope, and current pins

Reviewed source:
`INNER_PENTAGON_FREE_END_SHARED_C_RETURN_COMPLETE_EXCLUSION.md`.

- Bytes: 16,433.
- SHA-256: `bfe146ae4ba73a824f01b6b9bf4c34776e3a63923c417a36c6b104da3225991a`.
- Git blob: `a24212940081ea577dbfbbe367220bd8a35d91a3`.

I read the entire source and independently rederived its full D3
table, slider exclusion, HC sign, original-origin bounds, complete
C3 and E2 joins, arbitrary E support construction, closed angular
endpoint exit and final path application. I paid particular attention
to the coincident shared-mean endpoint in Section 4. All eleven
displayed direct current pins match exactly.

The original positive graph remains HA,HB,HC,HD,AB,BC,CD,DE,EA,
with unloaded H4 and D3, loaded C3 and E2, and the unchanged true
degree-three A and B. The four units A,B,C,E are physically boundary.
This is all of the specified feature in H4_D0.L0124, and the
physical-boundary-A mask of H4_D0.L124. A's total circle coefficient
in that latter mask remains zero. The radius is the complete original
79/40<=R<=sqrt(1105)/16 interval. All nine actual units and every
original physical contact, force, mask and mean remain.

The full generic moment and path inputs at c1694bb4 and 34c9a023
have already received my separate complete independent reviews at
these exact bytes. The physical occupied-rim, angular-order, proper
E2 and contact-moment inputs have also been reread and rederived in
the preceding same-axis and perpendicular caller reviews. Here I
checked every new caller hypothesis rather than assuming their earlier
applications supplied it automatically.

## 2. Full shared-CD table and the actual lower-slider exclusion

The original free HD strictly exposes vertices of both H and D.
In D=[0,1]^2 its point is P_H=(0,0), with original D-to-H vector
(-a,-b), a,b>0. The actual D-H-C triangle and the D-owned shared
CD axis exclude East and North. A whole-configuration diagonal
reflection takes the other two cases to West without changing roles.
Thus the full physical positive-length shared return has

    C=[-1,0] times [r,r+1], -1<r<1,
    D->C=(-mu,0), mu>0,
    P_C=(0,s), max(0,r)<=s<=min(1,r+1).

The actual D3 balance gives D-to-E=(a+mu,b), so its strict D
support is P_E=(1,1). Its complete torque about (0,0) gives
b=a+mu(1-s). Consequently the actual unit direction n_E=(p,q)
has p,q>0 and q/p=b/(a+mu)<=1. The s=0 equality q=p and
s=1 equality b=a are both retained. No E owner or fixed-singleton
selector follows from this shared-CD configuration.

If -1<r<0, P_H is in the relative interior of C's right side.
C's left half-plane and D's Northeast quadrant leave only the
Southeast right-angle sector for the actual H vertex. Its inward
axes would have to be East and South. East has negative dot product
with the actual inward-to-H support direction (-a,-b), contradicting
that point's minimum-support property. Thus r>=0. This is a full
tangent-sector exclusion and does not discard r=0. The r=+-1
values were never positive-length CD contacts.

## 3. The strict HC vertical sign, including the common vertex

Let N be the original H-to-C normal at its unchanged application S.
The actual H point (0,0) and C top-right point T_C=(0,r+1) give
N.P_H<=N.S<=N.T_C. Since r+1>0, N_y>=0.

If N is East, the common support would equate max_x(H), which is
at least zero, with min_x(C)=-1. This is impossible. If N is West,
it would give min_x(H)=max_x(C)=0. Both inward H axes at its
vertex P_H would then have nonnegative x component. Their minimum
support condition in direction (-a,-b) requires
a*v_x+b*v_y<=0 and a*w_x+b*w_y<=0. Since each axis is nonzero
and a,b>0, both y components would have to be strictly negative.
Their dot product would then be strictly positive, contrary to
orthogonality. Thus neither horizontal normal is possible, and
N_y>0 throughout the full HC owner and mean cover.

This argument still applies when r=s=0 and an HC application also
occurs at that junction. It uses the real whole supports and does
not remove an original H4 or C3 term.

## 4. The actual occupied-rim orientation at the coincident endpoint

For s>0, the actual C ray at the D center occurs before its Southwest
H ray in counterclockwise order; the E ray is Northeast. Hence the
H spoke is strictly in the counterclockwise sector from the C rim
ray to the E rim ray. The real H lies on the bounded rim side, so
the positive orientation is D-C-B-A-E-D.

The s=0 case cannot be justified merely by assuming distinct ports.
Here the original interval and r>=0 force r=0 exactly. C and D
occupy the Northwest and Northeast tangent quadrants at (0,0),
together filling the upper half-plane. The actual H vertex sector
is in the complementary lower half-plane. Its two inward axes
generate the whole unit, so H is wholly on that side and its center
is strictly below the common point. C and D centers are strictly
above, on the left and right respectively.

This physical three-sector order fixes the compatible local routing.
In a small junction disk the C and D strands enter from upper left
and upper right, while the H strand enters from below. The directed
rim connection D-to-C has the H sector on its left, the lower side.
The original coincident D-side strands can be separated in the
prescribed compatible routing without reversing this order. In
particular, one cannot move the H strand to the upper side without
crossing a C or D strand or changing their actual cyclic sectors.
The same positive rim orientation D-C-B-A-E-D therefore holds.

This is a conclusion from the actual sectors and the existing
compatible embedding. It does not rely on an unproved deformation
of the squares or a perturbation of the original mean s. The source's
weak-limit description is consistent with this direct sector argument;
no source edit or new distinct-application assumption is needed.

Protected simultaneous real circle accesses consequently give the
boundary order C,B,A,E. The strict pi/12 corner-to-center deviations
and greater-than-pi/5 center separations preserve it under every
physical corner choice. The actual contacts CB,BA,AE are their
counterclockwise minor arcs. Thus their real three-contact lift has

    3pi/5 < Delta < 6pi/5 < 2pi.

The complete boundary-pair moment theorem gives CB strictly positive
and E-to-A strictly negative, the latter reversing the final A-to-E
traversal. These are original-origin moments at the actual original
applications, including all shared means. A's physical boundary
status suffices even when its total load is zero.

## 5. Original-origin inequalities with every sign case retained

Write O=(xi,zeta) in the local D chart and d_R=sqrt(R^2-1/4)-1.
C's minimum West support has original-origin height xi, so the
universal center/halfwidth bound gives xi<=d_R. E's actual minimum
n_E support is

    a_E=p(1-xi)+q(1-zeta)<=d_R.

The original E2 torque and negative EA moment give
q(1-xi)-p(1-zeta)<0. Substituting its strict inequality into a_E
yields a_E>(1-xi)/p, hence

    xi>1-p*d_R>=1-d_R>-1/60>-1/2.

The substitution is valid regardless of the sign of 1-xi; no
unproved original-origin height assumption enters.

If xi<=1, the same E2 torque immediately gives zeta<1. If xi>1
and zeta>=1, the bound xi<=d_R and q/p<=1 instead give

    0<xi-1<1/60,
    0<=zeta-1<(q/p)(xi-1)<=xi-1<1/60.

Then the actual point P_E=(1,1) of the physically boundary unit E
would be at original-origin distance below sqrt(2)/60. Every point
of such a unit has distance at least R-sqrt(2)>11/20, by its actual
circle corner and unit diameter. This is impossible. When d_R<=1,
xi>1 was already impossible. Thus zeta<1 holds throughout the full
original radius window and all physical masks.

## 6. Complete C3 and genuine E2 resultant signs

Use the actual C top-right point T_C, without changing P_C. About O
it is a left horizontal support (-X_C,h_C), where X_C=xi>-1/2
and h_C=r+1-zeta>0. The original full C3 equation remains

    F_C-mu*West-mu_CH*N+mu_CB*g_CB=0.

Its incoming vertical components are zero and the strictly positive
N_y. The actual outgoing CB moment is positive. The complete
reflected arbitrary-frame moment theorem c1694bb4 therefore gives
(F_C)_y>0: assuming a nonpositive value forces (g_CB)_y<=0,
whereas the unchanged y projection would then be strictly positive.
C has not acquired a two-force equation or concurrence.

The full arbitrary-frame center lemma at this same actual support
puts C's center in the upper left quadrant, with strictly negative
x and nonnegative y. Its angle may therefore be represented in
[pi/2,pi]; retaining the slightly weaker closed lower endpoint is
harmless.

The genuine E2 properness theorem applies because its actual neighbor
A physically touches the circle. It gives q_E=t_E F_E, t_E>0,
and q_E=P_E-O+ell*n_E with ell>=0. Since zeta<1, its vertical
component is 1-zeta+ell*q>0, so (F_E)_y>0. This uses the full
E circle mask and does not claim that a two-corner concurrence lies
inside E. All original DE and EA applications remain unchanged.

## 7. Complete arbitrary-owner E left support and the closed angular exit

At a vertex P_E, E's two actual inward orthonormal axes have
nonnegative dot product with n_E=(p,q). At most one can have
negative x component, since otherwise n_E would have nonpositive
x component. Such an axis w satisfies q*w_y>=-p*w_x>0,
so w_y>0 and -w_x<=q. Adding it, when present, and zero on
the other axis gives an actual minimum-x point Q=(1-M,y_T) with
0<=M<=q<1 and y_T>=1. If neither axis decreases x, P_E is
already such a point. Zero-component axes cause no exception.

For an owned E side, the full original tangential interval is
[-rho,1-rho]J n_E with rho in [0,1], and J n_E=(-q,p).
The actual left corner P_E+(1-rho)J n_E gives the same bounds,
including both endpoints. Thus every original E support owner is
covered without inferring one from the shared CD contact.

Let X_E=1-M-xi and h_E=y_T-zeta>0. Suppose X_E<=-1/2.
Since xi<=d_R and M<1, one also has X_E>-d_R>-61/60.
Adding E's actual horizontal halfwidth in [1/2,1/sqrt(2)] gives

    -31/60 < (c_E)_x < 1/4.

The actual Q has positive original-origin height. If (c_E)_y<=0,
its circumradius distance from Q implies |(c_E)_y|<1/sqrt(2).
Then |c_E|^2<(31/60)^2+1/2=2761/3600<25/16, contradicting
the boundary-center radius greater than 5/4. Thus (c_E)_y>0.
If (c_E)_x>0, its cosine is below (1/4)/(5/4)=1/5<1/2;
otherwise its angle is already at least pi/2. Therefore
pi/3<arg(c_E)<pi.

Together with C's angle in [pi/2,pi], this makes the difference
of representatives belong to (-2pi/3,pi/2). Its positive advance
below 2pi is consequently below pi/2 or above 4pi/3. Neither
belongs to the actual interval (3pi/5,6pi/5). A zero difference
does not supply a permissible distinct endpoint lift. The whole
closed supposition X_E<=-1/2 is therefore excluded, including
the equality endpoint, and X_E>-1/2 strictly.

## 8. Uniform path contradiction and exact remaining domain

The actual path C-B-A-E now has two real opposite supports with
positive original-origin heights, X_C,X_E>-1/2, positive full
vertical resultants, and exact span

    X_C+X_E=xi+(1-M-xi)=1-M<=1.

Its real counterclockwise center lift, including s=r=0, was proved
above. All four units are physically boundary. Thus every premise
of the complete R>=79/40 arbitrary-frame short-path theorem
34c9a023 holds. Its conclusion that the span exceeds one is a
contradiction. No endpoint side ownership is required by that
theorem, and no original force application is replaced by T_C or Q.

This proves the whole positive-length CD return under a free HD,
for L0124 and L124 with physically boundary A. The original CD
mean endpoints, coincident lower application, arbitrary E frames,
free or owned DE normals, all HC means, and all physical circle
coefficients remain covered. The source does not close free-HD
features with nonshared CD, or L124's physically clear A mask,
or either entire original graph/load family.

## 9. Exact direct input audit and preservation

All eleven current identities matched:

| Source | SHA-256 |
| --- | --- |
| BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md | c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b |
| SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md | 34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1 |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a |

The established exact terminal-LF reconciliations in the historical
moment source remain unchanged. No source was edited or repinned.
All actual squares, full H4/C3/D3 equations, true E2 equation,
original normals and means, physical masks and zero individual
weights remain. The original 2513/58 inventory is untouched.
I performed no numerical pose search, sampling, Lean compilation,
CI, workflow, metadata edit, commit, push or publication. Root
adoption is separate from this complete independent review.
