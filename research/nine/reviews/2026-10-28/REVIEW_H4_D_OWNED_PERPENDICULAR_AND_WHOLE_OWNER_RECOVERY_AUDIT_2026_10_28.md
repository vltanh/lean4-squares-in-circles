# Independent review of the perpendicular return and entire D-owned pentagon end

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the entire perpendicular D-axis return, including the
shared-CD feature, and for the exact whole D-owned-HD assembly.** The
auxiliary E top point is a point of the unchanged actual square used only
for a geometric support theorem. It replaces no original force application.
Free HD and the physically clear A mask of L124 remain outside this result.

## 1. Exact source and independent review scope

Reviewed source:
`INNER_PENTAGON_D_OWNED_END_PERPENDICULAR_RETURN_COMPLETE_EXCLUSION.md`.

- Bytes: 19,590.
- SHA-256: `d9a723f10d7d36fd4f818c85a9133094519bde38882b24defc4b40d0ced401cc`.
- Git blob: `e6bb495a9ad4d745ee3fee03f334b75562df8b9c`.

I read the complete source and independently rederived every new quadrant,
support, force, torque, coordinate, and angular argument. All fourteen
displayed current direct pins match the checkout exactly. The complete
arbitrary-frame moment theorem c1694bb4, full-radius short-path theorem
34c9a023, nonaxis caller 74013228, and same-axis caller 1ea45fff already
have my separate full mathematical reviews at their current bytes.
The present review checks the new perpendicular proof and each complete
caller join rather than treating those earlier reviews as its approval.

The literal original graph remains HA,HB,HC,HD,AB,BC,CD,DE,EA. H and D
are unloaded with true degrees four and three; C and E are loaded with
true degrees three and two. A,B,C,E are physically boundary. This is
the full displayed feature in H4_D0.L0124 and the physical-boundary-A
mask of H4_D0.L124. In that latter mask A's total circle coefficient
remains zero. All nine actual squares and every original force and mean
are retained.

## 2. Complete D3 table and genuine singleton entry

The full shared-HD exclusion, independently reread in the preceding
same-axis review, applies to these actual H4/D3 systems. Thus an original
D-owned HD here is a physical singleton, with D-side-interior point
P_H=(0,t), 0<t<1. H is genuinely nonparallel and has a unique rightmost
vertex there. The strict singleton convention excludes a point-only
parallel-side endpoint using that D axis.

After the permitted whole-configuration rotation and reflection, take
D=[0,1]^2 and the original D forces to H and C as (-gamma,0) and
(0,mu), with their unchanged applications (0,t) and (s,1), 0<=s<=1.
Full D balance gives the E force (gamma,-mu), whose application is
the strict D vertex P_E=(1,0). The actual D torque is

    gamma*t+mu*s-mu=0.

Therefore l=1-s is strictly positive, l<=1, and mu*l=gamma*t.
The original inward-to-E direction is consequently

    n_E=(p,-q)=(l,-t)/sqrt(l^2+t^2), p,q>0.

In particular p,q<1. The excluded s=1 endpoint is a consequence
of the original positive force equation and t>0, not an imposed
generic condition. The s=0 endpoint remains. CD may be shared with
any original mean; no three-singleton selector or E ownership is
deduced from that feature.

## 3. Full radius-free HC quadrant, all actual C support features

At H's unique rightmost point P_H, write the actual inward axes
(-a,-b),(-b,a), with a,b>0. Then max_y(H)=t+a<2. Every original
HC application S belongs to C in y>=1, so S_y>=1 and S_x<0: the
only H point with x=0 is P_H, whose height is below one.

For the actual H-to-C normal N, whole supporting half-planes give
N.P_H<=N.S<=N.P_C, and hence s*N_x+(1-t)*N_y>=0. If N_y<0,
this forces N_x>0. The dot product with H's upward axis (-b,a)
is then strictly negative, so every maximum-N point of H has height
at most t, contrary to S_y>=1. If N_y=0, East exposes P_H and is
again too low. West would require min_x(H)=max_x(C)>=s>=0,
contrary to H's strictly positive width to the left. Thus N_y>0.

I checked the complete subsequent N_x cover. For a tilted C with
bottom vertex P_C and inward axes u=(c,d), v=(-d,c), c,d>0:

- P_C and P_C+u have nonnegative x coordinate and cannot be S.
- At P_C+u+v both incoming cone generators have negative y
  component, contradicting N_y>0.
- At P_C+v the incoming generators u and -v both have strictly
  positive x component, so N_x>0.
- The lower-right side has nonnegative x throughout; the lower-left
  side has incoming normal u; the two upper sides have incoming
  normals -u or -v with negative y component.

This covers all vertices, sides, and closed normal-cone endpoints.
For aligned C=[r,r+1] times [1,2], the right side has x>=s>=0 and
the top face has height two, strictly above H. The remaining bottom,
left and lower-left support cones have N_x>=0. All original CD and
HC side means and both possible mean endpoints are covered. Therefore
the full quadrant N_x>=0, N_y>0 is valid without a force equation
at H or C and without a C-owned North axis assumption.

## 4. Real rim order and the full three-contact angular interval

At the D center, the C ray has angle in [45,135] degrees, the H
ray has angle strictly between 135 and 225 degrees, and the E ray
has angle 315 degrees. These actual applications are distinct. The
H ray is strictly in the counterclockwise sector from the C rim ray
to the E rim ray. Since the real H is in the bounded side of the
occupied rim, its positive orientation is D-C-B-A-E-D, including
any reflex angle. Compatible weak-junction resolutions elsewhere
preserve this order.

The operative occupied-rim theorem and physical embedding supply
simultaneous real circle accesses, including at a zero-load but
physically boundary A. They give the circular order C,B,A,E. The
strict corner-to-center deviation below pi/12 and pairwise center
separation greater than pi/5 prevent any order reversal. The actual
CB,BA,AE contacts are their displayed counterclockwise minor arcs.
Thus the actual lift from C to E has three gaps each in
(pi/5,2pi/5), so

    3pi/5 < Delta < 6pi/5.

The original directed boundary moments are accordingly CB positive
and EA negative. These are original-origin moments at the original
applications, not at the auxiliary point used later. The E-to-A
direction reverses the last path edge A-to-E, explaining its sign.

## 5. Original-origin inequalities and the strict full-C3 torque exit

Write the unchanged circle origin in local D coordinates as
(xi,zeta), and k=1-xi. The genuine E2 torque and the negative
EA moment give

    det(P_E-O,n_E)=-q*k+p*zeta<0.

The actual E minimum support height along n_E is
a_E=p*k+q*zeta<=d_R, where d_R=sqrt(R^2-1/4)-1. The universal
support bound is valid in every actual frame: farthest-corner
containment gives center radius at most d_R+1/2, and every unit
halfwidth is at least 1/2. Since k>(p/q)zeta, one has
a_E>zeta/q. Therefore zeta<q*d_R<d_R. This substitution is valid
also when zeta is negative. C's North support separately gives
1-zeta<=d_R. Hence

    1-d_R <= zeta < d_R.

No height sign is read from the translated D chart.

Suppose xi>=s. Then k<=l and the same E2 moment gives
zeta<(t/l)k<=t<1. At every original HC application S, one has
S_x-xi<0, S_y-zeta>0, N_y>0 and N_x>=0. Its actual moment is
therefore strictly negative. But full C3 torque gives exactly

    mu_CH det(S-O,N)
      = mu_CB det(P_CB-O,g_CB)-mu*(s-xi)>0.

The first term is strictly positive, and the last subtraction is
nonnegative under xi>=s. This contradicts the geometric negative
moment. Thus xi<s strictly. The equality xi=s is covered by the
same contradiction. The actual HC force and original CD term are
both indispensable and have been retained; C is never treated as
a two-force tip.

## 6. Full C3 resultant sign and center quadrant

Use the oriented orthonormal chart e=South, f=East; det(e,f)=1.
The original C support is a left support at

    (-X_C,h_C), X_C=1-zeta>1-d_R>-1/60>-1/2,
    h_C=s-xi>0.

The full C3 equation is
F_C-mu*North-mu_CH*N+mu_CB*g_CB=0. Its incoming f components
are zero and N_x>=0; its outgoing CB moment remains positive
under the orientation-preserving rotation. The complete reflected
full-star theorem c1694bb4 therefore gives (F_C)_x>=0. Equality
is correctly retained when N_x=0; a strict sign is not required.
The argument uses C's arbitrary actual support frame and preserves
every physical circle-corner coefficient.

The complete center lemma of 34c9a023 now applies to this same left
support. It makes the actual C center's f component nonnegative
and its e component strictly negative. In the original D axes this
is (c_C)_x>=0 and (c_C)_y>0. Thus its actual representative angle
satisfies 0<arg(c_C)<=pi/2. The endpoint pi/2 remains included.

## 7. Every E support owner admits the required actual top point

The original DE point remains P_E=(1,0). At an E vertex there,
its actual inward orthonormal axes both have nonnegative dot product
with n_E=(p,-q). At most one can have positive vertical component:
if both did, expanding n_E in those axes would make its vertical
component nonnegative, contradicting -q<0. Any positive-height
axis w satisfies p*w_x>=q*w_y>0, so w_x>0 and w_y<=p by the
unit-length identity. Taking that axis, when present, and zero on
any nonpositive-height axis gives an actual top point Q with

    Q=(x_T,M), x_T>=1, 0<=M<=p<1.

If no axis increases height, P_E itself is such a point. A zero
vertical component leaves a top side, and the same chosen endpoint
is legitimate as a purely geometric support point.

If P_E is on an owned E side, the complete original pose is
P_E+[0,1]n_E+[-rho,1-rho]J n_E, retaining rho in [0,1]. Since
J n_E=(q,p), its actual top corner has x_T=1+(1-rho)q and
M=(1-rho)p. This proves the identical bounds for all side positions
and closed endpoints. No E ownership is asserted in the vertex case,
and no physical support face is missed.

The genuine E2 properness theorem is applicable because A is an actual
boundary neighbor. It supplies q_E=t_E F_E, t_E>0, and
q_E=P_E-O+ell*n_E, ell>=0. The newly proved xi<s gives k>l>0,
so (F_E)_x=(k+ell*p)/t_E>0. No assertion that a two-corner
concurrence lies inside E is needed. The auxiliary Q has not entered
any force or torque equation.

## 8. The full angular exit for the top-height equality and upper branch

Let Y=M-zeta be Q's original-origin height. Suppose Y>=1/2.
From M<=p<1 and zeta>=1-d_R, one gets
1/2<=Y<d_R<61/60. E's actual vertical halfwidth belongs to
[1/2,1/sqrt(2)], so its actual center satisfies

    -1/4 < (c_E)_y < 31/60.

The top point Q has original-origin x coordinate at least k>0.
If (c_E)_x<=0, its distance from Q at most the circumradius
forces |(c_E)_x|<1/sqrt(2), strictly because Q_x>0. Thus

    |c_E|^2 < 1/2+(31/60)^2=2761/3600<25/16,

contradicting the physical boundary-center radius greater than 5/4.
Consequently (c_E)_x>0. If its vertical component is negative,
the lower bound -1/4 and radius greater than 5/4 give
sin(arg(c_E))>-1/5>-1/2. In all cases its actual angle therefore
lies strictly between -pi/6 and pi/2.

Combining this with the actual C representative in (0,pi/2], their
difference is in (-2pi/3,pi/2). The unique positive counterclockwise
advance below 2pi is then either below pi/2 or above 4pi/3. A zero
difference cannot give a permissible distinct endpoint lift. Neither
alternative belongs to the actual three-contact interval
(3pi/5,6pi/5). This is a contradiction.

Every inequality needed for this argument remains strict at the
supposed Y=1/2 endpoint. Hence the proof establishes the full
strict conclusion Y<1/2, including the entire equality branch.
It uses actual center directions rather than circle-resultant
directions or an abstract graph order.

## 9. Opposite-support theorem and complete D-owned assembly

In the same e=South, f=East chart, the actual top support Q of E
is a right support with

    X_E=zeta-M=-Y>-1/2,
    h_E=x_T-xi>=k>l>0.

Together with the original C support, its exact span is
X_C+X_E=1-M<=1. Both support heights are positive, both horizontal
support coordinates exceed -1/2, and both full circle resultants
have nonnegative f component, with E's strict. The four original
boundary units C,B,A,E and their actual touching path supply the
previously proved center lift. All hypotheses of 34c9a023 hold
throughout the original R>=79/40 window, including its lower
radius endpoint. Its strict span conclusion greater than one is
the contradiction. No endpoint owns the auxiliary support direction
as a premise.

The complete D-owned-HD normal cover is now exact. The actual
D-H-C triangle excludes the D axis opposite DH. Every other
original DC normal is either nonaxis, the same D axis as DH,
or perpendicular to it. The complete source 74013228 excludes
the nonaxis class, 1ea45fff excludes the same-axis class, and
the present proof excludes both perpendicular axes by a whole
reflection. These sources have identical four-physical-boundary
scope. Thus the entire D-owned HD feature is excluded in L0124
and in L124's physical-boundary-A mask.

The earlier whole H-owned union has that same physical-boundary-A
extension, as checked in the separate same-axis review. This still
leaves free HD. L124's physically clear A mask has not acquired a
physical circle point or positive circle weight from this assembly.
Neither entire original graph/load row nor a coarse parent is closed.

## 10. Direct identities and preservation

All fourteen current identities matched the displayed table:

| Source | SHA-256 |
| --- | --- |
| BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md | c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b |
| SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md | 34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1 |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 |
| INNER_PENTAGON_D_OWNED_END_NONAXIS_C_RETURN_EXCLUSION.md | 74013228a4c4d762938fa5f7fe72c1c9d447508bbfae14b11c7f9902220bffd0 |
| INNER_PENTAGON_D_OWNED_END_SAME_AXIS_RETURN_COMPLETE_EXCLUSION.md | 1ea45fff7d584312dfd41f004e56f8ca5da805c7c17d6622c39bacad2f77779a |

The earlier exact terminal-LF reconciliations inside the shared-end and
moment-orientation inputs remain unchanged. No historical source was
edited or silently repinned. The actual D3, H4 and C3 remain full;
only the genuine E2 receives a two-force properness theorem. Every
original mean, physical mask, individual zero coefficient and actual
unit is retained. The auxiliary support point is never substituted
into an original equation. The original 2513/58 identifiers remain.

I performed no pose sampling, numerical exclusion, Lean compilation,
CI, workflow, metadata edit, commit, push, or publication. The only
tool calculation for this review checks exact source-byte identities.
This is a complete independent hand review; root adoption is separate.
