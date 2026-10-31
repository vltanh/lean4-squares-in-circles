# Independent review of the complete D-owned same-axis pentagon return

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Verdict: PASS for the entire stated original feature and its explicit
physical-boundary-A assembly, at the exact frozen bytes below.** The proof
uses the real D3, C3 and E2 equations and the actual occupied rim. It does
not require side ownership at C or E. No whole original family is closed.

## 1. Exact source and scope

Reviewed source:
`INNER_PENTAGON_D_OWNED_END_SAME_AXIS_RETURN_COMPLETE_EXCLUSION.md`.

- Bytes: 17,377.
- SHA-256: `1ea45fff7d584312dfd41f004e56f8ca5da805c7c17d6622c39bacad2f77779a`.
- Git blob: `b5d8c1e58dab7748f98c92abdac9b077753993f6`.

I read the entire new source and independently rederived all its geometry,
force signs, torque signs, coordinate bounds, and caller joins. I checked
all fifteen displayed current direct pins against the checkout; all match
exactly. The complete general theorems at c1694bb4 and 34c9a023 have their
own fresh full reviews by this reviewer. In particular the latter is
valid at every R>=79/40, rather than only at R>=2.

The original graph is HA,HB,HC,HD,AB,BC,CD,DE,EA. The unchanged true
degrees are unloaded H4 and D3, loaded C3 and E2, and the original
degree-three A and B. A,B,C,E are physically boundary. This covers all
of the displayed D-owned HD / same-D-axis DC feature in H4_D0.L0124,
and precisely the physical-boundary-A mask of H4_D0.L124. In the latter
mask A keeps its zero total circle coefficient. All nine actual squares,
all three completions, and every original equation remain.

## 2. Complete singleton entry and the equal-mean exit

The actual shared-HD exclusion applies to these full H4/D3 stars without
using an equation at A or E. I reread its whole proof and the operative
both-end-axis proof: full H4 first gives the required opposite-end
height bound; a shared aligned D and its full D3 force then place E
strictly above that bound, contradicting the actual AE edge. Its
strict support-span argument covers all side means and axis endpoints.
The both-end-axis input uses all four hub terms and treats the final
zero-slider CD point using the strict original normal, not an axis
substitution. These are radius-free physical reductions.

Consequently the D-owned HD here is a physical singleton. Under the
unchanged strict convention its point P_H=(0,t) has 0<t<1, and H has
a unique maximum-x vertex there with both inward axes strictly in the
left half-plane. Parallel H would create positive-length overlap at
such a D-side-interior point, so it is not an extra feature.

The same-axis DC point P_C=(0,s) retains its full original interval
0<=s<=1, including an aggregate side mean. If s=t, D's tangent sector
at the common point is the whole right half-plane. H's right-angle
sector lies strictly inside the complementary left half-plane. Each
of the two remaining left angular gaps is strictly smaller than a
right angle. C has a connected physical tangent sector of angle at
least a right angle. Such a sector cannot fit into either gap, cross
H's open sector, or enter D's open sector. This proves s!=t even
when the unchanged C application is a side point or segment endpoint.
No distinct-contact assumption is added to avoid this case.

A whole-packing vertical reflection takes s<t to t<s, while
transforming every normal, weight, application, and circle coordinate
together. It changes no load role. Thus the retained t<s chart is
exhaustive.

## 3. Full D3 and the strict original HC normal sign

With the original D vectors (-gamma,0) and (-mu,0), the full unloaded
D3 balance gives the E vector (gamma+mu,0). Its actual support is
P_E=(1,u), with E entirely in x>=1 and the original u in [0,1].
The complete D torque about its local corner gives exactly

    u=(gamma*t+mu*s)/(gamma+mu),
    t<u<s.

Both magnitudes are strictly positive. Thus the actual DE mean is
strictly between the two original left means, but it is never replaced
by a selected midpoint. The proof does not require either CD or DE
to be a singleton or an owned C/E axis.

Let N be the original H-to-C normal at its actual HC support. Since
P_H belongs to H and P_C belongs to C, their real supporting
half-planes give N.P_H<=N.S<=N.P_C. Hence (s-t)N_y>=0. If N_y=0,
an East normal forces min_x(C)=max_x(H)=0, contradicting C's
positive width and max_x(C)=0. A West normal instead forces
min_x(H)=max_x(C)=0, contradicting H's positive width. Therefore
N_y>0. This is a statement about the full physical units and covers
every original HC mean and owner.

The source's phrase about a horizontal normal vertically separating
the units denotes separation by a vertical line; the explicit min/max
coordinate argument fixes its mathematical meaning. It introduces no
opposite sign and needs no source change.

## 4. Original-origin supports and quantitative domain

If the circle origin has local D coordinates (xi,zeta), the actual
supports about that unchanged origin are

    P_C=(-X_C,h_C), X_C=xi, h_C=s-zeta,
    P_E=( X_E,h_E), X_E=1-xi, h_E=u-zeta.

Thus X_C+X_E=1 and h_C-h_E=s-u>0 exactly. A local positive D
coordinate is not mistaken for a positive original-origin height.

I also rederived the arbitrary-frame minimum-support bound used for
X_C and X_E. For a unit center of radius r, a farthest corner has
squared norm at least r^2+r+1/2: its two absolute own-center
coordinates have sum at least r. Hence
r<=sqrt(R^2-1/4)-1/2. Every horizontal halfwidth is at least 1/2,
so every minimum support coordinate is at most
d=sqrt(R^2-1/4)-1. Applying this in the West and East directions
gives X_C,X_E<=d. Combined with their exact sum, it gives
X_C,X_E>=1-d>-1/60>-1/2. The strict d<61/60 follows from the
stated upper radius bound and the positive comparison
sqrt(1041)/16<121/60. Neither C nor E is assumed aligned in this
bound.

## 5. Actual local sector, occupied rim, and boundary moments

At the actual D center, the left ray to (0,s) precedes the left ray
to (0,t) counterclockwise because t<s. The E ray points into the
right half-plane. Thus the strict H ray is in the counterclockwise
sector from the C rim ray to the E rim ray. Since the real H is in
the bounded rim side, the positive rim orientation is

    D -> C -> B -> A -> E -> D.

This is the correct local interior-sector rule at a positive rim
vertex, including a reflex angle. It does not rely on convexity of
the center polygon. The three D applications are distinct, so no
ambiguous local junction order is concealed here. Compatible weak
junctions elsewhere preserve the orientation.

I reread the operative occupied-rim construction, including its
physical center/contact loop, compatible resolutions and simultaneous
circle accesses. The real outward accesses carry the rim order to
the circular order C,B,A,E. A zero-load but physically boundary A
may be supplied with its actual circle access in the same unit;
this uses physical incidence and does not create a circle force.
The construction explicitly retains such unmarked physical boundary
units and their possible additional spokes.

The corner-to-center angular intervals cannot reverse this order:
each actual corner differs from its own center direction by less
than pi/12, while different boundary centers are more than pi/5
apart. Physical contact neighbors have their appropriate minor arc;
the opposite arc here contains the other two named boundary centers.
Consequently the real center path C-B-A-E has a strictly increasing
counterclockwise lift of total advance less than 2*pi, and each
successive advance is minor and less than pi. This establishes the
precise path premise of 34c9a023, not just an abstract rim order.

The complete actual boundary-contact moment theorem therefore gives
det(P_CB,g_CB)>0 and det(P_EA,g_EA)<0. The second directed pair
E->A reverses the last path traversal A->E, explaining its sign.
Both determinants use the original circle origin and the original
applications, including any shared-side means. Physical A status
suffices in both cases.

## 6. Genuine E2, then full C3: no missing force

The real E-to-D force is -mu_DE East. Its true two-contact torque,
with the zero torques of all actual radial circle atoms, gives

    det(P_E,East)=(mu_EA/mu_DE)det(P_EA,g_EA)<0.

Since the left side is -h_E, the actual original-origin height is
h_E>0, and the already proved difference gives h_C>h_E>0.

The complete proper two-force theorem applies to this genuine
loaded E2 because its actual neighbor A physically touches the
circle. It supplies q_E=t_E F_E, t_E>0, and
q_E=P_E+ell East, ell>=0. Thus (F_E)_y=h_E/t_E>0. No premise
that q_E lies in a two-corner E is made or needed. All physical
circle weights, including a zero individual coefficient, remain.

At C, the source retains its three actual pair terms:

    F_C - mu_CD*(-East) - mu_CH*N + mu_CB*g_CB = 0.

This has the correct physical directions: C points East toward D
and opposite N toward H. If (F_C)_y<=0, the reflected force-free
theorem c1694bb4 applies to C's actual max-x support, since
X_C>-1/2, h_C>0 and R>sqrt(2). The actual positive CB moment then
forces (g_CB)_y<=0. The y projection of the unchanged equation is

    (F_C)_y=mu_CH*N_y-mu_CB*(g_CB)_y>0,

a contradiction. Therefore (F_C)_y>0. This is genuinely a full
C3 argument; it assigns C no concurrence and needs no owned CD
axis. The strict positive HC contribution is retained.

## 7. Uniform path application and exact residual assembly

The actual four-unit boundary path C-B-A-E now satisfies every
hypothesis of 34c9a023: the real minor counterclockwise lift, all
four physical boundary statuses, both original support half-planes,
X_C,X_E>-1/2, both positive original-origin heights, and both full
positive vertical resultants. Their support span is exactly one.
The complete radius range in this caller is contained in that
theorem's R>=79/40 range. Its strict conclusion X_C+X_E>1 is the
required contradiction. No separate C/E orientation or mask case is
left to a numerical search.

I also checked the source's explicit extension of the two previous
H-owned-HD theorems to L124 with physically boundary A. The complete
H4/D3 fixed-return and side-feature reductions are radius-free and
already cover both load representatives. The return-height input
23bb6ede states explicitly that its A-side conclusion does not
depend on whether A is loaded; its proof uses physical AB and AE
contacts, and its force identities use the full H4 and D3 only.
In the strict-Northeast and East exclusions, the later uses of A
are exactly the physical rim circle access, actual boundary-pair
moment, and physical boundary neighbor in the genuine E2 theorem.
Their C3 tangent proofs neither use F_A nor suppress A's third force.
I reread these operative joins and the East branch's complete
tilted/aligned face cover. Thus the claimed physical-boundary-A
extension is valid while all original zero A coefficients stay zero.

The preceding complete D-owned nonaxis theorem explicitly has the
same physical-boundary-A scope and was independently reviewed at its
current bytes. Joining it with the present same-axis exit leaves
only D-axis returns perpendicular to the D-owned HD axis. The
opposite East DC axis is forbidden by the actual degree-free D-H-C
triangle rule against the West HD axis. A whole-packing vertical
reflection puts the surviving perpendicular pattern in West/North
form without changing roles. Its means and endpoints remain open.
Free HD and L124's physically clear A mask are separate unresolved
domains. This is an interface assembly, not whole-family credit.

## 8. Complete direct-pin audit

Every following current SHA-256 matched the new source's displayed
table byte for byte:

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
| INNER_PENTAGON_FOUR_BOUNDARY_H_OWNED_END_STRICT_NORTHEAST_EXCLUSION.md | d35d1d95347becdf45f4381db0f2d7cd16ff8dac92a525ff1979bb3c76e4759f |
| INNER_PENTAGON_H_OWNED_END_EAST_RETURN_TANGENT_AND_COMPLETE_FOUR_LOAD_EXCLUSION.md | 413a3ba7229f4685dff19253337d86bc89c0d30b18d8cda7a9f0bcc51f720c6a |
| INNER_PENTAGON_D_OWNED_END_NONAXIS_C_RETURN_EXCLUSION.md | 74013228a4c4d762938fa5f7fe72c1c9d447508bbfae14b11c7f9902220bffd0 |

The three historical direct pins inside the shared-end and both-end-axis
inputs remain the already recorded exact current-bytes-plus-one-LF
identities for the triangle, physical embedding, and load-cover files.
The two historical boundary-moment pins likewise remain their recorded
current-bytes-plus-one-LF identities. No frozen source was repinned or
edited. This audit verifies the operative mathematical uses; it does not
claim a new review of every unrelated theorem in the full transitive
repository history.

All actual units, full equations, physical masks, zero individual
weights, original side means and the original 2513/58 identifiers are
preserved. I performed no Lean compilation, CI, workflow, pose sampling,
metadata change, commit, push, or publication. Root adoption is separate.
