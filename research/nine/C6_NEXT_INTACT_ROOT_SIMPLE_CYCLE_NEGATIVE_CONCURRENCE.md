# Every remaining genuine simple cycle at an intact root has negative root concurrence

Date: October 27, 2026.

**Status: complete proposed uniform necessary reduction, frozen for full
root and separate independent review.** The nonparallel theorem covers
all actual endpoint masks, including parallel radial-S endpoint stars.
Its further convex force-polygon conclusion explicitly requires both
endpoint stars to be nonparallel. No whole C5, C6, C7, original cell,
global bound, or equality classification is declared closed here.

Keep the same nine actual unit squares, common canonical radius/Phi
packing, selected physical certificate and all original forces in

    79/40<=R<=sqrt(1105)/16.

Let E-P-Q-E be an actual intact triangle. Assume the complete original
component has the normal form of

    GLOBAL_NEXT_INTACT_ROOT_UNLOADED_MOMENT_AND_BLOCK_REDUCTION.md
    103a0f4ceccba044c132a45c632bd64df57540feb70fd69d6159c52759e449c6,

and its one other cyclic block is the genuine simple cycle

    E-T_1-...-T_m-E, m>=4.

Thus E retains its entire intact-petal star and zero or one genuine
direct S/D leaf. Every private T_i has true positive degree two and
no other original positive pair force. No physical circle corner,
individual zero weight, actual force, shared-side mean, completion
unit, or physical zero-stress contact is discarded.

Write u,v for the actual E-to-T_1 and E-to-T_m force vectors, including
their original positive magnitudes, and p_A,p_C for their actual
applications. Put A=T_1, C=T_m and let M be the full private cycle
circle sum. The normal form gives

    M=u+v,          c_E dot M<0.                         (1)

The separately complete equal- and opposite-parallel exclusions give
that u,v are nonparallel. Their pins are 0d534b23 and fc07a3b7 in
Section 8 below.

**Theorem 1.** The two actual root lines concur at

    q=-sigma M,       sigma>0.                         (2)

In particular c_E dot q>0. This is a necessary geometric reduction,
not a proof that q belongs to E or that both actual E ports are proper.

**Theorem 2.** If both A and C have nonparallel true loaded2 stars,
every private loaded star is nonparallel. Their genuine positive
radial concurrences, together with q, form a strictly convex polygon
containing O in its interior. Every polygon edge follows the actual
positive directed channel force with a strictly positive coefficient.
This auxiliary force polygon is not asserted to be a physical empty
region or to contain the full root square.

## 1. Original moments, endpoint loads, and at least three private loads

The full normal form gives O in int E, physical clearance of E, and
two distinct positively circle-loaded cycle neighbors of E. Since
the root degree within this block is two, these are exactly A,C.

The degree-free intact-block theorem 8def789e proves that every
positive edge between actual units other than E has nonzero original
origin moment. The private path has such an edge. Its true private
torque equations, including each full radial circle system, therefore
give one common nonzero directed cycle moment. Orient the actual
cycle so that

    det(p_A,u)=k>0,       det(p_C,v)=-k.                (3)

Every actual directed private path force has this same moment k.
Summing only the unchanged private equations gives (1), while
summing their moments gives the cancellation in (3). No E force
equation has been shortened.

There are at least three private loaded bodies. Otherwise A,C would
be the only two, and the actual A-to-C private path would contain
m-2>=2 unloaded true2 transmitters. Its normal reserve would be at
least two. The actual unit E physically touches both endpoints, so
UNIT_BYPASS_NORMAL_CHANNEL.md Sections 1--2 bounds that same reserve
by sqrt(2), a contradiction. This uses every original channel width
and mean; it does not create a new A/C contact.

List the t>=3 private loaded bodies in their actual path order,
with A first and C last. Write F_j for their unchanged whole positive
circle resultants.

## 2. Precise local star extraction, independent of the root-pair case

Sections 2--2.1 of fc07a3b7 give a complete local extraction whose
proof does not use opposite parallel root forces. Its inputs are
only the just-established nonzero private moment, true2 private
stars, loaded endpoints A,C, circle containment, and the unchanged
compatible normal selection. The extraction is retained here at
that scope, not as the isolated-cycle conclusion of cd2a8c76.

For clarity, its whole parallel cover is as follows. A loaded true2
parallel star must be radial D or radial S; the physical support
classification and weighted-mean torque include every physical mask
and zero individual weight. D makes the original moment zero and
is excluded by (3). An S star has its two actual nonzero inner-side
means on opposite sides of its radial axis.

For an interior loaded body, its nearest loaded bodies in both
private directions exist, are distinct, and are reached without
passing through E. If that body were S, its two channels would have
reserves from {0,1,sqrt(2),2}. Reserve zero is excluded by the full
radial-S inner-face boundary geometry; reserve one places the far
loaded port too near O. Two diagonal transmitters overlap. A reserve
two paired with a diagonal forces the latter endpoint circle-clear,
by the exact complete far-corner comparison at R^2>=17/4. Two
reserve-two channels violate the actual distinct-endpoint matching
theorem. Longer reserves have already been excluded by containment.
These are the exhaustive local cases in fc07a3b7 Section 2.1.

Consequently every interior private loaded body is nonparallel.
The endpoint bodies A,C are each either nonparallel or radial S.
No true2 equation is assigned to E in this argument.

At every nonparallel loaded true2 body, the complete conditional
proper-concurrence theorem, 8608a7ab Section 3, gives

    q_j=t_j F_j, t_j>0,
    p-q_j=ell n, ell>=0,                              (4)

for every actual outward port. It imposes no boundary-neighbor
premise. The two-circle-corner case and all original means remain;
in that case q_j is not asserted to lie in its physical square.

## 3. Strict private angular order, including both S endpoints

For consecutive nonparallel private loaded bodies, the actual
channel and (4) give

    q_(j+1)-q_j=L_j f_j,       L_j>=0,
    det(q_j,f_j)=k>0,                                 (5)

where f_j is its unchanged positive directed force. A nonempty
channel has L_j>0. For a direct contact, L_j=0 would identify two
distinct positive radial resultant directions. Those directions
are distinct: boundary centers are separated by more than pi/5,
and every actual circle corner or whole positive resultant lies
within pi/12 of its own center direction. Thus L_j>0 also at every
direct contact. Equation (5) implies

    det(F_j,F_(j+1))>0.                               (6)

If A is S, use its actual radial direction e_A. Its root force is
u=mu e_A with mu>0, and its directed private outgoing force is
-b e_A, b>0. In (e_A,J e_A) coordinates, the unchanged private
application has height k/b>0 by (3). The next loaded body is
interior and nonparallel; its proper concurrence lies on that same
positive-height line. This proves (6) for the first pair.

If C is S, use its own radial direction e_C. Its root force is
v=nu e_C, nu>0, while the incoming private directed force is
a e_C, a>0. Its unchanged private application has height -k/a<0
in (e_C,J e_C) coordinates. The preceding proper concurrence is
on that same line, so det(F_(t-1),F_C)>0. These arguments preserve
both actual S means and require no finite S concurrence.

Use the same physical embedding and the actual circle spokes as
in fc07a3b7 Section 5. The exterior-annulus order theorem gives
the private resultants either CCW or CW in the actual path order.
Each CW gap would exceed pi by (6). There are t-1>=2 disjoint
successive such gaps, impossible on one circle. Hence the actual
order is CCW. Choose its lifts

    theta_A=0<theta_2<...<theta_C=gamma<2pi.           (7)

Every successive private gap is strictly less than pi by (6).

Every actual circle corner of each intact tip and optional direct
E leaf lies in the complementary root arc

    gamma<theta<2pi.                                 (8)

This is the complete physical edge-plus-spoke location argument
in fc07a3b7 Section 5: a tip-to-circle path starts at E on the
cycle, avoids every private spoke, and preserves annular order.
All physical corners can be included simultaneously. Disjoint
corner intervals put them strictly between the full endpoint
resultant directions, including individual zero-weight endpoints.
The same argument needs no equation treating E as true2.

Let F_out be the unchanged sum of all component circle atoms
outside the private cycle. The normal form identifies exactly the
intact tips and optional direct leaf; E is physically clear.
The full original component balance is therefore

    F_out+M=0.                                      (9)

No force from another positive component is inserted or removed.

## 4. Exact endpoint angles of the original root forces

If A is nonparallel, (4) at its E-facing port says

    q_A=p_A+alpha u, alpha>=0.

Since E contains O openly, p_A dot u>0. Thus q_A dot u>0,
while det(q_A,u)=k>0 by (3). The actual direction of u therefore
has the unique lift beta_A with

    0<beta_A<pi/2.

If A is S, put beta_A=0, since its actual u is positive radial.
In both cases the direction of u is theta_A+beta_A=beta_A.

At a nonparallel C, q_C=p_C+beta v with beta>=0. The same open
support gives q_C dot v>0, and det(q_C,v)=-k. Consequently
the actual direction of v is gamma-beta_C for

    0<beta_C<pi/2.

For C of type S put beta_C=0. Define the real angle difference

    delta=gamma-beta_A-beta_C.                       (10)

These bounds cover every original physical endpoint mask, mean,
and zero proper-length limit. In particular beta is positive
whenever the corresponding star is nonparallel, even if its
proper application coefficient in (4) is zero.

## 5. Long and antipodal private arcs force positive root determinant

Suppose gamma>pi. Equation (10) gives

    0<delta<2pi.

If delta>=pi, the closed angular cone from the v direction
gamma-beta_C to the u direction 2pi+beta_A has width
2pi-delta<=pi. It contains both actual root vectors u,v, and
every outside circle atom from (8) is strictly inside that cone.
For width<pi, a positive projection on its bisector contradicts
u+v+F_out=0. For width exactly pi, the endpoint projections are
zero and every actual outside atom has strictly positive
projection. The intact tips have positive total load, so this
again contradicts (9). Hence

    0<delta<pi,      det(u,v)>0.                      (11)

If gamma=pi, (10) gives 0<delta<=pi. Equality would require
both endpoints to be S, making u+v horizontal. Every private
resultant strictly between the endpoints has positive vertical
projection, and there is at least one such load. Thus M is not
horizontal, contradicting M=u+v. Again (11) holds.

Let q be the intersection of the nonparallel original root lines.
The moment sum (3) gives det(q,M)=0, so q=t M for a real t.
Using the first root moment yields

    k=det(q,u)=-t det(u,v).                           (12)

Equations (11)--(12) prove t<0 in both arc cases.

## 6. Short private arcs, all endpoint alternatives

It remains to consider 0<gamma<pi. The full private circle sum
M lies strictly inside the cone between F_A and F_C. All the
original private resultants lie in this cone, and both endpoint
weights are positive; the interior loads remain positive as well.

If A is S, u has angle zero. If delta<=0, v has angle in
(-pi/2,0], and the positive sum u+v has angle at or below zero.
This contradicts the strict endpoint-cone placement of M.
Thus delta>0; (10) gives delta<pi. If C is S, the reflected
argument applies: delta<=0 would place u at or above angle gamma,
so u+v could not lie strictly below gamma in the endpoint cone.
This includes the case where both endpoints are S. Equations
(11)--(12) again give t<0.

Assume now both endpoints are nonparallel. Their actual positive
radial vectors q_A,q_C are independent. The entire private sum
has an expression

    M=A_0 q_A+B_0 q_C,        A_0,B_0>0.              (13)

Write, with initially arbitrary real a,b,

    q_A=q+a u,        q_C=q+b v.

Comparing coefficients of the independent u,v in (13) gives

    A_0 a=B_0 b=1-t(A_0+B_0).                        (14)

Neither a nor b is zero: then both would be zero, identifying
the distinct positive radial q_A,q_C. They have the same sign.

They cannot both be negative. Indeed (4) at the real endpoints
would then put q strictly on both distinct outward normal rays
of the closed convex E. For p+lambda n, lambda>0, with n an
actual outward unit normal, every x in E satisfies

    |p+lambda n-x|^2
      =lambda^2+|p-x|^2+2lambda n dot(p-x)>=lambda^2,

with equality only at x=p. Thus p is the unique nearest point
of E to q. The two root ports would have to coincide; their
nonparallel strict rays cannot then meet away from that point.
This contradiction proves a,b>0.

Put Delta=det(u,v). The genuine moments and endpoint determinant
give

    k=-t Delta>0,
    det(q_A,q_C)=[t(a+b)+ab]Delta>0.                 (15)

The second sign follows from the strict short arc. If t>=0,
the first identity forces t>0 and Delta<0, while the bracket in
the second is positive. This is impossible. Therefore t<0,
proving Theorem 1 in the last case and hence in every case.

## 7. Convex auxiliary polygon when both endpoint stars are nonparallel

All private loaded stars are then nonparallel by Section 2.
In the short-arc case the coefficients a,b from Section 6 are
strictly positive. In the long or antipodal case, (8)--(9) and
q=-sigma M=sigma F_out put the direction of q strictly within
the complementary root arc gamma<theta_q<2pi. That arc has width
at most pi. Hence

    det(q,q_A)>0,        det(q_C,q)>0.

Since det(q,u)=k and det(q,v)=-k, the same identities with
q_A=q+a u and q_C=q+b v again give a,b>0.

For the short arc, (13) places M strictly between angles zero
and gamma, so q=-sigma M has angle between pi and pi+gamma.
It too belongs to the complementary root arc, and each of its
two angular gaps to q_A,q_C is strictly less than pi.
Thus in all cases the ordered vertices

    q, q_A, ..., q_C

have their actual cyclic radial order around O, every successive
angular gap lies in (0,pi), and all closing/root coefficients
a,b and private channel coefficients L_j are strictly positive.
The polygon is simple: each edge has strictly positive angular
advance within its own radial sector, whose interiors are
disjoint from those of all other edges. Its total winding is one.

At a private loaded vertex, let f_- and f_+ be the unchanged
incoming and outgoing directed forces. Its true equation is
F_j=f_--f_+. By (4) and the common moment,

    det(f_-,f_+)=det(F_j,f_-)=k/t_j>0.                (16)

At q the incoming direction is -v and the outgoing direction is u,
so the turning determinant is det(-v,u)=det(u,v)>0 by (12)
and t<0. The actual positive edge coefficients preserve these
strict turns. A simple polygon whose every interior turn is
strictly positive is strictly convex. Its winding already places
O in its interior. This proves Theorem 2.

The real E ports still have their original positions on the two
root lines. They are not assigned nonnegative distances from q.
The auxiliary polygon is not substituted for the actual occupied
units, and its convexity is not a whole-unit capacity theorem.

## 8. Exact source pins and remaining scope

The precise current inputs are:

| Source | SHA256 |
| --- | --- |
| GLOBAL_NEXT_INTACT_ROOT_UNLOADED_MOMENT_AND_BLOCK_REDUCTION.md | 103a0f4ceccba044c132a45c632bd64df57540feb70fd69d6159c52759e449c6 |
| GLOBAL_NEXT_DEGREE_FREE_MOMENT_PORT_ORDER_AND_INTACT_BLOCK_EXCLUSION.md | 8def789e0cde632795f81d8ecf92d6dd3642b37fd4ca6e79cc4890594264fd49 |
| C6_NEXT_EQUAL_PARALLEL_ROOT_PAIR_NEGATIVE_PRESSURE_EXCLUSION.md | 0d534b2399f6d01d59c2caa121bc440957bb66bf08840e9e6da5bbff7a990f72 |
| C6_NEXT_INTACT_ROOT_SIMPLE_CYCLE_OPPOSITE_PARALLEL_EXCLUSION.md | fc07a3b7dd840b17eb13caba1d36193724afdea68c9c0acd23bfdc66a574017f |
| UNIT_BYPASS_NORMAL_CHANNEL.md | db073cd024a4f2e763e7cd0a21bf5cb6a2a8be67069f3f9d3aff638b8a40b258 |
| SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md | cd2a8c765c181ac803d8ee1c8672d1a8ceea3591248cbca449ef3653b4be6ebe |
| LONG_CHANNEL_ENDPOINT_MATCHING.md | 38fa41694cc24fcbe7ac13bc64481323117bcf9d283832a9ec95049cc265cf59 |
| ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md | 8608a7abc8eb8fd8af03132c914ca1134a9b7d09e2e4246defc67b17c8212bdf |
| SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md | 5dac2a88ac992ab72247e76eafcc5ee0fb1ad57a2ec4b11015d0caf07ec87635 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |

The endpoint-cone/projection algebra in Section 6 is also explicitly
proved in Section 7 of the terminal-simple-cycle origin-branch
source, at its own outside-origin scope. Here it has been restated
and proved using (7), (13) and the actual E supports. No conclusion
of that outside-origin theorem is applied to origin-containing E.

For the original C5, both private-load orbits {1,2,4} (and its
reflection) and {1,2,3,4} remain. For C6/C7 all original private
load/channel patterns remain unless one of the full local arguments
above excludes them. The optional real E leaf stays in (8)--(9).
Theorem 1 includes both S endpoints; Theorem 2 is conditional on
their absence. The root port locations and the real intact-petal
geometry still require a further complete exit. No shared ledger,
remote state, Lean file, or workflow was changed.
