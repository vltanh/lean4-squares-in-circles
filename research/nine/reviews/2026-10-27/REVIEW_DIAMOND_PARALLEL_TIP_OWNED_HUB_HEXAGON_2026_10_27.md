# Independent full review: parallel S tip and owned S hub in the diamond

Date: October 27, 2026.

Reviewer: hexagon, independent of the proof author and the root review.

**Conclusion: ACCEPTED at exactly the entire high-radius interface stated
in the source. No mathematical correction is requested.** This is not an
acceptance of the whole still-open high S/S hub-tip gate.

Reviewed source:

    DIAMOND_TWO_S_LEAVES_PARALLEL_TIP_OWNED_HUB_EXCLUSION.md
    SHA256 f8f118f4f326a4a83f0aab31909bdc3008af381086204c8ff16092b7d0a628b2

The actual graph is HK,HB,HC,KB,KC,HL,BM, with genuine S leaves at H
and B, true degrees H4,K3,B3,C2,L1,M1, and positive total circle loads
at K,C. The reviewed source excludes d>1 when the B-to-H/B-to-K forces
are parallel and HB is an actual H-owned side axis. All three additional
original units and all physical masks/means/zero-weight endpoints remain.

## 1. Full source and prerequisite-scope review

I read the entire new source. I also read or re-read the exact direct
inputs at the scopes used here:

* TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, including its
  one-/two-circle-corner proof and properness when the concurrence is
  outside a two-corner unit;
* UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, the complete physical
  nonobtuse-normal theorem, which permits perpendicular limits and
  requires no reduced force equation;
* TWO_NEAR_HUBS_BOUNDARY_DIAMOND_EXCLUSION.md, Sections 1--2, whose
  straight-center planarity and exposed-boundary-center facts were
  already independently fully audited in my separate near-hub review;
* S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md, Sections 1--2, at their
  geometric, degree-free two-arc scope;
* ACUTE_LOADED_CONTACT_GRAPH.md, Section 1, including its strict
  45-degree cone for every physical point of a boundary unit;
* CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md, Lemma 2.1 and the
  circle-corner order consequence, together with CENTERED_INNER_ARC.md
  for the strict 40-degree boundary-center separation.

No C2 concurrence was applied to K3 or H4. The two-arc result is applied
only to the actual connected boundary neighbors K,C of H, and the later
full component sum retains the second real leaf M.

## 2. Parallel-tip geometry and the entire H leaf feature cover

Opposite parallel B pair normals would separate H and K by B's full
width and prevent their genuine contact. Equal-sign parallel normals
point opposite to M by the original B3 equation. For a tilted B, its
two western forces share the western support vertex. The actual B
torque forces that vertex's height to zero, hence equal inward own
components and vertex (d-sqrt(2),0). Its norm is below r, so it cannot
belong to boundary K. This is an actual-port contradiction, not a
parallel-force assumption at K.

The surviving aligned B retains both original side means. The boundary
point estimate gives |z|>16/25. Reflection, the full B torque, and the
unit side length give z<0<y, 0<a<9/25, and z>-1 even when z is the
actual lower side endpoint. H owning the HB axis puts H in its actual
parallel frame; it does not prescribe its transverse slider h.

I checked all four actual H side axes and all four vertices. East and
west support heights are below d. The south side and lower-right vertex
contradict y>0. The north side and upper-right vertex put all of H
strictly above zero. The only other radial S supports are exactly the
two left vertices, with h=s or 1-s and s=2sqrt(epsilon). No radial
vertex/side endpoint with a zero coordinate has been dropped.

For the wholly-above-zero cases I verified the entire small-norm K
argument. In its translated right-support frame the tilted corner
condition is -t<=z<0. The upper adjacent corner has squared norm at
most one, the lower at most three, and the opposite at most three.
The aligned support-side case has the stronger bound two. Restoring
the actual translation gives sqrt(3)+epsilon<7/4<R. Thus every real
K circle mask is excluded without a K force or torque simplification.

## 3. Lower-left leaf: full component balance is retained

For f=(s,-p)/d, the stated exact reserve

    (p-s)|z|-epsilon(p+s)>1969/4500>0

indeed implies P_K.f>|det(P_K,f)|. Together with the strict 45-degree
cone between P_K and every K circle corner, it makes every such corner's
f projection positive. The geometric connected-neighbor two-arc theorem
then gives the same strict sign for all C physical circle corners.

M has strictly positive f component, L has zero f component, and K,C
have positive total original circle weights. The complete component
circle sum is therefore impossible. H4 is never replaced by a triangle
equation. Both genuine leaves are included, and any zero individual
circle corner weight is harmless because the sign holds on the entire
physical mask.

## 4. Upper-left leaf: center order and all HC endpoints

The H-owned east HB normal is nonobtuse with HK in the actual triangle
H,B,K. The actual B--K point rules out north/northeast HK, and K's
maximum-x support rules out east. Thus HK has precisely (u,-v),
u>=0,v>0. Its supporting inequality gives z<=-q and a<=s. Combining
the unchanged K support with its two directional halfwidth bounds
gives the displayed center inequalities (4), including u=0.

The straight-center embedding is valid for the selected positive
graph. Its only potential crossing equality is the aligned four-way
junction already treated by the original uncrossing. C is exterior
because it is physically boundary. B is also exterior to the diamond:
its genuine positive BM edge joins it to the exterior boundary center
M and cannot cross the diamond. Therefore B,C are on opposite open
sides of HK. The determinant calculation with

    c_K-c_H=(-eta,-zeta),       c_B-c_H=(1,-delta)

has eta,delta>=0,zeta>=1 and positive determinant eta*delta+zeta.
It correctly yields C_x<h_x whenever C_y<h_y. No new near-hub or
boundary premise on B is imported from the larger geometric source.

I checked the complete HC support cover. The upper-left leaf port is
unshareable. The upper-right vertex and positive-y right-side points
are too close to O for boundary C. The north axis is excluded by the
triangle nonobtuse theorem with the strictly downward HK direction.
Every other right-side interior point is occupied by the actual B
side, including its full slider interval.

At the remaining bottom-right point P_0, a<s puts P_0 in the relative
interior of B's side, so the original positive-x inward C segment
enters B. At a=s, the actual BK mean is also P_0. H and B occupy the
two upper quadrants; K and C must occupy the two lower quadrants.
The positive-x C direction assigns C the southeast quadrant, making
BK a singleton vertex/vertex contact with its original west side-axis
normal. That is exactly the previously forbidden strict-point
endpoint. The east-axis limit is included in this same reasoning.
The residual HC list is therefore exactly west, south, southwest.

## 5. Every residual HC normal is excluded with its genuine equations

For west HC, the proper-concurrence signs are correct: since C-to-H
points east, q_C=P_C-l e_x, l>=0. The genuine K support bounds the
actual CK point by T_y<=-q-u/v. If g_y>0, C properness contradicts
this. The u=0 equality subcase is explicitly handled: it forces t=0
on K's top side, where the actual inward g segment would immediately
leave K. A horizontal g would contradict the genuine nonparallel C2
pair. Hence g_y<0, and C's full force equation gives F_C,y>0.

Thus q_C, and therefore F_C, lies between west and the H leaf's own
direction. I checked

    s/p<78/295<2-sqrt(3),

including 512^2>3*295^2. Its angular distance from L is below pi/12.
The physical center/corner bounds require every distinct boundary
resultant to differ from the S-leaf center direction by more than
pi/9, including arbitrary nonnegative corner splits. This is a valid
strict contradiction.

For south HC, both actual K,C centers lie below -1 and left of
-29/60. Their norm bound places them in the rectangle in (7), whose
squared diameter is 2561/3600<1. Their physical center distance must
be at least one, so this case is impossible.

For strict southwest HC I checked the all-owner unit-segment argument.
Any minimum-normal support point of a unit contains its inward unit
normal segment, including side means and vertex limits. When a_0>=b_0,
the support is at least p and that actual segment's endpoint has
squared norm greater than 16097/3600>Q.

When a_0<b_0, the support increases with k=a_0/b_0 because p>q
(indeed 2sqrt(epsilon)>epsilon). The exact comparison at k=2/5
uses 338^2>61^2*29 and forces k<2/5. The center estimate then gives
C_y<-51/50<-1; the already proved opposite-side order gives
C_x<h_x. K is in the same small rectangle, yielding the identical
strict center-distance contradiction. Every value of the actual
C owner and all shared-mean endpoints survive this estimate.

## 6. Acceptance boundary

The proof excludes the complete stated high parallel-tip/owned-hub
interface inside M6.B4L2.DIAMOND.HUB_TIP.LKC.SS. Its remaining high
nonparallel-tip and unowned-hub interfaces are still separate, as the
source correctly states. The low/critical theorem remains its own
dependency. This review closes no whole parent by itself.

No correction, post-extraction force change, hidden degree reduction,
numerical pose, Lean compilation or CI is used in this acceptance.
Every original H4/K3/B3 force, all nine physical units and all real
physical circle masks remain in the audited proof.
