# Independent review of the complete parallel two-circle perpendicular-hub feature

Date: October 28, 2026 UTC.
Reviewer: house.
Decision: **PASS at the exact source and entire stated scope below.**
No source repair was required.

## 1. Exact source, full review and independence

Reviewed manuscript:

- PERPENDICULAR_HUB_PARALLEL_TWO_CIRCLE_TIP_COMPLETE_POCKET_EXCLUSION.md
- SHA256: 4fc35299caf0580d9f995d4bfc253c7fad40f95c9f48ae34dc40b976108a5807.

I read the complete new proof and all fifteen complete direct inputs, checked the current pins, and independently verified the full parallel-V mask/owner classification, every side endpoint, the original shared-mean handling, the actual T port and angular bounds, the occupied crosscut and cone, the centered-arc contradiction, and the literal original graph join.

The new proof is root-authored. I did not supply its new parallel-V classification or physical assembly. I did author the imported radial half-strip theorem, so this is not a claim of independent review of that prerequisite. Its complete separate independent pentagon review is:

- REVIEW_RADIAL_HALFSTRIP_FULL_RADIUS_COROLLARIES_PENTAGON_2026_10_28.md
- SHA256: 2a9791b3e47cc212e214abb44d20ae107774d92196d2ea7e75d1f4ee78f536e4.

I reread that full record and its exact source. My review of the new radial inner-corner scalar input is c59537d7ee575437f4460b4eb525fa0a194ec1753c58c96bf5885a1c1013412d. The angle input from the nonparallel proof is pinned to the repaired cef7f26f... bytes, not its earlier draft. Only its exact elementary angular comparisons are imported into the present physical proof.

The conclusion is complete for every return owner and every original UV mean in the stated parallel-V physical-two-circle feature. It does not exclude unique-circle V masks or the whole original D02 row.

## 2. Complete parallel physical-mask cover

The only bowtie input is its force-free complete Southeast cone for the actual V-to-W normal. Its loaded-two-tip contradiction is not applied at W3.

The full original V equation gives F_x<=0 and F_y>0. For a parallel physical-two-circle square at R>2, the two possible masks compatible with those signs are exactly radial North and radial West. Radial South has negative y at both corners, and radial East has positive x at both corners. A centered four-corner tie is impossible at this radius. This classification retains both actual circle corners and every individual zero coefficient.

In the radial West case, V's bottom height is H=-1/2. Since W lies in x>=L and actually meets V, one has L<=-d. The actual lower-left U corner then has squared radius at least

    (d+1)^2+9/4=R^2+2.

This is a direct containment contradiction. It makes no return-owner or mean assumption.

Thus the entire remaining mask is the actual radial North square [-1/2,1/2]x[d,d+1]. Its two physical circle corners are retained independently of the weights.

## 3. Complete axis and aligned-W exits

An original South return normal puts W below V's inner side with maximum height d and vertical width at least one. Since W actually meets this radial V, the full half-strip barrier gives min_W y>d-1, a contradiction. Every original contact point, mean endpoint and W mask is included.

For an East return normal, the original VW and UW minimum-x support lines of the same W give L=1/2. The complete U force equation, with both original positive North and East forces, gives a strictly Southwest third normal and the original singleton U support P_T=(L-1,d-1).

At L=1/2 the displayed port deficit is exact:

    |P_T|^2-(R-sqrt(2))^2=-4d-2+2sqrt(2)*R<0.

The strict sign follows from

    (2d+1)^2-2R^2=2d^2-3/2>0,

using d>9/10 and positive compared quantities. Any actual boundary unit containing P_T must have |P_T|>=R-sqrt(2), by its diameter. Hence this case is impossible without any T mask restriction.

For strictly Southeast m, the actual V support is its unique lower-right vertex M. If W is parallel, that normal exposes W's upper-left vertex, whose x-coordinate is the original UW support L. Again L=1/2 and the same actual-port contradiction applies. No aligned UW mean is replaced in a force equation.

## 4. Every remaining owner and side endpoint is classified physically

For nonparallel W, its original East contact with U is the unique left vertex Q_W. Both inward axes f=(C,S), g=(S,-C) have positive x components.

For every strictly Southeast m, m.g>0. Thus an actual minimum-m point of W has g-coordinate zero and must lie on the whole closed f side. This yields exactly

    M=Q_W+beta*f, 0<=beta<=1,
    L=1/2-beta*C, q=d-beta*S.

It does not assume at the outset that W owns the return normal.

At beta=0, L=1/2 and the complete T diameter contradiction applies. At beta=1, the actual bottom W corner has height d-S-C<=d-1, contradicting the radial half-strip barrier at the unchanged point M. This includes both free vertex normals and endpoint-valued W-owned normals.

For the remaining actual side-interior point, the original normal is necessarily m=g. This is forced by the unchanged support, not reselected. All owners have therefore been covered.

The radial inner-corner theorem applies to this literal W, with gamma=C, eta=S, the actual M and physical boundary status. Its force-free conclusion gives 0<beta*C<1/4. No nonparallel-V circle-resultant inequality is imported.

Consequently 1/4<L<1/2 and the actual UV intersection is the full segment [-1/2,L]x{d}. The original mean remains arbitrary on this whole segment, including both endpoints. The subsequent force argument needs only the original positive North/East forces and never substitutes the segment's left extreme into an equilibrium equation.

## 5. Complete actual T port, corners and center bounds

The original U third normal is strictly Southwest, so its actual application is

    P_T=(-a,b),
    1/2<a=1/2+beta*C<3/4,
    -1/10<b=d-1<1/60.

These are actual physical coordinates, independent of the variable original UV mean.

For any physical T circle corner Z, including zero-weight corners, Z_x>=-1/2 would give w_x>0 for w=Z-P_T. The genuine minimum-n support with both n components negative then forces w_y<0. The unit diameter gives the printed rectangle

    -1/2<=Z_x<1, -8/5<Z_y<1/4,

whose squared norm is strictly below 89/25<4. Hence every actual T circle corner is strictly left of x=-1/2.

The center-to-port circumradius and actual boundary-center lower bound give r_T>31/24. If the center's first coordinate were nonnegative, its coordinate bounds would contradict this. I checked the exact new reserve 67/72. Thus its angle has the valid lift theta_T in (90,270) degrees for every original T owner and physical mask.

## 6. Entire T-angle and actual V-point cover

The new port box is stronger than the small-tilt box used in the repaired nonparallel proof. In particular a<3/4<91/100, b>-1271/20000, and |P_T|<1.

I checked the distance minimization directly, without transferring a nonparallel premise. The port angle is above 90 and below 210 degrees. On center angles [216,270], the angle difference is in (0,pi), so squared distance increases with angle. It also increases with radius above 181/140 because that radius exceeds |P_T|.

The endpoint comparison at angle 216 degrees gives the same exact strict reserve

    10826627041/6350400000000

above the squared circumradius 1/2. Thus theta_T<216 degrees throughout the full actual domain.

For d>=24/25, the actual b>=-1/25, R>101/50 and r_T>919/700 yield 523/919<4/7<sin(35 degrees). Hence theta_T<215 degrees on that entire second range. The shared threshold is retained.

The two actual V interior points at radius 9/8 and angles 116 or 115 degrees have the correct signs, strict horizontal and vertical bounds, and lie below V's outer side. Their exact reserves are those printed in the repaired elementary angle source. Thus the complete d cover yields theta_T<phi+100 degrees for the chosen actual point, without changing an application or a circle coefficient.

## 7. Actual crosscut with a variable shared UV mean

The actual VW moment is negative, and the boundary-neighbor rule gives the complete loaded path in clockwise order. The closing gap is therefore counterclockwise from V to T.

The displayed occupied path uses V's actual left side, then U's actual top-left boundary arc, then T. Although U and V share a nontrivial segment, those chosen two path portions meet only at P_V=(-1/2,d): the V portion approaches from above, and the U portion leaves strictly left because beta*C>0. The U-to-T support is its unique southwest vertex. The complete U3 touching-return separator makes T closed-disjoint from V and W. Thus the chosen crosscut is simple.

Every piece lies in x<=-1/2. The same is true of its actual closing circle arc: Z_V is the upper cap endpoint, every physical T corner lies in the open cap, and the loaded path occupies the complementary clockwise order. The actual U box is strictly circle-clear by the printed norm bound, so no unaccounted U circle spoke changes the gap.

The original center/contact crosscut is homotoped to this barrier inside the unchanged closed U,V,T union. Its geometric UV junction may move along the actual shared segment to the gap-facing extreme, but its original mean remains unchanged in every equation. Every compact subset of an extra's open interior avoids that whole closed union, so winding and the assigned face are preserved. Closure gives the entire unit's containment.

Therefore every whole actual pocket extra lies in x<=-1/2, and its actual center lies in x<=-1. This is a complete shared-mean routing argument, not a fixed-point substitution.

## 8. T2 orders the actual angular cone

The genuine T2 torque and the actual counterclockwise final boundary-neighbor moment give det(P_T,n)>0. Proper concurrence applies with that actual boundary predecessor, retaining every physical T mask and either individual zero coefficient.

Both P_T and n lie in the same open left half-plane, so the determinant sign orders n counterclockwise from P_T. The positive concurrence combination gives arg(P_T)<=arg(F_T). The complete physical corner/resultant cone gives arg(F_T)<theta_T+15 degrees and the same strict upper bound for every physical T corner.

The earlier occupied path has the stated strictly positive determinant signs 1/2,d,a. Thus the V/U portion increases in angle up to P_T. Both endpoints of the T portion lie in the cone between arg(Z_V) and theta_T+15 degrees, as does the actual closing circle arc. Its aperture is below pi. The cone is an intersection of two half-planes and therefore contains the bounded Jordan region.

This proves the actual extra-center upper angle bound. It uses no inside-T concurrence assertion and no equation at W3 or another internal loaded body in place of T2.

## 9. Complete centered-arc capacity and original join

The whole-pocket half-plane and universal center-radius bound give 130<theta_E<230 degrees, with the exact cosine comparisons printed in the source.

Every such extra has center radius at least one, and T has radius above 31/24. The accepted closed centered-forty-degree theorem therefore applies literally to all of them. Each corresponding closed arc lies in its actual open square, so pairwise minor center separations are strictly greater than 40 degrees.

The angular cone puts an extra at most 15 degrees beyond T; such an extra would contradict that separation. Hence every extra precedes T. The actual V point forces each extra to follow phi by more than 20 degrees. If two extras were present, their ordered gaps to that point, to each other and to T would respectively exceed 20,40,40 degrees.

All three are actual minor gaps by the established lifts and angle bounds. Their sum contradicts theta_T-phi<100 degrees. This proves the complete closing-pocket capacity bound.

The literal D02 mapping retains its rim, positive chord 02, load set {0,1,3,4,5}, degrees U3,V2,W3,5_2,4_2,T2 and all three original extra units. The complete central capacity is one, all direct boundary-pair exterior pockets are empty, and the remaining closing pocket has capacity one. The occupied plane graph allocates all three extras among those actual regions, including weak-junction limits, giving the stated contradiction.

No parallel physical-two-circle owner, V mask, W frame, side endpoint or original UV mean remains untreated. Unique-circle V masks and the whole D02 row are outside this review's closure claim.

## 10. Exact complete direct-input pins

| Source | SHA256 |
| --- | --- |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 |
| RADIAL_HALFSTRIP_FULL_RADIUS_BOUNDARY_SUPPORT_COROLLARIES.md | e8cb01fa67033056433ce210ae0c286700606533cae5db18fc641e8d568804f8 |
| RADIAL_INNER_CORNER_BOUNDARY_NEIGHBOR_QUARTER_SIDE_BOUND.md | 37f0f207a86a9d2c4ead42edcfaac01c5dbdd4f08bc66e98e41f985adedc4011 |
| PERPENDICULAR_HUB_W_OWNED_TWO_CIRCLE_TIP_CLOSING_POCKET_CAPACITY_ONE.md | cef7f26f395968b9d1a68f07bb531569ba12e72500cd23839ca9d4f97bf29923 |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 |
| FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md | aef2fc2adfda6168d7e2c2f824b373d6beafb12c8937e0f6bc93f7f36b464a67 |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 |
| GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md | 5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 |
| CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md | b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b |
| CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md | 0b787eae6efe36d2ca6c40dbb079d3262192125fffe58026bacbfd657d1a9a34 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 |

All fifteen complete sources were read, with the prerequisite-authorship disclosure in Section 1. Exact arithmetic checked transcriptions only. No sampled pose, numerical search, angle mesh, computational exclusion certificate, normal reselection, changed original mean, force deletion, artificial degree-two neighbor, Lean compilation, CI, remote write or ledger edit was performed.

