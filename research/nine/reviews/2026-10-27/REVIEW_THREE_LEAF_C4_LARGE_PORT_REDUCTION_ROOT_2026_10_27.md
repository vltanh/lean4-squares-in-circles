# Root review of the complete three-leaf C4 necessary-domain reduction

Date: October 27, 2026.

Reviewed source:
`THREE_GENUINE_LEAF_C4_MIDDLE_ROOT_AND_LARGE_PORT_REDUCTION.md`,
SHA256 `7d789ce70b2444aadf0f0a7f1354d7c92ff92085357a91f5eea42a6acbddb1ac`.

**Root review passes for the complete necessary reduction at these
corrected bytes.** This is not a proof of the original C4 placement.
Its entire parallel-middle-root family and its final nonparallel
positive-side chart remain open. Separate independent review is still
required before an acceptance checkpoint.

The prior submitted pin 63c2bf54 had a harmless strictness error in
Section 7: the aligned leaf has y=d*u, so the common estimate must read
y<=d*u<61/900. The corrected pin above makes exactly that change.
The final strict bound below one half and every subsequent argument
are unchanged. No conclusion is credited to the old uncorrected pin.

## 1. Original degrees, middle root and radial endpoints

The graph is the original A-B-C-D-A with genuine leaves at A,B,C,
true A3/B3/C3/D2 and two arbitrary completion units. The complete
three-root theorem supplies the strict-high all-S domain, not a
prescribed root frame. A genuinely unloaded D2 would separate its
two actual near endpoints by at least one while their near points
give separation at most 2epsilon. Thus D is truly loaded and its
every point has norm at least r>129/200.

At B, the near points of its two original nonleaf neighbors bound
both actual supports by epsilon. These are all its nonleaf forces.
The complete small-support theorem applies to the full B3 force and
torque system and makes B aligned. Its actual chart then avoids O,
so the origin-free genuine-leaf concurrence lemma can legitimately
be used at B. Neither A nor C is assumed to avoid O at this stage.

The radial screen in Section 3 is physical. In this aligned B chart,
an outward radial nonleaf contact either is the actual far-side
leaf point or has support greater than d, contradicting the sharp
contained-unit minimum-support bound. At the leaf point the unique
possible outer unit is the actual genuine leaf. An inward radial
contact must be the unique nearest point (epsilon,0). These cover
all signs without requiring the other root to avoid O.

At that nearest contact, the inward unit segment puts O in the
other genuine root A closed. The complete support-feature cover
excludes a strict A vertex, then forces its exact owned-axis chart.
Its genuine S support fixes the transverse endpoint at
2sqrt(epsilon). The other three origin margins exceed epsilon,
so the only point of the near disk outside int A is (epsilon,0).
The third real root C would have that same genuine direction and
would repeat B's actual S leaf. This excludes radial cycle edges
without reducing any root degree. The corresponding common cycle
moment is nonzero because all real leaf and circle moments vanish.

The force-free Section 5 of
`THREE_GENUINE_LEAVES_WITH_A_TRANSMITTER_ROOT_EXCLUSION.md` was read
at precisely this radial-support scope. No transmitter equation at
A, B or C is imported from its separate caller.

## 2. Every nonparallel middle-root case is exterior

The two original B normal transverse components are nonzero and have
opposite signs. For an inside concurrence, each actual positive
proper length gives z^2<=epsilon(1+sqrt(2)), using the real support
height and the rectangle feature sign. A negative longitudinal
product necessarily occurs at the actual near face and is at least
-epsilon. A zero proper length has z=0 and is retained. Applying
the bound to both signs contradicts a+b=1. Thus the full inside
concurrence domain, including side-axis ports and endpoints, exits.

The actual exterior cover puts the two applications at the two
near vertices, with a>=1/2 assigned to the larger port. The
support inequalities give z^2<=2epsilon*T+epsilon^2 only after
retaining the nonpositive-numerator case before squaring. They
imply T>899/120. No physical A-C edge or triangle is introduced.

## 3. Closed-origin A is excluded without an A concurrence

The full genuine-S support enumeration proves the two-small-margin
lemma, including zero own heights. Every side or near/adjacent
vertex has radial support below d; the opposite corner has radial
norm above d. It also gives the entire side-interior-origin chart,
with both transverse margins greater than epsilon. A genuine
closed-origin high-S root cannot have an origin vertex.

For the larger reflected port, O in A implies T>=a^2/epsilon>15.
At its unchanged application the actual own-face cone supplies an
upper incident outward face (s,c) with 0<c/s<=epsilon/a<1/22 and
nonnegative height sigma<=epsilon. Choosing this actual face is
only a geometric support extraction; the original pair normal is
never replaced. The two-small-margin lemma puts every other A side
strictly beyond the near disk.

If sigma>0, A is open at O, forcing C to avoid O. If sigma=0 and
C also contained O, both would have side-interior origins with
opposite tangent halfplanes and transverse margins exceeding
epsilon. Their actual union would fill the near disk and a full
neighborhood at its common line, contradicting the actual B near
point and interior nonoverlap. This proves C's origin avoidance
also at the boundary endpoint.

The complete source
`GENERAL_NEAR_UNIT_OBLIQUE_FACING_CONTACT_SMALL_CORNER.md` was read,
including its genuine-S own-interval fact and both support-frame
cases. The new manuscript reproduces the operative construction
instead of asserting that the old strict-open statement covers
sigma=0. At a unique maximum vertex, beta_C>0 and origin avoidance
give delta_C>0; the actual nearest point gives delta_C<=epsilon.
The shallow-face inequality now gives E>=0, deliberately retaining
E=0. At an owned maximum side, beta_C<0 would put the nearest
point on the forbidden side; beta_C=0 and all actual means remain.

In both cases the actual C side crosses the actual A face at K,
with lambda>=0, lambda<epsilon/8<1-beta_C, D>49/50 and
K.j>0. A positive continuation of that same side enters int A
unless A's actual upper own height is at most K.j. The bound
|K|^2<(65/64)epsilon^2 then contradicts the genuine-S two-small-
margin lemma. The cases sigma=0, E=0, lambda=0 and beta_C=0 have
the same positive continuation and are all covered.

This entire closed-origin argument uses geometry and nonoverlap.
No positive or proper concurrence is assigned to A.

## 4. Complete origin-free large-vertex exclusion

Only after A is proved to avoid closed O is its true A3 concurrence
lemma invoked. The unique maximum-g vertex frame retains signed
tilt. beta<=0 would make the actual port the nearest point, too
far from O. The separate beta>1 feature enumeration is complete:
all side foot signs, both maximum-w vertices, the near vertex and
the far-v vertex are considered. No radial support of norm d is
available in that branch.

For 0<beta<=1, origin avoidance gives delta>0 and actual nearness
gives delta<=epsilon. Hence u<1/15, v>99/100 and beta>99/200.
The full genuine-leaf cover then leaves the aligned v_0 leaf or
the specified far-v vertex. Both have leaf-point ordinate at most
d*u<61/900. At the unchanged large port, actual properness instead
gives q_A,y>=a>=1/2.

The tilted leaf concurrence is on its genuine radial segment, so
these inequalities contradict each other. For the aligned leaf,
they force exterior concurrence, whose actual second port is the
other near vertex. Its norm is below 13/25, contradicting the
physical boundary point floor at D. The parallel pair cannot occur
here because its original normal would be an owned A axis, whereas
this branch strictly exposes an A vertex.

## 5. Entire remaining A-side cover and the exact open domain

The actual A-owned contact has fixed g support h and actual
transverse mean t>99/200. The lower support bound h>=-epsilon
comes from A's real near point, and the formula gives h<=epsilon.
When h<0 the own-interval property puts zero in the transverse
interval. Its upper endpoint t is too large to be a genuine radial
vertex, forcing the leaf's transverse component nonpositive.
A positive nonparallel concurrence cannot lie on the actual
AB line at transverse coordinate t>0.

The parallel h<0 alternative uses its original weighted means;
it does not place either mean at a midpoint. The other AD mean is
negative with absolute value at most 1-t<101/200. Together with
|h|<=epsilon this gives norm below 13/25 and again contradicts D's
physical boundary floor. The two distinct bounds for tilted and
parallel leaf cases are not conflated.

The retained chart consequently has 0<=h<epsilon, positive
rho<=epsilon, T>=a^2/epsilon>15, and the complete two genuine-leaf
alternatives in (17). The full A3 equation includes the real leaf
and forces the actual AD normal strictly negative in both own
coordinates. Its application is exactly the lower-left vertex
R_A in (18). Since |R_A|<d, the actual D cannot have two physical
circle corners: such a unit would be a radial S square whose
every point has norm at least d. Thus its true positive load is
at its one actual circle corner.

The A-owned/B-strict-vertex contact is at an A side interior by
the retained strict point convention. This justifies the strict
slider inequalities without changing the actual mean.

The two remaining whole domains are exactly those stated by the
author: parallel B with both genuine A3/C3 systems intact, or
nonparallel B with the positive A-owned chart and the complete
unchanged C3 system. Neither is excluded by this reduction.

## 6. Acceptance and accounting limits

The five directly named sources were checked at the actual scopes
used above; the complete small-support and origin-free concurrence
arguments were read in this session. The original canonical setup,
strict selection, physical boundary feature facts and elementary
normal-channel results remain declared inherited inputs. This
report does not replace the older full global prerequisite audit.

No original fine ID or coarse cell closes here. C1.4.b3 still has
22 complete placements and two open placements; the separate
diamond with leaves at both hubs and one tip is unchanged. No
origin-free lemma was transferred to a closed-origin root, no
extra force was deleted, and neither completion unit was removed.
No Lean, CI, numerical pose search or physical motion was run.
