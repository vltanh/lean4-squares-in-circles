# Independent review: two long channels force capacity eight

Date: October 30, 2026 UTC.

Reviewer: annular-capacity research agent, independent of the main
two-channel assembly author.

**Result: PASS at the entire stated scope. No repair requested.**

## 1. Literal source reviewed

The reviewed source is
`TWO_LONG_CHANNELS_FORCE_CAPACITY_EIGHT_AND_FOUR_LOAD_CYCLE_REDUCTION_2026_10_30.md`.
Its complete 22,842 bytes were read, including the geometric theorem,
stress corollary, separate compatible-plane alternative, cycle-family
consequences and scope section. The frozen SHA256 is

    e05fa0520279d957659f694fdaa5b08be750a848d5117f3792df4399476354f5

All four displayed dependency SHA256 values were recomputed and match
the source. The complete endpoint-matching proof and protected-ray and
enlarged-capacity sources were read. The local geometric construction
and compatible embedding in Sections 1--6 of the plane-uncrossing
dependency were also read for Theorem 2. The endpoint-matching import
uses its force-free Theorem 1.1, without importing the torque premise
of its separate transmission corollaries.

## 2. Geometric theorem

Theorem 1 genuinely needs only two vertex-disjoint actual four-square
contact paths with a signed common support normal on each path. Actual
contact points are explicitly required; support-plane equalities alone
are not substituted for physical incidence. The original family of
physical squares remains present throughout.

I checked the center bound and its strictness, the halfwidth telescope,
the endpoint radial and halfwidth bounds, and the two endpoint-angle
estimates. The nonalternating-order argument correctly uses that both
arcs joining a long pair have length less than 210 degrees, and removes
two gaps each exceeding 30 degrees. The four outward rays have disjoint
angular neighborhoods and preserve the alternating order of their
centers. The auxiliary circle of radius three avoids any unproved
circle-contact premise at a channel endpoint.

The center-and-contact-point path is strictly monotone in its channel
normal, since each center-to-contact projection is an actual positive
halfwidth. Appending the outward rays preserves that monotonicity and
gives a proper simple disk arc. The Jordan crosscut argument therefore
applies. Protected rays exclude all possible spoke intersections with
the other physical route, and their angular windows exclude spoke-spoke
intersections.

At a physical route intersection, every non-contact point of either
route lies in the interior of one of its original squares. An interior
of one physical square cannot meet another physical closed square.
Thus the intersection is an actual contact point from each path and
belongs to four distinct physical squares. Their local interior-angle
sum forces four right-angle sectors and an exact aligned two-by-two
block. This argument remains valid for endpoint means and other closed
contact cases; it does not assume a force line crosses a square's
interior or passes through its center.

The four-square junction screen is sound: a junction with norm at least
19/20 would force a block corner outside the disk, while each outer
contact mean has normal projection of magnitude greater than 19/20.
Consequently the shared contact is the middle contact of both paths
and its four incident squares are exactly their internal bodies.

## 3. Near-axis inversion and completion

After the junction is established, the four internal frames agree.
The two internal widths of either channel are therefore the same
quantity m. The inequality 1+2m<2M gives m<61/60 without torque.
Writing a and b for the larger and smaller absolute normal coordinates
gives b<1/30 and a>899/900. All square-root and strict-inequality steps
in this deduction are valid, including b=0.

If both normals were close to the same common axis, reversing their
signs as necessary gives two distinct positive-side endpoint centers
in the same cap with coordinate greater than 22/15. Its squared
diameter bound 719/1200 is less than one, contradicting their physical
incircle separation. Thus the two normals are close to different axes.
This argument needs no assertion that a normal equals a square side
axis.

The middle support identities bound the two normal projections of the
actual junction by 1/60. Choosing the normal close to its largest
absolute coordinate gives

    max(|p_x|,|p_y|)<15/869<1/30.

The enlarged junction-capacity theorem applies in that actual common
frame and leaves at most four additional arbitrary physical units.
This is a bound on the entire packing, including any ninth unstressed
square or square in another positive component.

## 4. Translational stress and graph consequences

At an unloaded true-degree-two body, positive force balance gives equal
opposite forces. This supplies each channel's common signed normal
without a torque equation. The source never asserts that the original
means are collinear under this translational premise.

The retained-endpoint argument is complete. Extending through an
unloaded true-degree-two endpoint either makes a path with three
internal transmitters and support span at least four, or makes a closed
positive-width common-normal loop. Both are impossible. The endpoint
matching theorem then gives four distinct endpoints for different
long pairs. An endpoint cannot be another path's internal body, and
shared internal bodies force the same complete channel and endpoint
pair by the true-neighbor condition. Thus the stress corollary supplies
the exact vertex-disjointness required by Theorem 1.

The four-load simple-cycle conclusions follow for all cyclic placements
of (2,2,0,0) on C8 and (2,2,1,0) on C9, while retaining all nine
physical squares. The stated remaining count families and seven-body
record family are not credited as closed. Multiple channels with the
same endpoint pair are explicitly preserved.

## 5. Separate selected-plane theorem and sharpness

Theorem 2 has an explicit additional physical embedding premise. It
does not infer a compatible local drawing from abstract graph
planarity. Protected rays miss all original junctions and all strands
away from their own endpoint center; near that center they have a
different direction from every contact strand. Finitely many small
local perturbations can therefore preserve all four rays. The two
vertex-disjoint graph paths then contradict the same alternating-end
crosscut theorem. This argument is correctly separate from the main
physical capacity theorem and is not used to impose a new selection
on a translational caller.

The eight-square example at squared radius 17/4 is valid and retains
the necessity of an actual ninth square for the principal exclusion.
It has two disjoint common-normal four-square paths but need not admit
the compatible physical embedding required by the separate theorem.

## 6. Exact checks and verification boundary

Direct rational recomputation verified every displayed numerical
identity used in the main assembly, including the center reserve
31/57600, angular reserves 359/960 and 709/9000, junction-screen reserve
3111/6400, common-axis projection 79411/54000 with reserve 211/54000,
cap diameter squared 719/1200, and inverse projection 15/869.

This is a full independent hand review of the frozen mathematical
source and its relevant joins. It is not a Lean verification, a
numerical pose certificate, a common-selection audit beyond the
explicit Theorem 2 premise, or a closure of any original ledger row.
No source bytes, ledger flags or remote state were changed by review.
