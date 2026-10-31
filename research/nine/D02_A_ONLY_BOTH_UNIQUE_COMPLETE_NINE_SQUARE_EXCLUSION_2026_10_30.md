# Complete A-only both-unique side exclusion with all nine actual squares

Date: 2026-10-30. Original PR #11 input: `71d385e75adc1f5183d35a92dbe18c208dc32f2a`.

**Status: complete exact finite exclusion; generation CLOSED and separate full-tree
replay PASSED.** This is an original-domain mathematical
certificate and a complete physical-completion join. It is not Lean compilation
or independent-kernel acceptance. No unrestricted n=9 theorem is asserted here.

## 1. The complete original feature being excluded

Assume an original packing of **nine actual, independently oriented unit squares**
in the disk centered at O, with

    79/40 <= R <= sqrt(1105)/16.

Keep the exact D02.L135 positive graph and original stars

    A:{V,D,B}, D:{A,V,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D are unloaded true3, N is unloaded true2, and V,B,C are loaded true2.
V has its original unique physical circle corner and the roof is the complete
Type II A-only h owner. The actual unloaded N is a side transmitter. Assume the
**both-unique endpoint alternative**: B and C each have exactly one physical
circle corner. Retain the same original normal selector, full positive forces,
actual applications and means, true degrees, and every physical zero-weight
body/circle contact. All three additional squares remain actual contained,
interior-disjoint units.

**Theorem.** This entire original feature is impossible.

The two physical-radial endpoint alternatives of the full A-only side row are
separate callers. They are not identified with the parallel directions d=b or
d=c. This theorem can be joined to their full exclusions without deleting their
unequal circle-corner coefficients. The loaded N of D02.L1345 is outside the
present theorem.

## 2. A bounded, exact, exhaustive original parameter cover

The original equations give the system in
[D02_A_ONLY_BOTH_UNIQUE_THREE_VARIABLE_REDUCTION_2026_10_30.md](D02_A_ONLY_BOTH_UNIQUE_THREE_VARIABLE_REDUCTION_2026_10_30.md).
Every original point has

    a=tan(alpha/2), bhalf=tan(beta/2), w=tan(psi),
    d=(-1,w)/sqrt(1+w^2),
    a,bhalf in (sqrt(2)-1,1), w in (0,1).

The original hub root u is the unique zero of the monotone positive-part cubic
Fplus in that source. Its positivity restrictions, t and omega are retained.
No arbitrary cubic root is substituted for an original placement.

The already complete high-angle source eliminates alpha+beta>=120 degrees.
The uniform original physical-roof bounds in
[A_ONLY_UNIFORM_POSITIVE_HUB_AND_NORMALIZATION_BOUNDS_2026_10_30.md](A_ONLY_UNIFORM_POSITIVE_HUB_AND_NORMALIZATION_BOUNDS_2026_10_30.md)
give

    a>41487/100000, u>1/12, s-c>1/625,
    u,t<3/5, H>sqrt(3)/2, 0<k<1/2,
    p>(sqrt(3)-1)/2.

Thus all remaining original points lie in the one closed comparison box used by
the certificate. At precision D=2^44 its integer endpoints are

    a:     [7298470224246,17592186044416]/D,
    bhalf: [7286922051387,17592186044416]/D,
    w:     [0,17592186044416]/D.

Both lower dyadic endpoints round downward from the corresponding exact entry
bound. The original strict domain is therefore contained, including every
possible approach to beta=pi/4 and every retained weak physical contact.
The larger closed comparison box is deliberately allowed to contain points
which have no physical realization.

## 3. The actual equations tested at a leaf

Use the unchanged common positive scale

    mu=u*t, rho=(s-c)*t, nu=(s-c)*p.

The own directions and original support coordinates are those of the complete
three-variable reduction. In particular

    v=u*s/(u*c+s-c), m=(t+p*k)/(p*H),
    0<m<v<1,
    a0=1/sqrt(1+v^2), b0=v*a0,
    cY=1/sqrt(1+m^2), cX=m*cY,
    b=(-a0,-b0), cvec=(-cX,cY),
    wB=(-b0,a0), wC=(-cY,-cX),
    Delta=(-1-q,p-u), sigma=b.wC=cvec.wB>0.

The positive offsets AB,AC and actual side coordinates xB,xC remain exactly
those of the source. Stable algebraic forms used by the checker are

    xB=1+[(m+w)/sqrt(1+w^2)-m*(1+q)-(p-u)]/[a0*(1+m*v)],
    xC=1+[(1-v*w)/sqrt(1+w^2)-(1+q)+v*(p-u)]/[cY*(1+m*v)].

The true side offsets are strictly between zero and one. The full two original
endpoint torques require

    PB*xB*kC-PC*xC*kB=0,
    kB=d.(wB-b)>0, kC=d.(wC-cvec)>0.             (T)

The checker multiplies (T) by the positive sqrt(1+w^2) before evaluating it.
It never divides by a force-matrix determinant.

Let F=mu*East+nu*nD and retain DB,DC from the original chart. Set

    EB=DB-b-xB*wB, EC=DC+cvec+xC*wC.

The normalization-free equivalent equations and actual roof position are
proved in
[D02_A_ONLY_REGULARIZED_FORCE_CHART_AND_DIRECT_CAPACITY_ENTRY_2026_10_30.md](D02_A_ONLY_REGULARIZED_FORCE_CHART_AND_DIRECT_CAPACITY_ENTRY_2026_10_30.md):

    |EB|^2*(F.EC)-|EC|^2*(F.EB)=0,               (C)
    |EB|^2*Dmoment-2*(F.EB)*Nmoment=0,           (M)
    lambda=|EB|^2/(2*F.EB)>0,
    Z=lambda*F, R^2=lambda^2*|F|^2.

Here Dmoment,Nmoment are the literal B radial-origin moment expressions in the
three-variable source, with g replaced by F only where it occurs. The actual
circle origin is fixed throughout. Equation (C) compares the two actual circle
corners; equation (M) keeps the complete original radial moment. A virial-only
radius or a freely chosen circle center is never substituted.

The implementation also permits the proved projection filters in
[UNIQUE_CORNER_TWO_FORCE_PROJECTION_FILTERS_2026_10_30.md](UNIQUE_CORNER_TWO_FORCE_PROJECTION_FILTERS_2026_10_30.md).
They are redundant necessary inequalities, not extra hypotheses imposed on an
original packing. The final tree did not need a leaf exit from these filters.

## 4. Why every interval enclosure is valid

All numerical predicates in the certificate use **integer arithmetic**. An
interval [l,h] means the real interval [l/D,h/D], D=2^44. Addition is exact;
multiplication, division, squaring and square root round the lower endpoint
downward and the upper endpoint upward. Square roots use integer square roots
of the appropriately scaled radicands. Division is attempted only when the
whole denominator enclosure avoids zero; a failure to establish this is not an
exclusion.

The sine/cosine half-angle expressions are evaluated monotonically at interval
endpoints. Since alpha+beta is in the retained high-angle interval, H and k
also have their exact monotone endpoint enclosures. The positive-root cubic
uses the monotone Fplus comparison: a uniformly nonpositive value at a rational
probe places every original root above the probe, and a uniformly nonnegative
value places it below the probe. Thirty-five exact bisection comparisons give
a containing interval; they do not assert that the displayed endpoint is a root.

For the direction axes the evaluator uses the following monotonicities rather
than repeatedly normalizing a two-dimensional rectangle:

* For z=c/s in [0,1] and u in (0,1), v=u/(1-z+u*z) increases with u and with z.
* m=t/[H*(H-k)]+k/H increases with t and k on 0<=k<=1/2. Indeed H*(H-k) decreases
  strictly in k there, and k/H increases.
* The own coordinates 1/sqrt(1+x^2) and x/sqrt(1+x^2) decrease and increase,
  respectively, for x>=0.
* For 0<=m<=v<=1, sigma=cos(atan(v)-atan(m)), tau=-sin(atan(v)-atan(m)) and
  sigma+tau decrease as the angle difference increases. Their extrema therefore
  occur at the appropriate opposite parameter corners, with the zero-difference
  endpoint retained if the rectangular intervals overlap.

Every safe intersection is with an independently proved necessary closed range,
including the uniform hub bounds, 0<=m<=v<=1, 0<=xB,xC<=1, the positive transverse
coordinate bounds, the original radius interval, and the fixed physical corner
signs. An empty such intersection means that no original point is in the cell.
An interval sign which is inconclusive causes subdivision; it is not treated as
an absence certificate.

## 5. Splits and contractions cover the whole original domain

A split divides one closed coordinate interval at its exact dyadic midpoint.
Both closed children are retained, so the shared face is covered. No angle mesh
or finite set of representative poses replaces a continuous interval.

Every recorded sector contraction comes from the strict original inequalities

    (1-v)/(1+v) < w < (1-m)/(1+m).

The evaluator intersects the current w interval with outward enclosures of these
two bounds. Every original point remains in the child interval. The removed
strips are therefore excluded by the stated necessary sector condition; they
are not silently omitted. All generated cells have positive coordinate widths.

The checker implements the additional one-variable mean-value contraction from
[EXACT_QUARTIC_SIDE_TORQUE_AND_ONE_VARIABLE_CONTRACTION_2026_10_30.md](EXACT_QUARTIC_SIDE_TORQUE_AND_ONE_VARIABLE_CONTRACTION_2026_10_30.md).
**No such Newton contraction was used in this final tree.** The complete adopted
tree uses only the elementary sector contractions and closed midpoint splits.
There is no derivative or matrix-inverse dependency in its actual coverage join.

## 6. Physical completion leaves count N and all three extra squares

At a cell whose algebraic intervals do not themselves give a contradiction,
reconstruct the five actual physical squares in the unchanged frame:

    P=Z-East-North, RA=P+omega*North,
    QB=Z-DB, QC=Z-DC,
    V=P+[0,1]East+[0,1]North,
    A=RA-[0,1]h-[0,1]e,
    D=P-[0,1]nD+[-t,1-t]tD,
    B=QB+[0,1]b+[-(1-xB),xB]wB,
    C=QC+[-1,0]cvec+[-xC,1-xC]wC.

The interval enclosure retains all four vertices of every one of these five
actual units. A physical-capacity leaf uses one of the exact profiles proved in
[FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md](FIVE_CORE_ROBUST_CENTER_COVER_CAPACITY_EIGHT_2026_10_30.md),
either through its uniform vertex-distance premise or its direct closed
vertex-box interface. The latter compares the same convex combination of the
four actual vertices with each finite spatial cell, using outward enclosures.
The fast dyadic implementation is the same rational distance comparison after
multiplication by a positive common denominator.

The three profiles actually used are:

| Profile | Completion statement used |
| --- | --- |
| `d02_type_ii_a_only_five_core_capacity_midpoint_balls.json` | Every other actual center lies in three disks of diameter below one |
| `d02_type_ii_a_only_five_core_capacity_curve_45.json` | The same conclusion for its separate explicit five-square vertex domain |
| `d02_type_ii_a_only_five_core_capacity_curve_47.json` | The same conclusion for its separate explicit five-square vertex domain |

Distinct unit-square centers have distance at least one, because the open
radius-1/2 incircles are disjoint. Thus each of the three disks holds at most
one other center, and the five core squares admit at most three further squares.
But the original packing has **four** further actual squares: N and the three
completing units. This is a contradiction.

No N slider, physical circle mask, zero-weight contact or completion orientation
is selected or discarded. The capacity conclusion is stronger than a statement
about one particular six-square placement: it includes every original point in
the whole certified parameter cell and every possible placement of all four
remaining physical units.

## 7. Complete finite accounting and assembly

The generated exact tree is
[certificates/d02_l135_a_only_both_unique_cover.json.gz](certificates/d02_l135_a_only_both_unique_cover.json.gz).
Its complete accounting is:

| Item | Count |
| --- | ---: |
| Total nodes | 216,878 |
| Closed midpoint splits | 104,505 |
| Necessary sector contractions | 7,867 |
| Newton contractions | 0 |
| Terminal exclusions | 104,506 |
| Algebraic/range/angle terminal exclusions | 85,313 |
| Physical completion terminal exclusions | 19,193 |
| Pending cells | 0 |
| Unresolved or depth-cutoff leaves | 0 |

The compressed tree is 652,269 bytes. It contains short node records and exact
input metadata, not hundreds of thousands of expanded proof scripts.

Take any alleged original packing in Section 1. Section 2 puts its actual
parameter point in the initial closed box. At each split it lies in at least one
child; at each contraction it remains in the recorded necessary-domain child.
The finite tree ends at a terminal cell. An algebraic terminal cell contradicts
an exact original necessary equation or range. A physical terminal cell
contradicts all nine actual units by Section 6. Therefore the alleged packing
cannot exist. This proves the entire original both-unique A-only side feature.

The theorem uses the already accepted high-angle exclusion as an earlier exit;
it does not silently narrow the original feature to a small angle region. The
full beta-to-pi/4 approach, upper radius equality and every weak completion
contact are covered by the closed comparison domains and strict capacity exits.

## 8. Reproduction and verification boundary

Generate and then replay the finite tree with:

    python scripts/n9_d02_a_only_both_unique_certificate.py --generate
    python scripts/n9_d02_a_only_both_unique_certificate.py

The replay starts from the original root box, reconstructs every midpoint and
necessary contraction, checks every exact terminal predicate, rejects open
nodes, checks source/capacity-data hashes, and verifies that every node is reached
exactly once and every recorded count agrees. It does not trust the generator's
claim that the tree is complete.

**Recorded generation:** CLOSED, 216,878 nodes, pending zero, open zero,
250.61 seconds in the continuation environment.

**Separate full replay:** PASSED, `verified=true`, all 216,878 nodes reached
exactly once, all exact terminal predicates and accounting checked, 73.57 seconds.
The replay did not run the search or regenerate the tree.

The exact tree SHA256 is
`732af6da533fb41fa336ab71ee5bcf0a2f5e80e9a0fb3328bafe5ff5d834466c`.
Its metadata records the complete checker and capacity-data hashes. The generic
capacity proof, original geometric reductions and full positive-hub bounds are
mathematical inputs; version hashes only identify the inputs and are not a proof
of their truth.

This is a complete exact original-feature argument with a compact computational
certificate. It has **not** been compiled in Lean, exported to Comparator, or
replayed by NanoDa. Python remains an untrusted implementation to be replaced by
ordinary kernel-checked certificate soundness and data replay. The original
common-selection/caller obligation, the remaining D02 original features and the
unrestricted sharp n=9/equality theorem retain their separate scope.
