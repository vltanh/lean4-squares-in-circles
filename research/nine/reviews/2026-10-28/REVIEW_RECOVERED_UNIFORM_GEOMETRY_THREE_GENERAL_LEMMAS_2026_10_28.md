# Fresh recovery audit of three general geometric lemmas

Date: October 28, 2026 UTC. Reviewer: recovery_audit continuation.

**Result: PASS for the three complete mathematical sources and their
stated literal applications below. Recovery integrity also passes for
all 34 source/review files and all 51 direct table references in the
historical checkpoint. No original obligation changes state.**

## 1. Exact recovery and current accounting

The isolated read base is commit
`a67ff01a9bc496bbfdaa96a6a970b816aa094c56`. The earlier proposed tree
`49cb12f8c03893f48f2c43c7606b1b270008e019` retained files absent from that
commit. Those files were restored by their Git blob identities. This
audit does not replace current metadata with the earlier tree's metadata.

The preserved historical record is
`UNIFORM_RIGIDITY_FULL_STARS_AND_LOCAL_INTERFACES_CHECKPOINT_2026_10_28.json`,
SHA-256
`b4ee0d8843c9ae5f71d700f400494d2e55af927266bcb014c39f0a5ffd98631f`.
It describes its own older base `477ab2ba2242299eb4ede4353b1af0e6ae6bae3a`
and its historical 2,349 checked fine obligations. Its old counts and
metadata hashes are historical data, not the current accounting.

The current accepted counts at the read base are **2,352/2,513 fine
obligations and 34/58 coarse cells**, leaving 161 fine and 24 coarse
obligations open. This review restores no obsolete checkbox state and
gives zero new original-family or coarse-cell credit.

I independently computed SHA-256 and Git blob hashes for every one of
the 34 entries in the historical `source_files_and_reviews` array. Every
digest matches. I separately computed all 51 current dependency hashes
in its `direct_table_pin_checks` array. Every direct pin matches its
current file exactly. The checkpoint itself is the thirty-fifth restored
file; its digest is stated above. All restored source bytes remain
unchanged.

## 2. Complete mathematical sources freshly reviewed

| Complete source | SHA-256 |
| --- | --- |
| FULL_LOADED_STAR_TWO_DIRECTION_AGGREGATION_AND_PROPER_CONCURRENCE.md | da53589e53d4bb702f2ffc7c6ff5c12efd7e3f22fd74adaf70dc4241fbe0e74a |
| UNIT_SUPPORT_POINT_RADIUS_RIGIDITY_AND_SIDE_CHANNEL_MASK_REDUCTION.md | 6d979ed8d53ac8ebf3fe2d8f9110c908aeee1c6c9b5a27f1993266c45585b80a |
| PHYSICAL_SIDE_GAP_CLOSED_BY_TOUCHING_NEIGHBORS_EXCLUDES_UNIT.md | f209207b7aed6ae2bbf8c6fb92dc81d855721173c88060f08a00fb69fdf81492 |

I read all three sources completely and independently rederived their
proofs before reading their complete earlier independent reviews. I
then checked their operative physical, channel and H4 inputs at the
current exact bytes. The other seven mathematical sources in the
historical checkpoint receive a byte-identity audit here, not a claim
of a new complete independent mathematical review.

## 3. Full loaded-star theorem

The grouping is mathematically exact. All original positive forces in
one oriented direction act on the same actual support face. Their
positive weighted mean therefore belongs to that face, and determinant
linearity preserves the full origin moment. No force is removed and no
new physical neighbor at the mean is asserted.

The two geometric witnesses remain valid after grouping. A circle
point is an extreme corner, so a positive average there would put all
original contact points at that forbidden shared circle point. A real
neighbor in each group supplies the original support bound
`h_K(n)<=R-1` through its own width of at least one. The proof does not
assume that a unit exists at the mean.

The entire parallel cover is valid. Opposite directions would require
a positive group pointing toward the full circle resultant, at a
forbidden circle corner or the overhigh outer radial face. One direction
instead gives the exact radial S/D classification from full force and
torque. Positive radiality follows from the diameter comparison, since
the normalized circle average has norm greater than `sqrt(2)`. An actual
boundary neighbor excludes radial D by the sharp diameter equality and
unshareability of its resulting circle point. In radial S, the whole
neighbor has `|x|<=d` and `|y|<=3/2`, whence
`|Z|^2<=d^2+9/4<R^2`. This treats every original point of the full inner
side, rather than a specially chosen average.

I checked the complete rectangle normal-cone partition for the remaining
two nonparallel directions. Coincident means give their actual common
point, positive radiality and zero proper lengths without a three-body
junction assumption. Distinct means in the unique physical circle mask
cannot have an exterior concurrence: the only additional candidate in
the left strip has support at least `R/sqrt(2)>R-1`. Writing `a=b+e`,
the exact scalar identity is

    N=b^2+e*(b+1)+e^2,
    2*N^2-(a^2+b^2)*(a^2+e^2)
      =e*[2*b^2*(2-b)+e*(2+4*b-3*b^2)+e^2*(4-2*b)].

The positive trigonometric support is concave; its two endpoint bounds
are sufficient over the whole stated interval. All displayed
coefficients are positive for `1/2<=b<3/2`.

In the physical two-corner mask, the interval after the outer radial
face is correctly retained. If its transverse coordinate lies in the
closed square interval, every permitted non-circle mean is on the inner
face or an endpoint, and its vector from the concurrence points along
the actual outward normal with positive length. A concurrence outside
the square is not silently moved inside. Both individual zero circle
weights and both transverse endpoints are covered.

The individual export is only the scalar support relation. It does not
assert that all original parallel force lines concur at the grouped
intersection. This distinction is essential and is correctly observed.

The literal H4 application uses the full loaded C3: original CH and CD
have the same directed C-outward axis, their entire two-force group is
kept, and the real B is a boundary neighbor. The roof application is
explicitly conditional on the original AX and AH directions agreeing.
Neither application suppresses a third distinct direction or invents a
degree-two equation.

## 4. General support-point rigidity and channel applications

At a genuinely tilted minimum-support point `(h,z)`, the point is the
actual unique support vertex. For its true inward axes put `k=c+s>1`
and `q=|c-s|<1`. Their exact relation `k^2+q^2=2` gives

    (h+k)^2+(|z|-q)^2
      -[(h+1)^2+(1-|z|)^2]
       =2*h*(k-1)+2*|z|*(1-q)>0.

The reverse-triangle comparison for the transverse coordinate is valid
for every real `z`. No hidden bound `|z|<=1` enters this pointwise
theorem. The uniform corollary states that additional bound explicitly
where monotonicity of `(1-|z|)^2` requires it. The weak radius inequality
forces exact alignment, including its equality endpoint. The exact
uniform comparisons `4+(9/16)^2=1105/256` and the reserve
`3551/57600` are correct.

I read the complete positive-mean channel source and its complete bypass
proof. Its original common mean `q` is not a center height. The full
C2/D3 system excludes both `q<0` and the complete `q=0` endpoint,
including parallel C and both aligned A positions. The radius-free
bypass proof supplies the real transverse separation and unchanged
support points. Thus `h_C=h+1>59/60` and `0<q<=1/3` legitimately force
the actual C frame parallel to B.

For the smaller interval `0<q<=59/238`, the parallel-force alternative
retains the true C2 and its original applications. Its radial D support
is too small, so only radial S remains. In the nonparallel alternative,
the operative rectangle proof gives conditional proper concurrence
without assuming that either original neighbor is boundary. A unique
physical circle corner would then yield

    q>=h_C/[2*(h_C+1)]>59/238,

contradicting the full closed mean interval. The resulting physical
two-corner rectangle retains both circle coefficients independently,
including an individual zero. This is a necessary mask reduction, not
an exclusion of the surviving radial C or of the whole TC family.

## 5. Physical side gap and H4 partition

The whole-square trapping proof is valid. A closed body cannot meet the
open interior of another body with disjoint open interiors. The three
actual contact segments therefore form a triangle boundary avoided by
the open interior of D. At the relative interior of its base, a short
segment toward any interior point of D enters both open interiors. The
connected interior of D consequently lies entirely within the triangle.
No horizontal position of the apex and no graph embedding is needed.

The triangle height is at most the actual unit diameter, so its area is
at most `sqrt(2)/2<1`. It cannot contain the actual unit D. This retains
all corner and side positions compatible with the stated relative-base
interior premise, including endpoint-valued original shared means.

The support criterion correctly places every BC intersection strictly
above the base: a point at or below it would need horizontal coordinate
both at most zero and at least one. Its two weak vertical-normal
endpoints remain included.

In the H-owned-HD, strict-NE-HC domain, the complete HB feature partition
has no omitted axis. The actual AB/BC triangles remove the four owned
axes; opposite strict corners remove NE and SW. A NW normal puts the
two literal H contact points at the two top endpoints, where the entire
side-gap theorem applies. Hence HB is strictly SE. This uses the real
H4 and D3 chart and changes no load at A, B, C or E. The separate East-HC
mean domain and both original full H4 families remain open.

## 6. Operative inputs and exact historical LF reconciliation

Besides the three complete target files, this fresh mathematical audit
read the complete sources for the positive channel mean, unit bypass,
unit triangle support, H4 fixed opposite returns, H4 end-height/owner
cover, H4 shared-end exclusion and fixed-port compatible selector. It
also checked the operative force/moment section of
`PHYSICAL_CONTACT_STRESS.md`, Lemma N.4 and the transmission proof in
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`, the entire relevant rectangle
calculations in `C7_FORCE_POLYGON.md`, the complete Lemma 2.1 in
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, the roof graph/load assignment,
and the physical contact-triangle localization proof. This does not
claim a new audit of the unrestricted minimizer-extraction theorem or
of the global prerequisite chain.

Twenty internal dependency references in the operative channel and H4
sources were also checked. Eleven match current bytes directly. The
other nine are exact one-final-LF differences: the historical digest
equals SHA-256 of the current bytes followed by exactly one extra LF.
The seven distinct affected dependency files are:

- UNIT_BYPASS_NORMAL_CHANNEL.md;
- TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md;
- PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md;
- UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md;
- PHYSICAL_BODY_GRAPH_UNCROSSING.md;
- FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md;
- SIX_BODY_INNER_PENTAGON_LOAD_COVER.md.

Six occurrences are in the positive-mean source and three in the H4
shared-end source. This is an exact byte reconciliation, not an assumed
equivalence between different proofs. No historical pin or source was
rewritten. All 51 direct pins of the restored checkpoint already match
current files without that reconciliation.

## 7. Preservation and remaining work

The three complete statements are approved at their literal hypotheses.
They preserve all nine original squares, actual true degrees, full
original force and torque equations, selected normals, actual
applications and complete shared intervals, physical circle masks and
individual zero weights. All restored source and prior review bytes
are unchanged. This document changes no original fine/coarse ID, order,
denominator, checkbox, metadata file or remote state.

There was no Lean compilation, CI, workflow dispatch, numerical pose
search or computational exclusion certificate. Hash checks are evidence
of source identity, not substitutes for the hand arguments above. The
unrestricted sharp bound, complete equality classification, remaining
global prerequisite audit and Lean integration remain separate open
obligations.
