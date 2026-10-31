# Adopted broad hand theorems: physical cap, unloaded cuts and endblock interfaces

October 31, 2026. Input branch head a965eb1133fb31e1b685da49e619d8fe8f6ef274.
The physical cap theorem and its two main hand reviews were first attached to
the branch in b873732506f2fc2fcec3fbdf2d0820daab679379.

**Unrestricted n=9 optimality is still OPEN. New original fine/coarse
closures: zero.** Original progress remains 37/58 coarse, 2373/2513 fine,
18/38 exterior six-body rows. This continuation proves broad mathematical
families without renaming them as new original gates. Every new proof below
has a separate hand reconstruction. No Lean, CI, mathematical scripts,
numerical sampling, or generated proof certificates were used.

## 1. A new sharp terminal that does not require common coordinate separation

Main source:

    PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md

For two arbitrary actual disjoint-interior unit squares M,B in D_R with
R<=sqrt(1105)/16, any unit direction e, and their actual projection
halfwidths h_M,h_B, the new theorem is

    46[-e.c_M-h_M(e)] + (27/2)[-e.c_B-h_B(e)] <= 211/4.

It is strict if R<sqrt(1105)/16. Equality forces the two frames to align
with e and their centers, in that frame, to be

    M=(-3/2,sigma/16), B=(-1,-15sigma/16), sigma=+-1.

This is a physical two-square statement. The proof selects an actual
separating axis owned by one square, keeps the other square's arbitrary
orientation, and uses an exact triangle bounding-rectangle minimization.
There are five distinct scalar ownership entries. Both full normal halves
are covered by convexity, short rational tables and one explicit quartic;
there is no sampled pose cover or omitted oblique pair.

Consequently **any seven physical squares forming two disjoint projection
chains of lengths four and three along one direction already force the
sharp radius**. Their weighted endpoint-span lower bound is exactly

    2*46+27/2 = 2*(211/4).

Applying the cap bound to the two actual endpoint pairs proves the result.
No other pair needs coordinate separation, and the remaining two physical
squares may have arbitrary orientations. The old endpoint interlocking and
common-coordinate-separation premise are unnecessary for this terminal.

The complete equality statement pins the four outer anchors and forces all
seven chain frames to align, while retaining their allowable perpendicular
sliding and arbitrary additional units. The known example with no globally
separating orthogonal frame passes: its seven anchors supply the chains even
though its two extra squares require an oblique separating axis.

The literal full-stress caller permits vertex-disjoint paths A-U-V-B and
C-W-D with U,V,W genuinely unloaded of true degree two and parallel
propagated normals. Endpoint degrees, chords elsewhere and all actual means
are unrestricted. A branch is never made degree two by deleting forces.

Reviews:

- REVIEW_PHYSICAL_CAP_POSITIVE_NORMAL_AND_RECTANGLE_REDUCTION_INDEPENDENT_2026_10_31.md
- REVIEW_PHYSICAL_CAP_NEGATIVE_HALF_AND_EQUALITY_ENDBLOCK_2026_10_31.md
- REVIEW_PHYSICAL_CAP_REDUCTION_AND_CHAIN_APPLICATION_ANNULAR_2026_10_31.md

The only correction found was the transcription B(19/20)^2=872289/1280;
the original bound was valid and the manuscript now contains the corrected
integer. All required scalar and geometric scopes passed hand review.

## 2. An unloaded tree cannot hide arbitrarily many bodies behind a small cut

Source and review:

    BRANCH_GLOBAL_FULL_CUT_TREE_SIZE_AND_DIRECT_FORCE_BUDGET_2026_10_31.md
    REVIEW_GLOBAL_UNLOADED_TREE_CUT_BUDGET_ROOT_2026_10_31.md

For any connected entirely unloaded tree K whose **full original positive
cut** has p>=3 edges,

    |K| <= 2p-3.

Thus a three-edge cut has at most three unloaded tree bodies. Every four-or-
more-body unloaded tree behind such a cut is excluded at once, independently
of outside degrees, repeated terminal squares, normal ownership and means.

The new quantitative core is a complete reduced force identity on each
direct-contact component S of unloaded branching bodies:

    Z_S > (29/60) C_S + I_S,

where C_S is its outgoing force magnitude, Z_S is the part carried by direct
exits, and I_S is its actual internal support work. Exact nonnegative width
reserves can be retained too. This forces every such component to have a
direct original cut exit. Degree counting then limits the number of actual
transmitter bodies. It does not require the outside endpoint to be loaded.

For p=3 the complete unordered arm cover is (0,0,0), (1,0,0), (1,1,0).
In the last case its direct force z and two subdivided-arm forces a,b obey
29/31<z/(a+b)<=1. No near-parallelism is inferred from this when a or b can
be arbitrarily small.

For cyclic K the proved extension explicitly retains cycle rank:

    |K| <= 2p-3+3 beta-eta-beta_0.

Discarding the beta terms would be invalid. In particular the existing exact
eight-body cross has a cyclic unloaded center and is not a counterexample;
its direct-force inequality has exact reserve 1/15.

## 3. A universal boundary-contact margin and arbitrary-degree interface pressure

Source and review:

    ENDBLOCK_GLOBAL_CONTACT_POINT_MARGIN_AND_COMMON_SIDE_PRESSURE_2026_10_31.md
    REVIEW_ENDBLOCK_GLOBAL_CONTACT_MARGIN_AND_COMMON_SIDE_ANNULAR_2026_10_31.md

For all nine actual squares with 2<=R<=sqrt(1105)/16, whenever H physically
touches a physical circle-touching square at any actual point p,

    c_H.p > 11401/4155200.

This has no origin-containment, force, degree, orientation or positive-load
premise. The proof combines the existing radius-dependent central-disk
theorem with |p|>=R-sqrt(2), |p-c_H|^2<=1/2, and one exact completed square.

Now retain a genuine endblock cut at an actual origin-containing root H.
If every root neighbor on the cut is physically boundary and all its actual
applications lie on one root side, its full cut resultant satisfies

    c_H.F >= 0,    c_H.F=0 implies F=0.

All resultant slopes and cut degrees are included. The key identity is
a(c_H.F)=sum alpha_e(c_H.p_e), using the original zero origin moment and
the actual root side height a. The proof handles zero a, zero normal sum,
and tangential endpoint forces separately. It does not apply a positive-
height formula to an origin-passing side.

Two genuine common-side boundary interfaces at an origin-containing clear
root are therefore excluded in the stated support-minimal certificate.
For a negative-pressure interface of arbitrary degree, an exact weighted
sum extracts an actual opposite-moment witness pair that cannot share one
root side. The witness pair is not claimed to be a physical subcertificate.

## 4. Negative radial access has a whole-angle restriction

Source and review:

    ANNULAR_GLOBAL_CENTRAL_UNIT_ANTIRADIAL_ACCESS_THEOREM_2026_10_31.md
    REVIEW_ANNULAR_GLOBAL_ANTIRADIAL_ACCESS_ENDBLOCK_2026_10_31.md

For an actual origin-containing square H, write its own center coordinates
as 0<=y<=x<=1/2 and theta=atan(y/x). If a physical neighbor has an actual
circle corner z with c_H.z<=0, then

    x^2+y^2 > (x-y)/2,
    sin(2theta) >= 4(R-sqrt(2))^2-1.

The complete angular domain is handled by an exact support maximum on the
anti-radial semicircle and one convex quartic with reserve 103/6400. The
resultant corollary applies to an entire collection when every positively
loaded member physically touches H; arbitrary internal graphs are allowed.
That adjacency cannot be inferred merely from membership in one endblock.

## 5. Scope across the unchanged original families

| Original family | New complete implication available | Qualitatively different remainder |
| --- | --- | --- |
| Any of the 21 parents, or no selected stress at all | Actual parallel 4+3 projection chains force the sharp radius | A universal extraction of such chains is not proved |
| All 11 one-block parents | Full-cut unloaded tree-size and direct-force budgets; unrestricted transmission-path cap caller | Cyclic unloaded modules, short/branching cores and full joint completion |
| All 10 two-block parents | Original cut identities, common-side boundary-interface pressure and mixed-side witness extraction | Mixed root sides, circle-clear root neighbors, distant loads and origin containment where not already proved |
| Any nine-square physical caller | Universal positive center/contact-point margin | It does not assert positive center/normal or center/circle-corner projection |
| Origin-containing central unit | Whole-angle restriction on negative neighboring circle access | Diagonal central frames and nonadjacent positive circle loads |

None of the hypotheses in the middle column is automatically established
by a coarse graph name. The original parent counts therefore remain fixed.

## 6. A precise remaining global extraction problem

The existing long-channel straight-line barrier places all five physical
extras on the two sides of an actual four-square force channel. The new
terminal finishes a side allocation when it supplies a parallel three-chain.
But "three on one side always form such a chain" is false.

An exact negative control is the eight-square cross at R^2=17/4. Choose
the four-channel centers

    (-3/2,0), (-1/2,-1/2), (1/2,-1/2), (3/2,0),

with force line y=0. The upper triple

    (-1/2,1/2), (1/2,1/2), (0,3/2)

forms a T, not a horizontal three-chain; the eighth unit is (0,-3/2).
All coordinates are exact and the center-contact interpretation is physical.

A useful sufficient next theorem would prove that any 3+2 allocation of the
five actual extras either supplies the new 4+3 terminal or forces the
opposite-side capacity below two. This is a **missing joint theorem**, not
an established reduction of all remaining configurations to a small case.
Short branching blocks without a long channel remain an additional global
class, and the two-block interfaces retain the exceptions in Section 5.

The unrestricted sharp-radius bound, complete equality classification and
downstream G4.2.c compatibility audit remain open. The fixed original
coverage ledger is unchanged; this document adds no artificial progress
denominator or new original case IDs.
