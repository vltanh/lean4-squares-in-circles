# The whole original lower-house TD family with a genuine S leaf is excluded

Date: October 28, 2026. Author: rooted_blocks.

**Status: complete original-family hand assembly, with both complete
direct interfaces independently and root accepted.** The exact
original-domain join is submitted for its separate full review. This
source introduces no new inequality, motion, contact, force or normal
selection after extraction. It does not change a fine/coarse flag.

## 1. Exact original family and true stars

This is the original fine family

    M6.B5L.HOUSE.LOWER.LTD.S.

The five-body house block has roof T, hubs A,D, lower vertices B,C,
and precisely the positive block edges

    AT, DT, AD, AB, BC, CD.

Its one genuine pendant is BL, with L an S leaf and B the lower
root. The positive block circle-load set is exactly {T,D}. Thus
the whole six-body positive graph is

    AT, DT, AD, AB, BC, CD, BL.

The actual degrees and loads are:

| Body | Positive pair neighbors | True pair degree | Circle load |
| --- | --- | --- | --- |
| A | T,D,B | 3 | Zero |
| B | A,C,L | 3 | Zero; genuine S root |
| C | B,D | 2 | Zero; actual transmitter |
| D | T,A,C | 3 | Positive |
| T | A,D | 2 | Positive |
| L | B | 1 | Positive; genuine S leaf |

An unloaded body is not assumed physically circle-clear. All
physical circle contacts, including zero individual weights, are
retained. The three remaining squares of the original nine-unit
packing are arbitrary and stay present.

The original graph/load cover in Section 4.3 of
FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md contains precisely this
lower-root TD representative. It is distinct from the house-hub
TC family, from the lower-root TA/TAC/TDC representatives, and
from the separate genuine-D-leaf LTD.D family. Neither a hub-root
A4 equation nor a loaded-tip D2 equation is used here: the relevant
full stars are the B3 and unloaded A3 displayed above, and D keeps
all three original pair forces and its circle load.

The radius range is the original examined range

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1.

No extra lower radius premise is imposed by this assembly.

## 2. Common actual channel and complete low/high join

Apply the full physical unit-bypass theorem to the original unloaded
path B--C--D and the actual unit A touching both endpoints. It gives
a genuine side-normal channel of reserve exactly one. In coordinates
about the original circle center, along its actual unit direction n,

    P_BC=(h,q), P_CD=(h+1,q),
    B subset {x<=h}, D subset {x>=h+1},
    C=[h,h+1] x [z,z+1], z<=q<=z+1.

The applications and their common coordinate q are the original
aggregate means. The physical bypass A spans the support interval
[h,h+1] in x and is transversely separated from C. This does not
assert an A--C contact or center q in either side.

The pure contained-unit support theorem at D gives

    h+1<=d.

For d<1 the genuine S root B contains O on its actual inward
unit-normal segment from the real radial leaf point d e. Hence
h>=0, contradicting the displayed support inequality. Both direct
interface proofs include this complete strict-low exclusion.

At d>=1 write d=1+epsilon. The original radius cap gives
0<=epsilon<1/60, and the real point epsilon e in B gives

    -epsilon<=h<=epsilon.

In particular the critical epsilon=0 endpoint is retained. There
is no assumption that an actual radial concurrence is inside a
two-corner loaded square, and no positive circle corner is removed.

## 3. Compatible initial selection and exhaustive frame split

Use the same physical positive-certificate convention as the
original graph reduction. Point-only vertex/vertex normals strictly
expose both vertices, and the compatible finite restrictions are
made before extraction.

The parallel interface uses only that existing strict singleton
convention. The oblique interface additionally uses the genuine
true-B3 fixed-singleton selector at its stated owned-leaf row.
There the leaf direction, channel axis and both application
vertices are pose-fixed; the coefficient determinants are nonzero
on the full retained range. Its source explicitly prelists this
finite condition at every eligible physical tuple before
extraction, with the original matched-junction compatibility. This
condition is compatible with the common strict convention and can
be included in the initial finite list for the entire original
family. No side mean is selected or replaced afterward.

In the resulting unchanged physical packing, the actual unit A
is either parallel to the square C or oblique to it. Here
parallel means equality of the square's two side-axis directions
up to signs and interchange. These alternatives are exhaustive
and disjoint. An endpoint of a side-angle interval that is an
axis alignment belongs to the parallel case; the oblique case
has strictly positive components in its stated frame.

Each direct theorem is invariant under reflection of the entire
packing. The parallel proof reflects the transverse coordinate to
put A below C; the oblique proof puts A above C. These are separate
coordinate choices for their respective physical cases. They do
not interchange the loaded T2 and D3, replace a unit, or move an
application.

## 4. Entire parallel-A/C interface

The complete source

    HOUSE_LOWER_TD_S_PARALLEL_BYPASS_EXCLUSION.md
    de2b585692b350e63be7f6f703a04fa9a8725b7dc5293ea0f241d2bac9ed5dec

applies to every original genuine S-root frame when A is parallel
to C. No B or D frame is supplied as an extra premise: the source
proves that both B and D own the channel axis, using their actual
endpoint support and the strict singleton convention.

Its full actual AB cover is:

1. A positive-length shared AB side. Full B3 forces the real leaf
   West. The complete A3 then excludes both a shared AD side and
   its precise singleton endpoint, using the actual D/T support
   or the strict unit support-span theorem.
2. A singleton AB contact. The full original B3 fixes the genuine
   strict northwest leaf and its radial point. The actual far
   D corner is then outside the circle throughout the entire
   retained mean range.

The full q,z sliders, a possible positive A/C gap, the equality
between the A top and D bottom, both D physical masks, and
epsilon=0 are all included. No D2 concurrence or D-load equation
is substituted. The theorem therefore excludes the entire
parallel alternative of Section 3.

Its separate complete independent and root records are
9f8a8e03 and 99d95b9b, pinned in Section 6 below.

## 5. Entire oblique-A/C interface

The complete final source

    HOUSE_LOWER_TD_S_OBLIQUE_BYPASS_EXCLUSION.md
    da1eaab1fd241da9747389e0f0a05dd5646f380ec8b56190dfae578f0be9fff5

applies when A is oblique to C. Its pure endpoint geometry retains
both the oblique and parallel D frames, with their full actual
AD/CD side means. Its new physical center cap is valid for every
contained unit, with no load, degree, mask or force premise.

The source's full B3/physical feature cover leaves exactly the
following original leaf/incoming possibilities, all of which it
then excludes:

| Actual B frame and leaf | Complete direct exit |
| --- | --- |
| Oblique B with strict lower leaf vertex | Full B3 gives its actual height and incoming-force bounds; D must be parallel; full A3 excludes both surviving AT features |
| Parallel B with strict lower-left leaf | Complete original B3 mean ratio and real leaf bounds give the same full A3 exit |
| Parallel B with genuine West leaf and collinear BA | The entire collinear row is covered, with both D frames, all AD owners, and every AT vertex/side endpoint |
| Oblique B with a genuine owned leaf side | Valid initial fixed-singleton selection, exact original rho/tau identities, and all A3 terms reduce to two D-owned rows; both are excluded with their actual means |

The last row retains the original CD mean on a parallel D side;
it is not treated as a D corner. Its proof splits the actual rho
range only for estimates, covering rho<1/2 and rho>=1/2 completely.
For oblique D the comparison at zero D tilt is an analytic scalar
bound, not a movement or frame replacement. No universal unique-D
mask or false lower-corner height premise is used.

The final source includes the sole review correction to the
strict-V0/B-owned-side torque label: the two stated nonzero
torques are about V0. The full independent review verified that
replacing those words by the earlier label reproduces the exact
old hash 14550fdd; all applications, equations and inequalities
were unchanged. This assembly uses only final da1eaab1.

The separately proved cap

    HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md
    75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8

covers the actual minimum-support equality and the horizontal
normal endpoint. It compares the centers of the real D and T
without deleting any of their forces or circle contacts. Its
complete proof is included in both independent and root audits
of the oblique interface.

Thus the entire oblique alternative of Section 3 is excluded.
Its full separate independent and root records are 15be887d and
fb2f9d8a, pinned below.

## 6. Exact complete direct sources and review pins

| Source or complete review | SHA-256 |
| --- | --- |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | 7ba98ef149c1faff4ef4baeaf0b0305a38cf1153f883a3fe4bfa92087d33622d |
| HOUSE_LOWER_TD_S_PARALLEL_BYPASS_EXCLUSION.md | de2b585692b350e63be7f6f703a04fa9a8725b7dc5293ea0f241d2bac9ed5dec |
| REVIEW_HOUSE_LOWER_TD_S_PARALLEL_BYPASS_TRIANGLE_BRIDGES_2026_10_28.md | 9f8a8e03abcbec5e9ecf6ca3c563e7d6e46d80262ab602982bb2516ab4c3d173 |
| REVIEW_HOUSE_LOWER_TD_S_PARALLEL_BYPASS_ROOT_2026_10_28.md | 99d95b9bfefa851835410ddcc5a96634adae2476d672439c88969a767d4c6aba |
| HOUSE_LOWER_TD_S_OBLIQUE_BYPASS_EXCLUSION.md | da1eaab1fd241da9747389e0f0a05dd5646f380ec8b56190dfae578f0be9fff5 |
| HIGH_VERTICAL_STRIP_AND_NEAR_EAST_UNIT_CENTER_EXCLUSION.md | 75def83e3a67168eb28014641ddfa3d53372028514facaab09529903ba6090f8 |
| REVIEW_HOUSE_LOWER_TD_S_OBLIQUE_AND_CENTER_CAP_TRIANGLE_BRIDGES_2026_10_28.md | 15be887d0d299976099bf59dc2b7df16eb627c9995d53d8f58f486d389111b96 |
| REVIEW_HOUSE_LOWER_TD_S_OBLIQUE_AND_CENTER_CAP_ROOT_2026_10_28.md | fb2f9d8ada25d609e85d029872c832abb5603e73d2f8d7f7cc49a1092d0122f2 |

Every direct source is complete and readable, and each mathematical
interface has full separate independent and root acceptance at
the exact final pin. The complete literal prerequisite manifests
inside the two interface sources remain operative; none is
replaced by a historical hash or a source with a different degree
hypothesis. The present whole-family join has its own separate
review obligation and does not infer that obligation from the
direct mathematical reviews.

## 7. Whole original conclusion

At strict-low radius the common support contradiction excludes
the original family. At every critical or strict-high radius,
the actual bypass is either parallel or oblique to the actual
channel square, and Sections 4 and 5 exclude those entire
alternatives. These cases preserve every original B leaf feature,
actual contact owner, selected normal, side mean, circle mask and
individual zero weight. All nine actual squares remain present.

Consequently the entire original

    M6.B5L.HOUSE.LOWER.LTD.S

family is impossible. The separate genuine-D companion remains
the already reviewed HOUSE_LOWER_TD_D_COMPLETE_EXCLUSION.md; it
is not a missing branch of this S-family join. No other lower-house
load orbit, whole house graph, or coarse C1.5.b1 cell is declared
closed by this theorem. There is no motion, numerical packing
premise, post-extraction choice, shared accounting change, remote
mutation, Lean compilation or CI operation.
