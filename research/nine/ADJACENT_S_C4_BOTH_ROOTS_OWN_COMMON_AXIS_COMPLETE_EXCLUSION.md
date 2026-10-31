# Complete adjacent-S C4 exclusion when both roots own their common contact axis

Date: October 27, 2026.

**Status: complete exact whole-interface assembly, submitted for full
root and separate independent join review.** Every substantive exit below
has a saved full independent review. This closes all physical boundary
masks of the high LCD.SS component when both roots own AB. It does not
claim the remaining exactly-one-owner interface or the whole C1.4.b2
cell closed.

## 1. Original domain and compatible necessary certificate

Retain the same nine actual units and the full positive component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

The leaves L,M are genuine S units. A,B are physically clear genuine
roots, and C,D have positive total circle loads. Every actual physical
circle corner remains in its mask, including a corner with zero individual
weight. Work in the declared strict-high range

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60, R^2<=1105/256.

The common domain is
ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md.
It retains the original full equations, physical circle-spoke order and
nonzero common cycle moment. The unique/unique mask has an actual AB
side owner by its compatible force-cycle selection. At a radial
two-corner boundary unit, the complete
RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md
supplies the corresponding original owner cover. This assembly takes
the entire case where **both** roots own that actual normal. Their
physical own frames are therefore parallel; no orientation of C or D
is assumed.

The necessary certificate is the same original pre-extraction one.
All finite determinant avoidances, the strict point-normal convention,
the actual matched-junction and uncrossing rules, and the open
near-bisector condition at radial/radial contacts in the both-two-corner
proof are imposed compatibly before extraction. The complete selection
proofs establish that compatibility. No selected normal is reselected
here, and no shared side mean is replaced by a point used in another
case. The all-cycle owner theorem is invoked only in its actual
unique/unique, nonparallel-root-pair domain.

## 2. The complete physical-mask split

Every physical boundary unit has one or two circle corners, as in the
original common domain. Thus the following three rows are exhaustive.

| Actual C,D physical masks | Complete whole-interface exit |
| --- | --- |
| Both two-corner | ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md |
| Exactly one two-corner | ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_EXCLUSION.md, with the actual attachment reflection if needed |
| Both unique-corner | The exhaustive original leaf-feature join in Sections 3--4 below |

The first row is the complete physical-mask theorem at source pin
`e55398acb2f544139113cfa30f93f8dd9dd68656c40d9ba0cfc4c20aeb7f870f`.
Its full independent review is
REVIEW_ADJACENT_S_C4_BOTH_TWO_CORNER_MASK_HEXAGON_2026_10_27.md.
It already excludes this whole mask; no positive circle weight is
deleted to move it to a different row.

The second row is the complete original both-owner mixed-mask theorem,
source pin
`a57c2f2892d46db72877f66632fdefba094180f26b6e89b07797de0545391523`.
It retains the radial unit, the other unique-corner true D2, both full
root equations, every side mean and all nine units. Its full independent
review is
REVIEW_ADJACENT_S_C4_MIXED_MASK_PARALLEL_ROOTS_HEXAGON_2026_10_27.md,
pin `59e6452f90599e72849991b9784b8c01c0ee9de39f86304a4efaca381a888e40`.

## 3. Complete unique/unique root-leaf cover

Use the complete necessary-domain source
ADJACENT_S_LEAF_C4_PARALLEL_ROOT_LEAF_REDUCTION.md,
pin
`702eba704af93e67b85b9101a947ae5b3fe9134e194de64d87e5820e9fcc379b`.
Its separate full independent review is
REVIEW_ADJACENT_S_PARALLEL_ROOT_LEAF_REDUCTION_ROOTED_BLOCKS_2026_10_27.md,
pin `c0faabfe29d1b5cb750b81f7c3bc8e1f1285325866ec6671448fd4a4e6f1f9b9`.

That theorem exhausts all eight physical support features of both
genuine leaves. It removes the upper and near-side alternatives using
the unchanged root equations, actual circle order and the owner-free
true-D2 port cap. In particular the horizontal-root exception is not
passed through an all-nonparallel-force-pair theorem.

Exactly the following original leaf types remain:

1. Both leaves are strict outer lower vertices. Their actual roots are

       A=[h-1,h] times [-v,1-v],
       B=[h,h+1] times [-w,1-w],
       (1-h)^2+v^2=(1+h)^2+w^2=d^2,
       0<v,w<13/50,
       P_AB=(h,-k), 0<k<=min(v,w).

2. One root has its owned horizontal outer leaf and the other its
   strict outer lower leaf, in either reflected labeling. In the West
   labeling h=-epsilon, the real AD normal is East with its original
   positive mean, and the full actual endpoint constraints remain.

Two simultaneous horizontal leaves are impossible at epsilon>0.
The theorem does not assume a grid or assign an orientation to C,D.

## 4. Exact complete exits for every surviving leaf type

### 4.1. Both strict leaves, smaller depth greater than 1/8

The force-free physical theorem
TWO_PARALLEL_ROOTS_OUTER_RADIAL_LEAVES_CAPACITY.md applies to the
four actual units A,B,L,M when min(v,w)>1/8. They admit at most
four further actual units in the containing circle, regardless of
orientation. The original nine units supply five further units,
including C,D and all three completion squares. This is a direct
same-nine contradiction.

The source is pinned at
`be87f34b2c973138703e1ea63fb4d33221e530057f7446babcd1917467c4769e`;
its full independent review is
REVIEW_TWO_PARALLEL_ROOTS_OUTER_LEAVES_CAPACITY_TRIANGLE_BRIDGES_2026_10_27.md,
pin `b75f15b5f8ee3fc89c3b42e8d6c93f1356ad350edee49fe48996f24a3427fd80`.
The actual closed occupied arcs, arbitrary extra orientations and
strict 1/8 clearance were all included in that review.

### 4.2. Both strict leaves, smaller depth at most 1/8

The complete original force-and-geometry theorem
ADJACENT_S_C4_PARALLEL_ROOTS_SHALLOW_DEPTH_EXCLUSION.md applies to
the complementary closed range min(v,w)<=1/8. It keeps the entire
actual C/D axis or tilted frame cover, every original North-side
mean and every endpoint of the original CD owner cover. Its final
comparison uses the equal actual circle radii and the two genuine
unique-corner inequalities. No smaller balanced core is substituted.

The source is pinned at
`d576ee24fc25ccc703520bccaad56b764a9a680015a570dcd460133c0a0ed344`;
its full independent review is
REVIEW_PARALLEL_ROOTS_SHALLOW_DEPTH_ROOTED_BLOCKS_2026_10_27.md,
pin `b16b4b988567d8abfe91d4d6f92923b575096a18c7adf75f762946a9c9648d20`.
In particular this range includes depth exactly 1/8 and all retained
common-vertex and zero side-parameter limits.

### 4.3. Either horizontal genuine-leaf endpoint

The whole source
ADJACENT_S_C4_PARALLEL_ROOT_HORIZONTAL_LEAF_EXCLUSION.md applies to
the complete horizontal feature from Section 3, in either reflected
labeling. It excludes North and both strict upper BC vertices, with
arbitrary actual C/D orientations. Its outward-vertex argument uses
the original full B3 ratio and an actual inward unit segment; it
does not require a C owner at the horizontal-root exception.

The source is pinned at
`351ce9a731e42464e26591b88e239ec5816eae08fce23b557042eace5554bb1a`.
Its full independent review, including the contributed Northeast
calculation, is
REVIEW_PARALLEL_ROOT_HORIZONTAL_LEAF_ROOTED_BLOCKS_2026_10_27.md,
pin `18e7c69a107b9cfdfddd5f5c0fe972ace41b20af7221546dffb5b390c03ca93f`.
The additional scope review
REVIEW_PARALLEL_ROOT_HORIZONTAL_LEAF_SCOPE_TRIANGLE_BRIDGES_2026_10_27.md
explicitly distinguishes its author's contribution from its independent
review of the remaining sections.

## 5. Whole original-interface conclusion

The three physical-mask rows in Section 2 are exhaustive. Within the
unique/unique row, the complete actual root-leaf theorem gives exactly
Section 3. Its strict-leaf type is partitioned by min(v,w)>1/8 and
min(v,w)<=1/8, with no missing equality. Its horizontal type is covered
in both labelings. Every cited exit has the same full original graph,
degrees, physical masks, actual means and nine-unit completion scope.

Therefore **no high LCD.SS component in which both roots own the
actual AB contact axis exists in the compatible original certificate**.
This is the whole both-owner interface across all physical C/D masks.

The exactly-one-owner interface remains a separate original domain.
This assembly does not mark the high LCD.SS gate or C1.4.b2 cell
complete. No positive force, physical corner, actual mean, completion
square or true degree was deleted, and no numerical pose, compilation,
CI, remote action or shared-metadata edit supplies the proof.
