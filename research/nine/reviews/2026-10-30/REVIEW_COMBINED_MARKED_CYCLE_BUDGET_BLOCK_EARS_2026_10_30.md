# Review of the combined marked-cycle budget and five-mark C8 reduction

Date: October 30, 2026 UTC.

**Verdict: PASS for the complete frozen literal join. No repair requested.**

Read the entire source
`COMBINED_MARKED_CYCLE_BUDGET_AND_EIGHT_BODY_FIVE_LOAD_SIDE_REDUCTION_2026_10_30.md`,
5,885 bytes, SHA256
`dbb9eaeee362c2148a6ada5319a05e0b962b5fdd2ea5ed36772e8175c8af005f`,
Git blob `350b8dcf921629506708b24e432a96488dd4222f`.

The reviewer authored the imported base marked-cycle theorem and
independently reviewed both newer geometric refinements. This review
checks the complete new arithmetic join and its exact same-certificate
callers; it does not claim independent authorship of the base theorem.

## 1. All three literal inputs and the uniform inequality

The frozen input hashes match the previously read complete sources:

- Base marked-cycle theorem: `b5d9f55141ca2ab2c4f4195de68a714340fa2de607b8b9e81bb484578e4b16be`.
- Long and diagonal refinement: `614382093c6c976e7767855c5234419fe3a3c477bafc8c4465e46d86446e56fc`.
- Obtuse unit-gap theorem: `fa63e0ef4a0d94d47ff05e848b46792ac2861d0504b8369bc109beb3fd7d5e5a`.

Their radius, physical boundary marks, common-normal runs and compatible
embedding premises agree. Their strict angle costs are respectively
40,90,105,175 degrees for direct, non-diagonal singleton, diagonal
singleton and long runs. The actual full-turn center order is supplied
by the unchanged base proof.

With d a subset of the singleton count k1, the exact sum is

    40*k0+90*(k1-d)+105*d+175*ell
      =40*m+10*k1+15*d+55*ell<360.

Dividing by five gives an integer strictly below 72, hence exactly

    8*m+2*k1+3*d+11*ell<=71.

No minor-angle equality, implicit equal radius, or missing endpoint
case enters this sum.

## 2. Every row of the eight-body count table

For m=8, ell>=1 is impossible because 64+11>71. Thus ell=0,
k1=8-t and 2*k1+3*d<=7. The nonnegative direct count gives k1<=4
and t>=4; t=4 would require 8<=7. The remaining exact rows are:

| Marks | Singletons | Allowed diagonal singletons |
| --- | --- | --- |
| 5 | 3 | 0 |
| 6 | 2 | at most 1 |
| 7 | 1 | at most 1 |
| 8 | 0 | 0 |

The source labels these as necessary count restrictions, not physical
existence claims or reversals of other exclusions. In particular the
five-mark row with one diagonal would give 73<=71, so every cyclic
placement of that diagonal feature is excluded.

## 3. Full-force versus full-moment callers

The geometric inequality uses actual support widths. Full translational
balance on genuine unloaded true-degree-two internals supplies common
normals but does not discretize their widths. The source correctly
requires the same certificate's full moment equations before converting
the absence of diagonal-width singletons into the statement that every
singleton is side-normal.

All marked endpoint forces and arbitrary additional positive edges
remain in the full graph. The compatible drawing, true degrees and
circle predicates belong to the same retained certificate. The source
does not transfer degrees between stress selections.

The record orbit has expression 56+2+11=69 and is preserved; its
diagonal-short variant gives 72 and is excluded. The five-mark all-side
C8 family and other permitted count rows remain beyond this inequality.
No original gate, proof certificate, Lean file or remote state was
changed by this review.
