# Four-spoke pentagon: the boundary neighbor opposite an H-owned unloaded end

Date: October 28, 2026 UTC. Author: frontier_audit continuation.

**Status: complete proposed radius-free necessary sign implication,
preserved for full root and separate independent review. No original
family or gate closes.**

Retain the exact actual six-body graph and whole-star hypotheses of
INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md:
the physical contacts HA,HB,HC,HD,AB,BC,CD,DE,EA; the full unloaded
positive H4 star A,B,C,D; and the full unloaded positive D3 star
H,C,E. A,B,C,E have arbitrary true degrees and loads. All original
normals, side means and singleton conventions are unchanged.

Suppose the actual HD normal is H-owned. By the complete shared-end
source, rotate and if necessary reflect the whole configuration so

    H=[0,1]^2, n_HD=North,
    n_HA,x<0, n_HA,y<0.

The same source gives n_HC,y>=0 from the actual triangle HCD.

**Claim.** Necessarily n_HC,x>0. Thus the original HC feature is
strict Northeast at (1,1), or an actual East side axis with its
unchanged mean. In particular it is on the opposite horizontal
side from the original strict Southwest HA feature.

Suppose n_HC,x<=0. The full original H force equation, with all
four strictly positive pair magnitudes, then forces n_HB,x>0,
because HA has strictly negative x component and HD has zero.

The positive x component leaves exactly three possible HB
feature types: strict Northeast, East axis, or strict Southeast.
Northeast is opposite the strict Southwest HA vertex, and the
physical AB contact forbids those opposite strict corners.
East is H-owned and its dot product with n_HA is negative;
the actual triangle HAB forbids it by the owned-axis triangle
lemma. Consequently HB must be strict Southeast.

Now n_HC,y>=0 and the supposed n_HC,x<=0 leave exactly
strict Northwest, West axis, or North axis. Northwest is
opposite the strict Southeast HB vertex, contrary to physical
BC contact. The H-owned West axis has negative dot product
with n_HB because n_HB,x>0. The H-owned North axis likewise
has negative dot product with n_HB because n_HB,y<0.
The actual triangle HBC forbids both axis endpoints.

All unit-normal possibilities have been exhausted, proving
the claim. No torque equation or degree assumption at B,C
was used, and no force was removed from H.

## Scope and exact inputs

| Source | SHA256 | Scope |
| --- | --- | --- |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 | Complete H-owned unloaded-end sign reduction, all-four-force hub equation and exact tilted-D residue |
| INNER_PENTAGON_FOUR_SPOKE_BOTH_END_AXES_EXCLUSION.md | e1106b043b8b6b61899177a7e68121fce49c65e3ebf86273ef332cf451f437bf | Complete opposite-strict-corner contact obstruction |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Degree-free physical triangle consequence for an actual owned side axis |

The first two sources are exact recovered bytes. Their older
dependency pins and the current terminal-LF-equivalent texts
are reconciled by

RECOVERED_H4_END_OWNER_INTERFACES_DEPENDENCY_AUDIT_2026_10_28.json,

SHA256 8f056eb6823a8c0bc87d9b2c8b3d6fe105f6457985dd0e85a9bdae5dc96d8e8e.

For both original H4_D0 load families substitute
(A,B,C,D,E)=(0,1,2,3,4). If a whole reflection was used above,
it transforms the geometric frame without changing actual
vertex labels or load roles. This is only a necessary sign
classification in the class where the actual unloaded end's
normal is H-owned. The other owner classes and all arbitrary
completion units remain.

No whole H4_D0 family is excluded. No additional contact,
origin-clearance condition, chosen mean, numerical pose,
Lean compilation, CI, metadata change or remote write is
part of this implication.

