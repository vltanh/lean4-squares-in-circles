# Independent review of occupied inner-pentagon localization

**Verdict: PASS as a complete physical localization theorem, with no
exterior-capacity or whole-load exclusion credit.**

I read and reconstructed all six sections of
`INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md`, SHA256
`37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502`.
The exact recovered source is in the `6f604094721b` workspace. This is a
fresh mathematical review; the existing two recovered review files were
not used as substitutes for the proof.

## Exact physical inputs checked

| Complete operative input | Exact SHA256 |
| --- | --- |
| `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md` | `cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a` |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe` |
| `CONTACT_RING_HOLE_AREA.md` | `50034e7eabf4812c6a9f87a801f07dabe7a444d723c62fdc63d096c6ceb0ec6f` |
| `CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md` | `b61b0dec7ded00984c687e353fd3f3bfb5a5a7ade45d87d69aaeade09f23d80b` |
| `CIRCLE_CONTACT_ANGULAR_ORDER.md` | `e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5` |

These pins match the current `cc143bb36c116590d1de7e7925ad04ca49ea675a`
baseline. I separately checked the original weak-embedding construction,
the complete contact-ring area argument and its long-chord and Fourier
steps, and the exact boundary-order and direct-pocket hypotheses used.

## Reconstruction

The proof first classifies whole open units, before making an area
comparison. A non-rim square's open interior avoids every closed rim
square by physical nonoverlap. Its connected interior therefore avoids
the original center/contact loop. Compatible small Jordan resolutions
preserve winding at its center and throughout that open unit. The
original inner-hub embedding puts the real hub at winding one. No
generic distinct-contact premise is used.

The center-to-chord-midpoint contraction stays in the actual rim units.
For every parameter below one it preserves the cyclic contact order;
coincident strands retain the original selected local sector order.
The available arbitrarily close simple resolutions consequently converge
to the actual contact pentagon. Winding of this limiting polygon is
zero or one off its edges, including retraced portions and tangent
junctions. The homotopy avoids every non-rim open unit and preserves its
classification. Thus a signed polygon area cannot hide cancellation
of differently oriented free regions.

At a chord longer than one, the open chord is in the open interior of
its own rim square, and no other polygon edge enters that open square.
Its winding-one side contains the entire appropriate chord-cut square
piece. The complete geometric long-chord lemma gives occupied area
at least `sqrt(l_i^2-1)/2`; pieces from different rim squares have
disjoint interiors. Subtracting precisely these pieces is legitimate.

For `C=cot(pi/5)/4`, the exact polygon inequality and the continuous
scalar maximum give each contribution
`C x-sqrt(max(x-1,0))/2 <= C` on all of `[0,2]`. On `[1,2]` that
function is convex and both endpoint values are at most `C`, since
`C<1/2`. Hence the free winding-one area is at most
`5 cot(pi/5)/4<2`. The strict comparison is valid:
`cot^2(pi/5)=1+2/sqrt(5)<64/25`, with positive squared reserve
`5*39^2-50^2=5105`. The real occupied hub uses one full unit of
this free area, so even one whole inner completion square is impossible.

The simultaneous actual circle spokes then cut the exterior annulus
with the same original cyclic rim order. Their non-circle pieces stay
in real core units. An extra's connected open interior avoids those
barriers, and the same shrinking-resolution argument assigns the whole
extra to a single pocket, including weak or collapsed junctions.
Additional zero-weight physical contacts can subdivide these regions;
they do not open a route through an occupied barrier.

For a direct marked rim contact, the exact boundary-neighbor rule
identifies the minor ordered circle arc. There are at least three
marked bodies, so the complementary circle arc belongs to other pockets.
The complete physical boundary-pair pocket theorem applies at its
full arbitrary-mean and physical-mask scope and excludes a whole extra
in that direct pocket. No displacement of this actual certificate is
performed during the application.

I checked every path in the source's five-row table and both stated
graph-preserving reflection maps. In four-load rows the last unloaded
rim body must be physically clear by the physical boundary-five-cycle
exclusion. In three-load rows at most one of the two zero-load bodies
can be physically boundary; when one is, adding its real circle spoke
does split its former pocket into two direct empty pockets. Zero load
alone is never mistaken for physical clearance.

## Degree-free scope and limits

Sections 1--4 do not use the hub's degree, any hub-force equation, or
the number of positive spokes. They apply unchanged to the original
four-spoke no-chord graph as well as to the source's five explicitly
listed H2/H3 caller rows. This is already within the source's stated
uniform physical theorem. Literal H4 path bookkeeping is a separate
caller reduction, not a new capacity conclusion.

The source proves all three extras are exterior and belong to the
specified one- or two-pocket union. It supplies no bound on how many
units a longer pocket contains. All original whole H2/H3 load families
listed there therefore remain open at this source alone. All nine
actual units, true degrees, original positive forces, normals, side
means and zero-weight circle masks remain. No ledger, remote object,
Lean source, build or CI was changed in this review.
