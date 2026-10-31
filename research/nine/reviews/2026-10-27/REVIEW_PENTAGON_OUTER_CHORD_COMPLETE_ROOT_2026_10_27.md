# Root audit: the complete positive-outer-chord pentagon branch

Date: October 27, 2026.

**Verdict: ACCEPT both entire original graph exclusions H2_D1 and
H4_D1.** The six-body coarse cell and the unrestricted nine-square
theorem remain open. No shared ledger is changed by this record.

## 1. Frozen source and independent review

I read the complete source
`CHORDED_HEXAGON_PENTAGON_OUTER_CHORD_COMPLETE_EXCLUSION.md`, SHA-256
`44ebc94621948142baa04160ebc39ed4d2f28f55f280367c29e5449e401db3eb`,
and the full separate review
`REVIEW_PENTAGON_OUTER_CHORD_COMPLETE_ROOTED_BLOCKS_2026_10_27.md`,
SHA-256
`198ee650b56c715cf1326ae23a2e4c0841aa5f1029f9f3e55237abe6f8305bd2`.

I reread the actual complete graph cover in
`SIX_BODY_CYCLIC_FRONTIER.md`, Sections 5--6.3a, and the full
`SIX_BODY_INNER_PENTAGON_LOAD_COVER.md`, SHA-256
`cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a`.
The full occupied-four-ring proof and its boundary equality were
reread in `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md`, SHA-256
`f4995aed33273c00c6695d96ff0a6a3b2723779784fcd719f29d9f40e047a752`.
The compatible strict-normal selection and its persistence under
uncrossing and sparsification were checked directly in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Sections 1--4. Its physical
embedding theorem was already accepted in the root chain.

## 2. Complete original graph and physical enclosure

The spoke sectors permit an outer chord only for the actual two-spoke
and four-spoke cases, up to the original pentagon symmetries. For two
spokes these are H0,H2 and chord03 (or its reflected chord24); for four
spokes they are H0,H1,H2,H3 and chord03. The three-spoke case forbids
each candidate chord by the true unloaded-degree-three theorem, and
the five-spoke case has no available chord sector. Thus the source
covers the entire positive-outer-chord pentagon branch.

In either retained graph the unchanged embedding places actual H on
the bounded side of ring0123 and body4 on the other side of chord03.
The inner-square homotopy in the source retains winding one throughout
H's whole open interior, including all shared junctions and endpoint
means. The degree-free equality argument uses no boundary premise in
its first two sections. It therefore forces the actual five units
H,0,1,2,3 to be the entire aligned cross, not merely a comparison
polygon with the same area.

## 3. Full original force proof

Every surviving point-only ring contact retains its original strictly
exposing normal. At body1 both ring forces have strictly negative
vertical component; its actual H1 force, if present, reinforces that
sign. At body2 both ring forces have strictly positive horizontal
component; the actual H2 force also reinforces it. Hence the complete
stars force positive circle loads at both1 and2 without inventing a
missing spoke or lowering either body's degree.

Physical circle contact at0 or3 would give three boundary units in
the occupied ring. The complete equality calculation then forces
R^2=5/2, whereas the declared lower bound gives

    (79/40)^2-5/2 = 2241/1600 > 0.

Thus0 and3 are physically clear, not merely zero-loaded. Their full
force equations force the04 normal to have strictly positive
horizontal component and the34 normal strictly negative vertical
component. Chord03 and every existing H spoke remain in those sums.
In particular body3 is true degree three in H2_D1 and true degree
four in H4_D1.

The actual common means must therefore be

    P04=(3/2,y), -1/2<=y<=1/2,
    P34=(x,-3/2), -1/2<=x<=1/2.

Both belong to the same actual unit4. Its diameter bound forces
x=1/2 and y=-1/2 and makes these its opposite vertices. The resulting
physical unit4 has a full horizontal shared side with0. That side's
only common supporting normal has zero horizontal component, in
contradiction with the complete0 equation. A mean at its endpoint
does not permit a different normal. This covers the entire actual
mean intervals and all circle masks and weights of unit4.

There is also a shorter independently accepted route after Section2:
`GENERAL_OCCUPIED_CROSS_NINE_UNIT_EXCLUSION.md` excludes all nine-unit
packings containing this actual cross, with arbitrary disk offset and
all four other physical units. The root record for that theorem is
`REVIEW_GENERAL_OCCUPIED_CROSS_NINE_UNIT_ROOT_2026_10_27.md`. This is an
alternative whole-domain route, not a replacement for a missing force
case; the source's complete force proof above is itself accepted.

## 4. Exact original joins and limits

The accepted original IDs are exactly

* `M6.B6.PENTAGON.H2_D1.L124`;
* `M6.B6.PENTAGON.H2_D1.L134`;
* `M6.B6.PENTAGON.H2_D1.L1234`;
* `M6.B6.PENTAGON.H2_D1.L0124`;
* `M6.B6.PENTAGON.H2_D1_EXIT`;
* `M6.B6.PENTAGON.H4_D1.L124`;
* `M6.B6.PENTAGON.H4_D1.L0124`;
* `M6.B6.PENTAGON.H4_D1_EXIT`.

The proof is independent of the load list and therefore also covers
the earlier exited H2_D1.L024 domain and every permitted original
image. No new fine IDs are created. No no-chord H--4 noncontact premise
is imported. All nine actual squares, all positive forces, physical
zero-stress contacts, zero individual circle weights, selected normals
and unchanged common means remain. The three no-chord pentagon graphs
and all other open six-body domains retain their obligations.

No sampling, numerical optimization, Lean compilation, CI, remote
mutation or shared-ledger edit was used.
