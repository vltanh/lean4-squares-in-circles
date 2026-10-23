# A sharp theorem for at most three columns

**Scope.** All ten squares share one orientation, and their centres lie on at
most three lines parallel to an edge axis of that orientation. The lines need
not start one unit apart. Translate the disk centre to the origin and rotate
the common square frame so these lines are vertical. Relabel as necessary.
This is a restriction on the packing, not a consequence of unrestricted
`Packing`.

**Theorem.** Such a packing requires `R ≥ 3/√2`. At equality it has exactly
three columns, at `x=-1,0,1`, containing respectively 3, 4, and 3 squares.
The outer heights are exactly `-1,0,1`. The four middle heights satisfy

`−L ≤ t₀`, `t₀+1 ≤ t₁`, `t₁+1 ≤ t₂`, `t₂+1 ≤ t₃`, `t₃ ≤ L`,

where `L=(√17−1)/2`. Conversely, all these configurations attain the bound.

## Proof

It suffices to classify a packing with `R ≤ R* = 3/√2`; put `q=R² ≤ 9/2`.
For every centre `(x,y)`, containment gives

`(|x|+1/2)² + (|y|+1/2)² ≤ q`.

In particular `|y| ≤ R−1/2 ≤ R*−1/2 < 2`. Any subset of centres whose
heights are pairwise at least one apart has at most four members: five would
span at least four, whereas every height lies strictly between -2 and 2.

**Column count and separation.** Centres on the same vertical line must have
heights at least one apart. Each column therefore holds at most four squares.
Ten squares on at most three lines require exactly three nonempty columns;
each has at least two members. Write their coordinates as `x₁<x₂<x₃`, and
their populations as `m₁,m₂,m₃`.

If two columns have horizontal gap less than one, every cross pair must be
vertically separated by at least one. Their union is then a vertically
separated set of size at most four. But any two of the three populations sum
to at least six, because the omitted column holds at most four. This is a
contradiction. Hence `x₂−x₁ ≥ 1` and `x₃−x₂ ≥ 1`, so `x₃−x₁ ≥ 2`.

**No outer column has four squares.** If an outer column has four, its height
span is at least three, so one centre has `|y| ≥ 3/2`. Its column coordinate
therefore satisfies

`(|x|+1/2)² ≤ 9/2−4 = 1/2`, hence `|x| < 1/2`.

The opposite outer column has at least two squares, so some centre in it has
`|y| ≥ 1/2`. Its coordinate `x'` satisfies

`(|x'|+1/2)² ≤ 9/2−1 = 7/2`, hence `|x'| < 3/2`.

These give `|x−x'| ≤ |x|+|x'| < 2`, contradicting the outer-column span.
Thus `m₁,m₃ ≤ 3`. Since `m₂ ≤ 4` and the total is ten, the populations are
exactly `3,4,3`.

**The outer columns are forced.** Each outer column has height span at least
two, hence a centre with `|y| ≥ 1`. Its coordinate satisfies

`(|x|+1/2)² ≤ 9/2−9/4 = 9/4`, hence `|x| ≤ 1`.

Both outer columns lie in `[-1,1]` while their separation is at least two.
Therefore `x₁=-1`, `x₃=1`; the adjacent gap bounds force `x₂=0`. In an outer
column, containment now gives `|y| ≤ 1`. Three such heights with unit gaps
must be exactly `-1,0,1`. A centre `(1,1)` has a vertex `(3/2,3/2)`, so
`q ≥ 9/2`. Together with the assumed upper bound, this proves `q=9/2`.

**The middle column.** At `x=0`, containment is precisely
`1/4+(|y|+1/2)² ≤ 9/2`, or `|y| ≤ L`. Interior disjointness is precisely the
ordered unit-gap conditions in the theorem. Conversely, those conditions,
with the outer columns fixed, give the special case `u=v=1` of the
[construction family](CONSTRUCTION.md#six-parameter-family). This proves both
the radius and the complete equality description within the stated class.

## Limitation

The proof does not classify all parallel-square packings: centres need not
lie on three edge-parallel lines. It also does not control relative square
rotations. In particular, the side slides in the six-parameter construction
give valid packings outside this class at the very same radius. No global
three-column reduction or unrestricted lower bound is assumed here.
