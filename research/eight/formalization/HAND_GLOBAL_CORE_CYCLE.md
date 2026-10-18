# Hand geometric reduction toward a table-free eight-square proof

**Status: hand proof of the structural lemma below; full table-free charged inequality remains open.**
This note deliberately contains no Lean implementation. It preserves the distinction
between a proven geometric reduction and replacement of the affine tables.

## Theorem: at most one core–core edge in the entire seven-cycle

Let seven unit squares have disjoint open interiors, with centers in
cyclic polar order around the origin and consecutive positive gaps
`g_0,...,g_6` summing to `2π`. Assume the existing unrestricted
boundary-geometry conclusion

```
g_i > 19/25  for every i.
```

Call a square *core* if its center has radial length strictly below
`4/5` (as supplied by the existing core-side and core-corner
boundary charts). Then **at most one** of the seven edges can join
two core centers.

### Step 1: any core–core gap is greater than 4/3

An interior-disjoint pair of unit squares contains two open disks of
radius `1/2` about the centers. Hence the two centers have Euclidean
distance at least `1`, independent of their orientations.

Suppose instead that the positive gap of two core centers is at most
`4/3`. Write their radii as `r,s ∈ [0,4/5]` and the gap as `g`.
The cosine rule gives
```
distance² = r² + s² - 2rs cos(g).
```
On `[0,4/3]`, cosine is decreasing and its alternating Taylor bound
gives
```
cos(g) >= cos(4/3)
       >= 1 - (4/3)²/2 + (4/3)⁴/24 - (4/3)⁶/720
        = 7709/32805 > 7/32.
```
For fixed `s` this squared-distance expression is convex in `r`;
for fixed `r` it is convex in `s`. Its maximum on the rectangle
`[0,4/5]²` occurs at a corner. At `(0,0)` it is zero, at either
`(0,4/5)` corner it is `16/25`, and at `(4/5,4/5)` it is bounded
strictly by
```
(32/25) (1 - 7/32) = 1.
```
Thus the distance would be strictly below one, a contradiction.
Therefore every core–core edge satisfies `g > 4/3`.

This argument proves the gap bound from geometry alone: it does not
use a selected separator axis, radial contact equality, charge,
vertex potential, affine row, or numerical subdivision.

### Step 2: two such edges exhaust the angular budget

If two distinct edges were core–core, Step 1 and the lower bound
on the other five edges would imply
```
2π = ∑ g_i > 2(4/3) + 5(19/25)
             = 97/15.
```
But `π < 22/7` gives `2π < 44/7`, whereas
```
97/15 - 44/7 = 19/105 > 0.
```
This contradiction proves the theorem. The two exceptional edges may
share a vertex; that case is covered identically.

## Corollary: a uniform finite classification of radial words

Encode a core vertex by C and an outer vertex by O. The complete
cyclic binary word of length seven has **at most one CC adjacency**,
without choosing a candidate quarter word or orienting any square.
Consequently:

* There can be at most four core vertices. Five or more would force
  at least three CC edges by counting maximal runs of C separated by O.
* If there are four core vertices, the word is, up to cyclic rotation,
  `CCOCOCO` (the unique arrangement with exactly one CC edge).
* Precisely 64 of the 128 indexed binary words satisfy the condition.
  The exact counts by number of C vertices are
  `1,7,21,28,7,0,0,0` for `0,...,7`, respectively.
  These can also be obtained by elementary placement counting:
  for three C vertices, seven patterns have no CC and 21 have one CC;
  for four C vertices, the seven rotations above are the only options.

The count is **a consequence, not a substitute for the proof**:
the angular-budget argument is what excludes every omitted radial
word, including all shared endpoints and all original feasible axes.

## What this does and does not replace

This structural result removes a global branch of the state
classification in *every* charged stage: no valid cycle can use a
radial word with two or more CC edges. Unlike a local row deletion,
the proof applies to all seven edges simultaneously.

It **does not yet justify deleting the remaining affine-row proofs**.
A pairwise `ChargedBound` theorem demands an inequality on arbitrary
pairs of chart states, including pairs which could not coexist with
other edges in a seven-cycle. To take advantage of this theorem,
the remaining proof should work directly with the **complete cycle**
rather than continue to demand independently certified inequalities
on all pairwise domains.

The precise table-free target is a whole-cycle statement: with
one shared potential per vertex (or with potentials eliminated
entirely), sum the seven original SAT inequalities, charge the five
aligned differences using the *same total mismatch* `S`, and prove
the required strict global reserve for every geometrically possible
seven-cycle. Its proof must cover all four original feasible axes,
both radial charts and their shared boundaries, and both signs of
each aligned error.

The exact half-angle/contact-root reduction in
`MISMATCH_GEOMETRY.md` is already a hand geometric method for
eliminating the *angular* mesh. Its unresolved gate is positivity
over the continuous outer-endpoint state coordinates. This note
does not assert that that gate has been closed.

## Verification boundary

This is a pen-and-paper argument with rational inequalities. No Lean,
CI, generated certificate, native kernel, or external decision script
was used to establish it. A future Lean implementation can use
ordinary theorem proving; it must be withheld until the full
mathematical proof is settled, per the current instruction.
