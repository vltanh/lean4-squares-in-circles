# The declared n=9 radius window follows from the existing n=8 theorem

**Status:** complete dependency assembly using the repository's existing
eight-square optimality theorem. This discharges the explicit import gate
G0.W.2. It does not provide a new standalone, table-free lower bound and
does not close the remaining n=9 cyclic completion problem.

The source declarations below were read at commit
`1760270deb45190883a23fb54a064a812a6bed6b`. No Lean compilation or CI was
run in this continuation.

## 1. The exact imported statements

The repository uses the physical definition `Packing S o R`: every
closed unit square is contained in the radius-R disk about o, and no
point lies in two open square interiors. Each square has its own
orthonormal frame. No common orientation, contact graph or circle-center
square is required.

The following existing declarations supply the import:

1. In [SquaresInCircles.lean](https://github.com/vltanh/lean4-squares-in-circles/blob/1760270deb45190883a23fb54a064a812a6bed6b/SquaresInCircles.lean),
   `SquaresInCircles.optimal_radius 8` states

   ```lean
   IsLeast {R | ∃ (S : Fin 8 → UnitSquare) (o : Point), Packing S o R}
     (optimalRadius 8)
   ```

   The definition of `optimalRadius 8` is `EightStatement.radius`.

2. In [Geometry.lean](https://github.com/vltanh/lean4-squares-in-circles/blob/1760270deb45190883a23fb54a064a812a6bed6b/SquaresInCircles/Geometry.lean),
   `EightStatement.radius = Real.sqrt EightStatement.qStar`,
   `EightStatement.qStar = EightStatement.selected.q`, and
   `EightStatement.Root.IsStationary` has the field

   ```lean
   q_lower : (79/40 : ℝ)^2 ≤ d.q
   ```

3. In [ExactFamily/StatementLink.lean](https://github.com/vltanh/lean4-squares-in-circles/blob/1760270deb45190883a23fb54a064a812a6bed6b/SquaresInCircles/Eight/ExactFamily/StatementLink.lean),
   `SquaresInCircles.Eight.ExactFamily.StatementLink.selected_stationary`
   proves that the selected root really satisfies `IsStationary`.
   The lower field is therefore an established property of the chosen
   radius, rather than an unsupported assumption about a choice value.

An equivalent direct lower-bound entry point is
`SquaresInCircles.Eight.lower_bound` in
[Eight/Uniqueness.lean](https://github.com/vltanh/lean4-squares-in-circles/blob/1760270deb45190883a23fb54a064a812a6bed6b/SquaresInCircles/Eight/Uniqueness.lean).
It states that every physical eight-square packing satisfies
`Eight.radius ≤ R`. The `radius_statement` theorem identifies that radius
with `EightStatement.radius`.

## 2. Deleting one square preserves exactly the required semantics

Let S be any physical packing of nine independently oriented unit
squares in a radius-R disk about o. Delete any one square and relabel
the remaining eight. For example, use the injective inclusion

\[
\iota:\{0,\ldots,7\}\longrightarrow\{0,\ldots,8\},
\qquad \iota(i)=i,
\]

and define \(S'_i=S_{\iota(i)}\).

Every closed square of S' is an unchanged square of S, so its disk
containment is inherited. If i and j are distinct eight-square labels,
injectivity gives \(\iota(i)\ne\iota(j)\); hence the open interiors of
their squares are disjoint by the original nine-square packing. The
radius remains nonnegative. Thus S' satisfies the original `Packing`
definition at the same o and R.

The imported least-radius theorem therefore gives

\[
R\ge\operatorname{EightStatement.radius}
 =\sqrt{\operatorname{EightStatement.qStar}}.
\tag{1}
\]

By `selected_stationary.q_lower`,

\[
\operatorname{EightStatement.qStar}\ge(79/40)^2.
\tag{2}
\]

Since \(79/40>0\), monotonicity of the nonnegative square root in
(1)--(2) yields

\[
\boxed{\qquad R\ge79/40.\qquad}
\tag{3}
\]

This is valid for every physical nine-square packing, independently of
minimality or the later selected-stress convention. No circle contact
or optimality of the eight retained squares is required.

## 3. Use at a hypothetical subcritical n=9 minimizer

Suppose a nine-square packing existed with

\[
R^2<Q=1105/256.
\]

The compact-minimizer argument produces a nine-square minimum at radius
\(R_*\le R\). Applying (3) to that minimizing packing, and using
nonnegativity of both radii, gives the exact working window

\[
\frac{79}{40}\le R_*<\frac{\sqrt{1105}}{16}.
\tag{4}
\]

Thus every window-dependent tree, reciprocal/layer, boundary-contact and
cyclic restriction in this branch can be applied to a hypothetical
subcritical minimizer with the lower endpoint now explicitly justified.
The nonstrict upper endpoint used in those manuscripts also includes
eventual equality analysis.

In particular, TREE_AND_TWO_LOAD_COMPLETION.md and the boundary-order
theorem together reduce every such minimizer to the still-open cyclic
completion cases. They do not exclude those cases merely because (4)
has been established.

## 4. Dependency and verification boundary

This argument imports the repository's existing n=8 theorem, including
its proof dependencies. The n=8 proof uses generated arithmetic tables;
for example, ExactFamily/Analysis.lean imports
`Eight.ExactFamily.Generated.LocalStationaryBounds`, and the global
normalization/capture chain contains further generated bounds. The
deletion argument does not remove those dependencies or turn the full
n=9 dependency chain into a standalone table-free hand proof.

Accordingly:

- **G0.W.2 is CLOSED:** the actual n=8 declarations and their deletion
  implication supply the stated lower window.
- **G0.W.3 remains separate:** if an entirely independent table-free
  n=9 derivation is required, replace this n=8 import by a hand proof
  of the coarse lower bound.
- The new P/Y capacity proofs themselves are direct analytic arguments
  in the disk of squared radius 17/4 and do not use this n=8 import.
- No new Lean verification, CI run, unrestricted n=9 sharp lower bound,
  or complete equality classification is claimed here.
