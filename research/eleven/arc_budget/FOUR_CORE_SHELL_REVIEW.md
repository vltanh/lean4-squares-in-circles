# Review of the empty shell in the four-core case

The `n8_lessons` agent independently audited the mathematics of
`FOUR_CORE_EMPTY_SHELL.md`. The root agent separately replayed its three
exact rational covers, reporting 7053 nodes and 2936 accepted arc leaves.
This note records those distinct checks; it does not claim Lean verification.

**Conclusion: pass.** The six positive weights sum exactly to one. The
single-square domains include all closed center-radius endpoints and use
only strict discard conditions. The common inner rectangle is contained
in every square represented by its box, so its angular measure is a valid
lower bound. The initial ring box follows from the farthest corner bound;
the middle-shell bound valid without imposing containment is stronger than
needed. The three covers preserve every actual square and individual frame.

Given four centers at radius at most `41/40`, the preceding weighted-arc
theorem rules out a fifth. If one remaining center were in the closed shell
through `11/10`, the sum of the four core bounds, its middle-shell bound,
and the six other ring bounds is exactly `1259/200`. I independently checked
that this exceeds `44/7` by `13/1400`, hence exceeds `2pi`, contradicting
the normalized weighted angular budget. Thus every other center is
strictly beyond `11/10`. This closes an actual shell, not the four-core
class itself.

The reviewed source SHA-256 is recorded below.

`4371633b23023f9c19db6ebef72bab51383d32c6645971fb3a05dba65a48ec8e`.
