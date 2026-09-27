# Prior work

[Back to the README](../README.md)

This review reflects the literature as of September 2026.

## Squares in a circle

Erich Friedman's [Squares in Circles](https://erich-friedman.github.io/packing/squincir/)
page has collected the best known packings since 1997, including his own of
three, five and seven squares. Before this repository:

| n | earlier result | this repository |
| :-: | --- | --- |
| 1, 2 | folklore, listed as trivial on Friedman's page | formal proofs of optimality and uniqueness |
| 3 | computer-assisted interval enclosure of the radius and the optimal arrangements by Montanher, Neumaier, Markót, Domes and Schichl [1]; no exact value | exact formal proofs of optimality and uniqueness |
| 4 | Problem 6 of IMSC 2026, whose official solution proves the radius [4]; an unpublished note by Wei Zhao proves the radius and uniqueness [5] | formal proofs of optimality and uniqueness |
| 5 | none found; the plus was listed only as the best known packing | formal proofs of optimality and uniqueness |
| 7 | none found; the packing of radius `√13/2` was listed only as the best known one | formal proofs of optimality and of uniqueness up to the heights of the three middle squares |

Montanher et al. [1] pose the three-square problem as a constraint satisfaction
problem and solve it by interval branch and bound, in C++ with the Filib and
Moore interval libraries. Their Theorem 2 encloses the radius in
`[1.28847050800547, 1.28847050800553]`, which contains `5√17/16`, and every
optimal arrangement in boxes of width at most `6.23·10⁻¹³` near the T; it
determines neither the exact radius nor whether the T itself is optimal. The
proofs here differ in:

- **Trust.** Theirs rests on the search code and the libraries' interval
  rounding; here Lean's kernel checks every step, and every numeric bound is an
  exact rational inequality.
- **Exactness.** They enclose the radius and the optimal arrangements; here the
  radius is exact and the T is the only optimal packing, up to rotation and
  relabelling.
- **Method.** They subdivide the configuration space; here one geometric
  argument, contact tangents and an angular budget, covers three to five
  squares.

Four squares were Problem 6 of the 4th International Mathematics Summer Camp
(IMSC 2026), posed as the largest side of four congruent squares in a unit
disk, `√2/2`. The official marking scheme [4] solves it by hand, and Friedman's
page lists the case as proved at the camp. We have not seen the scheme; by the
account in [5], it proves the radius with a concentric auxiliary circle and
does not discuss uniqueness. An unpublished note by Wei Zhao [5], dated 6 July
2026 and shared with us by Friedman, proves the radius and that the 2×2 block
is then the only packing, up to rotation, by the argument of
[Chapter 7](proof/four.md): on the circle about the disk centre of radius half
a side, every square holds at least a quarter, and exactly a quarter only when
the disk centre is one of its vertices. The proof here was written without the
note or the official solution: the arc idea came from Claude, and ChatGPT used
it on five squares first, then on four and three. The note was also developed
with Claude, so the two may not be independent.

In July 2026 Friedman's page
([snapshot](https://web.archive.org/web/20260723054450/https://erich-friedman.github.io/packing/squincir/)),
and in September 2026 the Wikipedia article
[Square packing](https://en.wikipedia.org/wiki/Square_packing#In_a_circle),
listed only one, two and four squares as proved optimal; neither records the
enclosure of [1]. The
[`legacy`](https://github.com/vltanh/lean4-squares-in-circles/tree/legacy)
branch of this repository holds an earlier formal proof of the three-square
lower bound, by rational certificates.

## Formal verification

Proof assistants have verified packing theorems elsewhere: the Kepler
conjecture in HOL Light and Isabelle [2], and sphere packing in dimension 8 in
Lean [3]. We found no formal proof of an optimal packing of squares or circles
in a circle or a square, and no earlier exact proof of optimality or of
uniqueness for three, five or seven squares; uniqueness for four squares is in
the note [5].

## References

1. T. Montanher, A. Neumaier, M. C. Markót, F. Domes, H. Schichl. Rigorous
   packing of unit squares into a circle. *J. Global Optim.* 73 (2019)
   547–565. [doi:10.1007/s10898-018-0711-5](https://doi.org/10.1007/s10898-018-0711-5)
2. T. Hales et al. A formal proof of the Kepler conjecture.
   *Forum Math. Pi* 5 (2017) e2.
3. S. Hariharan, C. Birkbeck, S. Lee, H. K. G. Ma, B. Mehta, A. Poiroux,
   M. Viazovska. A milestone in formalization: the sphere packing problem in
   dimension 8. [arXiv:2604.23468](https://arxiv.org/abs/2604.23468) (2026).
4. The 4th International Mathematics Summer Camp (IMSC 2026). *Marking Schemes
   and Solutions*, Day 2, Problem 6. July 2026. Not public; known to us from
   Friedman's page and [5].
5. W. Zhao. Four congruent squares in a unit disk: an elementary proof that
   `s_max = √2/2`. Unpublished note, 6 July 2026, shared with us by E. Friedman
   in private correspondence.
