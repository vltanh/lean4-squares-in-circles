# Independent review of the four-core radius-6/5 empty shell

Review outcome: **PASS** for the mathematical reduction, complete-domain
cover, and exact source arithmetic. This review is separate from the parent
researcher's independent arithmetic replay of all 20,405 nodes and 9,187
accepted arc leaves. The result is conditional: four centers at radius at
most `41/40` force each of the other seven centers beyond `6/5` when
`q<=49013/10000`. It does not exclude the four-core branch.

The radii and weights agree between the manuscript, generator, and replay.
All weights are strictly positive and sum to one. The three pose domains
are correctly represented: the core disk, the closed middle annulus, and
the outer ring subject to exact square containment. The middle-annulus
bound does not need a containing-disk assumption, so omitting that rejection
there strengthens the certified statement.

Every rejection predicate excludes the whole box and is strict. Equalities
on the diagonal, either radius threshold, and the containing-circle boundary
remain covered. Both closed children of every exact midpoint split are
checked. The replay verifies all parameters, root extents, node formats,
discard reasons, and counts without importing the generator.

The shared rectangle is contained in every square of its pose box, as in
the previously audited arc certificate. Each elementary arc lower bound is
rounded **down** to a rational denominator-`10^12` grid before weighting.
The code uses exact rational floor, not nearest rounding; positive weights
therefore preserve a valid lower bound. The rounding scale is checked in
the metadata. The elementary inverse-trigonometric arithmetic is unchanged
from the reviewed `exact_arcs.py`, and optimized Python mode is rejected.

If one of the seven ring centers lay in the closed middle annulus, the
three certified bounds would require

    sum W >= 4*(847/1000)+(133/200)+6*(187/500)
           =6297/1000 >44/7 >2*pi.

The strict rational difference is `79/7000`. This contradicts the same
angular circle budget used in the earlier certificate. The separate theorem
excluding five core centers justifies counting exactly four cores and seven
rings, including all threshold cases. No independence or mutual
realizability of the individual pose minima is assumed.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `FOUR_CORE_WIDE_SHELL.md` | `1c8301818dbe7846578d8ba0214f9ee71db4e7c96e722db501851ee8cb7f38d4` |
| `check_wide_shell.py` | `3df58b5262363d3d32c0b49d6c0debc4886c2047781db889e80c55228d16122f` |
| `generate_wide_shell.py` | `ad1810286aa1181b5b5699202a3fe9e996bcc2305e244fee174d57af7e5a15a2` |
| `WIDE_SHELL_CORE_COVER.json` | `a52bfc671c1a8ec2346433c9506f9acb923376cf94ffd57ed40e1932afe4fd7a` |
| `WIDE_SHELL_MIDDLE_COVER.json` | `a94d0624ef9f1f20ee7751d6feba83b59f51fd9a0191ad0e2c2f34f67e25e55f` |
| `WIDE_SHELL_RING_COVER.json` | `f96cc82627d69c42d6c800576ecd0a3d70136bb216ce2fca9c7e392a24fc7a05` |

The unchanged elementary module has SHA-256
`ff36dd0473037002496d319d09f3e1b15c0fad3f3c576e126baa3f5f0f69db73`.
