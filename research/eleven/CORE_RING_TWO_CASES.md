# Two remaining unrestricted radial count cases

For eleven independently oriented unit squares with disjoint open interiors
in a disk of squared radius q<=49013/10000, classify a center as core when
its norm is below 41/40 and ring otherwise. Exactly one of these counts
applies:

| Core | Ring | Sharp bound and global equality |
| ---: | ---: | --- |
| 3 | 8 | OPEN |
| 4 | 7 | OPEN |

[The rational annular theorem](boundary/RATIONAL_CORE_RADIUS.md) proves
at least three core centers. [The weighted arc theorem](arc_budget/WEIGHTED_ARC_EXCLUSION.md)
proves at most four, even with a closed core threshold. It combines exact
lower bounds for one square's occupied angles on three circles. Five
core squares and the remaining six would require at least 317/50 radians
of weighted angular measure, more than 2pi. Additional cores increase
that lower bound. Complete adaptive covers prove the single-square
bounds throughout their continuous pose domains; all boundaries remain.

[The earlier geometric extraction](CORE_RING_FOUR_CASES.md) supplies the
remaining structure without change: every core square is strictly inside
the containing disk, and the ring has a genuine cyclic order on the
auxiliary circle of radius 27/20. Every ring arc is longer than 7/10. All
eleven centers, all independent frames, all 44 corner inequalities, and
all 55 pair constraints remain in these two cases. The overlapping closed
threshold charts retain the same bounds and cover every limit.

The earlier six-core hand exclusion remains an independent geometric
result; the weighted proof also excludes it. No origin-containing square
is imposed on either surviving case. A complete proof still needs sharp
whole-domain inequalities or global capture for both cases, followed by
full equality reconstruction. The known candidate lies in the 3/8 row.

In the four-core row, the [empty-shell theorem](arc_budget/FOUR_CORE_EMPTY_SHELL.md)
forces every remaining center strictly beyond 11/10. Six weighted circles
and complete exact covers exclude the whole intervening closed shell.
This is a necessary restriction on the open four-core terminal.

A [conditional block exclusion](CENTERED_BLOCK_OBSTRUCTION.md) rules out
an exact two-by-two block centered within 1/50 of the containing circle
center. Every completion square would contain one of four fixed interior
markers, allowing at most four completions. The independent
[four-center moment theorem](boundary/FOUR_CENTER_SECOND_MOMENT.md) gives
`sum |p_i|^2 >= 2+4|centroid|^2`, with equality for physical squares only
in a two-by-two block. Neither theorem assumes all four-core configurations
are blocks.
