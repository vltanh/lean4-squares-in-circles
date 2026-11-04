# Independent review of the five-core center bound

The `n8_lessons` research agent independently checked
`boundary/FIVE_CORE_CENTER_BOUND.md`, SHA-256
`75c7ac6db8c493e10a691304738f062d2d415b13d3dce20349c1cd1f14d602be`.
This is a mathematical source review, not Lean kernel verification.

**Conclusion: pass.** The theorem excludes six pairwise interior-disjoint
unit-square centers in the closed disk of radius `41/40`, with arbitrary
individual orientations.

The previous independently reviewed six-center lemma supplies an
origin-containing square only inside the hypothetical six-member case.
Its center norm is strictly below `sqrt(2)/2`. All five remaining center
radii lie in `[1/2,41/40]`. The separate-convexity corner bounds and the
cosine Taylor bound prove that their pairwise minor angular gaps exceed
one radian. I independently recomputed the three rational corner values
as `23/100`, `5977/8000`, and `38663/40000`.

The center-pinning inequality uses necessary center separation and is
monotone in the neighbor radius because the central norm is below one.
Its upper-envelope function is convex in the central norm; both endpoint
values on `[3/40,3/4]` are below `2/5`. I independently recomputed the
Taylor residue `387656111/46080000000` at `23/20`. Thus all five rays
would occupy an arc shorter than four radians, impossible for their four
successive gaps greater than one. This proves central norm `<3/40`.

The inscribed-disk argument correctly gives distance at least `1/2` from
each neighboring center to the closed central square. At distance less
than `11/10` from its center, that condition forces one central-frame
coordinate magnitude to be at least one: the alternative with both
magnitudes above `1/2` would require squared norm at least `5/4`.
There are four disjoint possible regions. The same-region squared
distance is strictly below `17/20`, so five neighbors violate unit center
separation. Closed radial endpoints and arbitrary neighbor orientations
are covered throughout.

Combined with the independent annular-arc theorem, this leaves exactly the
three necessary core/ring rows `(3,8)`, `(4,7)`, and `(5,6)` at threshold
`41/40`. It closes the six-core row, but does not supply a sharp bound for
the three remaining rows or prove candidate optimality.
