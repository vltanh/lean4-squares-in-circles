# Independent audit of the complete equality parameter domain

## Result and scope

**PASS.** The classification in `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md`
is a necessary and sufficient description of all attaining packings,
conditional on its explicitly stated unrestricted terminal capture and
the fixed-witness equality pullback. No additional unproved pose,
separating-axis, slider, or equality assumption was found.

This audit does not replace global terminal capture by a hand proof.
The open global hand gate remains exactly the one identified in the
manuscript. In particular, the result is a complete equality *family*;
it does not assert that the optimal packing is isolated.

Reviewed immutable files:

| File | SHA-256 |
|---|---|
| `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md` | `c2dc592e5d8d8d099bd169f95b1609e476dd553c0238095b4b9de2837d9273ac` |
| `verify_equality_parameter_domain.py` | `ffa840554e9f60cef9d522588b30aae7cc3149db1bce82ff5bfaf09da7d3c2c1` |
| `equality_parameter_domain_arithmetic.json` | `50ea773c1ee87603ff92710a0714b215d450c3133ee5d3b6f1e6b321f9eaed6d` |

The supplied checker was read in full and independently replayed:
**84 strict rational comparisons passed**. Its arithmetic uses exact
integer fractions, interval endpoint products, reciprocal bounds away
from zero, and the eight displayed square-root brackets. No sampled
pose or numerical root is used to accept an inequality.

## Necessity of the exterior ranges

The fixed-witness equality pullback already identifies the original
five anchors, their two frames, the two slider lines, and the cyclic
order `H,G,A,B,T,D,E`. The ordering assertions used here concern the
original packing, not just its deformed representative.

The displayed coordinate bounds put `B` in the first quadrant and `D`
in the second. Their counterclockwise sector has angle less than pi
and lies in the upper halfplane, so the intermediate center `T` has
positive height. Both `H` and `A` lie strictly in the negative `f`
halfplane, and their positive determinant selects the counterclockwise
sector of angle less than pi in that halfplane. Hence the intermediate
center `G` also has negative `f` coordinate. These observations justify
both sign choices before the square-root containment inequalities are
solved.

For `T`, its horizontal center coordinate is in `(0,1/2)`, so its
distance from the origin is `max(z-1/2,0)` and its farthest vertex has
squared norm `(x_c+1/2)^2+(z+1/2)^2`. This gives precisely the stated
lower core bound and upper circle bound. For `G`, its own-frame first
coordinate is in `(0,1/2)` and its second is negative. The analogous
expressions are `max(-h_2-eta-1,0)` for the distance and
`(h_1+2)^2+(-h_2-eta)^2` for the farthest squared norm. They give
exactly `eta_-` and `eta_+` in the manuscript.

Actual exterior squares strictly avoid the closed core disk. The
manuscript deliberately uses weak core endpoints in its convenient
outer rectangle. This does not enlarge the final domain: a square at
either core endpoint would contain a point of the closed core disk,
which the central square contains in its open interior. The central
SAT inequalities would then fail. Thus the combination of (7) and (8)
removes both spurious endpoints automatically.

## Sufficiency for all exterior pairs

I rederived each separation independently from the center table.

* The two left standard squares end no farther right than `x_2-2`;
  `T` occupies the horizontal interval `[x_2-2,x_2-1]`; the two right
  standard squares start no farther left than `x_2-1`. The two pairs
  within the left and right columns have vertical center difference
  exactly one. These facts cover all ten pairs of standard squares,
  without any condition on the slider height beyond containment.
* Taking the `e` or `f` scalar products gives the four identities in
  (9): `H/G`, `G/A`, `H/A`, and `H/E`. Their support sums are respectively
  one, `W`, `W`, and `W`. In particular, `H/A` has the extra unit of
  separation claimed in the paper. All four identities are independent
  of `eta`.
* The smallest left edge of `G` is reached at `eta_+` and is
  `c(h_1+1)+s/12`. It lies strictly to the right of the right edge
  `x_4+1` of `E`.
* The top of `H` is negative. The largest possible top of `G` is
  `s(h_1+2)-c/12`, also strictly negative. The bottoms of `B,D,T` are
  positive. This proves the final six pair separations.

The disjoint list has exactly `10+4+1+6=21` pairs. Containment of the
anchors follows from the family construction and the verified strict
signs of their selected farthest vertices; containment of the sliders
follows from the two range calculations above.

## Central square and the exact joint domain

For two unit squares, all four candidate separating-axis directions
have the same sum of half-widths,
`(1+|cos(relative angle)|+|sin(relative angle)|)/2`.
Consequently the four absolute projections in each displayed maximum
are exactly the complete separating-axis theorem, including all signed
owners and weak boundary contacts. The omitted cosine absolute value
in `W_t` is valid throughout the stated quarter-turn frame interval:
the relative angle has absolute value strictly less than `pi/2`.

The central core inequalities are exactly the condition that the
closed radius-`1/12` disk lies in the open central square. They also
imply strict central containment because its farthest squared vertex
norm is below `2(11/12)^2=121/72<q_*`. The seven maxima therefore cover
all seven remaining pairs and supply every remaining geometric
condition. Combined with the exterior theorem, they prove the converse
in the equality classification.

At fixed central frame the displayed formula is indeed a finite union
of intersections of explicitly given linear halfplanes. The only
disjunctions are the eight signed projection possibilities for each
of the seven central/exterior pairs. There is no hidden optimization
or unlisted feasibility test in the parameter domain.

## Fixed arithmetic and stationary localization

The test-point derivative formulas were checked by direct differentiation
of the four successive radicals and the expressions for `h_1,h_2`.
The first table encloses those radicals uniformly on the stated narrow
`q` interval. Its `|F_y|<0.000027` and `|F_t|<0.000010` bounds combine
with the previously established broad estimates `F_yy>6`,
`|F_yt|<6`, and reduced curvature `M_tt>3/4` in the stated directions.
They imply the displayed bounds on the displacement of the stationary
position and tilt. The unique stationary graph and root remain in the
broad chart, so every mean-value segment used in this step lies in
the domain where those estimates apply.

The second radical table then applies to the resulting position
rectangle. I checked the paper's table entries and all seven chosen
normal formulas against the checker. The rational trigonometric endpoint
bounds in the five-parameter box have the required monotonic directions;
the sign of the relative sine is proved before the absolute value is
removed. The strict core bounds and the two positive disk reserves
also hold on the entire box, not just at its center.

## Dimension and noncongruence

The five independently varying parameters in the box change two central
coordinates, its frame, and the two exterior slider positions. All
inequalities involving these free parameters have strict reserve, and
the central half-angle parameter has nonzero derivative. This gives a
full open subset of dimension five.

Exactly the five anchors meet the bounding circle in this box; both
sliders and the central square lie strictly inside it. Any congruence
must preserve the unique least enclosing circle and hence its center.
Among its five boundary squares, the group of four common frames is
uniquely identified, leaving the distinct tilted boundary square `H`
fixed. A rotation preserving that common frame is a quarter turn; only
the identity can fix the nonzero center of `H`. A reflection preserving
the common frame has an axial or diagonal mirror line, and the strict
coordinate bounds put `H` on none of those four lines. No reflection
is possible. The remaining isometry is therefore the identity, after
which the central square and the two differently framed slider roles
recover all five parameters. Distinct points of the displayed box are
noncongruent even when relabeling is allowed.

No equality case was discarded by a strict numerical estimate: the
strict estimates in this proof certify the fixed anchor geometry and
an interior example. The full joint domain retains every allowable
boundary contact through its weak separating-axis inequalities.
