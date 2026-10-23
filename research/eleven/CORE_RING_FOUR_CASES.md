# Four unrestricted core and ring counts in the eleven-square window

Let eleven closed unit squares have pairwise disjoint open interiors and lie
in a disk centered at the origin with squared radius
`q <= U = 49013/10000`. Individual square orientations remain arbitrary.
Put

\[
r_*=41/40,\qquad \rho=27/20.
\]

Call a square a **core square** when its center has norm strictly less than
`r_*`, and a **ring square** otherwise. These names describe an auxiliary
radial partition; they do not assert that a square contains the origin.

## 1. Exhaustive count rows

[RATIONAL_CORE_RADIUS.md](boundary/RATIONAL_CORE_RADIUS.md) proves that
every ring square cuts the circle of radius `rho` in a connected arc of
angular length strictly greater than `7/10`. Nine such arcs cannot have
pairwise disjoint interiors, since `9(7/10)>2pi`. Thus at least three centers
are in the core.

[SIX_CORE_CENTER_BOUND.md](boundary/SIX_CORE_CENTER_BOUND.md) proves that
at most six pairwise interior-disjoint unit squares can have centers in the
closed disk of radius `r_*`. In the six-member case exactly one contains
the origin in its open interior. Hence the complete necessary count list is

| Core count | Ring count | Additional mandatory condition |
| ---: | ---: | --- |
| 3 | 8 | None yet |
| 4 | 7 | None yet |
| 5 | 6 | None yet |
| 6 | 5 | Exactly one core square contains the origin in its open interior |

These are necessary alternatives, not realizability claims or terminal
sharp lower bounds. This is a stronger partition than the earlier
[five-case extraction](CORE_RING_FIVE_CASES.md): its threshold is different.
The earlier seven-core count cannot occur at this new threshold. The four
displayed cases all remain open for the unrestricted sharp bound.

## 2. Every core square is strictly inside the containing circle

Area gives `11 <= pi q`; the strict bound `pi<22/7` gives `q>7/2`.
Every point of a core square has norm at most its center norm plus
`sqrt(2)/2`. Even allowing a closed core-center endpoint,

\[
(41/40+\sqrt2/2)^2
=2481/1600+41\sqrt2/40
<4941/1600<7/2<q,
\]

where `sqrt(2)<3/2`. Therefore every core square is strictly inside the
containing disk. In particular all circle-contact vertices, and all positive
circle-load atoms in a physical optimality stress, must belong to ring
squares. This does not exclude pair contacts among core squares or between
core and ring squares.

## 3. The ring has a genuine cyclic order

For any square with center norm `r`, a farthest corner satisfies
`r^2+r+1/2 <= q <= U < 491/100 < 89/18`. Thus `r<5/3`.
For a ring center,

\[
41/40\le r<5/3,\qquad |r-27/20|<1/2.
\]

Indeed the two possible endpoint differences are `13/40` and `19/60`.
The point on the auxiliary circle in the direction of the square's center
therefore lies strictly inside the square's inscribed disk of radius `1/2`.
Its center ray lies in the interior of the square's connected auxiliary
arc.

Consequently the ring centers have distinct polar angles and can be indexed
in their cyclic order, with lifted angles
`beta_1 < ... < beta_m < beta_1+2pi`. Write their arcs as

\[
[\beta_i-\ell_i,\beta_i+u_i],\qquad
\ell_i,u_i>0,\qquad \ell_i+u_i>7/10.
\]

Here arc interiors can overlap only at finitely many square-boundary points,
which do not change angular length. Since a positive overlap interval would
contain points interior to both squares, consecutive arcs obey

\[
\beta_{i+1}-\beta_i\ge u_i+\ell_{i+1},\qquad
\sum_i(\beta_{i+1}-\beta_i)=2\pi,
\]

with cyclic indices. These are geometric constraints on the original ring
squares, not a replacement for their original pairwise separation conditions.

## 4. Closed charts and the remaining obligation

The actual partition assigns each threshold equality to the ring. For a
compact closed-chart cover one may allow every assigned core center to have
norm `<=41/40` while requiring every assigned ring center to have norm
`>=41/40`. The original strict partition witnesses that the four count rows
cover every actual packing. Overlap on the threshold is harmless; the closed
six-core theorem and the strict circle-unloaded conclusion remain valid.

All eleven original squares, their individual frames, all forty-four corner
containment constraints, and all fifty-five physical pair constraints remain
present. Ring order alone does not prove nonneighbor separation or a feasible
core completion. A complete unrestricted proof must still exclude or sharply
solve all four rows, retaining those constraints. In particular this result
does not establish that every optimum has three core squares, or that the
known candidate is globally sharp.
