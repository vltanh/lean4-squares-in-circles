# Root review: occupied-channel center bound and complete five-load C6 diameter

Date: October 26, 2026.

**Result: PASS at the complete stated local and five-load domains.** This is
a fresh mathematical review of CHANNEL_CAP_OCCUPANCY_TRANSMITTER_CENTER_BOUND.md,
not a sampled-pose check. Its author did not perform this review. The reviewed
mathematical source has SHA-256
`3d13440a07091a70cbab894cdac56e231d73ba955e5fa46768fd50d8a5abbd36` before any
status-only acceptance update.

## 1. Original quantifiers and actual geometry

I read the entire new source and the full relevant statements and proofs in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md, CONTACT_RING_HOLE_AREA.md, and
BOUNDARY_THREE_EDGE_PATH_DIAMETER.md. The local input consists of actual
endpoint supports, a true unloaded degree-two transmitter, and an actual
additional whole unit in the outward cap. It imposes no endpoint degree,
circle-mask, or weight-split restriction. The implication does not follow
from a cap-center condition alone, and the source correctly does not make
that substitution.

For a side transmitter the physical square is exactly
`[l,l+1] x [h+sigma-1/2,h+sigma+1/2]`, with the entire original interval
`-1/2 <= sigma <= 1/2`. Its center height is `y=h+sigma`; the actual cap
unit's center obeys `Y_E>=h+1/2>=y`. Both mean endpoints remain. For a
diagonal transmitter the unchanged opposite application vertices force
the center height to equal h. There is no extra transverse parameter to
choose in that alternative.

## 2. Independent inequality derivation

Put `Q=1105/256`, `M=91/60`, and `m=89/60`. The farthest-corner inequality
gives every contained unit center radius strictly below M. The endpoint
support gaps then give `|x|<M-(w+1)/2<=31/60`, using the actual projection
halfwidths, each at least one half.

Assume a side transmitter has radius at least m. Its height is greater
than minus one half, so `y^2>(11/8)^2` forces the positive branch
`y>11/8`. Whole containment of this axis-aligned physical transmitter
gives `|x|+y<Q-1/2-m^2<13/8`, hence `|x|<1/4`. The cap unit has
`Y_E>=y>11/8`, `|X_E|<2/3`, and `0<=Y_E-y<17/120`. Their squared center
distance is consequently less than
`(11/12)^2+(17/120)^2<1`. This contradicts disjoint open incircles of
radius one half. Each bound is strict in the needed direction even when
one of the original side means is an endpoint.

For the diagonal alternative, cap occupancy gives `0<h<61/60`, so the
coarser same horizontal bound already gives
`|c_U|^2<(31/60)^2+(61/60)^2<m^2`.

I recomputed all six rational reserves independently with exact fractions:

| Comparison | Exact positive reserve |
| --- | ---: |
| `M^2+M+1/2>Q` | `31/57600` |
| `m^2-(31/60)^2>(11/8)^2` | `41/960` |
| `13/8>Q-1/2-m^2` | `511/57600` |
| `(2/3)^2>M^2-(11/8)^2` | `167/4800` |
| `1>(11/12)^2+(17/120)^2` | `2011/14400` |
| `m^2>(31/60)^2+(61/60)^2` | `3239/3600` |

These are displayed scalar identities, not a parameter partition or a
new coefficient certificate.

## 3. Whole original FIVE orbit and every center pair

The genuine component is `U-S1-S2-S3-S4-S5-U`, with exactly the five Si
loaded, U unloaded of true degree two, and all three other physical
squares retained. The existing actual routing theorem excludes all four
direct-boundary pockets. Its central bound concerns the entire free
central union, including weak junctions and extra zero-weight physical
contacts: `3sqrt(3)/2<3` leaves capacity at most two. Thus at least one of
the three actual extras is wholly in the sole channel cap, precisely the
local theorem's extra-square premise.

The fifteen unordered center pairs are covered as follows:

* Five U/Si pairs use the newly proved `|c_U|<89/60` and the general
  `|c_i|<91/60`; their sum is exactly three.
* Four adjacent and three separation-two boundary pairs use their actual
  one- or two-contact paths, with distance at most `sqrt(2)` or
  `2sqrt(2)`, both strictly below three.
* The two separation-three pairs S1/S4 and S2/S5 use exactly four actual
  circle-touching path bodies. I checked that the accepted boundary-path
  diameter theorem has this four-body scope and requires no seventh
  boundary body, component degree, or unchanged force equation.
* The final S1/S5 pair uses the real two-contact path S1-U-S5. Its bound
  is `2sqrt(2)<3`; it is not inferred from a reserve lower bound or a
  fictitious three-edge boundary path.

This is all `5+4+3+2+1=15` pairs. Every actual circle load, zero individual
corner weight, selected force normal, shared mean, side slider, and
physical mask is retained throughout.

## 4. Accepted boundary

The local occupied-cap implication and the complete FIVE center-diameter
corollary pass. This review establishes no central-capacity-one transfer,
no cap-capacity-one statement, and no whole FIVE exclusion. Those are
separate geometric obligations. No original gate is discharged solely
by this necessary center bound. No Lean compilation or CI was run.
