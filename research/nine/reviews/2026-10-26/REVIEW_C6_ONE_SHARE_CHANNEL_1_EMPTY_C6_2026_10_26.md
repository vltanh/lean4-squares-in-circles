# Independent review: the remaining one-share channel-1 pocket is empty

Date: October 26, 2026.

Reviewed source: `SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md`.

**Verdict: accepted as a complete whole-domain empty-pocket theorem.**
The theorem applies to the actual channel between the two nonshared
loads in the remaining canonical `110`, sole-share-0 orbit. It
does not exclude the full three-extra completion problem or assert an
unproved capacity for either other pocket.

## 1. Exact physical corner geometry

The two support vectors in (3) agree with the original nonshared
bit-one and bit-zero force formulas. Their positive-vector cones give
the displayed intervals for `phi` and `psi`; hence `a,b>=0`
and `a+b<=alpha_0<=pi/4` follow without restricting a force
ratio. The signs in the actual channel frame were checked directly:
`n_1` has absolute angle `pi/2+alpha_1`, while its outward
perpendicular has angle `alpha_1`. The two `-J u_i` vectors
therefore have exactly the components `(-cos(a),sin(a))` and
`(cos(b),sin(b))`.

Because the outgoing port of the bit-one body and incoming port of
the bit-zero body are the respective vertices directly adjacent to
their actual unique circle corners, (7) gives those original corner
positions exactly. No circle corner is replaced by a resultant point
or an endpoint chosen after extracting the certificate.

The sum-to-product formulas give the chord `(U,V)` and its length
`D` exactly. Both actual circle corners have positive channel-frame
height. Their midpoint consequently has positive height, and the
positive perpendicular branch in (9) is forced. Moreover `U>0`
and `D<2R`, so every divisor and square root used in that identity
has the claimed positive sign.

## 2. Whole-interval height inequalities

The bound for `|V|/U` retains every `|t|<=m` and every
`0<=m<=pi/8`. Its numerator and denominator estimates have the
correct directions, and the comparison with `7/24` gives the
stated strict `U/D>24/25`. Combining the chord-length bound
and `sin(m)cos(t)<=sin(m)` yields (12) pointwise over the
entire angular domain.

Direct differentiation reproduces `F_R'`. The lower bound on its
radical denominator and the elementary sine/cosine bounds make it
strictly negative on the full closed interval. The later fixed
`pi/8` comparisons justify the same elementary bounds used in this
derivative estimate. The replacements `cos(pi/8)<37/40` and
`sin(pi/8)<39/100` preserve the lower direction in (13).

## 3. Radius monotonicity and exact arithmetic

I independently differentiated `g(R)`. Both root denominators are
positive throughout the retained radius interval, so the comparison
of their squares is valid. It yields exactly the expression in (15),
which decreases with `R^2`; evaluating it at the full upper
endpoint therefore gives the claimed uniform lower reserve.

The two central exact rational values were independently recomputed:

```
(57/40)^2 - 144/625 - (49/625)(1105/256)
    = 233891/160000 > 0,

(12/125)(1367/100) + 61/100 - 7643/4000
    = 1157/100000 > 1/100.
```

The radical identities at `R=79/40`, both radical squared
reserves, the derivative denominator reserve `141/1600`, and both
fixed trigonometric comparisons also agree with the manuscript.
Thus `H>d_R+1/100` is a uniform rigorous inequality, not a
rounded numerical estimate.

## 4. Actual pocket and completion scope

The original channel-cap theorem puts every entire extra in that
pocket beyond the actual support line of height `H`. The sharp
whole-unit half-plane threshold `d_R` applies to any orientation
and does not assume a positive circle multiplier on the extra.
Consequently the whole channel-1 pocket is empty, including its
subdivisions by additional zero-weight contacts.

The stated occupied-transmitter consequence agrees with equations
(19)--(20) of the residual-domain source: `w_1>=H-d_R` is a
lower bound common to every original permitted transmitter slider.
It does not move the actual transmitter or choose a preferred mean.
The seven displayed residual allocations are exactly all nonnegative
integer allocations of three extras when central capacity is at most
one and channel 1 is empty. Repeated occupancy of a remaining pocket
is explicitly retained.

All nine physical squares, unique masks, positive original forces,
actual means and the full radius interval are preserved. The result
does not close the one-radial family, the remaining coupled one-share
completion, the unrestricted radius theorem, equality, or the earlier
prerequisite audit. No numerical optimization premise, coefficient
packet, Lean compilation or CI action was used in this review.
