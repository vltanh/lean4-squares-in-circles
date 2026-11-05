# Full-caller reflection and extra-label symmetries

**Prepared for physical/code review. No normalized adapter or numerical
search is installed.** These transformations apply to the entire original
nine-square fixed-mask caller, for every one of the 32 exact masks and
either strict or closed corner containment.

Vertical reflection preserves x and alpha, negates y and beta, and sends
corner `(epsilon,tau)` to `(epsilon,-tau)`. An owned v-axis separator
changes sign. Swapping the two unmarked extras H and I transports their
centers, frames, corners and every pair condition. If a transported pair
is re-sorted, its displacement and separator sign both reverse.

The two involutions commute. Any full caller can therefore be represented
with the two closed conditions `beta_D>=0` and `x_H<=x_I`. This is a
whole-caller existence equivalence, and does not add unconditional rows to
an existing unnormalized root. Registered original-cell paths and their
proof records are not transported by this packet.

The hand proof gives the complete physical argument. The separate exact
checker reconstructs rational polynomials rather than testing only sample
angles: 144 corner-norm identities, 4,608 owned support identities, 576
proxy identities, and all marked cone/bit identities are checked across
the four maps. It also checks 200 rational normalization assignments,
including 100 shared zero-face cases, and rejects seven damaged maps or
sign conventions. These controls call no optimizer and yield no closure
credit.

Run with a fresh output path:

```sh
python -B -S global_work/full_mask_symmetries_v1/check_full_mask_symmetries.py \
  --output /tmp/full_mask_symmetry_controls_fresh.json
```

`PREMISE_BINDINGS.json` freezes the source, hand proof and completed exact
report. Independent physical review and parent acceptance are required
before a new root may use the normalized caller.
