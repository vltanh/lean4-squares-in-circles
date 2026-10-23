# Independent review of the reverse-angle cover and full contact-class theorem

Review outcome: **PASS**. Together with the separately reviewed ordered-angle
cover, this closes the whole parameter square `0<=ta,tb<=1` for the stated
three orientation groups and fourteen signed owner separator halfspaces.
It proves `q>=qc` and the known physical slider equality family throughout
that contact class. It does not establish that arbitrary eleven-square
packings belong to the class.

The reverse branch uses the previously reviewed nonsingular nonnegative
weight profile without modification. Its signed support
`(1+cd-sd)/2` equals the physical support when `tb<=ta` and is a lower bound
for physical support everywhere on the angle square. Nonnegative edge
weights preserve the weak-dual direction on any tile crossing the diagonal.
The same exact force balances, zero-total identities, smoothness, rational
Taylor estimates, and closed-strip coverage proof therefore apply.

The new checker verifies `delta_sign=-1` for every dual tile and discards
a tile only when `tb_lower>ta_upper`, strictly. Thus the diagonal is checked,
not removed. Its target Q is checked to exceed the certified upper endpoint
of `qc`. There is no retained unsolved region: every tile meeting the reverse
triangle has a strict dual bound above Q.

Direct exact replay passed all 265 reverse-cover rectangles: 141 dual
rectangles and 124 strictly outside the reverse triangle. The minimum
reported strict lower margin above Q has rational floor
`37288361/10^12`. The checker imports no numerical discovery solver.

The ordered and reverse closed triangles cover the whole angle square,
including endpoints and the equal-angle locus. The reverse branch excludes
equality altogether. The reviewed ordered branch places equality in the
quantitative candidate neighborhood, where the exact-angle and fixed-frame
equality theorems give the physical slider family. The final manuscript
states the necessary label, orientation-group, and separator assumptions
explicitly and does not assert unrestricted geometric capture.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `check_reverse_angle_tiles.py` | `f7fb1f86279eafc435851668611ebbbfa953c9deea4e6a3b8d798a690edb7be1` |
| `REVERSE_ANGLE_TILES.json` | `be3ae0f9f76adbf98d98abca7fe965df7fb4bb928a57d82ddfc69ca68a65b5ed` |
| `FULL_GROUP_ANGLE_CLASS.md` | `109d5af0c312c5e7d5d1718fd8ffa1b2d8579c76e1238430ca986314a71ec280` |

The unchanged helper, cover-checking routine, ordered data, root enclosure,
and quantitative neighborhood are dependencies with their own review
bindings in `ORDERED_ANGLE_COVER_REVIEW.md` and
`ANGLE_NEIGHBORHOOD_REVIEW.md`.
