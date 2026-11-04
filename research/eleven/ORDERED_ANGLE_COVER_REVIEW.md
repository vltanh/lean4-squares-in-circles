# Independent review of the full ordered-angle contact-class certificate

Review outcome: **PASS**, including direct exact replay of all 242 closed
rectangles. Under the specified fourteen signed separator inequalities and
the three prescribed orientation groups with `0<=ta<=tb<=1`, the squared
radius is at least `qc`. Equality for actual packings is exactly the known
slider family. This is a theorem for that contact class; it does not capture
all unrestricted packings into the class.

## Symbolic dual checked

The new parameterization uses nine nonnegative constants. The edge weights
`B=Z*cos(beta-alpha)`, `H=Z*cos(beta)`, and `J=Z*sin(alpha)` are nonnegative
throughout the full first-quadrant angle square, including its endpoints.
The identity `H*u_alpha-J*v_beta=B*ex` is exact, so the forces on the three
unloaded labels vanish without division by a cosine. Direct summation of
the fourteen directed edge contributions reproduces all eight displayed
boundary force vectors and the weighted support sum S.

Each condition required when a boundary label has zero total corner weight
is sufficient to make its entire force vector identically zero. The checker
requires these rational identities, rather than accepting a small residual.
For positive totals the weighted-corner vectors, denominator `4*Li`, and
completed-square signs agree with the previously proved weak dual.

On unordered parts of a rectangle, the signed expression
`(1+cd+sd)/2` is at most the physical mixed support width
`(1+cd+abs(sd))/2`. Its coefficient is nonnegative. Replacing that support
by the signed expression therefore weakens the dual lower bound in the safe
direction. The angle-dependent weights remain nonnegative there, and all
identities remain valid. Every dual function is smooth on its closed tile;
there is no omitted diagonal cusp.

## Taylor bounds and complete cover checked

The midpoint gradient bound and full-rectangle Hessian bound use the already
reviewed outward rational second-order arithmetic. Taylor's integral
remainder gives the implemented lower estimate with the factor `1/2` and
the full sum over both off-diagonal entries. The checker verifies every
lambda and parameter is nonnegative, total lambda is exactly one, every
zero-total identity holds, and the recomputed lower bound exceeds Q. Q is
strictly larger than the certified upper endpoint of `qc`.

The cover checker sweeps every rational x endpoint. On each open strip,
the active rectangles form an exact y partition from zero to one, without
a gap. Since all rectangles are closed and there are finitely many, their
closures also cover every vertical strip boundary and every vertex. The
strict test `ta_lower>tb_upper` discards only points outside the ordered
triangle. Equality on `ta=tb` remains in checked tiles. Retained tiles are
verified to lie entirely within the solved `1/2000` neighborhood of the
exact root, using worst-case endpoints of its rational enclosure.

Direct replay passed 214 dual rectangles, 27 strictly unordered rectangles,
and one retained neighborhood rectangle. The smallest reported strict dual
margin above Q has rational lower floor `383171/10^12`. All dual tiles thus
exclude equality; the neighborhood theorem and fixed-frame equality theorem
give exactly the asserted physical slider family. Numerical discovery code
is not imported or trusted by this replay.

## SHA-256 bindings

| File | SHA-256 |
| --- | --- |
| `angle_tile_dual.py` | `42a7cfe69a4f69e6d4c2756016338c8315266db78d53f61907de47d44682cb43` |
| `check_angle_tiles.py` | `62c176f41bf728039f5c6be78b2fc95eeaace9d469f11b4bb8dd2f4a4fa0d4f6` |
| `ANGLE_TILES.json` | `8e11576a05db3e5e6639b92853a1d5bd2b84a3573efc37aab3e0659bba157a95` |
| `ORDERED_GROUP_ANGLE_CLASS.md` | `67f9df0a6c14ade754de05621354571647383adb2a1312244a5f345cbdd43bb2` |

The root, interval solver, and quantitative-neighborhood certificates remain
dependencies, with their existing independent reviews.
