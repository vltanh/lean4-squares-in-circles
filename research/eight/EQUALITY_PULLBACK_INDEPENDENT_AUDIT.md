# Independent audit of equality pullback

**Result: PASS, conditional on the global terminal capture stated in the
manuscript.** The argument transfers equality to the seven original
exterior squares. It correctly retains the final central-square and
joint slider-domain classification as separate work.

Reviewed manuscript SHA-256:
`0e0ab2b2da5b88f7799793762bd5a1157a779c8781caf6f7d872990d2a0fdbc9`.

## Retaining the original witnesses

Each signed SAT inequality has a unit normal fixed by one of the two
square frames. During a one-center motion, both incident inequalities
are halfplanes in that center. Their two unit inward normals have a
common nonzero recession direction: their sum unless they are opposite,
and a perpendicular direction in the opposite case. Thus the radial
boundary construction can keep the initially selected axis on every
edge throughout all motions. The other five inequalities are unchanged
by that motion. The original boundary theorem's cyclic-order argument
continues to apply, since every adjacent pair remains separated.

This strengthening needs no assertion that individual center rays or
the original positions remain fixed. Nor does it require nonadjacent
pairs to remain separated in the adjacent-pair relaxation.

If an outer-radius expansion is used in capture, its already-proved
axis-preservation property applies separately to every originally
feasible signed separator. Consequently the selected original
witnesses are still feasible at the expanded representative. An owner
exclusion there forces each of those witnesses into the allowed set.
This implication does not reverse an implication about existence of
some separator: it retains the same actual separator throughout.

## Frames and the stationary dual

At squared radius `q*`, the displayed terminal inequality is a sum of
nonnegative terms with strictly positive coefficients. It forces
`t=t*` and `S=0`. The boundary construction preserved all frames, so
these are statements about the original packing as well. At `S=0`,
the tied allowed owners on an aligned edge have the same signed
normal; the mixed-edge allowed owners already specify the required
stationary directions.

With those fixed directions, the selected gap sum is affine in all
seven original centers. Its two slider force coefficients vanish.
For each anchored center its force coefficient is
`-2*mu_i*(p_i^0+o_i)`. Completing the five squares therefore gives the
exact identity (2) for arbitrary original centers, without proximity
or projected-slider hypotheses. Its constant can be evaluated at any
stationary comparison: all five selected vertices have squared norm
`q*` and all seven selected gaps are zero. The comparison's slider
coordinates do not affect the identity.

Every selected vertex of an original contained square is in the disk,
and every originally selected gap is nonnegative. Thus (3) has the
correct sign. Combining (2) and (3) forces all five anchored centers
to equal their stationary centers and all seven gaps to vanish.
The latter conclusion uses positivity of every contact weight, which
is an explicit premise of the stationary hand dual.

## Exterior freedoms and scope

The two horizontal contacts determine the T center's horizontal
coordinate and leave its vertical coordinate free. The HG and GA
contacts determine the same longitudinal coordinate of G and leave
its transverse coordinate free. The formulas (5) are therefore the
correct necessary forms of the original exterior sliders. No
positional pullback along the radial paths is needed.

This proves a rigid exterior skeleton with two specified slider
directions, modulo the stated isometries and relabeling. It does not
prove an isolated optimal configuration, and the manuscript correctly
does not claim one. A complete equality classification must still
give necessary and sufficient joint conditions for the two sliders
and the eighth square, including that square's orientation.
