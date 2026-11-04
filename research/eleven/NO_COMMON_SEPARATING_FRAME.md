# The exact eleven square family has no common separating frame

Every packing in the exact family of `CANDIDATE_CONTACT_SYSTEM.md` lacks a
common orthogonal separating frame. Two pairs of squares force different,
nonorthogonal separator normals. The conclusion holds throughout the horizontal
slider interval and survives rotations, reflections, translations, and
relabeling.

Here a **common orthogonal separating frame** means an orthonormal basis
`(e,f)` such that, for every pair of squares, their projection intervals in
at least one of directions `e` or `f` are weakly separated. Equality of projection
endpoints is allowed. Equivalently, for each pair `A,B`, one of these two
nonzero directions `n` satisfies

\[
\max_{x\in A} n\cdot x\le\min_{y\in B} n\cdot y
\quad\text{or}\quad
\max_{y\in B} n\cdot y\le\min_{x\in A} n\cdot x.
\]

This concerns the full physical square sets. It does not depend on which
separating-axis owner was selected in a certificate.

## A shared edge forces its normal

**Lemma.** Suppose two compact sets `A,B` contain the same nondegenerate
line segment `L`, and `n≠0` weakly separates their projection intervals.
Then `n` is perpendicular to the direction of `L`.

**Proof.** Choose the ordering
`max_A(n·x) ≤ min_B(n·x)`; the reverse ordering has the same proof.
For every point `p` of `L⊆A∩B`,

\[
n\cdot p\le\max_A(n\cdot x)
\le\min_B(n\cdot x)\le n\cdot p.
\]

All terms are equal. Thus `n·p` is constant on `L`. For two distinct points
`p,p'∈L`, `n·(p−p')=0`, so `n` is perpendicular to the segment. In the plane,
this determines its direction up to sign. ∎

This argument retains boundary contact; replacing weak separation with a
strict gap would incorrectly discard the pairs used below.

## Pair 0 and 2 forces the horizontal normal

The exact centers are

\[
p_0=(a,b),\qquad p_2=(a+1,d),
\]

and both squares are parallel to the coordinate axes. Their common vertical
support line is `x=a+1/2`. On that line, their side intervals are

\[
[b-1/2,b+1/2],\qquad[d-1/2,d+1/2].
\]

The exact interval certificate verifies

\[
-9/10<d-b<0
\]

uniformly on the root's entire isolating rectangle. Consequently these side
intervals overlap in a segment of length
`1−|d−b|>1/10`. The shared-edge lemma forces every separating normal of
squares 0 and 2 to be horizontal, parallel to `ex=(1,0)`.

## Pair 7 and 8 forces the oblique normal

Both squares use the orthonormal frame

\[
u=(c,s),\qquad j=(-s,c),
\]

with centers

\[
p_7=-ru,\qquad p_8=(1-r)u+zj.
\]

In this frame their center displacement is `(1,z)`. Their common support line
is therefore the line of local `u` coordinate `1/2−r`. The two side intervals
in the local `j` coordinate are

\[
[-1/2,1/2],\qquad[z-1/2,z+1/2].
\]

The exact interval certificate verifies

\[
0<z<1/20.
\]

Their shared edge segment has length `1−z>19/20`, parallel to `j`. The
shared-edge lemma forces every separating normal of squares 7 and 8 to be
parallel to `u`.

The same certificate verifies `c>0` and `s>0`. Thus `u` is neither horizontal
nor vertical.

## Contradiction for a common orthogonal frame

If a common orthogonal frame existed, one of its axes would have to be
horizontal to separate squares 0 and 2. Its other axis would consequently be
vertical. Neither axis is parallel to `u`, so neither could separate squares
7 and 8. This contradicts the definition of a common separating frame.

The argument does not involve square 1's horizontal parameter `h`, so it
applies to every member of the constructed sliding family. Planar rigid motions
preserve shared segments, perpendicularity, and the nonparallel directions;
relabeling only changes the names of the two pairs.

## Reproducible exact check and gate consequences

`check_oblique_witness.py` imports the existing root certificate and evaluates
the new bounds with its rational interval arithmetic:

```sh
python check_oblique_witness.py
```

Its exact assertions are `−9/10<d−b<0`, `0<z<1/20`, `c>0`, and `s>0` over the
whole certified root rectangle. The shared-edge and orthogonal-frame arguments
above turn those assertions into the geometric obstruction. The previously
reviewed root, family, and feasibility certificate files are unchanged.

The constructed family has `q_c<49013/10000`, so it lies inside the radius range
used for the unrestricted finite-case reduction. It is a concrete feasible
oblique class within that range. Consequently a claimed exhaustive reduction
of those physical packings to a common orthogonal frame, using only rigid
motions and relabeling, is false. A parallel-only case list cannot cover this
family. A different deformation-based reduction would require its own theorem
about preservation of radius and feasibility.

This closes the obstruction gate for a common separating frame. It does not
prove that the candidate radius is sharp, that every optimum is oblique, or
that the constructed family exhausts global equality cases.
