# A small-tilt full cone grid is impossible at the target radius

November 3, 2026. Complete hand argument, following numerical exploration
of the full nine-original grid. No Lean, Lake, or CI. This is a geometric
input to frame selection, not an unrestricted mask closure.

## 1. Statement

Let nine original unit squares be pairwise interior-disjoint in the closed
disk `R^2<=Q=1105/256`. Fix a coordinate frame and suppose that every
original folded side slope satisfies

\[
|\tan\theta_i|\le\frac1{43}.
\]

There cannot be a labeling `S_ij`, `1<=i,j<=3`, with all three center-cone
rows and all three center-cone columns:

\[
S_{1j}\prec_x S_{2j}\prec_x S_{3j},\qquad
S_{i1}\prec_y S_{i2}\prec_y S_{i3}.
\]

Consequently, using the already proved universal height-at-most-four
theorem, at least one of the two pure center-cone orders has height four
in *this same frame*. The conclusion is a four-cone chain, not an assertion
that its outer links are actual.

## 2. Two uniform necessary geometric inequalities

Write `t=1/43`, `r=sqrt(1+t^2)`,

\[
\ell=\frac{r}{1+t},\qquad \gamma=\frac{1-t}{r}.
\]

For an original square of folded slope `s<=t`, its coordinate halfwidth is
`h=(1+s)/(2sqrt(1+s^2))`. The same physical square contains its centered
aligned inset of halfwidth

\[
g=\frac1{4h}=\frac{\sqrt{1+s^2}}{2(1+s)}\ge\frac\ell2.
\]

The function on the right decreases in `s` on `[0,1]`. Two original
insets belonging to a cone edge must separate in its dominant coordinate.
Thus every prescribed row x-gap and column y-gap is at least `ell`.

If the original square center is `(x,y)`, its farthest physical corner has
squared norm

\[
x^2+y^2+\frac12+|c\cdot u|+|c\cdot v|.
\]

For either original chirality, the reverse triangle inequality gives

\[
|c\cdot u|+|c\cdot v|
\ge(\alpha-\beta)(|x|+|y|)\ge\gamma(|x|+|y|),
\]

where `alpha=1/sqrt(1+s^2)` and `beta=s alpha`. The final coefficient is
decreasing in `s` on `[0,1]`. Every original center therefore satisfies
the same convex, dihedrally invariant necessary condition

\[
F(x,y):=x^2+y^2+\gamma(|x|+|y|)+\frac12\le Q.       \tag{1}
\]

These are relaxations derived from unchanged original insets and corners.
No physical orientation is averaged or replaced in the actual packing.

## 3. Convex symmetrization of the necessary center system

Consider only the eighteen center variables, the twelve linear row/column
gap inequalities, and condition (1) for each center. Their feasible set is
convex. It is invariant under reflections and interchange of coordinates,
with the corresponding reflections/transposition of the `3 by 3` labels.

Average the eight images under this square symmetry group. Convexity makes
the averaged center array feasible for these *necessary inequalities*.
This is not asserted to be a new physical packing; only feasibility of
the convex relaxation is used.

The symmetrized lower-left corner center has the form `(-a,-a)`, its
lower-right counterpart is `(a,-a)`, and the lower-middle center has
x-coordinate zero. The two lower-row x-gaps are at least `ell`, so
`a>=ell`. Applying (1) to the symmetrized corner yields

\[
Q\ge 2a^2+2\gamma a+\frac12
\ge2\ell^2+2\gamma\ell+\frac12
=\frac4{(1+t)^2}+\frac12.                            \tag{2}
\]

The last identity is exact:

\[
2\ell^2+2\gamma\ell
=\frac{2(1+t^2)}{(1+t)^2}+\frac{2(1-t)}{1+t}
=\frac4{(1+t)^2}.
\]

At `t=1/43`, the right side of (2) is `2091/484`, whereas

\[
\frac{2091}{484}-\frac{1105}{256}
=\frac{119}{30976}>0.
\]

This contradiction excludes the full grid, including every equality face.

## 4. From absence of the grid to height four

If both pure center-cone orders had height at most three, the ordinary
ending-rank argument would assign all nine distinct squares distinct
pairs in `{1,2,3}^2`: every pair is comparable in at least one order.
All nine rank pairs would occur. Squares of equal y-rank form an x-chain,
and squares of equal x-rank form a y-chain, giving exactly the prohibited
grid. Thus one height is at least four. The inherited geometric no-five
theorem makes that height exactly four.

The accepted nine-element chain/antichain extraction then gives disjoint
cone chains of sizes four and three in this frame or its perpendicular.
Their actual/weak statuses remain unrestricted. A separate geometric
argument is still needed to supply actual outer links or another sharp
terminal.

## 5. Scope and numerical discovery

The more general bound (2) holds whenever all original folded slopes are
at most `t<1`, and a full cone grid is present. It excludes the grid when
`t<32/sqrt(977)-1`; the rational `1/43` is a convenient strictly interior
choice.

Numerical exploration first confirmed that a bare full cone grid *without*
the tilt condition can attain Q in a diagonal frame. Therefore neither
that bare grid nor a one-sided first-birth condition has been silently
substituted for the stated hypothesis. The proof above needs no numerical
claim, optimizer status, or finite interval cover.

This changes no fixed-mask, positional-root, or roadmap count.
