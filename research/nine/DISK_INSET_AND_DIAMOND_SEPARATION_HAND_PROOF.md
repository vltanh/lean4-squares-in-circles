# Universal disk-to-inset and disk-to-diamond separation inequalities

This is a complete necessary geometric argument for any two distinct
original physical unit squares with disjoint open interiors. It does
not require a marked chain, a radius bound, a tilt sign, or a chosen
physical separator owner. It supplies rational linear inequalities for
a finite search; an unfinished search remains unfinished after adding
them. No Lean, Lake, or CI is involved.

## 1. Physical containment and distance

Every original unit square contains the open Euclidean disk of radius
`1/2` about its center. If another original contains a centered closed
convex set K which is the closure of its interior, the distance from the
first center to the translated K is at least `1/2`. Indeed a smaller
distance would make the open disk meet the interior of K and hence the
interiors of both unchanged original squares. This is a necessary
condition even when the physical squares touch.

Write the center displacement as `(d_x,d_y)` and define, for `s>0`,

\[
                         f_s(t)=(|t|-s)_+^2.
\]

The squared distance to a centered coordinate square of halfwidth s is
`f_s(d_x)+f_s(d_y)`. The function `f_s` is convex on the entire real
line, including the transition points `-s,0,s`.

## 2. Coordinate inset

Represent each unchanged original frame by

\[
 u_i=(\alpha_i,\beta_i),\quad v_i=(-\beta_i,\alpha_i),\quad
 \alpha_i>0,\quad |\beta_i|\le\alpha_i,\quad
 \alpha_i^2+\beta_i^2=1.
\]

Its coordinate halfwidth is `h_i=(alpha_i+|beta_i|)/2`, and it contains
the centered coordinate square of halfwidth

\[
                 g_i=\frac{1}{2(\alpha_i+|\beta_i|)}
                     =\frac1{4h_i}.
\]

For example, if both coordinates have magnitude at most `g_i`, their
absolute scalar products with either original frame vector are at most
`(alpha_i+|beta_i|)g_i=1/2`, proving containment directly.

Suppose a closed search cell gives positive rational lower bounds
`g_i^-<=g_i` and `g_j^-<=g_j`. Set

\[
                         g=\max(g_i^-,g_j^-).
\]

Choose the original whose recorded lower bound equals g. Its centered
coordinate square of halfwidth g is contained in that same original;
the other original supplies its open radius-`1/2` disk. Section 1 gives

\[
                  \boxed{f_g(d_x)+f_g(d_y)\ge\frac14.}       \tag{1}
\]

There is no simultaneous substitution of two new physical squares.
The maximum chooses only which original supplies the contained inset.

## 3. A complementary diamond inset

The same original frame also contains the centered diamond

\[
 |x|+|y|\le p_i,\qquad p_i=\frac{1}{2\alpha_i}.
\]

Indeed each absolute frame scalar product is bounded above by
`alpha_i(|x|+|y|)<=1/2`. This uses only the canonical inequality
`|beta_i|<=alpha_i`, with no chosen sign of beta.

In the unnormalized diagonal coordinates

\[
                      U=x+y,\qquad V=x-y,
\]

this diamond becomes the square `|U|,|V|<=p_i`, because
`max(|x+y|,|x-y|)=|x|+|y|`. Squared Euclidean distances are multiplied
by two. The other original's open radius-`1/2` disk therefore becomes
an open disk of squared radius `1/2` in U,V coordinates.

If rational upper bounds `0<alpha_i<=a_i^+` and
`0<alpha_j<=a_j^+` are valid on the cell, put

\[
               p=\max\left\{\frac1{2a_i^+},\frac1{2a_j^+}\right\}.
\]

The same selection of one unchanged original and the other original's
disk proves

\[
          \boxed{f_p(d_x+d_y)+f_p(d_x-d_y)\ge\frac12.}       \tag{2}
\]

All coefficients can be rational; no numerical value of `sqrt(2)` is
needed. The coordinate inset is exact for an aligned original, while
the diamond inset is exact for an original at a diagonal canonical
endpoint. Inequalities (1) and (2) are independent valid necessary
conditions and may both be imposed.

## 4. Exact secants give linear necessary rows

For any closed rational interval `[l,u]` with `l<u`, define

\[
 A_s(l,u)=\frac{f_s(u)-f_s(l)}{u-l},\qquad
 B_s(l,u)=\frac{u f_s(l)-l f_s(u)}{u-l}.
\]

Convexity gives the upper bound

\[
                    f_s(t)\le A_s(l,u)t+B_s(l,u)
                    \quad(l\le t\le u).                  \tag{3}
\]

This remains valid when the interval crosses any of `-s,0,s`. If
`l=u`, the exact contribution is the constant `f_s(l)`; take A=0
and B=`f_s(l)` without dividing by zero.

For valid rational intervals for `d_x,d_y`, apply (3) to (1). The sum
of the two affine secants is at least `1/4`. For valid intervals for
`d_x+d_y,d_x-d_y`, apply it to (2); that sum is at least `1/2`.
Each resulting inequality is a linear row on the same original center
variables. Its coefficients are computed from the recorded cell bounds
and rational lower inset size. All shared interval endpoints are kept.

These inequalities may strengthen an existing rational contradiction,
but they do not certify an exclusion by themselves. Every resulting
finite leaf still needs an exact positive-reserve check, and every
remaining cell still needs coverage.
