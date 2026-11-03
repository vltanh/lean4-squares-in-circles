# The original C/F insets separate vertically, with a strict cone reserve

November 3, 2026. Complete hand consequence of the accepted short-middle
order theorem. No new interval forest, Lean, Lake, or CI is needed.

Retain the unchanged original strict `001/00` caller in a disk of radius
`R<=sqrt(Q)`, where `Q=1105/256`, normalized by `v=y_D-y_C>=2/3`.
The original marked links AB, BC, EF, and FG are actual. Every original
physical frame and pair remains present. Write

\[
 h_i=\frac{\alpha_i+|\beta_i|}{2},\qquad
 g_i=\frac1{4h_i},\qquad
 \frac12\le h_i\le\frac1{\sqrt2},\qquad
 h_i+g_i\ge1.
\]

Here g_i is the halfwidth of the aligned square contained in the same
physical original. The completed F-order theorem supplies `y_F>y_C`.

**Conclusion.** The same original C,F satisfy

\[
 \boxed{y_F-y_C\ge g_C+g_F\ge\frac1{\sqrt2}>\frac7{10}},       \tag{1}
\]

and the stronger horizontal-overlap estimate

\[
 \boxed{|x_F-x_C|<g_C+g_F-\frac1{25}.}                       \tag{2}
\]

Consequently C to F is a strict vertical center-cone comparison with
uniform reserve

\[
                 y_F-y_C-|x_F-x_C|>\frac1{25}.               \tag{3}
\]

These statements concern the original physical squares and their
contained insets. Actual separation of their full vertical projection
intervals is not asserted.

## 1. The original left cap bounds F's horizontal coordinate

Set

\[
 u=x_C-h_C,\quad a=46,\quad b=27/2,\quad T=211/4=a+b/2,
 \quad \kappa=a/b=92/27,\quad \lambda=1+\kappa=119/27.
\]

As in the completed F-order argument, the original actual AB and BC
links give `-x_A-h_A>=1-u`, and actual EF gives
`-x_E-h_E>=h_F-x_F`. The ordinary physical A/E cap yields

\[
 a(1-u)+b(h_F-x_F)\le T,
 \qquad
                 x_F\ge h_F-\frac12-\kappa u.               \tag{4}
\]

The original C/D cone inset comparison is
`x_D-x_C>=g_C+g_D`. Coordinate containment of the same D gives
`x_D+h_D<=R`. Therefore

\[
\begin{aligned}
 u&\le R-(h_C+g_C)-(h_D+g_D)\\
  &\le R-1-h_C-g_C.                                        \tag{5}
\end{aligned}
\]

No C/F or F/G height assumption was used in (4)--(5).

## 2. C cannot lie too far to the right of F

Using (4), then `h_F+g_F>=1`, and then (5), gives

\[
\begin{aligned}
 x_C-x_F-g_C-g_F
 &\le h_C-g_C-(h_F+g_F)+\frac12+\lambda u\\
 &\le h_C-g_C-\frac12+\lambda u\\
 &\le\lambda(R-1)-\frac12
       -(\lambda-1)h_C-(\lambda+1)g_C.              \tag{6}
\end{aligned}
\]

Since `h_C*g_C=1/4` and both coefficients are positive, the elementary
arithmetic-geometric mean inequality implies

\[
 (\lambda-1)h_C+(\lambda+1)g_C
 \ge\sqrt{\lambda^2-1}=\sqrt{\frac{13432}{729}}.
\]

The already established radius bound `R<133/64` gives

\[
 \lambda(R-1)-\frac12<\frac{2449}{576}.
\]

The following exact positive comparison proves a convenient reserve:

\[
 \frac{13432}{729}
  -\left(\frac{2449}{576}+\frac1{25}\right)^2
 =\frac{11647591}{1866240000}>0.                    \tag{7}
\]

All terms being compared are positive. Equations (6)--(7) therefore
give

\[
                  x_C-x_F<g_C+g_F-1/25.             \tag{8}
\]

The weaker zero-reserve square comparison has numerator 1,039,063;
the stronger reserve in (7) is included explicitly so that (3) may
be used as a quantitative necessary row.

## 3. The opposite horizontal direction is also covered

Actual FG, the original center-radius bound `x_G<rho=91/60`, and
`h_F+h_G>=1` give `x_F<31/60`. The inherited left-cap localization
`x_C>h_C-1/60` gives `x_C>29/60`. Thus

\[
                    x_F-x_C<1/30.
\]

Also `g_C+g_F>=1/sqrt(2)`, and

\[
 \frac12-\left(\frac1{30}+\frac1{25}\right)^2
 =\frac{11129}{22500}>0.
\]

It follows that `1/30<g_C+g_F-1/25`. Together with (8), this proves
the two-sided estimate (2), including every original chirality.

## 4. Original physical nonoverlap fixes the vertical separation

Equation (2) says that the open horizontal projections of the two
contained aligned C,F insets overlap strictly. The inset interiors
are subsets of the disjoint original interiors, so the insets must
separate vertically. The completed original order `y_F>y_C` fixes
the positive sign, proving the first inequality of (1). The universal
inset lower bound gives its second inequality; the last strict
comparison follows from `1/2-(7/10)^2=1/100>0`. Subtracting (2) yields
the strict vertical-cone reserve (3).

The exact arithmetic companion is
`computer_assisted/extraction_search_CF_inset_arithmetic.py`, with a
saved PASS report. Its comparisons use only fractions. The proof is
acyclic: the existing F-order forest used no C/F inset-separation row.
This new original comparison can therefore strengthen subsequent
placement and order arguments, without changing the accepted F-order
certificate or closing a whole fixed mask by itself.
