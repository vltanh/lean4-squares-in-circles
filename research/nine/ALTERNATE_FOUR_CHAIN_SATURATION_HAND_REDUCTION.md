# Every alternative outer-actual four-chain is a terminal

November 3, 2026. Complete finite reduction using the already accepted
whole-mask proofs. This is a family of valid analytic terminals and
necessary escape conditions, not a claim that an alternative chain always
exists. No Lean, Lake, or CI.

## 1. The original caller and the global implication

Retain the original nine physical squares in the fixed `001/00` caller:
main chain A,B,C,D, actual short chain E,F,G, and unrestricted extras H,I.
Every original frame, corner and physical pair is retained. Put
`Q=1105/256`. In particular `x_A<x_B<x_C<x_D`, the original AB and BC
links are actual, and CD is a genuinely weak center-cone link.

Choose any four distinct originals U0,U1,U2,U3 from
`{A,B,C,D,H,I}`. Suppose their three successive differences satisfy

\[
x_{U_{j+1}}-x_{U_j}\ge |y_{U_{j+1}}-y_{U_j}|\qquad(0\le j<3),
\]

and the two outer links satisfy

\[
x_{U_1}-x_{U_0}\ge h_{U_0}+h_{U_1},\qquad
x_{U_3}-x_{U_2}\ge h_{U_2}+h_{U_3}.
\]

The middle link is either actual or genuinely weak. With the *unchanged*
E,F,G as the short chain, the original packing therefore has another
witness of `000/00` or `010/00`. The former gives `R^2>=Q`; the latter
is impossible even at Q. Thus the displayed alternative four-chain is
impossible in every strict counterexample `R^2<Q`.

No hypothesis about the vertical gaps being small is used. The replacement
originals keep their actual physical frames. The two originals omitted by
the alternative witness remain in the physical configuration. This is an
application of an accepted terminal, not a new cone comparison attached
without proof.

More generally, since all eight masks `000/**` and `010/**` are closed for
strict radius, in a hypothetical strict counterexample *every* frame and
every four-cone chain with actual outer links has a complement containing
no three-cone chain in that direction. The fixed E,F,G above provide the
complementary three-chain automatically.

## 2. A complete finite selector with 105 entries

Every four-cone chain orders its original A,B,C,D members in their known
increasing x-order. Consequently it is enough to enumerate the ordered
four-tuples from `{A,B,C,D,H,I}` that preserve the subsequence order A,B,C,D.
There are exactly

\[
1+\binom43\,2\,4+\binom42\binom42\,2=1+32+72=105.
\]

The terms distinguish zero, one, and two selected extras. This is a finite
terminal list inside the unchanged domain; it does not create 105 roadmap
gates or assert 105 mask closures. The original tuple A,B,C,D is included
for a uniform formula, although its original strict CD bit prevents it
from satisfying the terminal premises.

For any listed tuple, define eight slacks: the six cone slacks

\[
r_{j,-}=x_{U_{j+1}}-x_{U_j}-(y_{U_{j+1}}-y_{U_j}),\qquad
r_{j,+}=x_{U_{j+1}}-x_{U_j}+(y_{U_{j+1}}-y_{U_j}),
\]

for `j=0,1,2`, followed by its two outer actual slacks

\[
r_L=x_{U_1}-x_{U_0}-h_{U_0}-h_{U_1},\qquad
r_R=x_{U_3}-x_{U_2}-h_{U_2}-h_{U_3}.
\]

Every strict counterexample has at least one of these eight slacks strictly
negative, for every selector. Hence the eight **closed** escape children
`r_k<=0` cover the remaining domain. Shared equality faces are retained.
An interval proof may use the terminal only when its whole box satisfies
all eight nonnegative inequalities, or may branch on the complete escape
union. No positive arithmetic reserve is asserted merely because the
terminal itself uses a strict-radius theorem.

Useful particular tuples include A,B,H,D; A,B,I,D; A,H,I,D; and A,I,H,D.
The first two need only the two newly displayed cone links and an actual
last link, since the original AB data already supply the other outer link.
These are often much wider regions than the earlier `1/8` replacement-row
terminal.

`alternate_four_selectors.json` contains the complete index list with
labels `A=0,B=1,C=2,D=3,E=4,F=5,G=6,H=7,I=8`. The exact Fraction utility
`alternate_chain_selector.py` checks that list and computes the eight
slacks for an exact configuration. It does not test the truth of a global
existence assertion.

## 3. Same-endpoint selectors are impossible even at closed Q

There is a stronger scope when `U0=A` and `U3=D`. Suppose the original
strict `001/00` caller lies in the closed Q-disk and such an alternative
chain satisfies all terminal premises. If its middle edge is weak, the
accepted `010/00` theorem already contradicts the configuration at Q.
Otherwise it is an actual four-chain disjoint from the actual E,F,G chain.

Equality in the accepted physical 4+3 cap theorem forces the original
endpoints A,D to be aligned in this frame and

\[
h_A=h_D=g_D=\frac12,\qquad x_D-x_A=3.
\]

The *original* AB and BC actual comparisons, together with the original
CD cone and its contained-inset comparison, give

\[
\begin{aligned}
3=x_D-x_A
&\ge h_A+2h_B+h_C+g_C+g_D\\
&=1+2h_B+(h_C+g_C)\ge3.
\end{aligned}
\]

For every original square,

\[
h_C+g_C-1=\frac{(2h_C-1)^2}{4h_C}\ge0.
\]

Equality therefore gives `h_B=h_C=1/2`. Since D is aligned as well, the
original CD inset comparison yields `x_D-x_C>=1=h_C+h_D`, contradicting
the retained strict weak CD bit. This proves closed-Q exclusion for every
same-endpoint selector, including all owner, orientation and contact
boundaries. It never asserts equality classification for an arbitrary
alternative-endpoint selector.

## 4. Remaining logical obligation

The necessary saturation statement is now exact: all 105 selectors must
fail in a hypothetical strict `001/00` counterexample. What remains is to
prove that the original nine-square geometry forces at least one selector
to succeed, or to exclude the complete saturated complement by other
arguments. No such exhaustive routing is proved here. In particular this
reduction changes no whole-mask or positional-root count.
