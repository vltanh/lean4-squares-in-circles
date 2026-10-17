# Wrong word 0011011: the symmetric aligned outer contact

This is a self-contained hand proof of the strict symmetric aligned
outer/outer contact inequality used in the whole-angle edge-4 theorem.
It concerns exactly that contact regime, not the remaining seven-edge
table. All terminating decimals are rational numbers.

## 1. Statement

Set
\[
 Q=\frac{9789}{2500},\qquad
 d=\sqrt{Q/2}-\frac12,\qquad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,
\]
and
\[
 L(b)=.03965+3.85510b-1.49748b^2-1.89442a(b)b.
\]
For any two outer states satisfying
\[
 0\le b,B\le d,\qquad b+B=1,
\]
we prove
\[
 \boxed{L(b)+L(B)>.89777>.89765.}                       \tag{1}
\]
At aligned frames this is the edge-4 corrected cost. The whole-angle
theorem separately proves that the relevant feasible secondary-axis
pairs reduce to these contacts; no such reduction is assumed or needed
in the present calculation.

## 2. Eliminate the two radicals symmetrically

Write
\[
 b=\frac12+x,\quad B=\frac12-x,\quad z=x^2,\quad
 R=Q-1=\frac{7289}{2500},
\]
and put
\[
 u=\sqrt{R-z-2x},\qquad v=\sqrt{R-z+2x},\qquad U=u+v.
\]
These radicals are positive. Since `u^2-v^2=-4x`,
\[
 u-v=-\frac{4x}{U},\qquad
 U^2+\frac{16z}{U^2}=4(R-z).
\]
Consequently
\[
 \boxed{z=\frac{U^2(4R-U^2)}{4(U^2+4)}.}              \tag{2}
\]
This identity is obtained from the actual radicals; squaring has not
introduced an extra admissible branch.

Let `p=1.49748`, `g=1.89442`, and `gamma=.89765`. Expanding the two
labels before substituting (2) gives
\[
 L(b)+L(B)-\gamma
   =C-\frac g2U-2pz+\frac{4gz}{U},\qquad C=3.23522.
\]
Therefore
\[
 L(b)+L(B)-\gamma=\frac{P(U)}{U^2+4},                  \tag{3}
\]
where the explicit quartic is
\[
\begin{split}
 P(U)={}&\frac{161761}{12500}
 +\frac{572020119}{31250000}U
 -\frac{42944417}{7812500}U^2\\
 &-\frac{284163}{100000}U^3
 +\frac{37437}{50000}U^4.                              \tag{4}
\end{split}
\]
For a direct coefficient check, these five coefficients are respectively
`4C`, `g(4R-2)`, `C-2pR`, `-3g/2`, and `p/2`.

## 3. A rational interval for the radical sum

Squaring positive numbers proves `.5<d<.9`. The contact domain thus
gives `|x|<=d-.5<.4`. Each summand of
\[
 U(x)=\sqrt{Q-(1+x)^2}+\sqrt{Q-(1-x)^2}
\]
has second derivative `-Q` divided by the cube of its own radical.
Hence `U` is strictly concave and even on `[-.4,.4]`. Its minimum on
that interval is at an endpoint and its maximum is at zero.

The three elementary square comparisons
\[
 Q-1.4^2>1.398^2,\qquad Q-.6^2>1.885^2,\qquad
 4(Q-1)<3.42^2
\]
then give
\[
 U(x)\ge U(.4)>1.398+1.885>3.28,
 \qquad U(x)\le U(0)<3.42.                             \tag{5}
\]
The extended interval in this argument only makes the lower bound
weaker. No extremizer of an unproved numerical search is used.

## 4. One strongly convex quartic comparison

The third derivative of (4) is
\[
 P'''(U)=-17.04978+17.96976U.
\]
It is positive for `U>=3.28`. Thus `P''` increases there, and direct
rational substitution gives
\[
 P''(3.28)>29.
\]
At the rational reference point
\[
 U_0=\frac{16987}{5000}=3.3974
\]
the two exact comparisons are
\[
 P(U_0)>.001948,\qquad |P'(U_0)|<.0015.                \tag{6}
\]
Taylor's integral formula and `P''>29` therefore imply throughout
`[3.28,3.42]`
\[
\begin{split}
 P(U)&\ge P(U_0)+P'(U_0)(U-U_0)+\frac{29}{2}(U-U_0)^2\\
 &\ge P(U_0)-\frac{P'(U_0)^2}{58}\\
 &>.001948-\frac{(.0015)^2}{58}>.0019.                 \tag{7}
\end{split}
\]
All quantities in (6) and (7) are explicit rational numbers; they do
not depend on locating a critical point of the quartic.

Finally, (3), (5), and (7) yield
\[
 L(b)+L(B)-\gamma>
 \frac{.0019}{3.42^2+4}
 =\frac{19}{156964}>.00012.
\]
This proves (1). In particular this regime has no equality case for
the rounded bound `.89765`. \(\square\)

## Optional exact arithmetic replay

`verify_wrong_0011011_symmetric_aligned_hand.py` checks only the fixed
coefficient identities and rational comparisons displayed above.
It has no root solver, partition refinement, optimizer, or imported
proof data. The geometric reduction, radical identity, concavity,
and completed-square argument are the proof.
