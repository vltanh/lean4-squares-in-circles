# Common routing of an outsider cone three-chain beside an actual four-chain

November 2, 2026. Complete hand reduction for original physical squares.
It uses no actual edge of the selected three-chain, and therefore applies
to the selected weak/weak triple of `000/11`.

Let \(M_0<_xM_1<_xM_2<_xM_3\) be an actual horizontal four-chain
whose consecutive centers also obey the horizontal cone comparisons.
Let \(L<_cP<_cR\) be a disjoint outsider horizontal cone three-chain.
All units are original squares with arbitrary independent frames, all
pairwise open interiors are disjoint, and all corners lie in the closed
disk of squared radius \(Q=1105/256\).

Use the inherited actual-four bounds

\[
 \begin{gathered}
 l=29/60,\quad |x_S|<13/12\text{ for every outsider }S,\\
 -31/60<x_1<-29/60,\quad29/60<x_2<31/60,
 \quad g_1,g_2>15/31,\\
 -139/120<y_1,y_2<139/120,\quad |y_2-y_1|<31/30,
 \quad |y_0|,|y_3|\le1/8,\\
 -91/60<x_0<-89/60,\quad89/60<x_3<91/60.
 \end{gathered}
\]

For an original unit S, \(g_S=1/(4h_S)\) is the halfwidth of its
contained aligned square. Every selected cone edge implies both

\[
 x_T-x_S\ge g_S+g_T\ge1/\sqrt2>7/10,
 \qquad |y_T-y_S|\le x_T-x_S.                    \tag{1}
\]

## 1. Horizontal placement

The two separate edge gaps give

\[
 |x_P|<23/60<l,\quad x_L<-19/60<0<x_R,
 \quad x_R>19/60.                              \tag{2}
\]

In particular P is central and lies strictly between the two inner main
centers. The total cone span is at least

\[
 x_R-x_L\ge g_L+2g_P+g_R\ge\sqrt2>7/5.         \tag{3}
\]

Thus the selected triple cannot consist of three central units, whose
total horizontal span would be at most \(2l=29/30<\sqrt2\).

## 2. One common vertical choice

For a physical outsider's contained radius-one-half disk to avoid an
inner main's aligned inset of halfwidth g, the center gaps D,V obey

\[
 \max(D-g,0)^2+\max(V-g,0)^2\ge1/4.             \tag{4}
\]

For P, both inner-main horizontal gaps are below \(9/10\).
Since \(g_i>12/25\), (4) gives

\[
 |y_P-y_i|>(12+\sqrt{46})/25>3/4\quad(i=1,2).
\]

Here \(D-g<1/2\), so the vertical excess in (4) is necessarily
positive. If P were between the two main heights, their difference
would exceed \(3/2>31/30\). Hence P is above both or below both.
Reflect vertically so that P is above both.

By (2), L's horizontal gap from M1 and R's gap from M2 are below
\(3/5\). Formula (4) gives

\[
 |y_L-y_1|>29/30,\qquad |y_R-y_2|>29/30,
\]

using the exact positive reserve

\[
 1/4-(18/155)^2-(29/30-15/31)^2=2960/864900>0.
\]

If L were below M1, then
\(y_P-y_L>3/4+29/30=103/60\). But (1)--(2) give
\(y_P-y_L\le x_P-x_L<23/60+13/12=88/60\).
This contradiction shows L is above M1. Reflection proves R is above
M2. Every central selected endpoint is consequently above both inner
mains by the general central routing lemma (Section 2 of
`ACTUAL_FOUR_FULL_SIDE_OCCUPANCY_CLOSED_HAND_PROOF.md`). A selected
endpoint in its actual side column also forces its own main below
\(7/20\), by the one-sided main-height theorem.

This is a common center routing. It does not assert an original vertical
projection separator or impose a frame or contact owner.

## 3. A central endpoint forces the opposite side endpoint high

Suppose R is central. Equation (3) gives

\[
 x_L<l-7/5=-11/12,
 \qquad x_P\le l-g_P-g_R<0.                    \tag{5}
\]

Thus L is an original left-side unit and its horizontal center gap from
M0 is below
\(91/60-11/12=3/5\). Their disjoint radius-one-half disks give
\(|y_L-y_0|>4/5\). Section 2 gives

\[
 y_L>y_1+29/30>-139/120+29/30=-23/120.
\]

L cannot be below M0, since that would give
\(y_L<1/8-4/5=-27/40<-23/120\). Therefore

\[
                         \boxed{y_L>27/40>3/5.}  \tag{6}
\]

The reflected assertion holds when L is central: R is an original high
right-side endpoint. Hence any selected cone triple containing a central
endpoint already supplies a high original shoulder on the opposite side.

## 4. Arithmetic record

All comparisons in this reduction are rational except
\(1/\sqrt2>7/10\), \(\sqrt2>7/5\), and
\(\sqrt{46}>27/4\); each follows by squaring positive quantities.
The supporting arithmetic is reconstructed in
`verify_coupled_cone_inset_loss.py` alongside the coupled floor lemma.
