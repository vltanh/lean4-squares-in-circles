# The canonical negative outer boundary is sharp once its two errors are small

## 1. A five-anchor theorem, with its exact remaining input

Put
\[
 Q_0=\frac{9789}{2500},\qquad
 Q_1=\frac{1957767069}{500000000},\qquad
 q_L=\frac{19577}{5000},\qquad K=\frac{13}{12},
 \qquad W(z)=\frac{1+\cos z+\sin z}{2}.
\]
Let H, A, B, D and E have nonnegative sorted coordinates with
\[
 a_i\ge b_i\ge0,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_1.
\tag{1}
\]
Take
\[
 t,u,e\ge0,\qquad \alpha=t+u+e\le\frac{27}{100},
 \qquad r=t+e\le\frac3{200},
\tag{2}
\]
and suppose
\[
\begin{aligned}
 b_H+a_A\cos u-b_A\sin u&\ge1+W(u),\\
 b_A+b_B&\ge1,\qquad b_B\ge\frac12,\\
 (\sec e)b_D+a_B\cos t-b_B\sin t
   &\ge W(t)+\frac12+\frac12\sec e+K\tan e,\\
 a_D+b_E&\ge1,\\
 a_H+a_E\sin\alpha-b_E\cos\alpha&\ge W(\alpha).
\end{aligned}
\tag{3}
\]

Then
\[
                         q\ge q_*.
\tag{4}
\]
At equality, `t=e=0`, `u=alpha=t_*`, and the five original
anchors in (1) have exactly the stationary coordinates of
`HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md`.

These are the canonical-side negative TD2 boundary equations.
In reflected variables they are the negative HG0 equations with
`b_A>=1/2`, `epsilon=0` and a nonpositive signed E transverse
coordinate. The small-error input `r<=3/200` is explicit here;
this note does not derive it from the unrestricted negative
branch. The proof applies to the five-anchor necessary system
itself, without assuming it is already a packing or a G0--G2
boundary cycle.

## 2. Reconstruct both discarded intermediates on the true core

It suffices first to consider `q>=q_L`. If `q<q_L`, use the
same anchors with the larger ceiling `q_L`; the conclusion
below contradicts `q_L<q_*`. That strict inequality, together
with `q_*<Q_1`, is the established stationary enclosure.

The circle and sorting bounds give `b_i<9/10` and the original
center-norm bound
\[
 |(a_i,b_i)|<\frac{283}{200}.
\tag{5}
\]
The latter follows from corner containment alone, as proved in
`HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md`; it does not
require a boundary or a core hypothesis.

Set
\[
 a_G=a_T=\frac7{12},\qquad
 b_G=1-b_H,\qquad
 b_T=a_B\cos t-b_B\sin t-W(t).
\tag{6}
\]
The first line of (3) and (5) imply
\[
 \frac1{10}<b_G<\frac{83}{200}.
\]
Multiply the third line of (3) by `cos e`. It gives exactly
\[
 b_D+b_T\cos e-\frac7{12}\sin e\ge W(e).
\tag{7}
\]
Consequently `b_T cos e>=1-b_D>1/10`. Its defining expression
and (5) also give `b_T<83/200`. Thus
\[
                 \frac1{10}<b_G,b_T<\frac{83}{200}<\frac7{12}.
\tag{8}
\]
Both new centers are sorted and on the actual core side: their
distance from the origin to their square is exactly `1/12`.
They lie strictly inside the common containing circle, because
\[
 (a_G+1/2)^2+(b_G+1/2)^2,
 \ (a_T+1/2)^2+(b_T+1/2)^2
 <\frac{169}{144}+\left(\frac{183}{200}\right)^2
 =\frac{723901}{360000}<q_L.
\tag{9}
\]

Use the normal signed tangents
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E)
\]
and the real frames
\[
 \theta_D=\theta_E=0,\quad\theta_T=e,\quad
 \theta_A=\theta_B=r,\quad\theta_H=\theta_G=\alpha.
\tag{10}
\]
Equations (3), (6) and (7) are precisely the weak original signed
SAT inequalities for HG0/2, GA0, AB0/2, BT2, TD2, DE3 and EH1.
HG and BT are equalities in the reconstructed intermediate
coordinates; no A, B, D, E or H coordinate has changed.

The intermediates satisfy all required G/T tangent cuts. Indeed
\[
 \frac1{20}<\frac{6}{35}
 <\frac{b_G}{a_G},\frac{b_T}{a_T}
 <\frac{249}{350}<\frac45.
\tag{11}
\]
In particular the actual free coordinates have
`a_G=a_T=7/12<1.396` and `0<b_G,b_T<.797`.

This construction asserts a feasible necessary neighbor system.
It does not assert new nonneighbor disjointness, physical gaps,
or a G1 marker theorem. None of those assertions is used below.

## 3. The positive tilt tails are excluded directly by the circle identity

The exact force-and-corner identity in Section 2 of
`HAND_OWNER_GAUGE_POSITIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`
uses only the seven signed separation inequalities and the five
anchor circle bounds. Therefore it applies directly to (6)--(10).
Its error variables and actual DE-owner tilt here are
\[
 x_1=0,\quad x_2=-t,\quad x_3=-e,\quad x_4=0,\quad h=0,
 \qquad \tau=\alpha,\qquad S=r.
\tag{12}
\]
The mixed-angle branches used by that identity are nonnegative:
the GA angle is `u=alpha-r` and the EH angle is alpha. On the
straight error segment from zero to (12), the GA angle lies
between u and alpha, so the same smooth width expression remains
valid, including u zero.

If alpha were zero, then `t=u=e=0`. The first and third lines
of (3) give `b_H+a_A>=2` and `a_B+b_D>=2`. The shared-cap bound
in `HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md`, which uses only
these two inequalities, AB and the circle bounds, gives
`a_H+a_D<2`. The last two inequalities of (3) give the contrary
sum `a_H+a_D>=2`. Thus alpha is positive. It follows that
\[
                  0<\sin\tau<\frac3{10}.
\tag{13}
\]

Use the explicit weights and circle masses in Section 3 of the
positive-tilt note. Its Sections 4--6 require only (13),
`S<=3/200`, the coordinate bounds following (11), and the exact
identity already verified. Their hypotheses do not include a
physical-gap or common-marker condition. They prove that the
necessary demand-minus-circle scalar is positive on either
complete tail `sin(tau)<=1/10` or `sin(tau)>=79/500`, which
contradicts the same scalar's necessary nonpositivity. Hence
\[
                         \frac1{10}<\alpha<\frac4{25}.
\tag{14}
\]
This invocation uses the printed identity and its analytic
estimates directly. It does not infer G0--G2 membership for the
auxiliary system from the title or scope of an earlier assembly.

## 4. Complete the five unchanged anchor circles

Now use the stationary weights at
`(q_*,u(q_*,alpha),alpha)`. The proof of
`HAND_OWNER_GAUGE_SHARP_TERMINAL_AT_THREE_TWO_HUNDREDTHS.md`
again uses the same force identity, the primitive bounds in
(11), (14), `S<=3/200`, and the five circle inequalities.
Its stationary flux estimates and its error remainder apply
without any G1 input. In its notation, they give
\[
 q\ge q_*+\mu_H M(q_*,\alpha)
 +\sum_{i=A,B,D,E,H}\mu_i
       \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
 +\frac{r}{5000}\ge q_*.
\tag{15}
\]
Every circle mass is positive, and the stationary theorem gives
`M(q_*,alpha)>=0` with equality only at `alpha=t_*`.
This proves (4), including the earlier `q<q_L` contradiction.

At `q=q_*`, (15) forces `r=0`, so `t=e=0`. It fixes the
stationary tilt and all five anchors in (1). They are the
original anchors of this five-anchor input, not centers
identified with a moved descendant. The reconstructed G and T
are used only to evaluate an algebraic identity; no assertion
about equality of those auxiliary intermediates with discarded
original squares is needed.

The proof retains each actual anchor circle bound throughout.
Thus any strict A/B or E circle loss inherited from a preceding
reduction is also incompatible with equality in (15).
