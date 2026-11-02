# Vertical center clearance from the nearer inner square of an actual four-chain

November 2, 2026. Hand proof. No coordinate cover, orientation restriction
on outsiders, numerical search, mathematical scripts, Lean, or CI are used.

Let physical unit squares lie in the closed disk of squared radius
\(Q=1105/256\), and suppose four of them form the actual horizontal chain

\[
 M_0<_xM_1<_xM_2<_xM_3.
\]

Write \(h_i\) for a main square's projection halfwidth and
\(g_i=1/(4h_i)\) for its inscribed aligned-square halfwidth. Let
\(\rho=91/60\).

## 1. A disk-versus-inscribed-square clearance

If a physical unit square F is interior-disjoint from a square containing
the aligned square of halfwidth g centered at \((x_M,y_M)\), put

\[
 D=|x_F-x_M|,\qquad V=|y_F-y_M|.
\]

The open radius-1/2 disk centered at F lies in its interior. Consequently
its center has distance at least \(1/2\) from the open aligned square.
If \(0<\varepsilon<1/2\) and \(D-g<\varepsilon\), this implies

\[
 V\ge g+\sqrt{\frac14-\max(D-g,0)^2}
 >g+\sqrt{\frac14-\varepsilon^2}.
 \tag{1}
\]

Indeed, \(V\le g\) would give distance less than \(\varepsilon<1/2\),
and otherwise the squared distance is
\(\max(D-g,0)^2+(V-g)^2\). The strict inequality in (1) also holds when
\(D\le g\), because then the first lower bound is \(g+1/2\).

This uses genuine physical disjointness; it supplies a vertical center
clearance without asserting separation of the full vertical projections.

## 2. The whole right and left half-planes

The actual four-chain and \(|c_i|<\rho\) give

\[
 \frac12\le h_2<\frac{31}{60},\qquad
 h_2-\frac1{60}<x_2<\frac{61}{60}-h_2,
 \qquad g_2>\frac{15}{31}.
 \tag{2}
\]

For example, the lower x bound follows by adding the two projection
gaps from \(M_0\) to \(M_2\), and using \(x_0>-\rho\),
\(h_0\ge1/2\), \(2h_1\ge1\). The upper bound follows from
\(M_2<_xM_3\) and \(x_3<\rho\), \(h_3\ge1/2\). Their compatibility
forces \(h_2<31/60\). Reflection gives the corresponding statements
for \(M_1\).

Every outsider F has \(|x_F|<13/12\), by
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.
Suppose \(x_F\ge0\). From (2),

\[
 D=|x_F-x_2|<
 \max\left\{\frac{61}{60}-h_2,\frac{13}{12}-h_2+\frac1{60}\right\}
 =\frac{11}{10}-h_2.
\]

Since \(h_2+g_2\ge1\), this gives \(D-g_2<1/10\). Apply (1):

\[
 |y_F-y_2|>
 \frac{15}{31}+\frac{\sqrt6}{5}>
 \frac{97}{100}.
 \tag{3}
\]

For the final rational comparison, use \(\sqrt6>61/25\), justified by
\(3750>3721\). Then

\[
 \frac{15}{31}+\frac{61}{125}-\frac{97}{100}
 =\frac{29}{15500}>0.
\]

Thus every outsider in \(x\ge0\) lies strictly above
\(y_2+97/100\), or strictly below \(y_2-97/100\). Reflection gives

\[
 x_F\le0\quad\Longrightarrow\quad
 |y_F-y_1|>\frac{97}{100}.
 \tag{4}
\]

Both bounds apply to an outsider with \(x_F=0\).

## 3. A stronger clearance for the middle outsiders

Suppose \(0\le x_F<29/60\). Equation (2) puts \(x_2>29/60\), and
therefore

\[
 D=x_2-x_F<\frac{61}{60}-h_2,
 \qquad D-g_2<\frac1{60}.
\]

Applying (1) again gives

\[
 |y_F-y_2|>
 \frac{15}{31}+\frac{\sqrt{899}}{60}>
 \frac{59}{60}.
 \tag{5}
\]

The last comparison is equivalent to \(\sqrt{899}>929/31\), and
its squared reserve is

\[
 899\cdot31^2-929^2=898>0.
\]

For \(-29/60<x_F\le0\), the reflected inequality is
\(|y_F-y_1|>59/60\). Again an outsider on the central line satisfies
both bounds.

## 4. Consequences when both inner centers are low

Assign each outsider in the right half-plane to \(M_2\), and each in the
left half-plane to \(M_1\); choose either assignment on \(x=0\).
Call it lower if its y-center is below the corresponding inner center,
and upper otherwise. Equations (3)--(4) give a strict gap, so this is an
exhaustive classification.

If

\[
 y_1,y_2\le-\frac25,
\]

every lower outsider has

\[
 y_F<-\frac25-\frac{97}{100}=-\frac{137}{100}.
\]

The sharp two-square directional cap in
`TWO_SQUARE_SHARP_CAP_HAND_PROOF.md` gives
\(\min(-y_F,-y_G)\le H<109/80<137/100\) for two physical units.
Hence there is **at most one lower outsider**.

If the stronger inequalities \(y_1,y_2\le-11/20\) hold, there is no
lower outsider at all: (3)--(4) would give

\[
 y_F<-\frac{11}{20}-\frac{97}{100}=-\frac{38}{25}< -\rho,
\]

contrary to the center-radius bound.

These are joint constraints on the five outsiders, not a bound on the
number of upper outsiders by itself. For example, the eight aligned units
at centers

\[
 (-3/2,0),\ (-1/2,-1),\ (1/2,-1),\ (3/2,0),\qquad
 (-1/2,0),\ (1/2,0),\ (-1/2,1),\ (1/2,1)
\]

form an actual four-chain together with four upper outsiders and fit the
disk of squared radius \(17/4<Q\). Their coordinate intervals directly
verify interior-disjointness. Thus a proof of the full nine-square
capacity must retain the remaining outsider and the joint vertical
constraints.
