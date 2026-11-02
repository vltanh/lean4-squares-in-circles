# The outer part of the central band supplies the missing whole floor

November 2, 2026 UTC. Complete hand derivation. No mathematical
program, numerical evaluation, Lean, Lake, or CI is used.

Retain the equal-top-marker(2,1,2) configuration and notation of
`EQUAL_EXTREME_ZERO_BAND_AND_CENTRAL_FLOOR_SUBCASE_HAND_PROOF.md`.
The physical central outsider F is below both zero-marker outsiders.
Let U be the zero unit on F's own side, with either choice allowed
when x_F=0.

We prove the additional whole-floor implication
\[
          |x_F|\ge5/12\quad\Longrightarrow\quad y_F+h_F<-7/60.
                                                               \tag{1}
\]
Thus a failure of the desired whole-floor caller forces not just a
positive same-side zero unit, but also |x_F|<5/12. Reflection gives
the corresponding equal-bottom-marker statement.

## 1. A physical proxy clearance retaining the lower square's orientation

Let a centered aligned square of halfwidth g and a physical unit F
be interior-disjoint. Suppose F's center is below the proxy center,
with positive vertical gap V and horizontal gap D<g. Write
\[
 \alpha\ge\beta\ge0,\quad\alpha^2+\beta^2=1,
 \quad h_F=(\alpha+\beta)/2,
 \quad k_F=(\alpha-\beta)/2,
 \quad\delta=g-D>0.
\]
The horizontal coordinate axis cannot separate the two squares,
since D<g<g+h_F. The vertical axis, if separating, gives V>=g+h_F.
If a physical side axis of F separates them, choose the more favorable
signs of its two components. Its separating inequality necessarily gives
\[
 V\ge g+\frac{1/2+\delta |n_x|}{|n_y|}.
\]
A zero vertical component is impossible. Of the two possible component
orders, the smaller expression is (1/2+delta beta)/alpha: for beta>0
the difference of the other expression has numerator
(alpha-beta)[1/2+delta(alpha+beta)]>=0. If beta=0, only the
coordinate vertical axis remains. Thus in every case
\[
 V\ge g+\min\{h_F,(1/2+\delta\beta)/\alpha\}.          \tag{2}
\]

Let v=beta/alpha, so0<=v<=1. The possible whole-top loss relative
to the proxy's bottom satisfies
\[
\begin{aligned}
 h_F-\min\{h_F,(1/2+\delta\beta)/\alpha\}
 &=\max\{0,v(k_F-\delta)\}\\
 &\le\max\{0,v(1/2-\delta)-v^2/2\},                  \tag{3}
\end{aligned}
\]
because k_F=alpha(1-v)/2<=(1-v)/2. If delta>=21/80,
completing the square in (3) gives the uniform bound
\[
                h_F-\min\{h_F,(1/2+\delta\beta)/\alpha\}
                            \le361/12800.              \tag{4}
\]
Indeed the maximum of (19/80)v-v^2/2 is (19/80)^2/2.
This argument uses every physical separating-axis alternative and
does not replace physical separation by a vertical comparison.

## 2. Apply the clearance to the same-side zero unit

If y_U<=1/120, the earlier whole-floor theorem already gives (1).
Suppose y_U>1/120. The proved positive-zero orientation bound then
gives h_U<5/8, and hence its contained aligned proxy has
\[
                              g_U>2/5.
\]
Assume |x_F|>=5/12. The previous center bands give
|x_F|<29/60<=|x_U|<2211/4000, and U is on the same side. Thus
\[
 D=|x_U-x_F|<\frac{2211}{4000}-\frac5{12}
                         =\frac{1633}{12000},
\]
\[
 \delta=g_U-D>\frac25-\frac{1633}{12000}
                =\frac{3167}{12000}>\frac{21}{80}.     \tag{5}
\]
The final comparison has reserve17/12000. In particular D<g_U,
so Section1 applies to the proxy contained in U and the lower unit F.
Their interior disjointness follows from physical disjointness of U,F.

The earlier whole-zero-top bound is y_U+h_U<41/48, while
h_U+g_U>=1. Equations (2),(4) consequently give
\[
\begin{aligned}
 y_F+h_F
 &\le y_U-g_U+361/12800\\
 &<\frac{41}{48}-(h_U+g_U)+\frac{361}{12800}\\
 &\le-\frac7{48}+\frac{361}{12800}
   =-\frac7{60}-\frac{37}{38400}<-\frac7{60}.          \tag{6}
\end{aligned}
\]
The exact positive final reserve proves (1).

## 3. What the remaining central-floor domain must satisfy

If the whole top y_F+h_F<-7/60 has not been established by either
this note or the earlier same-side-zero threshold, a counterexample
to that top bound must satisfy
\[
 |x_F|<5/12,\qquad y_U>1/120,\qquad h_U<5/8,
 \qquad y_U+h_U<41/48.
\]
All previous physical constraints and the other zero unit remain.
At x_F=0, both choices of U are possible, so both must satisfy the
positive-height condition if the whole-top bound fails.

The configurations covered by (1) now have the required central
whole floor after vertical reflection. Their matched endpoint
separators must still be in a proved class before invoking the union
terminal. The remaining central band is not declared excluded, and
no unrestricted lower bound or canonical root closure follows here.
