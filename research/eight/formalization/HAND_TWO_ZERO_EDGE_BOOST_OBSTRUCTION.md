# The common G1 marker does not exclude a two-zero-edge path

**Status.** This is an exact counterexample to one proposed local
strengthening of G1. It includes a shared middle square, the actual
secondary separator owners, and the compulsory frame-return charge.
It does not construct a seven-square packing or refute a whole-cycle
wrong-word inequality.

The proposed inequality was

\[
 \phi_0+\phi_1+\ell_0-\ell_2
 +\frac9{50}h(|\theta_2-\theta_0|)
 >2\pi-5\frac{8833}{10000},                         \tag{1}
\]

on a path with two zero quarter increments, where

\[
 h(x)=\frac{\sin x+\cos x-1}{2}.
\]

Here the \(\ell_i\) are the unchanged common G1 markers in
[the zero-primary exclusion](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md).
Equation (1) would combine with the five other G1 edges to exclude
either residual wrong word. The example below satisfies the complete
local geometric hypotheses and has left side less than \(46/25\),
whereas the right side exceeds \(3727/2000>46/25\).

All terminating decimals below denote exact rational numbers.

## 1. Three exact outer-boundary squares

Put

\[
 \begin{gathered}
 Q=\frac{9789}{2500},\qquad
 A=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{\frac Q2}-\frac12,\\
 d=2\arctan\frac1{10},\qquad
 c=\cos d=\frac{99}{101},\qquad
 s=\sin d=\frac{20}{101},\\
 W=\frac{1+c+s}{2}=\frac{110}{101},\qquad
 b=W-As=\frac{110-20A}{101},\\
 a=\sqrt{Q-(b+\frac12)^2}-\frac12.
 \end{gathered}                                      \tag{2}
\]

Let \(R(\theta)\) denote rotation by \(\theta\). Choose frames and
actual square centers

\[
 \begin{array}{c|c|c}
 i&\theta_i&p_i\\ \hline
 0&-d&R(-d)(a,-b)\\
 1&0&(A,0)\\
 2&d&R(d)(a,b).
 \end{array}                                         \tag{3}
\]

Each square has side length one and the frame shown in (3).
In particular all three frame matrices have rational entries.

The following deliberately coarse bounds follow by squaring:

\[
 \begin{gathered}
 1.4145<A<1.4146,\qquad
 .8089<b<.8091,\qquad .9838<a<.9841,\\
 .8992<c_0<.8993.
 \end{gathered}                                      \tag{4}
\]

For explicit radical checks,

\[
 \begin{aligned}
 Q-\tfrac14-(1.9145)^2&=\frac{1159}{4000000}>0,\\
 (1.9146)^2-Q+\tfrac14&=\frac{2329}{25000000}>0.
 \end{aligned}
\]

The two resulting endpoints for \(b\) are

\[
 \frac{20427}{25250}<b<\frac{8171}{10100},
\]

which imply the bounds in (4). The bounds for \(a\) follow from

\[
 \begin{aligned}
 Q-(1.3091)^2-(1.4838)^2&=\frac{779}{4000000}>0,\\
 (1.4841)^2+(1.3089)^2-Q&=\frac{8601}{50000000}>0.
 \end{aligned}
\]

Finally the corresponding two comparisons for \(c_0\) are

\[
 Q/2-(1.3992)^2=\frac{123}{3125000}>0,\qquad
 (1.3993)^2-Q/2=\frac{24049}{100000000}>0.
 \]

Thus \(0<b<a\), and all three canonical states are valid outer
states. Their farthest-corner squared norms are exactly \(Q\).
They avoid the open radius-\(1/12\) core, since their canonical
primary coordinates exceed \(.9838>7/12\).

## 2. The original separators and quarter increments

Let \(f_i=R(\theta_i)(0,1)\). The first pair is separated on the
positive secondary axis of square 0:

\[
 (p_1-p_0)\mathbin\cdot f_0=As+b=W.                 \tag{5}
\]

The second pair is separated on the positive secondary axis of
square 2:

\[
 (p_2-p_1)\mathbin\cdot f_2=As+b=W.                 \tag{6}
\]

In both cases \(W\) is exactly the sum of the two square support
widths in the chosen direction. Hence (5)--(6) are true separating
axes, with disjoint interiors and boundary contact. In the
zero-based original-axis convention these witnesses are respectively
0 and 2.

To check the contact itself, the middle square's lower supporting
corner, expressed in square 0's frame relative to its center, has
normal coordinate \(1/2\) and tangential coordinate
\[
 Ac-a-\frac{c-s}{2}.
\]
The bounds (4) place the latter strictly between
\(5707/505000>.0113\) and \(1477/126250<.0117\).
It therefore lies in the interior of the supporting side. Reflection
gives the second actual contact.

Neither consecutive pair has a primary separator. For the first
pair the projections on both positive primary axes are positive,
and their margins are

\[
 A-ac+bs-W,\qquad Ac-a-W.
\]

Using (4) and the exact \(c,s,W\) in (2) bounds them respectively
above by \(-.47\) and \(-.68\). For the second bound the exact
upper substitution is \(-43324/63125<-.68\). The opposite
signed margins are negative because both projections are positive.
Reflection gives the same two
negative margins for the second pair. Thus the example respects
the unconditional zero-primary exclusion.

The two endpoint squares are also disjoint: their centers have
vertical separation

\[
 2(as+bc)>2(.8089)\frac{99}{101}>
 \frac{119}{101}=c+s,
\]

and \(c+s\) is the sum of their vertical support widths.

The canonical signs of the endpoints are \(+\) and \(-\).
The middle transverse coordinate is zero, so its sign is immaterial.
The actual center-angle lifts are

\[
 -d-\arctan(b/a),\quad 0,\quad d+\arctan(b/a).
\]

Their nearest-primary-axis lifts have quarter indices \(0,0,0\);
therefore both increments are zero and

\[
 \phi_0=\phi_1=d,\qquad
 |\theta_2-\theta_0|=2d<\frac25<\frac7{10}.          \tag{7}
\]

Each of the two consecutive physical center gaps is greater than
\(19/25\). Indeed \(b/a>4/5\), while

\[
 d=2\arctan(1/10)>
 2\left(\frac1{10}-\frac1{3000}\right)>\frac{19}{100}
\]

and

\[
 \arctan(b/a)>\arctan(4/5)>
 \frac45-\frac{(4/5)^3}{3}=\frac{236}{375}.
\]

Their sum exceeds \(19/25\). All local hypotheses of the G1
pair theorem therefore hold on both edges, with the same actual
middle state.

## 3. The common marker and the exact failed inequality

The middle state is the axial endpoint of the L chart, so its
unsigned G1 marker is exactly zero. The endpoint states satisfy
\(3/7<b/a<1\) and both use the H marker

\[
 F_H(a,b)=\frac\pi4-.569472(a-c_0)+.390886(b-c_0).
\]

Thus

\[
 \ell_0=F_H(a,b),\qquad \ell_1=0,\qquad
 \ell_2=-F_H(a,b).                                  \tag{8}
\]

The frame-return term is exact:

\[
 \sin(2d)=\frac{3960}{10201},\qquad
 \cos(2d)=\frac{9401}{10201},\qquad
 h(2d)=\frac{1580}{10201}.                           \tag{9}
\]

Consequently the proposed left side equals

\[
 \begin{split}
 B={}&4\arctan(1/10)+\frac\pi2
       -1.138944a+.781772b+.357172c_0
       +\frac9{50}\frac{1580}{10201}.                \tag{10}
 \end{split}
\]

Use \(\arctan(1/10)<1/10\), \(\pi<22/7\), and (4).
All signs in the following substitution are explicit:

\[
 \begin{aligned}
 B
 &<\frac25+\frac{11}{7}
     -1.138944(.9838)+.781772(.8091)+.357172(.8993)
     +\frac9{50}\frac{1580}{10201}\\
 &=\frac{163571264115529}{89258750000000}
 <\frac{46}{25}.                                    \tag{11}
 \end{aligned}
\]

The reserve in the final rational comparison is

\[
 \frac{46}{25}
 -\frac{163571264115529}{89258750000000}
 =\frac{664835884471}{89258750000000}>0.
\]

On the other hand \(\pi>157/50\) gives

\[
 2\pi-5\frac{8833}{10000}
 >\frac{3727}{2000}
 =\frac{46}{25}+\frac{47}{2000}.                    \tag{12}
\]

Equations (11)--(12) refute (1). For orientation only, the actual
left side is approximately \(1.830301\); no decimal evaluation of
a trigonometric function or radical is an input to the proof.

## 4. Scope of the obstruction

The local bound (1) fails after retaining the compulsory return cost.
Replacing the five complementary edges by the single universal
G1 lower bound \(8833/10000\) discards too much information for this
approach.

Both residual wrong words may still be excluded by an inequality that
uses additional vertices, their actual type-dependent G1 costs, or a
different common marker justified on the whole domain. The example
does not assert that this local path extends to an admissible seven-cycle.
