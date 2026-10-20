# Global EH owner rigidity from the all-high cycle contradiction

## 1. Statement and original witnesses

Work on the original G0--G2 boundary cycle at
\(q\le Q=9789/2500\), with its established orientation
\(y_E\le0\). Keep every original feasible separating-axis
witness, including ties. Apply the established G0 boundary
reduction once at the working ceiling Q, preserving each
chosen original weak witness; the outer states below are
the resulting Q-boundary representatives. Then
\[
\boxed{\qquad
\text{Every original EH witness has index 0 or 1.}
\qquad}                                                        \tag{1}
\]
Consequently H has strictly positive signed tangent and is
outer. This theorem does not assume a GA owner, the signs
of A or T, any frame order, or a small mismatch bound.

The new point is the following complete exclusion:
\[
\boxed{\quad
\text{The original GA, BT, DE, EH quarter witnesses cannot
all have indices in }\{2,3\}.
\quad}                                                         \tag{2}
\]
Sections 2--3 prove (2) with one common potential around
the actual cycle. Section 4 joins it to the already proved
conditional EH theorem to obtain (1).

## 2. Radial and sign scope of the all-high case

Suppose that each quarter edge has a chosen original high
witness. The global quarter-sign theorem gives
\[
                         y_G,y_B,y_D,y_E<0.          \tag{3}
\]
Every one of these four sources is outer by
[`HAND_G3_EVERY_QUARTER_HAS_AN_OUTER_ANCHOR.md`](HAND_G3_EVERY_QUARTER_HAS_AN_OUTER_ANCHOR.md).
These are the four anchors for the common potential below.

No sign is imposed on H, A, or T. Each is the source of a
zero edge. If its signed tangent is nonpositive, it is outer
by
[`HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md`](HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md).
Otherwise it can be either of its original radial kinds.
Thus each of the three repeated high quarters EH, GA, BT
has a negative outer source and an outer or positive-core
target. Each zero HG, AB, TD has a negative outer target.
These are exactly the hypotheses of the two component
theorems used next.

Let \(a_i,b_i\) be the sorted primary and absolute transverse
coordinates of an outer anchor, and put
\[
\begin{gathered}
c_0=\sqrt{Q/2}-1/2,\qquad
\kappa=103/100,\quad \rho=11/10,\\
J_i=\pi/4-.569472(a_i-c_0)+.390886(b_i-c_0)-F_i,\\
\Pi_i=\kappa a_i+\rho J_i,
\end{gathered}                                                   \tag{4}
\]
where F_i is its unchanged original L, M, or H marker.
Either adjacent marker is allowed at a junction. Assign
one potential to each actual vertex:
\[
\mathcal P_i=
\begin{cases}
\kappa y_i,&i\in\{H,A,T\},\\
\Pi_i,&i\in\{G,B,D,E\}.
\end{cases}                                                     \tag{5}
\]
The potential is not reselected on individual edges.

For an original edge i to j with quarter count k and lifted
frame increment d, its new charge is
\[
                    k\pi/2+d+\mathcal P_i-\mathcal P_j.           \tag{6}
\]
The seven charges sum exactly to 2pi: the quarter word has
four ones, the real increments sum to zero, and (5)
telescopes.

## 3. The exact cyclic reserve

The fully signed and radial quarter theorem in
[`HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md`](HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md)
gives, for each of EH, GA, BT,
\[
                  C_{\rm quarter}\ge\pi/2+\kappa.  \tag{7}
\]
It allows both original high owners and every error sign.

The three-zero theorem in
[`HAND_G3_THREE_ZERO_AUGMENTED_PRIMARY_CHARGE.md`](HAND_G3_THREE_ZERO_AUGMENTED_PRIMARY_CHARGE.md)
gives
\[
 C_{HG}+C_{AB}+C_{TD}>
                    3\kappa(1-2c_0)-7/1000.          \tag{8}
\]
Its possible loss is bounded once for the three zeros
together: the total positive variation is less than 7/10,
so at most one zero can enter its d>7/20 loss range.

The remaining original DE edge has two negative outer
endpoints. Its bridge theorem,
[`HAND_G3_ALL_HIGH_OUTER_BRIDGE_CHARGE.md`](HAND_G3_ALL_HIGH_OUTER_BRIDGE_CHARGE.md),
proves
\[
                  C_{DE}=\pi/2+d_{DE}+\Pi_D-\Pi_E
                                      >957/1000.     \tag{9}
\]
That theorem uses the unchanged six-edge G1 return cap
only as a necessary inequality of the actual cycle. Its
proof covers both original DE owners, every outer chart
pair, and both signs of d_DE.

Sum (7)--(9) using the identity after (6):
\[
\begin{split}
2\pi
&>3\pi/2+3\kappa+3\kappa(1-2c_0)
                       -7/1000+957/1000\\
&=3\pi/2+6\kappa(1-c_0)+19/20.                       \tag{10}
\end{split}
\]
But the defining square identity gives c0<.89922, while
\(\pi<355/113\). Hence
\[
\begin{split}
6\kappa(1-c_0)+\frac{19}{20}-\frac\pi2
&>6\frac{103}{100}\left(1-\frac{44961}{50000}\right)
                    +\frac{19}{20}-\frac{355}{226}\\
&=\frac{571763}{282500000}>0.                        \tag{11}
\end{split}
\]
Equations (10) and (11) contradict each other. This proves
the all-high exclusion (2), strictly below or at the stated
radius, without an equality exception.

## 4. From the exclusion to every original EH witness

Global BT and DE rigidity already restrict every original
witness on those two edges to indices 2 or 3; see
`HAND_G3_GLOBAL_BT_OWNER_RIGIDITY.md` and
`HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md`.

Suppose an original EH witness had index 2 or 3. Choose
any original GA witness. If that GA witness has index 0
or 1, it contradicts
[`HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md`](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md).
If it has index 2 or 3, the chosen GA and EH witnesses,
together with any original BT and DE witnesses, contradict
(2). Every possible original GA witness has been covered.
Therefore no high EH witness exists, proving (1), even
when another low EH witness is simultaneously feasible.

The global quarter-sign theorem now gives y_H>0. Its
outer radial kind follows either from the global
outer-anchor theorem or directly from
`HAND_G3_GLOBAL_LOW_EH_TARGET_IS_OUTER.md`.

The remaining global owner question is GA: (1) does not
exclude a high GA witness paired with low EH. No such
claim is imported into this theorem. Every estimate used
above has a whole-domain analytic proof with exact
rational reserves; no mesh, numerical feasibility result,
Lean build, or CI run is a premise.
