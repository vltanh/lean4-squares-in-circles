# A low upper central floor forces lower central originals downward

November 2, 2026. Computer-assisted discovery, complete exact rational
replay, and the physical hand reduction below. No Lean, Lake, or CI.

## 1. Two original-square conclusions

Retain four original physical unit squares A,B,C,D in horizontal
center-cone order in the closed Q-disk, Q=1105/256. Their outer links
A--B and C--D are actual projection comparisons; the middle may be
actual or weak. Let F,G be two further distinct original squares with

\[
 |x_F|,|x_G|\le l=29/60,\qquad
 y_F>\max(y_B,y_C),\qquad y_G<\min(y_B,y_C).
\]

Suppose the upper original has low whole floor:

\[
                         y_F-h_F\le1/10.             \tag{1}
\]

**General conclusion.** Every such lower original satisfies

\[
                              y_G<-3/5.              \tag{2}
\]

**Same-half-plane conclusion.** If F and G have x coordinates in the
same closed horizontal half-plane, then

\[
                            y_G+h_G<-9/20.           \tag{3}
\]

Neither theorem uses a selected outsider chain or an occupancy count.
All original independent orientations and all physical owner choices
are retained. These are six-original lemmas, not a whole nine-square
mask closure.

## 2. Retain a strict horizontal clearance margin

Put \(\delta=331/20000\) and \(r_*=3/2+\delta\).
For any original unit with center distance r, its farthest corner has
squared norm at least \(r^2+r+1/2\): the sum of the absolute center
projections on its two original side axes is at least r. Therefore

\[
 |c|\le\sqrt{Q-1/4}-1/2<r_*.
\]

The final strict rational comparison has squared reserve

\[
                 (2+\delta)^2-(Q-1/4)
                       =27061/400000000>0.           \tag{4}
\]

For M=B,C put \(g_M=1/(4h_M)\), \(\eta_M=h_M+g_M-1\),
and \(V=\eta_B+\eta_C\). The outer-actual main theorem gives
\(1/2\le h_B,h_C<13/20\) and \(V<1/30\).
Using r* instead of 91/60 in its main-position argument yields

\[
 b_-=h_B-1-\delta<x_B<\delta-g_B-\eta_C=b_+,
\]

\[
 c_-=g_C+\eta_B-\delta<x_C<1+\delta-h_C=c_+.
                                                        \tag{5}
\]

Every central/main horizontal gap, including the closed endpoint
relaxation in (5), is at most

\[
                   l+(1+\delta)-1/2
                     =1-7/60000<1.                  \tag{6}
\]

The explicit margin in (6) is necessary at aligned frames; replacing it
by an unqualified gap at most one would admit an irrelevant horizontal
separator at an artificial endpoint of the relaxed root.

## 3. A correlated path through each original main

Use the full original-pair clearance function K defined and proved in
Section 3 of `WEAK_MIDDLE_UPPER_CENTRAL_PAIR_REPLACEMENT_HAND_PROOF.md`.
It keeps the minimum over all four physical owners and the smaller
support sum over both possible chirality relations. An original pair
with horizontal gap at most D has absolute vertical gap at least K.

For fixed original frames, each
\(K(M,S,|x_S-z|)\) is concave as a function of the main coordinate z
on the present intervals: (6) keeps all finite owner numerators positive,
and every zero vertical-component owner is impossible. Thus the sum of
two such functions has its minimum at a main-interval endpoint.

Define the two correlated sums

\[
 T_B=\min_{z\in\{b_-,b_+\}}
       [K(B,F,|x_F-z|)+K(B,G,|x_G-z|)],
\]

\[
 T_C=\min_{z\in\{c_-,c_+\}}
       [K(C,F,|x_F-z|)+K(C,G,|x_G-z|)].                \tag{7}
\]

The two terms in each sum use the same original main position. Because
F is above and G below that main, their actual height difference obeys

\[
                          y_F-y_G\ge T_B,T_C.        \tag{8}
\]

It is unnecessary to choose favorable main positions independently
for the two pairs; (7) preserves the needed correlation.

## 4. The original middle physical pair supplies a third path

For S=F,G let

\[
 B_S=K\left(B,S,\max_{z\in\{b_-,b_+\}}|x_S-z|\right),
\quad
 C_S=K\left(C,S,\max_{z\in\{c_-,c_+\}}|x_S-z|\right),
\]

and put \(M=K(B,C,c_+-b_-)\). Monotonicity of K in its horizontal
gap argument makes all five quantities valid original-pair lower bounds.

If C is higher than B, follow the original vertical path F,C,B,G.
If B is higher, follow F,B,C,G. Both possible height orders give

\[
 y_F-y_G\ge M+\min(C_F+B_G,B_F+C_G).                  \tag{9}
\]

Set

\[
 T=\max\{T_B,T_C,M+\min(C_F+B_G,B_F+C_G)\},
\quad Z=T-h_F-1/10.
\]

Equations (1), (8), and (9) imply the single necessary inequality

\[
                                  -y_G\ge Z.         \tag{10}
\]

No original frame is changed by reflecting the heights in (10); K had
already included both chiralities and normal signs.

## 5. The two complete exact tables

Reflect horizontally so xF>=0. Fold the F,G original frames using
\(t=\beta/\alpha\in[0,1]\), with
\(\alpha=1/\sqrt{1+t^2}\), \(\beta=t\alpha\).
The six parameters are \((h_B,h_C,t_F,t_G,x_F,x_G)\).

For (2) the closed root is

\[
 [1/2,13/20]^2\times[0,1]^2\times[0,l]\times[-l,l].
\]

For (3), the same-half-plane hypothesis and reflection change only the
last interval to [0,l]. The two complete binary midpoint trees have
the following exact replay results:

| Conclusion at non-budget leaves | Leaves | Nodes | Maximum depth | Budget leaves |
|---|---:|---:|---:|---:|
| Z>3/5 | 4,029 | 8,057 | 62 | 12 |
| Z-hG>9/20 | 8,278 | 16,555 | 19 | 79 |

Each budget leaf has V>1/30 and is impossible in the original domain.
Every other leaf proves the stated strict bound. The least exact
reserves are, respectively,

\[
 \frac{848421225106421}{23058430092136939520}>0,
\qquad
 \frac{5997044552684051}{92233720368547758080}>0.
\]

The certificates are `wide_lower_height_candidate.json` and
`wide_own_lower_floor_candidate.json`, with SHA256 values

`fb7c85683cd187d62a11ba3595f7bd4c908d3b484737b9f6a89082244daf5f22`

and

`1315576b59f780891595d9c3c672fd596a97579f895e2881f47f026d339f3588`.

`verify_wide_lower_height.py` independently reconstructs (5)--(10)
using the separately reviewed original-pair integer evaluator. No
producer or exploratory code is imported. The checker uses exact
rational root and bisection endpoints, 64-bit outward integer enclosures,
and integer square roots. It verifies the strict gap reserve (6), all
tree children, every leaf, and the empty frontier. All eight changed-root,
illegal-axis, missing-child, and false-terminal controls were rejected.

Together with (10), the first exact table proves (2); the second proves
(3). Their proofs include every boundary of their closed roots.

## 6. Consequences when two lower central originals remain

Suppose G,H are two distinct lower central originals opposite a low-floor
upper F. By (2), their vertically reflected centers are both above 3/5.
The accepted upper-column theorem forces their horizontal gap above l,
so they have opposite strict horizontal signs. Neither can be at zero.
After making xF>=0, label xG<0<xH and write YG=-yG, YH=-yH.

By (3), \(Y_H-h_H>9/20\). The accepted stronger ordered form of
`TWO_SQUARE_CENTRAL_STRIP_CAP_HAND_PROOF.md` says that an original
strip square with whole floor at least 9/20 cannot have another strip
square with center at least as high. Consequently

\[
                       Y_H>Y_G,\qquad Y_G-h_G<9/20.  \tag{11}
\]

The second inequality follows because otherwise G would itself forbid
the higher original H. These conclusions route both remaining original
units and fix their height order; they do not yet exclude the entire
configuration. The wider-frame singleton remainder is a separate gate.
