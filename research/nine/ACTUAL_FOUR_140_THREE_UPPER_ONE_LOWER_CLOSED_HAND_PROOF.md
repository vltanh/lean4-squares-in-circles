# Complete normalized (1,4,0) closure with three upper central units

November 2, 2026. Complete original-nine hand caller with one new exact
317-row input. Numerical direction checks preceded the new scalar work;
all final comparisons have exact arithmetic replays. No Lean or CI.

Put \(Q=1105/256\), \(l=29/60\), \(u=13/12\),
\(\rho=91/60\).

## 1. Exact normalized scope

Work in the closed-disjoint normalization of an original strict
counterexample with an actual horizontal main four-chain whose centers
also form a horizontal cone chain. Its adjusted original endpoint span is

\[
                      D=x_3-x_0-h_0-h_3>2.
\tag{1}
\]

Classify the outsider columns at these normalized positions. Suppose the
count is \((L,C,R)=(1,4,0)\), and retain the designated outsider cone
three-chain \(L<_cP<_cR\). The common cone routing places L at the sole
left-side outsider and P,R among the central outsiders. Reflect vertically
so P is above both inner mains. Then L is above its own inner main and R
is above both inner mains. The selected R is central, so
`ACTUAL_FOUR_CONE_THREE_COMMON_ROUTING.md` gives

\[
 -u<x_L<-11/12,\qquad y_L>27/40,
 \qquad -23/60<x_P<0<x_R\le l.
\tag{2}
\]

The second cone gap is at least \(g_P+g_R\ge1/\sqrt2>7/10\).
Consequently

\[
                           x_P<-13/60.
\tag{3}
\]

Assume exactly three of the four original central outsiders are above
both inner mains, and the fourth G is below both. Thus P,R and one other
central unit A are the three upper originals. Their orientations and all
original pair constraints remain unrestricted.

This manuscript closes that complete normalized height alternative. It
does not assert that common expansion preserves an unnormalized (1,4,0)
count; classification here takes place after normalization. Horizontal
reflection covers (0,4,1), and vertical reflection covers the corresponding
one-upper/three-lower central alternative.

## 2. Exactly two upper central units are high

`TWO_LOW_MAINS_23_60_AND_OPPOSITE_LOW_CENTRALS.md` applies with the original
lower central G. It proves that at most one upper central unit can have
center height below three fifths. Thus at least two of P,R,A have center
heights at least three fifths.

The upper-column separation theorem says that any two such high units have
horizontal center gap strictly greater than l. There cannot be three:
ordering their x-coordinates would give total span greater than 2l inside
\([-l,l]\). Therefore exactly two are high and one is low. The two high
central units have opposite strict horizontal signs, since either closed
half of the central strip has width l.

Write Hminus,Hplus for the negative and positive high central units, and
B for the unique low central. If \(x_B\le0\), the horizontal center
gap from B to Hminus is at most l<1/2. The accepted half-width replacement
theorem applies to these two original upper central units. Since Hminus
has the higher center, it gives

\[
                         y_{Hminus}-h_{Hminus}
                                  >2807/24000>1/10.
\tag{4}
\]

The original high side unit L, central U=Hminus, and positive shoulder
V=Hplus satisfy the widened five-square cap's complete hypotheses. Together
with the original endpoints, it gives D<=2, contradicting (1).

It remains only that \(x_B>0\). In that case the selected negative P
must itself be high: the unique low unit has positive x. We next prove its
whole floor directly from the actual far-left original L.

## 3. A high selected middle unit has whole floor above one tenth

The following two-original-disk argument is useful independently. Retain
physical unit squares L,P satisfying (2)--(3), with \(y_P\ge3/5\).
Then

\[
                              y_P-h_P>1/10.
\tag{5}
\]

Suppose instead that this floor is at most one tenth. Since
\(h_P\le1/\sqrt2<17/24\), its center height is less than
\(97/120\). Write

\[
                 s=-x_L\in[11/12,13/12],
                 \qquad p=-x_P\in[13/60,23/60].
\]

Their horizontal gap is positive and at most \(s-13/60\).

If \(y_L\le y_P\), then (2) gives vertical center gap less than
\(97/120-27/40=2/15\), while the horizontal gap is less than 13/15.
Their squared center distance is therefore less than

\[
                          (13/15)^2+(2/15)^2
                               =173/225<1.
\tag{6}
\]

Suppose instead \(y_L\ge y_P\). The universal original-unit center
bound gives \(y_L<\sqrt{\rho^2-s^2}\), and \(y_P\ge3/5\).
Their squared center distance is consequently bounded above by

\[
 f(s)=(s-13/60)^2+
              (\sqrt{\rho^2-s^2}-3/5)^2.
\tag{7}
\]

The replacements increase both nonnegative coordinate differences.
Expansion gives

\[
 f(s)=\rho^2+(13/60)^2+9/25
        -(13/30)s-(6/5)\sqrt{\rho^2-s^2}.
\]

The square root is concave on the interval; hence f is convex. Its maximum
is attained at one of the two interval endpoints. At the left endpoint,

\[
 \rho^2-(11/12)^2=73/50<(49/40)^2,
\]

so

\[
 f(11/12)<(7/10)^2+(5/8)^2=1-191/1600<1.
\tag{8}
\]

At the right endpoint,

\[
 \rho^2-(13/12)^2=169/150<(17/16)^2,
\]

and therefore

\[
 f(13/12)<(13/15)^2+(37/80)^2=1-403/11520<1.
\tag{9}
\]

Both possible vertical orders of L,P thus give center distance less than
one. Their original contained open radius-one-half disks would overlap,
contradicting physical disjointness. This proves (5). No frame, contact,
separator owner, or extra cone edge was assumed in this two-unit argument.

## 4. Completion of the remaining horizontal sign case

When the unique low upper central B has positive x, Section 2 gave
\(y_P\ge3/5\). Section 3 applies to the original selected L,P and
proves P's whole floor above one tenth. The positive high central unit
Hplus is distinct from P and from L. Thus the three original units

\[
                             L,\qquad U=P,\qquad V=Hplus
\]

meet the widened cap's predicates: L and V have opposite horizontal signs
and centers at least three fifths high, U is central with whole floor above
one tenth, and the original endpoints supply their actual-four bounds.
The cap again gives D<=2, contradicting (1).

The cases \(x_B\le0\) and \(x_B>0\) are exhaustive, including x=0.
All four central units have a stated role: the original lower G forces the
at-most-one-low theorem; the low upper B either forces the negative high
unit's replacement floor or forces the selected P to be high; the high
central units supply the remaining cap members. The original sole side
L supplies its actual endpoint-derived high center and, when needed, the
whole-floor contradiction (6)--(9). No original unit is omitted from the
caller logic or replaced by an independently selected frame.

## 5. Verification and scope boundary

`verify_140_three_upper_arithmetic.py` checks all new rational comparisons,
including both low-central disk reserves, the far-side arc endpoints,
the square-root comparison reserves, and the final threshold arithmetic.
Its output is `140_three_upper_arithmetic_replay.json`. The new main-height
input has the complete 317-leaf cover and independent replay named in
`TWO_LOW_MAINS_23_60_AND_OPPOSITE_LOW_CENTRALS.md`.

The common cone routing, upper-column theorem, half-width replacement,
and widened five-square cap are separate complete inputs. This proof
retains their full original-square hypotheses. It closes the normalized
(1,4,0) three-upper/one-lower central family and the stated reflections;
other central height patterns and outsider counts remain separate callers.
