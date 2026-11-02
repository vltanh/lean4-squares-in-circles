# Complete (1,3,1) closure when both side outsiders are above their mains

November 2, 2026. Complete original-nine hand caller. New computer-assisted
inputs have complete 25-row and 112-row exact covers; the additional hand
comparisons have a standard-library Fraction replay. No Lean or CI.

Set

\[
 Q=1105/256,\quad l=29/60,\quad u=13/12,\quad\rho=91/60,
\]

\[
 g_0=15/31,\quad \delta=331/20000,\quad
 A=503/480,\quad c=221/600,\quad f=119/310.
\]

## 1. Complete scope and the common terminal

Work in the closed-disjoint normalization of a strict counterexample with
an actual horizontal main four-chain that is also a center-cone chain.
Retain a designated outsider cone three-chain and all nine original
squares. Classify outsider columns at these normalized positions. Suppose
the count is (1,3,1), the central outsiders consist of two originals F1,F2
above both inner mains and one original G below both, and the two original
side outsiders S,T lie above their own inner mains M1,M2 respectively.
The selected cone chain may have either both side endpoints or one central
endpoint; neither option will be discarded.

The original adjusted endpoint span is

\[
                             D=x_3-x_0-h_0-h_3>2.
\tag{1}
\]

The widened five-square cap contradicts (1) whenever three distinct
original squares L,U,R satisfy

\[
 x_L\le0\le x_R,\quad |x_U|\le l,\quad
 y_L,y_R\ge3/5,\quad y_U-h_U\ge1/10.
\tag{2}
\]

Every branch below extracts these actual original units. A high unit means
one whose center height is at least three fifths; a low unit has center
height strictly below three fifths.

At least one of the two side outsiders is high. Indeed a low side outsider
above its own main has |x|<49/80 by the endpoint disk/zero-band argument
in `LOW_SIDE_UNIT_FORCES_SAME_SIDE_CENTRAL_FLOOR.md`. If both side outsiders
were low, all five outsider center x-coordinates would lie between
-49/80 and 49/80. Their total span would be below 49/40<sqrt(2), whereas
any physical outsider cone three-chain has span at least sqrt(2).
This is impossible.

Also, `TWO_LOW_MAINS_23_60_AND_OPPOSITE_LOW_CENTRALS.md`, using the original
lower G, proves that at most one of F1,F2 is low. Thus at least one of the
two central upper originals is high.

## 2. A high central bad floor must be near the vertical axis

Suppose an original high central unit F has whole floor at most one tenth,
and there is an original high right-side unit T. Then

\[
                              x_F<1/5.
\tag{3}
\]

The reflected statement gives xF>-1/5 in the presence of a high left-side
unit. To prove (3), suppose instead \(1/5\le x_F\le l\). Its center
height satisfies

\[
                           3/5\le y_F<97/120,
\]

since \(h_F\le1/\sqrt2<17/24\). Write (s,z) for T, so
\(l\le s\le u\), \(z\ge3/5\), and \(s^2+z^2<\rho^2\).
If T is below F, their horizontal gap is at most 53/60 and vertical gap
is less than 5/24. The sum of these squared bounds is below one.

If T is above F, their squared center distance is bounded by

\[
                (s-1/5)^2+(\sqrt{\rho^2-s^2}-3/5)^2.
\tag{4}
\]

This function is convex on [l,u]: after expansion its only nonlinear term
is a negative multiple of the concave square root. Its maximum is at an
endpoint. Using

\[
 \sqrt{\rho^2-l^2}<36/25,\qquad
 \sqrt{\rho^2-u^2}<17/16,
\]

its two endpoint values are strictly below

\[
              (17/60)^2+(21/25)^2<1,
 \qquad       (53/60)^2+(37/80)^2<1.
\]

Both vertical orders therefore contradict the original disjoint
radius-one-half disks. This proves (3), including its boundary xF=1/5.

## 3. Both side outsiders are high

The complete one-main theorem
`ONE_LOW_MAIN_NINE_TENTHS_CENTRAL_EXCLUSION.md`, applied to the original
G below each inner main, gives

\[
                            y_1,y_2>-9/10.
\]

The physical central own-half-plane clearance is greater than 59/60.
Consequently both upper central centers are strictly above 1/12.

Suppose neither central upper unit has whole floor above one tenth.
Choose a high one H, which exists by Section 1. Section 2 and its
reflection give |xH|<1/5, since both original side outsiders are high.
The other central unit has |x|<=l. Both bad-floor centers lie strictly
between 1/12 and 97/120. Their squared center distance is therefore below

\[
             (l+1/5)^2+(97/120-1/12)^2
                    =(41/60)^2+(29/40)^2
                    =1-107/14400<1.
\tag{5}
\]

This contradicts their original disks. Thus one central upper unit U has
whole floor above one tenth. The original high S,U,T satisfy (2), and the
widened cap closes this entire branch.

## 4. Exactly one side outsider is low

Reflect horizontally so the low side is the left original S and the high
side is the right original T. We prove that **every** original central
upper unit has whole floor above one tenth.

For a central upper unit with x<=0, this is exactly the accepted low-side
extraction theorem applied to S. It remains to consider an original
central upper F with

\[
                         0<X=x_F\le l,
\]

and suppose for contradiction that its whole floor is at most one tenth.
Write its center height as Y and its folded frame as a>=b>=0,
\(a^2+b^2=1\), \(t=b/a\), \(h=(a+b)/2\), \(k=(a-b)/2\).
Its aligned inset has halfwidth \(g_F=1/(4h)>7/20\).

### 4.1. The opposite main is above minus three fifths

The low side S has |xS|<49/80. Its horizontal center gap from M1 is
therefore below 31/240<g1. Its original radius-one-half disk and the M1
inset give vertical center gap greater than
\(g_0+1/2=61/62\). Thus

\[
                            y_1<3/5-61/62=-f<-23/60.
\tag{6}
\]

The strengthened two-low-main theorem and the original lower G force
\(y_2>-3/5\). In particular the original F center satisfies

\[
                             Y>23/60.
\tag{7}
\]

The complete own-half-plane inset loss formula gives

\[
                    Y-h>y_2+g_0-r_F,
 \qquad r_F=\max\{0,t(k+\delta-X)\}.
\tag{8}
\]

This is the physical formula from Sections 2--3 of
`CENTRAL_SINGLETON_FLOOR_HAND_TABLE_PROOF.md`. It includes both original
chiralities and every separator owner, rather than assuming a vertical
projection edge.

### 4.2. A very low helper is already covered by the accepted two-proxy lemma

If \(y_S<f\), its near-main gap gives \(y_1<-3/5\). Applying the
strengthened two-low-main theorem to the original G now yields
\(y_2>-23/60\). Hence

\[
 Y>3/5>223/372,
 \qquad y_2+g_2>-23/60+15/31=1/10+1/1860.
\]

The low S satisfies |yS|<7/16: its lower bound -113/600 follows from the
main cone, and f<7/16. The endpoint and near-main zero-helper arguments,
which do not require a full side, give

\[
        -x_S-g_S<23/150,
        \qquad y_S+g_S>18911/59520.
\]

All predicates of
`LOW_FLOOR_RIGHT_CENTRAL_AND_HIGH_RIGHT_SHOULDER_EXCLUSION.md` therefore
hold with the same original S,F,M2,T. Its complete physical argument
excludes F's assumed floor. This closes the very-low-helper case.

### 4.3. A moderate low helper forces X above seven twentieths

It remains that \(f\le y_S<3/5\). Put \(s=-x_S\) and \(z=y_S\).
The original S disk avoids the fixed left-endpoint rectangle, so

\[
 s\le K(z):=A-\sqrt{1/4-(z-c)^2},
                    \qquad f\le z\le3/5.
\tag{9}
\]

Here z>c and s<A, as supplied by the established side bounds. At the two
endpoints the positive-root comparisons give

\[
                            K(f)<11/20,
                       \qquad K(3/5)<243/400.
\tag{10}
\]

Suppose X<=7/20. By (7), the assumed bad floor, and h<17/24,

\[
                         23/60<Y<97/120.
\]

For a fixed z, the squared distance from S to F is bounded by
\((K(z)+7/20)^2+(z-Y)^2\), whose maximum over this Y interval is
at one of the two endpoints Y=23/60 or Y=97/120. For either fixed
endpoint Y, expansion shows that this expression is convex in z: the only
nonlinear term is \(-2(A+7/20)\sqrt{1/4-(z-c)^2}\).
Thus it suffices to check z=f and z=3/5. At the first endpoint the larger
vertical difference is 97/120-f; at the second it is 13/60. Using (10),

\[
 (9/10)^2+(97/120-f)^2<1,
 \qquad (383/400)^2+(13/60)^2<1.
\tag{11}
\]

The original disks would overlap. Therefore

\[
                                  X>7/20.
\tag{12}
\]

All vertical orders of S and F are included in the two endpoint maxima;
none has been assumed.

### 4.4. The original F inset is too high and too far right

Since \(\delta<1/60\), (12) gives

\[
 r_F\le\left[t\left(1/6-t/2\right)\right]_+
                                 \le1/72.
\tag{13}
\]

Indeed k<=(1-t)/2, and the final maximum follows by completing the square
at t=1/6. The identity
\(h+1/(4h)-1=(h-1/2)^2/h\ge0\), (8), and \(y_2>-3/5\)
therefore give

\[
 X+g_F>7/10,
 \qquad Y+g_F>2/5+15/31-1/72
                 =9709/11160>869/1000.
\tag{14}
\]

The high right-side unit T lies horizontally to the right of this actual
F inset center, since xT>=l>=X. It also lies vertically above F. Otherwise
its center gap from F would have horizontal magnitude below 11/15 and
vertical magnitude below 5/24, giving squared distance below one. This
uses xT<=u, (12), yT>=3/5, and Y<97/120.

Consequently the original physical T and the original aligned inset of
F satisfy every premise of
`RIGHT_SIDE_UNIT_ABOVE_RAISED_PROXY_HAND_TABLE.md`: the proxy's right edge
is above 7/10, its top is above 869/1000, T's center has l<=xT<=u, and
both center orders are correct. Its complete 112-row exact cover excludes
this physical pair. This contradiction finishes the moderate-helper case.

### 4.5. Extract the original cap units

Every upper central unit has now been proved to have whole floor above
one tenth. Both central centers exceed three fifths, so upper-column
separation forces their horizontal signs to be opposite. Let Fminus,Fplus
be the negative and positive originals. Choose

\[
                         L=Fminus,\qquad U=Fplus,\qquad R=T.
\]

Their frames and original pair constraints are unchanged, and they satisfy
(2). The widened cap contradicts (1), closing the one-low-side branch.

## 5. Completion and exact review boundary

Section 1 excluded two low side outsiders. Section 3 closes two high
side outsiders; Section 4 closes exactly one low side outsider, including
either horizontal reflection and both sides of the boundary yS=f. Thus
the entire normalized (1,3,1), two-upper/one-lower central family with
both side outsiders above their own mains is excluded. No selected short
link was added or discarded, and no actual short-edge premise is used.

The original lower G supplies both the at-most-one-low routing and the
main-height lower bounds. The side units supply their actual high/low
alternatives, the endpoint profile, and the final physical cap pair.
Both original upper central units remain available throughout; no virtual
unit or independent replacement orientation is introduced.

`verify_131_both_side_upper_arithmetic.py` recomputes every new rational
comparison in this manuscript. Its report is
`131_both_side_upper_arithmetic_replay.json`. The complete one-main and
raised-proxy exact tables have their own independent replay records.
The widened terminal and the other named geometric inputs remain separate
complete theorems. This manuscript makes only the stated occupancy/height
claim; the full `000/11` mask is assembled from all required callers.
