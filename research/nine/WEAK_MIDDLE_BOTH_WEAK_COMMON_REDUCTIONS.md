# Common physical reductions for the full original-nine 010/11 domain

November 2, 2026. Hand deductions from accepted exact physical tables.
This document does not claim the complete mask closed. No Lean or CI.

Let the original main squares be A,B,C,D in horizontal cone order. The
outer comparisons A--B and C--D are actual horizontal projection
comparisons; B--C is weak. Let L,P,R be the designated outsider cone
three-chain, with both of its comparisons weak. The remaining two original
squares retain every physical and corner constraint. All squares have
arbitrary independent frames in the closed disk of squared radius

\[
 Q=1105/256,\qquad \rho=91/60,\qquad l=29/60,\qquad u=13/12.
\]

For every unit put h equal to its coordinate halfwidth, g=1/(4h),
k=sqrt(1/2-h^2), and eta=h+g-1. Write

\[
 U=h_A+h_D-1,\quad V=\eta_B+\eta_C,\quad
 \mathcal D=x_D-x_A-h_A-h_D.
\]

The endpoint-reserve theorem supplies

\[
 \mathcal D\ge2+V,\quad U+V<1/30,\quad
 |y_A|+|y_D|+(37/50)U+(32/9)V\le1/8,                 \tag{1}
\]

\[
 -\rho<x_A<-89/60,
 \quad89/60<x_D<\rho,
 \quad 1/2\le h_A,h_D<8/15,                          \tag{2}
\]

\[
 h_B-61/60<x_B<1/60-g_B-\eta_C,
 \quad g_C+\eta_B-1/60<x_C<61/60-h_C,               \tag{3}
\]

\[
 h_B,h_C<13/20,\quad g_B,g_C>5/13,
 \quad -31/60<x_B<0<x_C<31/60.                      \tag{4}
\]

Every outsider has |x|<u. The actual source is
`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`; no inner-width
bound 31/60 is assumed. Since the middle bit is genuinely weak, V>0:
V=0 would make B,C aligned, and their weak horizontal gap and cone
vertical gap would both be below one, contradicting physical disjointness.

## 1. Uniform main-height range

For either inner main M, with its own h,g,eta, the matched outer cone,
(1), and (3) give

\[
 y_M>g-199/120+(32/9)\eta.
\]

For example, on the right,
\(y_C\ge y_D-x_D+x_C\), with
\(y_D\ge-1/8+(32/9)V\), \(x_D<\rho\), and
\(x_C>g_C+\eta_B-1/60\). Dropping the nonnegative other-main
contribution gives the displayed inequality. Moreover

\[
 g+(32/9)\eta
  =(32/9)h+41/(36h)-32/9
  \ge4\sqrt{82}/9-32/9>11/24.
\]

The last comparison is exactly \(32\sqrt{82}>289\), whose positive
squared reserve is 447. Thus, by vertical reflection too,

\[
                    -6/5<y_B,y_C<6/5.             \tag{5}
\]

The original middle cone also gives \(|y_C-y_B|<31/30\).

## 2. Every central original is above both mains or below both

Let F be any original outsider with |x_F|<l. This argument applies to
all central outsiders, without a selected low-floor hypothesis.

For M=B or C write \(D_M=|x_F-x_M|\). The bands (3) imply

\[
                         D_M-g_M<1/2.             \tag{6}
\]

For example, if x_F<=x_C then
\(D_C<3/2-h_C\), so \(D_C-g_C<1/2-\eta_C\le1/2\).
If x_F>=x_C then \(D_C<1/2-g_C-\eta_B\), which is even smaller.
Horizontal reflection gives the B assertion.

The radius-one-half disk contained in F must avoid the aligned inset of
M. Consequently

\[
 \max(D_M-g_M,0)^2+
 \max(|y_F-y_M|-g_M,0)^2\ge1/4.                   \tag{7}
\]

In particular (6) gives \(|y_F-y_M|>g_M\), excluding equality with
either main height. At least one of D_B,D_C is less than 31/60. If F
is between the main x coordinates, this follows from
\(x_C-x_B<31/30\). If F lies outside that interval, its gap to the
nearer main is less than \(1/2-5/13=3/26<31/60\).

For that nearer main, the square-root excess in (7) is greater than
12/25, because

\[
 1/4-(31/60-5/13)^2-(12/25)^2
                   =32891/15210000>0.
\]

If F were between the two main heights, their difference would exceed

\[
 g_B+g_C+12/25>10/13+12/25>31/30,
\]

where the last reserve is 421/1950. This contradicts the original
middle cone. Therefore every central original lies strictly above both
mains or strictly below both. No near-aligned inner frame is used.

There is also a useful own-half-plane clearance. For x_F>=0 choose
M=C, and for x_F<=0 choose M=B. Equations (3)--(4) give

\[
 |x_F-x_M|\le61/60-h_M.
\]

The accepted twelve-row physical table in
`WEAK_MIDDLE_CENTRAL_ROUTING_AND_LOWER_COUNT.md`, Section 1, then gives

\[
                         |y_F-y_M|>9/10.          \tag{8}
\]

Thus every upper central original has center height greater than -3/10,
and every lower central original has center height less than 3/10.
The later low-floor-specific consequences in that source are not used.

## 3. The selected triple has a common upward choice

Each original cone gap is at least the sum of the two contained aligned
inset halfwidths, and hence is greater than 7/10. Since |x|<u,

\[
 |x_P|<23/60<l,\qquad x_L<-19/60<0<x_R,
 \qquad x_R>19/60.                                \tag{9}
\]

In addition

\[
 x_R-x_L\ge g_L+2g_P+g_R\ge\sqrt2>7/5.           \tag{10}
\]

P is central, so Section 2 routes it above both mains or below both.
Reflect vertically to make P above both.

The accepted wider-main three-quarter clearance table in
`WEAK_MIDDLE_ROUTING_AND_HIGH_FLOOR.md`, Section 1, states that

\[
 |x_S-x_M|\le7/5-h_M\ \Longrightarrow\
 |y_S-y_M|>3/4\qquad(1/2\le h_M\le13/20).         \tag{11}
\]

For P and either main, (3),(9) bound the horizontal gap by the larger
of \(7/5-h_M\) and \(2/5-g_M-\eta_{\rm other}\); both are no
greater than \(7/5-h_M\). Hence P is above each main by more than
three quarters.

For L and B, the two horizontal orders give the bounds

\[
 x_B-x_L<11/10-g_B-\eta_C,
 \qquad x_L-x_B<7/10-h_B.
\]

Both are less than \(7/5-h_B\), because
\(h_B-g_B<13/20-5/13=69/260<3/10\). Thus L has vertical
clearance greater than three quarters from B. If L were below B, then
\(y_P-y_L>3/2\), whereas its original cone edge gives
\(y_P-y_L\le x_P-x_L<22/15<3/2\). This is impossible. Therefore
L is above B. Reflection gives R above C. Every selected central
endpoint is consequently above both mains by Section 2.

## 4. A central selected endpoint forces the opposite endpoint high

If R is central, (10) gives

\[
 x_L<l-7/5=-11/12,
 \qquad x_P\le l-g_P-g_R<0<x_R.                  \tag{12}
\]

The horizontal gap from L to A is below 3/5. Their original contained
radius-one-half disks therefore give \(|y_L-y_A|>4/5\).
By (5),(11), \(y_L>-6/5+3/4=-9/20\). L cannot be below A,
since that would imply \(y_L<1/8-4/5=-27/40<-9/20\). Hence

\[
                         y_L>27/40>3/5.           \tag{13}
\]

Horizontal reflection proves the counterpart when L is central.

## 5. The same complete outsider-count list survives

For a strict-radius counterexample, apply the accepted small common
center expansion, retaining all five bits and the outsider columns.
The expanded closed original squares are pairwise disjoint. The outer
actual-link marker theorem applies to both endpoints and proves that B
and C still consume one side marker each, even when their centers lie
inside |x|<l. Thus each side contains at most two outsiders.

Up to horizontal reflection, the complete list of five-outsider counts
is therefore

\[
 (2,1,2),\quad(2,2,1),\quad(2,3,0),\quad
 (1,3,1),\quad(1,4,0),\quad(0,5,0).               \tag{14}
\]

The last count is impossible already by (10), since three central
selected units have span below 2l<sqrt(2). This eliminates that entire
occupancy family of 010/11. No other count is declared closed here.

## 6. Universal physical-pair caps retain the middle surplus

Let a shoulder have folded frame components a>=b>=0, a^2+b^2=1,
and define the accepted orientation toll and effective halfwidth

\[
 \tau=\max\{2b,\ 6b-(27/2)(1-a)\},
\quad
 \psi=h-(2/27)\tau
   =\min\{a/2+19b/54,\ 1-a/2+b/18\}.             \tag{15}
\]

The two accepted universal physical-pair toll theorems require only
the original disjoint pair and closed-Q containment. They do not
assume a shoulder height. Put
\(A_0=-x_A-h_A\), \(A_3=x_D-h_D\),
\(Z=-x_L>0\), and \(X=x_R>0\). Applied to the original endpoint
pairs A,L and D,R, they give

\[
 46A_0+(27/2)(Z-\psi_L)\le211/4,
\quad46A_3+(27/2)(X-\psi_R)\le211/4.             \tag{16}
\]

Since \(A_0+A_3=\mathcal D\ge2+V\) and each \(A_i<61/60\),
the complete necessary resources are

\[
 \boxed{Z+X-\psi_L-\psi_R\le1-(92/27)V},          \tag{17}
\]

\[
 Z-\psi_L<451/810-(92/27)V,
 \quad X-\psi_R<451/810-(92/27)V,                  \tag{18}
\]

\[
 A_0\ge157/184+V+(27/92)(X-\psi_R),
 \quad A_3\ge157/184+V+(27/92)(Z-\psi_L).         \tag{19}
\]

These inequalities preserve the original shoulder frames and are
independent of the widened five-square cap. They provide quantitative
input for future low-floor elimination without assuming an actual
middle main link or an actual selected short link.

## 7. Available terminal and the exact seven-unit obstruction

The endpoint bands (2) satisfy the accepted widened five-square cap.
If three distinct original outsiders can be chosen with opposite-sign
shoulders of heights at least 3/5 and a central original whole floor at
least 1/10, that cap gives \(\mathcal D\le2\), contradicting
\(\mathcal D\ge2+V>2\). Every remaining count must still supply
those witnesses or another complete contradiction.

A selected-seven low-floor exclusion is false. The rational data
`selected_seven_01011_exact_control.json` and standalone checker retain
the four main originals and L,P,R. All 28 corners and 21 physical pairs
are strictly valid, the five exact bits are 010/11, and

\[
 h_B-31/60=239/72060>0,\qquad
 y_P-h_P=-188030093/10^9<1/10.
\]

The minimum physical pair reserve is 1/2000. This seven-unit control
is not a nine-square counterexample. It records precisely why the two
additional originals cannot be discarded in the whole-domain argument.

`verify_weak_middle_both_weak_reductions.py` reconstructs every new
finite rational comparison and cap coefficient in this note. The two
clearance tables and two universal toll covers keep their separately
accepted exact certificates and independent reviews.
