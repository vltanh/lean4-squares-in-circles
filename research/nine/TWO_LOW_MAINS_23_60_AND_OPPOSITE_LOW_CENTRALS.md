# A sharper two-low-main exclusion and opposite low central units

November 2, 2026. Complete physical strengthening of the accepted
two-low-mains theorem. Its new 317-leaf exact cover has passed independent
dyadic replay. The application below is a hand argument with exact
rational arithmetic. No Lean or CI.

Put \(Q=1105/256\), \(l=29/60\), \(g=15/31\),
\(\rho=91/60\).

## 1. The strengthened complete theorem

Retain an actual horizontal four-chain of physical original unit squares
in the closed Q-disk. If the inner main centers satisfy

\[
                       y_1\le-3/5,\qquad y_2\le-23/60,
\tag{1}
\]

there is no distinct original central unit F with \(|x_F|\le l\)
below both inner main centers and physically interior-disjoint from both
main squares. Every orientation and physical separator owner is retained.
Horizontal and vertical reflection give the corresponding variants.

This strengthens `TWO_LOW_MAINS_CENTRAL_EXCLUSION_HAND_TABLE.md` by replacing
119/310 with the smaller 23/60. All geometric reductions in its Sections
2.1--2.3 remain unchanged except for this one right-main height constant.
For completeness, reflect vertically and write F's center as (X,Y). The
left-main argument forces \(1/3<X\le l\), \(Y>3/5+g>X\). For its
one original folded frame, put

\[
 a=(1+t^2)^{-1/2},\quad b=ta,\quad
 h=(a+b)/2,\quad k=(a-b)/2,\quad 0\le t\le1.
\]

Both chiralities imply the common corner upper bound

\[
 Y\le U=\min\{\sqrt{Q-(X+h)^2}-k,
                 \sqrt{Q-(X-k)^2}-h,\rho\}.
\tag{2}
\]

The right main's aligned inset of halfwidth g and all four of its pair
separating-axis alternatives imply

\[
 Y\ge L=23/60+g+
       \min\{h,(1/2+b(g-31/60+X))/a\}.
\tag{3}
\]

For the left inset, put \(d=X+31/60-g\), \(v=U-3/5-g\).
Disjointness requires one of

\[
                d-h,\quad v-h,\quad ad+bv-1/2,
                         \quad bd+av-1/2
\tag{4}
\]

to be nonnegative. The same original frame occurs in (2)--(4).

The complete root \([1/3,l]\times[0,1]\) is covered by
`two_low_mains_23_60_cover.json`: 633 binary nodes, 317 leaves, maximum
depth 14. There are 249 strict rows with the lower interval endpoint of L
above the upper endpoint of U, and 68 strict rows with all four interval
upper bounds in (4) negative. Both children of every split are retained,
including midpoint faces; there are no unresolved boxes.

The producer uses exact Fraction intervals. The independent standalone
`verify_two_low_mains_23_60.py` reconstructs every box and recomputes all
bounds using outward 64-bit integer dyadic intervals, with no producer or
interval-library import. Its saved report is
`two_low_mains_23_60_dyadic_replay.json`. All 317 rows pass, with least
positive reserve \(276834140688067/2^{64}\).
The certificate SHA256 is
`1552a4a3480859004732f5f910e739b22992801eac55630a6509690c5efc5f51`.
This proves the entire strengthened physical statement (1), including
equality in either main-height bound.

## 2. Opposite low upper central units cannot coexist with a lower central

Now suppose the actual main four-chain is also a center-cone chain. Retain
an original central G below both inner mains. Let A,B be original central
units above both mains, with

\[
 x_A\le0\le x_B,\qquad y_A<3/5,\quad y_B<3/5.
\tag{5}
\]

The physical own-half-plane central clearance is greater than 59/60.
Thus (5) forces \(y_1<-23/60\), \(y_2<-23/60\). The theorem in
Section 1 and its horizontal reflection, applied to the same original G,
then force both main centers strictly above -3/5. Applying the same
physical clearance again gives

\[
                     23/60<y_A,y_B<3/5.
\]

Their horizontal center gap is at most \(2l=29/30\), and their
vertical gap is less than \(13/60\). Therefore

\[
 |c_A-c_B|^2<(29/30)^2+(13/60)^2
                         =3533/3600<1.
\tag{6}
\]

The original open radius-one-half disks inside A,B would overlap. This
proves the exclusion, including a central center at x=0.

## 3. At most one low upper central unit in total

The retained main cone bounds give \(y_i>-139/120\). Every upper
central unit consequently has center height greater than -7/40, using its
own-half-plane clearance 59/60. If two upper central units are in the same
closed horizontal half-plane and both have heights below three fifths,
their squared center distance is strictly less than

\[
                         l^2+(31/40)^2<1.
\tag{7}
\]

Thus they cannot coexist either. Combining Sections 2 and 3, in the
presence of an original central unit below both mains, **at most one**
upper central unit can have center height below three fifths. Both same
and opposite horizontal halves have been covered, without assigning an
arbitrary side to x=0.

The scalar comparisons (6)--(7) are independently recomputed in
`verify_140_three_upper_arithmetic.py`. This is a standalone original-unit
routing theorem, not a whole-mask closure by itself.
