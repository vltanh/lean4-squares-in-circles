# An upper side square bounds the position of a good central cone neighbor

November 2, 2026. Complete physical hand reduction and exact finite table.
The final 6,302-leaf cover has passed independent directed-dyadic replay.
No Lean, Lake, or CI is used.

## 1. Statement

Retain an actual horizontal four-chain that is also a center-cone chain
in the centered closed disk of squared radius Q=1105/256. Let L and P
be two further distinct original unit squares, with independent frames
and physical nonoverlap from each other and from every main square.
Write l=29/60 and u=13/12. Suppose

\[
-u\le x_L\le-l,\qquad y_L\ge0,\qquad |x_P|\le l,
\qquad y_P-h_P\ge1/10,
\]

and their original centers obey the horizontal cone comparison

\[
x_P-x_L\ge|y_P-y_L|.
\tag{1}
\]

Then

\[
\boxed{x_P>-1/10.}
\tag{2}
\]

Horizontal reflection gives the corresponding statement for P preceding
a right-side upper original: \(x_P<1/10\). No actual projection edge is
required between L and P. No other outsider is replaced by a proxy, and
the assertion does not assume a common physical orientation.

## 2. A fixed rectangle inside the original left endpoint

Let E be the original left endpoint of the actual four-chain. The
accepted endpoint bounds give

\[
-91/60<x_E<-89/60,\qquad g_E>15/32,
\qquad g_E-|y_E|>221/600,
\]

where E contains its centered aligned inset of halfwidth \(g_E\).
Therefore E contains the fixed rectangle K with center \((-3/2,0)\)
and halfwidths

\[
g_x=217/480,\qquad g_y=221/600.
\tag{3}
\]

Its horizontal interval is \([-937/480,-503/480]\), contained in
every permitted endpoint inset; its vertical interval is contained by
the last displayed endpoint bound. Thus L and K have disjoint open
interiors. K is used only as a necessary contained subset of the one
original E.

Suppose (2) is false and set \(x_L=-z\), \(x_P=-v\). Each physical
unit contains its centered radius-one-half disk. Nonoverlap and (1)
give \(x_P-x_L\ge1/\sqrt2>7/10\). Hence every counterexample is in

\[
4/5\le z\le13/12,\qquad1/10\le v\le29/60.
\tag{4}
\]

Its horizontal displacement from K to L is
\(D_E=3/2-z\). In particular

\[
s:=D_E-g_x\in[-17/480,119/480],\qquad
D_E+g_x\ge139/160.
\tag{5}
\]

## 3. Retain L's actual frame sign in its endpoint clearance

For either physical square write its reduced signed angle as
\(\theta=\epsilon\arctan t\), where \(\epsilon\in\{-1,1\}\)
and \(0\le t\le1\). Set

\[
a=(1+t^2)^{-1/2},\quad b=ta,\quad
h=(a+b)/2,\quad k=(a-b)/2.
\]

Its original side axes are \((a,\epsilon b)\) and
\((-\epsilon b,a)\). Both independent frame signs will be retained
in the finite root cover.

The rectangle's horizontal coordinate axis cannot separate L from K:
\(D_E-g_x\le119/480<1/2\le h_L\). Its upward vertical axis
requires \(y_L\ge g_y+h_L\). A downward separating unit axis is
impossible. If its horizontal component is nonpositive, its scalar
product with the nonnegative displacement \((D_E,y_L)\) is
nonpositive. Otherwise its adjusted projection is at most
\(\max(0,D_E-g_x)<1/2\), below L's owned support one half.

For an upward L-owned axis, the two possible thresholds are as follows.
For \(\epsilon_L=-1\), they are

\[
g_y+1/(2a_L)-t_L(D_E-g_x),\qquad
g_y+1/(2b_L)+(D_E+g_x)/t_L.
\tag{6}
\]

For \(\epsilon_L=1\), they are

\[
g_y+1/(2a_L)+t_L(D_E+g_x),\qquad
g_y+1/(2b_L)-(D_E-g_x)/t_L.
\tag{7}
\]

Terms with b_L or t_L in the denominator are used only for t_L>0.
At t_L=0 the only possible remaining axis is the coordinate vertical
axis. The extra \(D_E+g_x\), rather than \(D_E-g_x\), in the
negative-horizontal directions is essential to retain the physical
frame sign.

By (5), \(D_E+g_x>k_L\). Each negative-horizontal upward threshold
in (6)--(7) is consequently at least the coordinate top threshold.
The complete endpoint clearance therefore reduces to

\[
y_L\ge g_y+h_L-r_L,
\tag{8}
\]

where

\[
\begin{array}{ll}
\epsilon_L=-1:&r_L=\max\{0,t_L(k_L+s)\},\\
\epsilon_L=1:&r_L=\max\{0,(s-k_L)/t_L\}\quad(t_L>0).
\end{array}
\tag{9}
\]

For the aligned positive-sign endpoint define r_L=0. Thus all original
separator owners and all physical frame signs are included.

Every threshold that can remain is at least

\[
g_y+1/2-119/480=1489/2400>31/50.
\tag{10}
\]

For the shallow threshold this uses \(1/a\ge1\) and \(t\le1\);
for the steep threshold it uses
\((\sqrt{1+t^2}/2-s)/t\ge1/2-s\). The last strict reserve in
(10) is exactly 1/2400. This explains why the weaker hypothesis
\(y_L\ge0\) suffices in the statement.

## 4. The two exact slope charts and the signed circle caps

Split t_L into the two closed rational charts

\[
[0,1/4],\qquad[1/4,1].
\tag{11}
\]

On the first chart,
\(k_L\ge3/(2\sqrt{17})>25/96\). Equations (5) then give
\(k_L+s>0\) and \(s-k_L<0\). Thus (9) is respectively the
division-free shallow expression or zero there. On the second chart
the displayed division in (9) has denominator at least 1/4. Both
charts include their shared boundary and give the same physical value.

For a unit at center \((-x,Y)\), with x nonnegative and Y positive,
write \(\rho=\sqrt{Q-1/4}-1/2\). Its two relevant actual corners
and its center-radius bound give

\[
\begin{aligned}
U_{-}(x,t)&=\min\{\rho,\sqrt{Q-(x+k)^2}-h,
                                  \sqrt{Q-(x+h)^2}+k\},\\
U_{+}(x,t)&=\min\{\rho,\sqrt{Q-(x-k)^2}-h,
                                  \sqrt{Q-(x+h)^2}-k\}.
\end{aligned}
\tag{12}
\]

The subscript in (12) is the actual physical frame sign at negative x.
In particular signs are not chosen separately for the circle and the
endpoint inequality. All radicands are strictly positive on (4).

Define the necessary center-height bounds

\[
\begin{array}{ll}
L_0=\max\{31/50,g_y+h_L-r_L\},&L_1=U_{\epsilon_L}(z,t_L),\\
P_0=h_P+1/10,&P_1=U_{\epsilon_P}(v,t_P).
\end{array}
\tag{13}
\]

Both y_L and y_P are positive, by (10) and the assumed whole floor.

## 5. Complete physical pair axes

Put D=z-v. By (4), \(D\le59/60<1\). The cone comparison confines
the actual vertical displacement \(\Delta=y_P-y_L\) to

\[
d_0=\max\{P_0-L_1,-D\}\le\Delta
             \le\min\{P_1-L_0,D\}=d_1.
\tag{14}
\]

A directed physical separating normal from L to P cannot have
nonpositive horizontal component: its projection would be at most
\(|\Delta|\le D<1\), whereas the support sum is at least one.
Thus every possible separating side axis is one of the two
positive-horizontal representatives of each original frame:

\[
(a,\epsilon b),\qquad(b,-\epsilon a).
\tag{15}
\]

The common support sum on such an owned axis is exactly

\[
\sigma=\tfrac12\{1+|a_La_P+\epsilon_L\epsilon_Pb_Lb_P|
                    +|\epsilon_Pa_Lb_P-\epsilon_Lb_La_P|\}.
\tag{16}
\]

For each axis (15), maximize its projection \(n_xD+n_y\Delta\)
over the closed interval (14), selecting d_1 for nonnegative n_y and
d_0 for negative n_y. Let B be the maximum of the four resulting
values. Nonoverlap requires B at least sigma.

The original aligned insets also give
\(D\ge1/(4h_L)+1/(4h_P)\): if their horizontal gap were smaller
than the sum of their inset halfwidths, the cone comparison would make
their vertical gap smaller too, yielding an interior intersection.

Consequently a physical counterexample supplies a point where all five
quantities are nonnegative:

\[
L_1-L_0,\quad P_1-P_0,\quad d_1-d_0,\quad
D-1/(4h_L)-1/(4h_P),\quad B-\sigma.
\tag{17}
\]

The complete exact table proves that their minimum is strictly negative.

## 6. Exact cover and independent acceptance

There are eight roots: all four pairs of physical frame signs, and both
charts (11). Each root is the complete rational box (4), its t_L chart,
and \(0\le t_P\le1\). Every internal split retains both closed
midpoint children. Every final leaf has a strictly negative exact
interval upper bound for (17).

The producer uses the 96-bit outward interval and automatic derivative
kernel in `joint_five_interval.py`. The independent checker uses the
separate 64-bit directed-dyadic implementation in
`verify_joint_five_dyadic.py`. It reconstructs the three physical
endpoint thresholds (6)--(7) directly, instead of importing the
producer's simplified loss formula. The point expressions agree, but
the interval forms have different widths. Refining 286 original leaves
made the latter form sufficient on every final leaf.

Fresh independent replay of the final tree verified all 12,596 nodes
and all 6,302 strict leaves, with maximum depth 29. The largest replayed
leaf upper bound was

\[
-87402506829127/18446744073709551616<0.
\]

The certificate SHA-256 is
`794ddb292c0914e2aa5f097fd68f2abea037bcc7bba08cba659de9630cbc8028`.
The checker fixes the roots, signs, charts, constants, complete child
coverage, and node uniqueness. It recomputes every numerical inequality
and does not trust a stored producer upper bound. The physical reduction
has a separate independent agent audit; no human or formal-kernel
verification is claimed.

All fifteen damaged or false certificate controls were rejected,
including altered rectangle constants, a missing root, uncovered central
boundary, wrong physical frame signs or slope charts, malformed child
coverage, and an asserted negative whole-chart leaf whose inequality is
recomputed. The control report uses the same certificate hash above.

Files and reproduction commands:

```sh
python computer_assisted/verify_low_endpoint_central_position.py computer_assisted/low_endpoint_central_position_cover.json
python computer_assisted/check_low_endpoint_central_position_controls.py
```

The producer is `computer_assisted/certify_low_endpoint_central_position.py`;
the optional leaf refinement is
`computer_assisted/refine_low_endpoint_central_position.py`.
The independent replay, refinement, and damaged-certificate control
reports accompany the cover. Earlier incomplete or more relaxed attempts
are not dependencies of this proof.
