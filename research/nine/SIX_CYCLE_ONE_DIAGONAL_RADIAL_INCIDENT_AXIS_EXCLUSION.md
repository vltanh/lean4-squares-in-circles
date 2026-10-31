# The sole-radial-incident family with a C-owned bottom axis is impossible

**Status: complete whole-domain hand argument; root and separate independent full source, geometry, routing and exact audits passed.**

Use the full incident-radial domain and notation of the central-region theorem: \(B-W-C-U_C-T-U_B-B\), B radial, C,T unique, W sole diagonal,
\[
 B=[-K,1-K]\times[-1/2,1/2],\quad C=[c-1,c]\times[e-1,e],\quad K=d+1,
\]
\[
 91/100<d<1,\quad\sqrt2<c<31/20,\quad5/4<e<3/2,\quad127/300<h<1/2. \tag{1}
\]
B's other application and normal are \(p_B=(-d,-1/2),n_B=(a,-s)\), a=cos(alpha),s=sin(alpha). Assume C's other normal is its bottom axis, with its original mean \(p_C=(c-1+\zeta,e-1)\), 0<=zeta<=1. Then
\[
 P=(-d+a,-1/2-s),\quad Q=(c-1+\zeta,e-2),\quad Q_x=ch/e<31/50. \tag{2}
\]
Every original weight and shared mean is retained.

## 1. The complete unique T feature cover

The actual T force turn is alpha+pi/2. Its unique-corner turn bound gives alpha<=pi/4, and the turn is strictly greater than pi/2. The full unique feature cover therefore puts P,Q on a common inner side, at least one a vertex. Both T-owned axes are impossible at this turn. Classify actual T side-axis owners first. The possibilities are: T owns the B normal; T owns the C normal; or neither T interface owns a side-axis normal, in which case P,Q are both vertices. The owned cases include every original shared-side mean and its endpoints.

The directed chord has positive horizontal component \(\Delta_x=\sqrt2+\zeta-a>0\), and \(\Delta_y=e-3/2+s\). The actual T interior is below this chord, and its right application's outward vertical normal forces Delta_y>=0.

## 2. T cannot share the B channel

If T owns the B normal, the side direction from P to Q is (s,a). Thus \(\Delta_xa-\Delta_ys=0\), or
\[
 \sqrt2\,a+\zeta a-1=s(e-3/2). \tag{3}
\]
The left side is nonnegative because alpha<=pi/4 and zeta>=0. The right side is strictly negative by (1), contradiction. This includes alpha=pi/4 and every endpoint mean.

## 3. The case with neither T side-axis owner is impossible

Suppose neither T interface owns a side-axis normal. Then both actual applications are vertices, and their common inner side has unit length. Write \(Q-P=(v,u)\), with v²+u²=1. Strict T vertex support gives u>0; moreover \(u=e-3/2+s<s\), so
\[
 v>a\ge1/\sqrt2. \tag{4}
\]
Put N=(-u,v), the outward normal of that inner side. The unique circle corner is either P-N or Q-N.

The original C force line is vertical, so the unique T concurrence has first coordinate Q_x>0. If the circle corner were P-N, its first coordinate would be \(Q_x-v+u<Q_x\). But a unique concurrence has form q_T=tau z_T with 0<tau<=1, contradicting its positive first coordinate. Hence \(z_T=Q-N=(Q_x+u,Q_y-v)\).

The B force ray through P reaches x=Q_x after horizontal displacement v. It follows that
\[
 (q_T)_y=P_y-vs/a=-1/2-s-vs/a.
\]
Both q_T and z_T have negative second coordinates, and tau<=1 gives \((q_T)_y\ge(z_T)_y=-1/2-s+u-v\). Thus
\[
 u\le v(1-s/a)\le1-s/a. \tag{5}
\]
Since u=e-3/2+s>s-1/4 by (1), this implies
\[
 s+s/a<5/4. \tag{6}
\]

On the other hand, (2),(4) give \(Q_x=-d+a+v>2a-1\), and therefore a<81/100. Thus s>29/50 by squaring (3439>3364), and
\[
 s+s/a>29/50+58/81=5249/4050>5/4,
\]
with final margin 373/8100. This contradicts (6). The argument used containment only at unique T, never radial B.

## 4. The surviving actual T--C channel is parallel

Therefore T owns the C normal. Its inner side is horizontal, P is its left endpoint and Q is its unchanged application on that side, including endpoint means. Consequently
\[
 e=3/2-s. \tag{7}
\]
The unique feature cover places the actual T circle corner opposite P:
\[
 z_T=(1-d+a,-3/2-s).
\]
Its circle equality is exactly
\[
 d=\frac{3+2a+3s}{2(2+a)}. \tag{8}
\]
Equation (7) and e>5/4 give s<1/4. Also s>1/10: otherwise a>99/100 and (8) would give \(d<265/299<91/100\), where the last gap is 709/29900. It follows that
\[
 e<7/5<\sqrt2<c. \tag{9}
\]
The original vertical C line gives the actual side-channel cap height
\[
 h_C=Q_x=ch/e>h>21/50. \tag{10}
\]

The two loaded units C and T are parallel in the displayed frame. Their opposing horizontal sides differ in height by exactly one: C bottom is e-1, T top is e-2. Their center heights consequently differ by exactly two. Their horizontal unit intervals meet at the original Q_x, so the horizontal center difference has magnitude at most one. Therefore
\[
 |c_C-c_T|^2\le5. \tag{11}
\]
Both centers have positive first coordinate: \(c_C{}_x=c-1/2>0\), while \(c_T{}_x=a-d+1/2>a-1/2>0\). Every boundary unit center has norm
\[
 |c_i|\ge R-\sqrt2/2>5/4. \tag{12}
\]
Let gamma be the actual center angle through this right-hand exterior pocket. It lies in (0,pi), and (11)--(12) imply
\[
 \gamma<\arccos(-3/5)<127^\circ. \tag{13}
\]
Indeed gamma>=arccos(-3/5) would give \(|c_C-c_T|^2\ge|c_C|^2+|c_T|^2+(6/5)|c_C||c_T|>5\). The final 127-degree comparison is the same exact Taylor/integral comparison already audited in the side-capacity source.

## 5. Full physical capacity of this C--T pocket

The actual cap theorem puts every whole extra in the C--T pocket beyond the vertical line x=h_C. Its center therefore has norm greater than h_C+1/2>23/25. ANNULAR_CENTER_ARC_AT_23_25.md gives its entire radius-5/4-circle intersection as a connected open arc, containing its radial-center point and of length strictly greater than 43.5 degrees.

Both loaded endpoint centers lie in the actual positive cap half-plane, as checked above. The full side-channel crosscut routing used in RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md and SIX_CYCLE_ONE_DIAGONAL_SIDE_CAPACITIES.md applies directly: the actual occupied crosscut joins the two closed endpoint circle arcs through the original unit channel segment; an extra circle point outside their center-angle interval can follow the inner circle away from the crosscut to the cap axis and then that axis to infinity. It cannot belong to the bounded physical exterior pocket. Each closed endpoint arc, including a part extending beyond the axis, blocks the open interior of any other square. The centered closed 40-degree arcs from CENTERED_INNER_ARC.md consequently leave free length less than \(\gamma-40^\circ<87^\circ\).

Two extras would contribute two disjoint connected open arcs each longer than 43.5 degrees, impossible. Thus this entire original C--T pocket has capacity at most one. No endpoint arc was truncated, no side mean was moved, and all weak shared-junction routing limits are included by the cited compact-interior argument.

## 6. The diagonal exterior proof includes the radial endpoint

For the actual remaining geometry, (9) gives c>e>1/2. The other diagonal endpoint has physical coordinates a_B=K,b_B=1/2, with a_B<2. The original mean inequalities are
\[
 b_B-1<h<b_B,\quad e-1<h<e,\quad
 h\ge b_B(1-1/a_B),\quad h\ge e(1-1/c). \tag{14}
\]
The first lower radial concurrence inequality follows already from h>21/50 and \(b_B(1-1/a_B)<1/4\); it is not an assumed unique resultant at B.

The complete separating-axis proof in SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md applies at this physical boundary value b_B=1/2 directly, with no limit of weights or masks. Here are the endpoint checks needed for that transfer. Its actual cap and horizontal-strip routing is mask-independent, and the chosen upper radial B corner has positive original weight because omega>0. The bounds 10/7<a_B,c<2 remain valid from the same circle comparisons (the strict upper bound for a_B is already in (1)). The height bound h>2/5 is strengthened by (1). Every owner-row calculation allows b>=1/2; Certificates I--III explicitly cover the closed rectangle 1/2<=b<=3/2. In the vertical row, inequalities (18)--(20) remain valid at b=1/2, with \(T-a_B=0=(b^2-1/4)/(T+a_B)\). Certificate IV likewise includes the closed lower endpoint. The possible auxiliary tuple in Section 6 has b'>=b; if b'=b=1/2, it is the original tuple and the same strict scalar certificate applies. No proof step requires a positive gap b-1/2 after these endpoint checks. Reflection, if used for the separator, merely puts the radial half-coordinate at the other loaded endpoint; the same inequalities remain valid. Thus the actual diagonal exterior pocket is empty.

## 7. Completion

The whole incident-radial central theorem already gives central capacity zero. The B--T side pocket has capacity at most one by the full radial side-channel theorem. Sections 4--5 give capacity at most one for the C--T pocket, and Section 6 gives zero for the diagonal pocket. All three actual extras must belong to these original regions. Their total available capacity is at most two, contradiction.

This excludes the entire C-owned-bottom-axis incident-radial subfamily, including every original axis mean and all zero individual radial corner weights. The C nonaxis family retains its separate side-capacity obligation. No radial concurrence containment, motion, replacement of means, sampled angle box, Lean compilation or CI is used.
