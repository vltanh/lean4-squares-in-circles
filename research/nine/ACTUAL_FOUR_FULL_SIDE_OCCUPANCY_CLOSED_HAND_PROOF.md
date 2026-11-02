# Complete actual-four closure when both side columns are full

November 2, 2026. Complete hand caller for the widened five-square cap.
The original nine physical squares and all their pair constraints are
retained. The hand scalar reductions have an exact rational arithmetic
replay; the widened cap has its separately verified complete finite
tables. No Lean or CI.

Put

\[
 Q=1105/256,\quad l=29/60,\quad u=13/12,\quad
 \rho=91/60,\quad \zeta=2211/4000,
 \quad J=23/150,\quad A_0=18911/59520.
\]

## 1. Exact scope and normalization

Suppose nine original unit squares form a strict counterexample
\(q<Q\), and four of them form an actual horizontal projection chain
\(M_0<_xM_1<_xM_2<_xM_3\) whose consecutive center comparisons are
also horizontal cone comparisons.

Suppose the five outsiders have column counts \((L,C,R)=(2,1,2)\):
two have \(x\le-l\), one has \(|x|<l\), and two have \(x\ge l\).
The side-capacity theorem permits common expansion of all centers until
the largest squared corner norm is Q, retaining all frames. The normalized
closed squares are disjoint, and both actual and cone main comparisons
remain valid. The adjusted original endpoint span satisfies

\[
 D=x_3-x_0-h_0-h_3>2.
 \tag{1}
\]

All four original side outsiders remain in their side bands. The sole
central outsider cannot expand into a side band, since that would give
three side outsiders and violate the normalized three-marker capacity.
Thus the same \((2,1,2)\) occupancy is retained.

Each side contains its inner main and two outsiders, occupying its three
distinct markers in their actual center-height order. The full-side
height theorems give the three possible main positions:

\[
 \begin{array}{c|c}
 \text{main position}&\text{main center height}\\ \hline
 \text{bottom}&y_M<-3/5\\
 \text{middle}&|y_M|<7/20\\
 \text{top}&y_M>3/5.
 \end{array}
 \tag{2}
\]

The main cone comparison gives \(|y_2-y_1|<31/30\), so opposite
extremes are impossible: their height difference would exceed \(6/5\).
Up to horizontal and vertical reflection, the complete remaining list is

\[
 (\text{middle},\text{middle}),\quad
 (\text{bottom},\text{bottom}),\quad
 (\text{bottom},\text{middle}).
 \tag{3}
\]

In each case we produce three distinct original outsiders L,F,R with

\[
 x_L\le0\le x_R,\quad |x_F|<l,\quad
 y_L,y_R\ge3/5,\quad y_F-h_F\ge1/10.
 \tag{4}
\]

These are exactly the caller hypotheses of
`WIDENED_JOINT_FIVE_SQUARE_CAP.md`, together with the original endpoint
bounds from the actual four-chain. That complete cap gives

\[
 46D+27/2\le211/2,
\]

and hence \(D\le2\), contradicting (1). No short-chain edge, separator
owner, or central frame is added to the original hypotheses.

## 2. Routing the sole central outsider

Write F for the original central outsider. It is either above both inner
main centers or below both. Here is the short physical argument retaining
the main cone comparison.

Since \(x_1<-l<x_F<l<x_2\), let
\(p=x_F-x_1\) and \(q=x_2-x_F\). The correlated main bands
\(x_1>h_1-61/60\), \(x_2<61/60-h_2\), and \(h_i+g_i\ge1\)
give \(p-g_1<1/2\), \(q-g_2<1/2\). The radius-one-half disk of F
therefore has vertical center gap greater than \(g_i\) from each inset.
One of p,q is less than \(31/60\); for that inset its vertical gap is
greater than \(g_i+49/100\), by the positive-root comparison
\(1/4-1/900>(49/100)^2\). If F were between the two main heights,
their difference would consequently exceed

\[
 g_1+g_2+49/100>30/31+49/100>31/30,
\]

contradicting the retained inner main cone comparison. This also excludes
equality with either main height.

## 3. Both mains in the middle

Reflect vertically so F is above both mains. The adjacent-proxy barrier
for the original inner mains gives

\[
 y_F-h_F>\min(y_1,y_2)+869/1860
                 >-7/20+869/1860=109/930>1/10.
 \tag{5}
\]

Choose L and R to be the upper outsider in their respective full sides.
Their same-half-plane main clearances give

\[
 y_L,y_R>-7/20+97/100=31/50>3/5.
\]

Thus all conditions (4) hold in this complete pattern.

## 4. Both mains at the bottom

Write U_L,U_R for the lower outsiders in the two full sides and H_L,H_R
for the higher outsiders. These are four distinct original units. The
local full-side conclusions of `ZERO_SIDE_PROXY_EDGE_AND_TOP_HAND_PROOF.md`
give, for i=L,R,

\[
 -113/600<y_{U_i}<7/16,\quad
 l\le|x_{U_i}|<\zeta,\quad |x_{U_i}|-g_{U_i}<J,
\]

\[
 y_{U_i}+g_{U_i}>A_0>3/10,
 \qquad y_{H_i}>367/600>3/5.
 \tag{6}
\]

F cannot be below both inner mains: the clearance from the main in its
own horizontal half-plane would give
\(y_F<-3/5-97/100<-\rho\). Therefore F is above both.
The main cone lower bound \(y_i>-139/120\), and the stronger central
clearance \(59/60\), give

\[
                             y_F>-7/40.
 \tag{7}
\]

Choose U to be the zero unit on F's own side. Its horizontal center gap
from F is below \(\zeta\), and \(\zeta^2<11/36\). The two original
unit disks therefore give \(|y_F-y_U|>5/6\). If F were below U, then
\(y_F<7/16-5/6=-19/48\), contrary to (7). Hence

\[
 y_F>y_U+5/6>-113/600+5/6=129/200.
 \tag{8}
\]

In particular F is above both zero centers, although the next section
argument needs only (8).

### 4.1. One horizontal section forces F's whole floor

Suppose, for contradiction, that \(T=y_F-h_F\le1/10\). At height
\(v=3/10\), F has a nondegenerate horizontal section, since
\(T<v<y_F\). Its depth above a bottom vertex is
\(d=v-T\ge1/5\), with \(d<h_F\).

For any orientation of a unit square, that section has length at least
\(\min(2d,1)\), and hence at least \(2/5\). To see this explicitly,
write \(a\ge b\ge0\) for its side components. For b positive, the
section length is \(d/(ab)\) when \(d\le b\), and \(1/a\) when
\(b\le d\le h_F\). The aligned case has length one. Since
\(ab\le1/2\), the stated lower bound follows.

At the same height v, both aligned zero insets contain the interiors of
their full horizontal projections. Their tops exceed \(A_0>3/10\),
and their bottoms are below

\[
 7/16-g_{U_i}<7/16-1/3=5/48<3/10.
\]

Their middle horizontal gap is less than \(2J=23/75<2/5\). Thus F's
section cannot lie wholly in that gap.

Nor can it lie wholly to the left of both insets. In the bottom-right
vertex orientation its right endpoint is at least \(x_F\ge-l\).
In the bottom-left orientation, if \(d\ge b\) its right endpoint is
greater than \(x_F\). If \(d\le b\), its right endpoint is at least

\[
 x_F-k_F+d\ge-l-1/2+1/5=-47/60.
\]

The left inset's outer left endpoint is less than
\(-l-1/3=-49/60\), so all these bounds exclude the exterior left
component. Reflection excludes the exterior right component. The aligned
case is immediate from its section length one and endpoints
\(x_F\pm1/2\).

The section of F must consequently intersect the interior of an aligned
zero inset at height v. This is a physical interior overlap, a contradiction.
We have proved

\[
                              y_F-h_F>1/10.
 \tag{9}
\]

Choose L=H_L and R=H_R. Equations (6) and (9) supply (4) and close
the entire equal-bottom pattern. Vertical reflection covers equal top.

## 5. Left main at bottom, right main in the middle

Let U be the lower left outsider, H_L the higher left outsider, and let
H_R and B_R be respectively the right upper and lower outsiders.
Thus the two previously unselected outsiders are retained as U and B_R.

The main ranges are

\[
 y_1<-3/5,\qquad -7/20<y_2<7/20.
\]

`ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md`, applied
with the original B_R, excludes F below both mains. Section 2 therefore
places F above both. The high shoulder bounds are already available:

\[
 y_{H_L}>367/600>3/5,
 \qquad y_{H_R}>-7/20+97/100=31/50>3/5.
 \tag{10}
\]

It remains to prove the whole floor of F. We keep the aligned insets of
the original U and M2 and the single physical orientation of F.

### 5.1. The two original proxy tops and their inner gap

Write the left zero center as \((-Z,y_U)\), with halfwidth \(g_U\).
The local zero theorem supplies

\[
 l\le Z<\zeta,\quad |y_U|<7/16,\quad Z-g_U<J,
 \quad y_U+g_U>A_0.
 \tag{11}
\]

For M2, the correlated actual-four bounds give

\[
 x_2-g_2<1/60,\qquad x_2+g_2>59/60,
 \qquad y_2+g_2>B_0:=83/620.
 \tag{12}
\]

Suppose \(T=y_F-h_F\le1/10\). Put

\[
 c_L=A_0-1/10=12959/59520,
 \qquad c_R=B_0-1/10=21/620.
 \tag{13}
\]

Both are positive, \(c_L>1/6\), and

\[
 4c_Lc_R-(17/100)^2=45993/76880000>0.
 \tag{14}
\]

Let \((X,Y)\) be F's center and write
\(a\ge b\ge0\), \(a^2+b^2=1\), \(h=(a+b)/2\), \(k=(a-b)/2\)
for its one original physical frame. We will not choose its orientation
independently for the two proxy pairs.

### 5.2. Every right-proxy separator is upward and points left

Let \(D_R=x_2-X>0\), \(V_R=Y-y_2>0\). Equations (12)--(13) give

\[
 D_R-g_2<1/60-X\le1/2,
 \qquad V_R-g_2<h-c_R.
 \tag{15}
\]

The coordinate horizontal and vertical axes cannot separate F from this
inset. A side-axis separator must therefore be owned by F, where its
support is one half. If its vertical component were nonpositive, its
center projection would be at most \(|n_x|D_R\), requiring
\(|n_x|(D_R-g_2)\ge1/2+g_2|n_y|\); (15) makes that impossible.
Its vertical component is thus positive.

Its horizontal component must be negative. To see this, an upward
F-owned axis pointing right would have absolute components either
\((a,b)\) or \((b,a)\). The first alternative has proxy-adjusted
center projection less than \(bh\le1/2\). For the second it is less
than

\[
 ah-b(D_R+g_2)=1/2+b\{k-(D_R+g_2)\}\le1/2,
\]

because \(D_R+g_2>59/60-l=1/2\ge k\). Both are less than the
required one half. Vertical axes were already excluded.

An aligned F would now have no possible side axis, so \(b>0\). Put
\(t=b/a\in(0,1]\). The two remaining right-axis possibilities are
\((-a,b)\) and \((-b,a)\). Using
\(1/2-bh=ak\) and \(1/2-ah=-bk\), their necessary inequalities give

\[
 X<1/60-k-tc_R
 \quad\hbox{or}\quad
 X<1/60+k-c_R/t.
 \tag{16}
\]

In either case \(X<4/15\). For the second use
\(k\le(1-t)/2\) and

\[
 t/2+c_R/t\ge\sqrt{2c_R}>1/4,
 \qquad 2c_R-1/16=13/2480>0.
\]

The first bound in (16) is smaller than \(1/60\).

### 5.3. F is above the original left zero unit

Since \(D_R-g_2<1/2\), the radius-one-half disk of F and the right
inset give \(V_R>g_2\), so \(Y>B_0\). If \(Y\le y_U\), their
original unit disks would have squared center distance less than

\[
 (\zeta+4/15)^2+(7/16-B_0)^2<1.
 \tag{17}
\]

Indeed \(0\le X+Z<4/15+\zeta\) by (11), (16), while
\(0\le y_U-Y<7/16-B_0\). The strict rational comparison in (17)
is reproduced by the companion arithmetic checker. Thus \(Y>y_U\).

Let \(D_L=X+Z\ge0\) and \(V_L=Y-y_U>0\). We now have

\[
 D_L-g_U<X+J<4/15+23/150=21/50<1/2,
 \qquad V_L-g_U<h-c_L.
 \tag{18}
\]

As on the right, both coordinate axes fail, and every genuine F-owned
separator has positive vertical component. Its horizontal component must
be positive. An inward axis with vertical component b has adjusted
projection below \(bh\le1/2\). For an inward axis with vertical
component a, the adjusted projection is below

\[
 1/2+b(k-D_L-g_U)-ac_L<1/2,
\]

since \(g_U>1/3\), \(D_L\ge0\), \(k\le1/2\), and
\(t(k-D_L-g_U)<1/6<c_L\). This covers both chiralities.

### 5.4. The same original F frame makes the two inequalities incompatible

The left separator points up and right, and the right separator up and
left. They are F's two different orthogonal side axes. Thus there are
exactly two component assignments, including the diagonal case t=1.

If the left axis has components \((a,b)\), the right has \((-b,a)\).
Equations (13), (15), and (18) imply

\[
 D_L-g_U>k+tc_L,
 \qquad D_R-g_2>-k+c_R/t.
\]

Their sum gives

\[
 G:=D_L+D_R-g_U-g_2>tc_L+c_R/t
                              \ge2\sqrt{c_Lc_R}>17/100.
 \tag{19}
\]

For the other component assignment, the sum is
\(G>c_L/t+tc_R\), with the same lower bound. The last strict
comparison in (19) is (14). But the actual proxy edges in (11)--(12)
give

\[
 G=Z-g_U+x_2-g_2<J+1/60=17/100.
\]

This contradiction proves \(y_F-h_F>1/10\). Taking L=H_L and R=H_R
in (10) supplies (4) and closes the entire mixed pattern.

## 6. Completion and dependency boundary

The marker list (3) is exhaustive, and Sections 3--5 supply the same
original-square caller (4) in every remaining pattern. The widened cap
then contradicts the strict original endpoint span (1). Therefore a
strict counterexample with an actual cone four-chain cannot have outsider
occupancy \((2,1,2)\).

The proof retains all five outsiders. In the mixed case, B_R excludes the
lower central placement and U forces its whole floor. In the equal-extreme
case, both zero units force the central floor, while both higher outsiders
are the shoulders. No missing square or original pair is replaced by an
independent proxy configuration.

The new hand inputs are `ZERO_SIDE_PROXY_EDGE_AND_TOP_HAND_PROOF.md` and
`ACTUAL_FOUR_MIXED_FULL_SIDES_LOWER_CENTRAL_EXCLUSION.md`. Their other
geometric dependencies are the already proved actual-four side marker,
inner-clearance, side-pair cap, main-height, and adjacent-proxy theorems.
The widened five-square terminal is a separate complete hand/table theorem;
its 3,453 strict interval rows and seven local analytic leaves must retain
their independent successful replay record.

This closes the whole stated occupancy family. It does not by itself close
the other outsider column counts or all of `000/11`.
