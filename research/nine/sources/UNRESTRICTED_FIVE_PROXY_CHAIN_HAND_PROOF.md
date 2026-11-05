# Selective coordinate orders for unrestricted square packings

This note concerns physical, pairwise interior-disjoint unit squares in the
closed disk of squared radius

\[
 Q=\frac{1105}{256},\qquad r=\sqrt Q.
\]

No two-direction cover or bound on exceptional pairs is assumed. We construct
two completed coordinate orders that cover every pair, prove that both have
height at most four, and obtain an unconditional nine-square disjunction:
a full completed three-by-three rank grid, or disjoint completed chains of
sizes four and three. Added comparisons remain explicitly distinguished
from physical projection separation.

Everything below is a hand argument. The key intermediate step localizes an
arbitrary five-chain of inscribed-square projections. Such a full proxy
five-chain is not itself excluded; the stronger maximal-coordinate rule in
the selective completion is what makes its five-chains impossible.

For a square in an orthonormal coordinate frame, let

\[
 h\in[1/2,1/\sqrt2],\qquad
 k=\sqrt{1/2-h^2},\qquad g=\frac1{4h}.
\]

The coordinate projections have halfwidth \(h\); the concentric,
coordinate-aligned square of halfwidth \(g\) lies in the physical square.
Write \(c=(x,y)\) for its center. Set \(\rho=91/60\).

## 1. A unary bound for a proxy edge

**Lemma.** Every unit square contained in the closed \(Q\)-disk satisfies

\[
 |x|-g<\frac{17}{16},\qquad |y|-g<\frac{17}{16}.
 \tag{1}
\]

**Proof.** It suffices to bound \(X=|x|\). Put

\[
 a=h+k,\quad b=h-k.
\]

Then \(a\ge b\ge0\), \(a^2+b^2=1\), and \(a+b=2h\).
In physical side coordinates \((U,V)\), containment is precisely

\[
 (|U|+1/2)^2+(|V|+1/2)^2\le r^2.
\]

Moreover \(X\le a|U|+b|V|\). Maximizing this last expression over the
displayed quarter-disk gives

\[
 X\le
 \begin{cases}
 r-h,&rb\ge1/2,\\
 a\bigl(\sqrt{Q-1/4}-1/2\bigr),&rb<1/2.
 \end{cases}
 \tag{2}
\]

For completeness, set \(P=|U|+1/2\), \(W=|V|+1/2\). The unrestricted
linear maximum on the circle is at \((P,W)=r(a,b)\). It is feasible if
\(rb\ge1/2\). Otherwise the constrained maximum is at
\(W=1/2\), \(P=\sqrt{Q-1/4}\). The other constraint \(P\ge1/2\)
does not bind because \(a\ge1/\sqrt2\) and \(r>2\).

In the first branch of (2), \(h>3/5\). Indeed, if \(h\le3/5\), then

\[
 b\le\frac35-\sqrt{\frac7{50}}<\frac{23}{100}
 <\frac6{25}<\frac1{2r},
\]

where \(r<25/12\). Since \(h+1/(4h)\) is increasing for \(h\ge1/2\),

\[
 X-g\le r-h-g\le r-\frac{61}{60}
 <\frac{499}{240}-\frac{61}{60}=\frac{17}{16}.
\]

The bound \(r<499/240\) follows from
\(499^2=249001>1105\cdot225=248625\).

In the second branch,

\[
 \sqrt{Q-1/4}-1/2=\frac{\sqrt{1041}-8}{16}<\frac{91}{60}=\rho.
\]

Thus \(X-g<F(h)\), where

\[
 F(h)=\rho\left(h+\sqrt{1/2-h^2}\right)-\frac1{4h}.
\]

For \(1/2<h<1/\sqrt2\),

\[
 F''(h)=-\frac{\rho}{2k^3}-\frac1{2h^3}<-7,
 \tag{3}
\]

because \(k\le1/2\), \(h\le1/\sqrt2\), and
\(4\rho+\sqrt2>7\). Use the rational point

\[
 h_0=\frac{119}{202},\qquad k_0=\frac{79}{202}.
\]

Direct fraction arithmetic gives

\[
 F(h_0)=\frac{255347}{240380},\qquad
 F'(h_0)=\frac{10201}{14161}-\frac{182}{237}
 =-\frac{159665}{3356157},\qquad |F'(h_0)|<\frac1{20}.
\]

Integrating (3), then maximizing its quadratic upper bound, yields

\[
 F(h)\le F(h_0)+F'(h_0)(h-h_0)-\frac72(h-h_0)^2
 \le F(h_0)+\frac{F'(h_0)^2}{14}
 <F(h_0)+\frac1{5600}<\frac{17}{16}.
\]

The last comparison uses

\[
 \frac{17}{16}-F(h_0)=\frac{227}{961520}>\frac1{5600},
\]

equivalent to \(1271200>961520\). Continuity includes both endpoints of
the \(h\)-interval. Interchanging the coordinate axes proves the bound
for \(y\). \(\square\)

## 2. The three internal squares are close to diagonal

Suppose five physical squares, denoted \(A,B,C,D,E\), have ordered centers
with

\[
 x_{i+1}-x_i\ge g_i+g_{i+1}
 \quad(i=A,B,C,D).
 \tag{4}
\]

These are comparisons of their inscribed coordinate-aligned squares; they
need not be comparisons of the full physical projections.

Summing (4) and using (1) gives

\[
 2(g_B+g_C+g_D)
 \le(x_E-g_E)-(x_A+g_A)<\frac{17}{8}.
\]

Consequently

\[
 g_B+g_C+g_D<\frac{17}{16}.
 \tag{5}
\]

Each \(g_i\ge1/(2\sqrt2)\). If any one of \(h_B,h_C,h_D\) were at most
\(45/64\), its \(g_i\) would be at least \(16/45\), and

\[
 g_B+g_C+g_D\ge\frac{16}{45}+\frac1{\sqrt2}>
 \frac{16}{45}+\frac{509}{720}=\frac{17}{16}.
\]

Here \(1/\sqrt2>509/720\) is just
\(259200>259081\). This contradicts (5). Thus all three internal squares
satisfy

\[
 h_i>\frac{45}{64},\qquad
 k_i^2<\frac{23}{4096}<\frac9{1600},\qquad
 k_i<\frac3{40}\quad(i=B,C,D).
 \tag{6}
\]

Equivalently, their two absolute physical side-axis components
\(h_i+k_i\) and \(h_i-k_i\) differ by less than \(3/20\).

The outer centers also satisfy the two-sided necessary condition

\[
 -x_A-g_A>\frac3{\sqrt2}-\frac{17}{16},\qquad
 x_E-g_E>\frac3{\sqrt2}-\frac{17}{16}.
 \tag{7}
\]

Indeed, the sum of the two left sides is at least \(3/\sqrt2\), and each
is individually less than \(17/16\) by (1).

In particular \(x_A<0<x_E\). Since \(h+g\ge1\), the leftmost physical
vertex of \(A\) and rightmost physical vertex of \(E\) have horizontal
coordinate of absolute value greater than

\[
 \frac3{\sqrt2}-\frac1{16}.
\]

Their vertical coordinates therefore have absolute value less than

\[
 \eta=\frac14\sqrt{3(\sqrt2-1)},
 \tag{8}
\]

because

\[
 Q-\left(\frac3{\sqrt2}-\frac1{16}\right)^2
 =\frac{3(\sqrt2-1)}{16}.
\]

## 3. Center bands and the outer orientations

Put

\[
 \delta=\frac{17}{16}-\frac3{2\sqrt2}.
\]

Then \(0<\delta<1/500\). Positivity follows from
\(289/256>288/256\). For the upper bound, square the positive comparison
\(3/(2\sqrt2)>2121/2000\); it becomes
\(4500000>4498641\).

Using (1) at either outer endpoint, and (4) along the relevant subchain,
gives

\[
 \left|x_B+\frac1{\sqrt2}\right|<\delta,\qquad
 |x_C|<\delta,\qquad
 \left|x_D-\frac1{\sqrt2}\right|<\delta.
 \tag{9}
\]

For example,

\[
 -\frac{17}{16}+\frac1{2\sqrt2}<x_B
 <\frac{17}{16}-\frac5{2\sqrt2}.
\]

The other two bounds follow in exactly the same way, by counting the
intervening proxy halfwidths. In particular

\[
 x_B< -\frac{169}{240},
 \tag{10}
\]

because \(5/(2\sqrt2)>53/30\), equivalent after squaring to
\(5625>5618\).

The adjacent internal center heights satisfy

\[
 |y_B-y_C|>\frac7{10},\qquad |y_C-y_D|>\frac7{10}.
 \tag{11}
\]

Indeed (9) bounds either horizontal gap above by
\(1/\sqrt2+2\delta=17/8-\sqrt2<711/1000\), using
\(\sqrt2>707/500\). Two physical unit squares contain disjoint open
disks of radius \(1/2\), so their center distance is at least one. Since
\((711/1000)^2+(7/10)^2=995521/1000000<1\), (11) follows.

The two outer squares satisfy

\[
 \frac{11}{20}<h_A,h_E<\frac{49}{80}.
 \tag{12}
\]

Here is a hand verification using the unary estimates already proved.
Let \(X=|x_A|\) or \(|x_E|\), and let \(h,k,g\) refer to that square.
By (7),

\[
 X-g>p_0:=\frac3{\sqrt2}-\frac{17}{16}>\frac{127}{120}.
 \tag{13}
\]

The last strict inequality is \(3/\sqrt2>509/240\), whose square is
\(259200>259081\).

In the first branch of (2), already \(h>3/5\). If \(h\ge49/80\),
monotonicity of \(h+1/(4h)\) gives

\[
 X-g\le r-\frac{49}{80}-\frac{20}{49}
 <\frac{133}{64}-\frac{4001}{3920}
 =\frac{16581}{15680}<\frac{127}{120},
\]

contradicting (13). The last comparison is
\(1989720<1991360\); the bound \(r<133/64\) follows from
\(17680<17689\).

In the second branch, \(X-g<F(h)\). On \([1/2,11/20]\), we have
\(k>11/25\) and hence

\[
 F'(h)>-\frac\rho4+\frac{100}{121}>0.
\]

Also \(k(11/20)=\sqrt{79}/20<89/200\), so

\[
 F(11/20)<\frac{91}{60}\frac{199}{200}-\frac5{11}
 =\frac{139199}{132000}<\frac{127}{120}.
\]

Thus \(h\le11/20\) is impossible. At \(h=49/80\),
\(k=\sqrt{799}/80<17/48\), and therefore

\[
 F(49/80)<\frac{91}{60}\frac{29}{30}-\frac{20}{49}
 =\frac{93311}{88200}<\frac{93345}{88200}=\frac{127}{120}.
\]

Furthermore, at that point

\[
 F'(49/80)<-\frac{2821}{2550}+\frac{1600}{2401}<0.
\]

The strict concavity (3) makes \(F\) decreasing thereafter. This excludes
\(h\ge49/80\) and proves (12).

Several convenient geometric consequences follow:

\[
 a_A,a_E>\frac{77}{80}>\frac{24}{25},\qquad
 b_A,b_E<\frac{21}{80}<\frac4{15},
 \tag{14}
\]

where \(a=h+k\), \(b=h-k\). Indeed \(a\) decreases and \(b\) increases
for \(h\ge1/2\); at \(h=49/80\), \(k>7/20\). Also

\[
 |y_A|,|y_E|<\frac25.
 \tag{15}
\]

To see this, (12)--(13) give

\[
 X>\frac{127}{120}+\frac{20}{49}>\frac{293}{200},
\]

and the center bound \(|c|<91/60\) applies. The exact comparison

\[
 (293/200)^2+(2/5)^2-(91/60)^2=\frac{2141}{360000}>0
\]

proves (15). Since \(g>20/49>2/5\), the inscribed proxy squares of
\(A,E\) contain, in their interiors, the points
\((-17/16,0)\) and \((17/16,0)\), respectively. The horizontal
containment follows directly from \(p_0<X-g<17/16\).

## 4. Unconditional coordinate orders

For any finite packing, define the full proxy relations by

\[
 S<_x^g T\quad\Longleftrightarrow\quad x_T-x_S\ge g_S+g_T,
\]

and similarly for \(y\). The inscribed aligned squares have disjoint
interiors, so each pair is comparable in at least one of these two orders.
These are strict partial orders: every displayed gap is positive, and
transitivity follows by adding gaps.

Every two-step proxy chain already gives an actual physical comparison
between its extremes. Indeed

\[
 x_U-x_S\ge g_S+2g_T+g_U\ge\sqrt2\ge h_S+h_U.
 \tag{16}
\]

The center bound \(|c|<91/60\) implies that a full proxy order has height
at most five. A six-chain would have center span at least
\(5/\sqrt2>91/30\). In a five-chain, none of its four consecutive
comparisons can be an actual comparison in the same coordinate. One actual
gap would give total center span at least

\[
 1+\frac3{\sqrt2}>\frac{91}{30}.
 \tag{17}
\]

This last statement by itself does **not** say that the adjacent pair is
exceptional in both coordinates: it could be an actual comparison in the
other coordinate.

Now make a more selective completion, denoted \(P_x,P_y\):

* Include every actual physical \(x\)-comparison in \(P_x\), and every
  actual physical \(y\)-comparison in \(P_y\).
* For each pair with neither kind of actual comparison, choose the coordinate
  whose absolute center gap is larger, resolving a tie arbitrarily. Add its
  directed proxy comparison in that coordinate only.

The added comparison exists because the larger gap is at least
\(g_S+g_T\). Every pair is covered by \(P_x\) or \(P_y\). Each order is a
subrelation of its full proxy order, and is transitive without any further
added pairs: (16) makes the extremes of every two-step path an actual
comparison, which was already included.

## 5. The selective completed orders have height at most four

We first record the elementary orientation-dependent center separation.
If the relative angle of the physical side frames is reduced to
\(\Delta\in[0,\pi/4]\), two interior-disjoint unit squares satisfy

\[
 |c_S-c_T|\ge\frac{1+\cos\Delta+\sin\Delta}{2}.
 \tag{18}
\]

Indeed a separating axis may be chosen as a physical side normal of one
square. Along every such owned unit normal, the sum of the two support
halfwidths is exactly the right side of (18). The center distance is at
least its projection on the separating unit normal.

**Theorem.** For every packing of physical unit squares in the closed
\(Q\)-disk, the two selective completed orders \(P_x,P_y\) above each have
height at most four.

**Proof.** Suppose \(A<B<C<D<E\) is a five-chain in \(P_x\). It is a full
proxy five-chain, so all the estimates of Sections 2--3 apply. By (17), none
of its consecutive edges is actual in \(x\). By the construction of
\(P_x\), each is consequently an added edge for a pair uncovered by both
actual orders. In particular

\[
 |y_B-y_A|\le x_B-x_A.
 \tag{19}
\]

By (10) and \(x_A>-91/60\),

\[
 0<x_B-x_A<\frac{91}{60}-\frac{169}{240}=\frac{13}{16}.
\]

Together with (19), this gives

\[
 |c_B-c_A|<\frac{13\sqrt2}{16}<\frac{23}{20}.
 \tag{20}
\]

The last comparison, after squaring and multiplying by positive
denominators, is \(67600<67712\).

For the opposite bound, write the unsigned physical side angles as
\(\alpha,\beta\in[0,\pi/4]\), with
\(\cos\alpha=a_A\), \(\sin\alpha=b_A\) and
\(\cos\beta=a_B\), \(\sin\beta=b_B\). We have \(\beta>\alpha\), since
\(h_B>45/64>49/80>h_A\) and
\((\cos t+\sin t)/2\) increases on this angle interval.

If the side frames have the same chirality in the coordinate frame, then

\[
 \cos\Delta+\sin\Delta
 =2h_Ba_A-2k_Bb_A.
\]

For opposite chiralities the expression is
\(2h_Ba_A+2k_Bb_A\); reducing \(\alpha+\beta\) modulo a quarter-turn
does not change its cosine-plus-sine value. Thus in all cases (18), (6),
and (14) yield

\[
 \begin{aligned}
 |c_B-c_A|
 &\ge\frac12+h_Ba_A-k_Bb_A\\
 &>\frac12+\frac7{10}\frac{24}{25}
       -\frac3{40}\frac4{15}
 =\frac{144}{125}>\frac{23}{20}.
 \end{aligned}
\]

This contradicts (20). Interchanging the coordinate axes gives the same
conclusion for \(P_y\). \(\square\)

## 6. A global nine-square combinatorial reduction

Apply the selective construction to all nine squares. An antichain in one
completed order is a chain in the other, since every pair is covered.
Consequently both widths, as well as both heights, are at most four.

If both heights are at most three, attach to each square the pair
\((i,j)\) of lengths of longest completed chains ending there, in
\(P_x,P_y\), respectively. These pairs are distinct: a comparison in an
order strictly increases that order's chain-ending rank. The nine pairs
therefore fill \(\{1,2,3\}^2\). Each fixed \(j\)-row is a completed
\(P_x\)-chain in increasing \(i\), and each fixed \(i\)-column is a
completed \(P_y\)-chain in increasing \(j\). Indeed, two squares of equal
rank in one order cannot be comparable in that order, so the other order
must compare them. Every row's two outer squares have an actual
\(x\)-comparison, and every column's two outer squares have an actual
\(y\)-comparison, by (16).

If one completed height is four, use the nine-element poset extraction
lemma in Section 3 of
[TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md](TWO_DIRECTION_SEPARABLE_NINE_HAND_PROOF_2026_11_01.md). Its exact argument
is recalled here. Greene's finite-poset partition theorem associates to a
poset the decreasing partition

\[
 \lambda=(c_1,c_2-c_1,c_3-c_2,\ldots),
\]

where \(c_k\) is the largest union of \(k\) chains. Its conjugate is the
corresponding partition of maximal unions of antichains. This is the
classical theorem of Curtis Greene, *Some partitions associated with a
partially ordered set*, Journal of Combinatorial Theory, Series A 20
(1976), 69--79,
[DOI 10.1016/0097-3165(76)90078-9](https://doi.org/10.1016/0097-3165(76)90078-9).

For height four and width at most four, either \(c_2\ge7\), or
\(c_2\le6\). In the first case two chains realizing such a union can be
made disjoint and trimmed to sizes four and three. In the second case
\(\lambda_1=4\), all remaining parts are at most two, there are at most
four parts, and their sum is nine. Thus

\[
 \lambda=(4,2,2,1),\qquad\lambda'=(4,3,1,1).
\]

The maximum union of two antichains is seven, and two realizing
antichains can likewise be made disjoint with sizes four and three.
They are completed chains in the other coordinate order.

We have therefore obtained an unconditional disjunction for every
nine-square packing in the \(Q\)-disk:

1. All nine squares occupy a full three-by-three grid of completed ranks,
   with the row and column comparisons just specified; or
2. Seven of the squares form two disjoint completed chains of sizes four
   and three, in one coordinate direction.

This argument selects only the two extremal families actually needed.
It does not infer a simultaneous chain partition having all Greene parts.
No geometrical placement is inferred from a Greene diagram.

## 7. Scope

The completed orders are unconditional: there may be any number of physical
pairs uncovered by the two original projection orders. Every two-step path
in either completed order has an actual physical comparison between its
extremes, and both completed heights are at most four.

The theorem does not make the completed edges physical comparisons. In
particular both alternatives of Section 6 must retain their added edges,
and a physical four-plus-three terminal cannot be applied to the second
alternative without further justification. The remaining unrestricted
global caller is therefore not claimed to be closed here.

