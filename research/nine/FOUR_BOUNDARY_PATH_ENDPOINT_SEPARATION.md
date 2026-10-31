# A balanced four-body boundary path has widely separated endpoint contacts

**Status: complete hand geometric implication; root and separate independent full
hand audits passed.** Work in
\[
 R_*:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Let \(S_1,S_2,S_3,S_4\) be four distinct interior-disjoint unit squares
in \(D_R\), each physically touching the circle. Suppose consecutive
squares physically touch, and assign nonnegative weights to their actual
circle corners, with a strictly positive total on each square. Write
\[
 F_i=\sum_{z\text{ on }S_i}\lambda_{i,z}z,
 \qquad F_1+F_2+F_3+F_4=0.
\tag{2}
\]
The convention omitting the common factor2 from circle forces has no
effect on the assertion.

**Theorem.** Their endpoint centers satisfy
\[
 |c_4-c_1|>1+\sqrt2.
\tag{3}
\]
Consequently, if an arbitrary fifth unit square H physically touches
both endpoints, then **every** pair of actual points
\(P\in H\cap S_1\), \(Q\in H\cap S_4\) satisfies
\[
                              |P-Q|>1.
\tag{4}
\]
In particular (4) applies to every aggregate shared-side application
mean. If both endpoint applications are vertices of H, they must be
opposite vertices. Neither positive hub-edge weights nor any degree-two
assumption is needed for this theorem.

It is a necessary whole-family restriction for the four-load fan and
the four-load house. It is not by itself a core exclusion: an arbitrary square has pairs of
points at distance greater than1.

## 1. Every physical circle corner is less than15 degrees from its center

This bound holds more generally whenever \(R^2>2+\sqrt3\). Choose
orthonormal outward side coordinates at a physical circle corner z,
so that
\[
 z=(a,b),\quad a\ge b\ge\tfrac12,\quad a^2+b^2=q=R^2,
 \qquad c=(a-\tfrac12,b-\tfrac12).
\tag{5}
\]
The coordinate lower bounds follow by comparing the adjacent corners
with z. The positive dot product \(z\cdot c\) and the determinant give
its angle \(\delta\) from c as
\[
 \tan\delta=\frac{a-b}{2q-a-b}.
\tag{6}
\]
Put \(t=a+b\). The right side is
\(\sqrt{2q-t^2}/(2q-t)\). Its derivative has the sign of \(1-t\)
on the nondegenerate interval; here \(t>1\). It is therefore largest
at the smallest allowed t, namely b=1/2. Continuity includes a=b.
At that endpoint, with \(A=\sqrt{q-1/4}\), the ratio simplifies exactly:
\[
 \frac{A-1/2}{2q-A-1/2}
       =\frac{A-1/2}{A(2A-1)}=\frac1{2A}.
\tag{7}
\]
The window (1) has \(q>2+\sqrt3\). Hence
\[
 A>\frac{2+\sqrt3}{2},\qquad
 \tan\delta<\frac1{2+\sqrt3}=2-\sqrt3=\tan\frac\pi{12}.
\tag{8}
\]
Thus every physical circle corner has angular distance less than
\(\pi/12\) from its center direction. Both coordinates in (5)
cannot equal1/2 because of the radius lower bound, so c is nonzero.

All corners of one body lie in this same open center interval.
Consequently every nonzero nonnegative weighted circle resultant also
lies in that interval. Such a resultant is nonzero because all its
corners lie in an open cone of aperture \(\pi/6<\pi\).
This retains a physical two-corner square even if one corner's weight
vanishes.

## 2. The actual boundary-path order and the balanced resultant gap

The established angular-neighbor contact rule in
`CIRCLE_CONTACT_ANGULAR_ORDER.md` says that a physical boundary pair
follows consecutive minor center directions, each less than72 degrees
apart. Distinct boundary center directions are more than40 degrees
apart by `CENTERED_INNER_ARC.md`.

It follows that the three successive contacts of the path all traverse
the center circle in the same direction. At either internal path body,
its two distinct boundary neighbors must occupy its two neighboring
center positions. Reversing traversal there would repeat its previous
neighbor, which is not the present path. After reflecting orientation,
choose lifts
\[
 \alpha_1<\alpha_2<\alpha_3<\alpha_4<\alpha_1+2\pi
\tag{9}
\]
for the center directions, in their actual path order. Additional
physical boundary bodies, if present, remain in the complementary arc;
they cannot be between a touching pair.

Section1 puts the direction \(\beta_i\) of \(F_i\) strictly within
\(\pi/12\) of \(\alpha_i\). Since the center intervals are disjoint,
these lifts retain exactly the order in (9). In particular the closing
resultant gap is
\(2\pi-(\beta_4-\beta_1)\).

Every gap between consecutive directions of the four positive
resultants is strictly less than \(\pi\). A gap greater than \(\pi\)
would put all four vectors in an open half-plane through0, contrary
to (2). For a gap equal to \(\pi\), the other two distinct resultant
directions lie strictly inside the complementary semicircle. Their
strictly positive projections onto its inward normal, together with
nonnegative endpoint projections, again contradict (2).
Thus
\[
 \beta_4-\beta_1>\pi,
 \qquad
 L:=\alpha_4-\alpha_1>\pi-2\frac\pi{12}=\frac{5\pi}{6}.
\tag{10}
\]
No equality-corner or zero individual corner weight can turn this
strict inequality into an endpoint case.

## 3. Three physical contacts give the complementary angular bound

Every boundary center has norm
\[
                    |c_i|\ge R-1/\sqrt2>5/4.
\tag{11}
\]
For the last inequality, \(R\ge79/40\) and
\(1/\sqrt2<29/40\). Two touching unit-square centers have distance
at most \(\sqrt2\), since each center is at distance at most
\(1/\sqrt2\) from an actual common point. If \(\gamma\) is their
minor center angle, the cosine law and (11) give
\[
 \cos\gamma
 =1-\frac{|c_i-c_j|^2-(|c_i|-|c_j|)^2}{2|c_i||c_j|}
 >1-\frac{16}{25}=\frac9{25}.
\tag{12}
\]
Put \(\theta=\arccos(9/25)\). Each consecutive angle in (9) is less
than theta, so \(L<3\theta\).

Here \(\pi/3<\theta<\pi/2\). The exact triple-angle identity gives
\[
                  \cos(3\theta-\pi)=\frac{13959}{15625}.
\tag{13}
\]
This number is greater than \(\sqrt3/2\): squaring positive sides
reduces to
\[
                4\cdot13959^2>3\cdot15625^2.
\]
As \(3\theta-\pi\in(0,\pi/2)\), equation(13) implies
\[
                    3\theta-\pi<\pi/6,
               \qquad L<7\pi/6.
\tag{14}
\]
Combining (10) and (14), the minor endpoint center angle is strictly
greater than \(5\pi/6\), regardless of which side of \(\pi\)
contains L.

## 4. The metric conclusion retains every contact point

Let \(\gamma_{14}\) be that minor endpoint angle. From (11),
\[
\begin{split}
 |c_4-c_1|^2
 &= (|c_4|-|c_1|)^2+2|c_4||c_1|(1-\cos\gamma_{14})\\
 &>\frac{25}{8}\left(1+\frac{\sqrt3}{2}\right)
   =\frac{25(2+\sqrt3)}{16}
   >(1+\sqrt2)^2.
\end{split}
\tag{15}
\]
The last strict comparison is equivalent to
\(2+25\sqrt3>32\sqrt2\). Squaring once reduces it to
\(100\sqrt3>169\), which follows from \(30000>28561\).
This proves (3).

For arbitrary actual P,Q in (4), both endpoint-center distances obey
\( |c_1-P|,|c_4-Q|\le1/\sqrt2\). The triangle inequality gives
\[
 1+\sqrt2<|c_4-c_1|
       \le |c_1-P|+|P-Q|+|Q-c_4|
       \le\sqrt2+|P-Q|.
\tag{16}
\]
Hence \(|P-Q|>1\). An aggregate shared-side mean belongs to the
actual closed intersection segment, so it is automatically included.
There is no fixed-mean or singleton assumption.

The two vertices of a unit square have distance0,1 or \(\sqrt2\).
Thus endpoint vertex applications are opposite. More generally the two
full physical endpoint-contact sets are at distance greater than1:
compactness allows (4) to be minimized over their product. They cannot
meet the same unit side of H.

## 5. Exact scope

The theorem uses the full positive circle-load balance of the four
boundary path bodies and their actual circle masks. It applies to the
four-load fan, whose clear hub touches both endpoints, with all four
completion squares retained. It does not assert that the four hub
forces balance merely from the geometric hypotheses, and it does not
replace the local force/torque equations of either internal degree-three
body by a degree-two concurrence equation.

For the house load set {1,2,3,4}, the four boundary bodies form the
actual path3--1--4--2. The common zero-load hub5 touches both endpoint
bodies3 and2. Thus every pair of its actual endpoint applications also
has distance greater than1. Reflection covers {2,3,4,5}. Its hub has
three positive edges, not four; no absent fourth spoke is introduced.

Closing the fan still requires showing that its complete physical
positive certificate cannot realize the remaining endpoint-contact
sets at distance greater than1, or proving a uniform capacity of at
most3 for all completions of those surviving cores. No numerical
certificate, Lean compilation or CI is used here.
