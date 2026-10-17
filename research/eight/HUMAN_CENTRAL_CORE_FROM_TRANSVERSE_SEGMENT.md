# A hand proof of the central one-twelfth core

**Theorem.** Suppose eight closed unit squares with pairwise disjoint open
interiors lie in a disk of squared radius at most

\[
Q=\frac{9789}{2500}.
\]

Then exactly one square contains the entire closed disk of radius \(1/12\),
concentric with the containing disk, in its open interior. Every other
closed square has distance strictly greater than \(1/12\) from the disk
center.

This proof uses the analytic central-existence theorem at squared radius
\(98/25\) in `HUMAN_GLOBAL_GEOMETRY_CLOSURE.md`, and the three explicit
polynomial lemmas in
`CENTRAL_BAND_COMMON_POINT_LEMMAS.md`.
That companion note prints all 19 fixed Bernstein rows used below. The
remaining geometry, calculus, and scalar arithmetic are given here.

The theorem is asserted at \(9789/2500\), which suffices for the sharp
eight-square proof. No assertion at the larger ceiling \(98/25\) is needed.

## 1. A small positive central depth follows from the radius buffer

Take the disk center as the origin. The analytic central-existence theorem
gives a unique square containing the origin in its open interior. Rotate
and reflect coordinates so that its center is \((a,u)\), where

\[
0\le u\le a<\frac12.
\]

Its minimum distance from the origin to a side is
\(\delta=1/2-a\). We first prove

\[
\delta>\frac1{1000}. \tag{1}
\]

Otherwise, let \(p\) be a nearest point on its boundary, so that
\(|p|=\delta\). No square contains \(p\) in its open interior. This is
true for the central square because \(p\) is on its boundary. It is true
for every other square because an open neighborhood of \(p\) would
contain points in the central square's interior.

If \(R\le\sqrt Q<2\) is the original radius, all eight squares lie in
the disk centered at \(p\) of radius \(R+\delta\). But

\[
(R+\delta)^2
<Q+\frac4{1000}+\frac1{10^6}
=\frac{3919601}{10^6}
<\frac{98}{25}.
\]

The central-existence theorem at this new disk center says that one
square contains \(p\) in its open interior, a contradiction. This proves
(1).

For any other square, rotate its own axes and change their signs so that
its center has coordinates \((A,B)\) with \(A\ge B\ge0\). Since the
open disk of radius \(\delta\) is inside the central square, this square
avoids that disk. In particular \(A>1/2\), and

\[
\delta^2
\le (A-1/2)^2+\max(B-1/2,0)^2
\le 2(A-1/2)^2.
\]

Consequently

\[
A\ge\frac12+\frac{\delta}{\sqrt2}.
\tag{2}
\]

Here \(1/\sqrt2>7/10\). Equation (1) therefore gives
\(A>5007/10000\). If \(a\le9/20\), the stronger depth
\(\delta\ge1/20\) gives \(A>107/200\).

## 2. Three one-square geometric facts

Use the following constants:

\[
L=\frac{11}{12},\qquad c=\frac7{20},\qquad
r=\sqrt{L^2+c^2},\qquad
r^2=\frac{1733}{1800}<1,
\qquad \phi=\arctan\frac cL.
\tag{3}
\]

The companion polynomial proof gives these three facts for a square in
the disk of squared radius \(Q\). Its primary own-frame center coordinate
is the larger absolute center coordinate in its own square axes.

1. If the primary coordinate is greater than \(1/2\), then, after making
   its center ray horizontal, the entire segment
   \[
   V=\{(L,y): -c\le y\le c\}
   \tag{4}
   \]
   lies in its open interior.
2. If the primary coordinate is greater than \(5007/10000\), then any
   two such squares with disjoint interiors have smaller center angle
   greater than \(3741/5000\).
3. If the primary coordinate is at least \(107/200\), the corresponding
   smaller center angle is greater than \(19/25\).

For clarity, the angle facts come from actual common points, not from
an estimate of center distances. A square whose center ray is within
\(3741/10000\) of a fixed ray contains the point of that ray at radius
\(10007/10000\). In the second band the angle is \(19/50\) and the
point radius is \(41/40\). Applying the assertion to the bisector of
two center rays proves each strict pair-angle bound.

## 3. How a rectangle forbids directions of the common segment

Let \(L\le A<r\), and consider the first-quadrant rectangle

\[
T_A(y)=[0,A]\times[0,y],\qquad y\ge0.
\]

Put \(k_A=\sqrt{r^2-A^2}\), and define the following continuous function:

\[
F_A(y)=
\begin{cases}
\displaystyle
\arctan\frac yA+
\arccos\frac L{\sqrt{A^2+y^2}},&0\le y\le k_A,\\[5pt]
\displaystyle
E(y):=\arcsin\frac yr+\phi,&k_A\le y\le L,\\[5pt]
\displaystyle
\frac\pi2+\arccos\frac Ly,&L\le y\le r,\\[5pt]
\displaystyle
\frac\pi2+\phi,&y\ge r.
\end{cases}
\tag{5}
\]

Every rotated segment \(R_\beta V\) with

\[
0\le\beta\le F_A(y)
\tag{6}
\]

meets \(T_A(y)\). Here is a direct verification of this interval
assertion, including its connectedness.

If a point \(p\in T_A(y)\) satisfies \(|p|\le r\) and
\(p\cdot e_\beta\ge L\), the radial multiple

\[
q=\frac L{p\cdot e_\beta}p
\]

belongs to \(T_A(y)\), has \(q\cdot e_\beta=L\), and has transverse
coordinate of absolute value at most \(c\). Thus \(q\in R_\beta V\).

If \(y<L\), every direction from 0 through
\(\theta_0=\arcsin(y/L)\) is already covered by the points
\(L e_\beta\in T_A(y)\). For the first line of (5), use
\(p=(A,y)\); for the second, use
\(p=(\sqrt{r^2-y^2},y)\). In either case \(p\) is in the rectangle
and in the disk of radius \(r\). The interval on which
\(p\cdot e_\beta\ge L\) has right endpoint exactly the stated
\(F_A(y)\), and contains the direction of \(p\). That direction is
at most \(\theta_0\). Its interval therefore joins the interval already
covered, proving (6) without a gap.

If \(y\ge L\), the points \(L e_\beta\) cover \([0,\pi/2]\).
The additional interval follows from the vertical point
\(p=(0,\min(y,r))\). This proves the remaining two lines of (5).

Reflecting in the horizontal axis now shows that, for

\[
T=[0,A]\times[-d,1-d],\qquad 0\le d\le\frac12,
\]

the entire interval

\[
[-F_A(d),F_A(1-d)]
\tag{7}
\]

consists of rotations whose segments meet \(T\). Its width is
\(F_A(d)+F_A(1-d)\).

We will need the following two estimates:

\[
\begin{aligned}
F_L(d)+F_L(1-d)&>\frac{347}{200},\tag{8}\\
F_{19/20}(d)+F_{19/20}(1-d)&>\frac{899}{500},\tag{9}
\end{aligned}
\qquad 0\le d\le\frac12.
\]

## 4. The first forbidden-width estimate

For \(A=L\), the first line of (5) simplifies to

\[
F_L(y)=2\arctan(y/L),\qquad 0\le y\le c.
\tag{10}
\]

Write \(d_0=1-L=1/12\).

### 4.1. The range \(0\le d\le d_0\)

If \(1-d\ge r\), equation (5) gives a width at least
\(\pi/2+\phi>157/100+9/25\), which is greater than \(347/200\).

For \(L\le1-d\le r\), differentiate the sum in (5):

\[
\frac{d}{dd}\{F_L(d)+F_L(1-d)\}
=\frac{2L}{L^2+d^2}
-\frac{L}{(1-d)\sqrt{(1-d)^2-L^2}}
\le\frac2L-\frac L{rc}<0.
\]

The final inequality is equivalent to \(L^2>2rc\); its square is a
strict rational inequality. Therefore the minimum in this range is
at \(d=d_0\), where the width is

\[
\frac\pi2+2\arctan\frac1{11}
>\frac{157}{100}+\frac9{50}
>\frac{347}{200}.
\tag{11}
\]

### 4.2. The range \(d_0\le d\le c\)

The sum is now

\[
W(d)=2\arctan(d/L)+E(1-d).
\]

Its derivative has the sign opposite to

\[
P(d)=d^4+6L^2d^2-8L^2d+4L^2-3L^4-4L^2c^2.
\tag{12}
\]

Indeed this follows by comparing the two positive terms in
\(W'=2L/(L^2+d^2)-1/\sqrt{r^2-(1-d)^2}\) and squaring.
On the entire interval,

\[
P'(d)\le4c^3+12L^2c-8L^2<0.
\]

The two exact evaluations

\[
P(1379/10000)>0,
\qquad P(69/500)<0
\tag{13}
\]

therefore locate the unique minimum of \(W\) between those two
rational numbers. Since both \(2\arctan(d/L)\) and \(E(y)\) are
increasing in their own arguments, at that minimum

\[
W(d)
\ge 2\arctan\frac{1379/10000}{L}+E(431/500)
>\frac{149}{500}+\frac{1437}{1000}
=\frac{347}{200}.
\tag{14}
\]

The strict scalar inequalities are displayed in Section 6.

### 4.3. The range \(c\le d\le1/2\)

Both terms use \(E\). The function \(\arcsin(y/r)\) is convex for
\(0\le y<r\). Hence

\[
E(d)+E(1-d)\ge2E(1/2)
>2\frac{899}{1000}
>\frac{347}{200}.
\tag{15}
\]

Together, these three ranges prove (8).

## 5. The stronger estimate when the central square reaches \(19/20\)

Take \(A=19/20\). In this case

\[
k_A^2=\frac{217}{3600},\qquad
\frac1{12}<k_A<\frac14,
\qquad A^2-L^2=\frac{14}{225}.
\tag{16}
\]

### 5.1. The range \(0\le d\le1/12\)

The first term is at least \(F_A(0)=\arccos(L/A)>1/4\). The second
is at least \(\pi/2\). Their sum is therefore greater than
\(1/4+157/100>899/500\).

### 5.2. The range \(1/12\le d\le k_A\)

Differentiating the first line of (5) gives

\[
F_A'(d)=
\frac{A+Ld/\sqrt{A^2+d^2-L^2}}{A^2+d^2}.
\]

The ratio \(d/\sqrt{A^2-L^2+d^2}\) increases with \(d\). At
\(d=1/12\) it is \(5/\sqrt{249}>5/16\). Also
\(A^2+d^2\le r^2\). Consequently

\[
F_A'(d)>
\frac{A+5L/16}{r^2}>\frac54.
\tag{17}
\]

The point \((A,1/12)\) is inside the disk of radius \(r\), and

\[
A\cos(9/25)+\frac1{12}\sin(9/25)>L.
\]

The geometric argument of Section 3, or the first line of (5), yields
\(F_A(1/12)>9/25\). Using (17), the width is therefore greater than

\[
\frac9{25}+\frac54\left(d-\frac1{12}\right)+E(1-d).
\tag{18}
\]

This last expression decreases on \([1/12,1/4]\), because

\[
r^2-(1-d)^2
\le r^2-\frac9{16}
=\frac{1441}{3600}<\frac{16}{25}.
\]

Its value at \(1/4\) is greater than

\[
\frac9{25}+\frac5{24}+\frac{123}{100}
=\frac{1079}{600}
>\frac{899}{500},
\tag{19}
\]

where \(E(3/4)>123/100\).

### 5.3. The range \(k_A\le d\le1/2\)

Both \(d\) and \(1-d\) lie in \([k_A,L]\). Convexity again gives

\[
F_A(d)+F_A(1-d)=E(d)+E(1-d)
\ge2E(1/2)>\frac{899}{500}.
\]

This completes (9).

## 6. The short scalar arithmetic

All uses of trigonometric numerical bounds above can be checked with
the following explicit rational inequalities. Put

\[
S_9(x)=x-\frac{x^3}{6}+\frac{x^5}{120}
-\frac{x^7}{5040}+\frac{x^9}{362880},
\]

\[
C_{10}(x)=1-\frac{x^2}{2}+\frac{x^4}{24}
-\frac{x^6}{720}+\frac{x^8}{40320}-\frac{x^{10}}{3628800}.
\]

For the arguments below, alternation gives
\(\sin x<S_9(x)\) and \(\cos x>C_{10}(x)\).
The following table consists of rational substitutions:

| \(x\) | \(y\) | Lower bound for \(y-LS_9(x)+cC_{10}(x)\) |
|---:|---:|---:|
| \(1437/1000\) | \(431/500\) | \(1/5000\) |
| \(899/1000\) | \(1/2\) | \(1/3000\) |
| \(123/100\) | \(3/4\) | \(3/1000\) |

Since \(L\sin x-c\cos x\) is strictly increasing between 0 and
\(\pi/2\), and its value at \(x=E(y)\) is \(y\), these three rows
prove all three stated lower bounds for \(E\).

The inequality \(\arctan x>x-x^3/3\), for \(0<x<1\), gives

\[
2\arctan\frac{1379/10000}{L}>\frac{149}{500},\qquad
2\arctan\frac1{11}>\frac9{50},\qquad
\phi>\frac9{25}.
\]

The other comparisons in Sections 4 and 5 are the rational inequalities

\[
\begin{gathered}
L^4>4r^2c^2,\qquad
4c^3+12L^2c-8L^2<0,\\
P(1379/10000)=\frac{112414051807787}{270000000000000000}>0,\\
P(69/500)=-\frac{1525661}{13183593750}<0,\\
A+\frac{5L}{16}>\frac54r^2,\qquad
1-\frac{(1/4)^2}{2}>\frac LA,\\
A\left(1-\frac{(9/25)^2}{2}\right)
+\frac1{12}\left(\frac9{25}-\frac{(9/25)^3}{6}\right)>L.
\end{gathered}
\]

For the bounds on \(\pi\), Machin's identity and the first two
alternating arctangent terms give

\[
\pi=16\arctan(1/5)-4\arctan(1/239)
>16\left(\frac15-\frac1{375}\right)-\frac4{239}
>\frac{157}{50}.
\]

The upper bound follows, for example, from the elementary identity

\[
\frac{22}{7}-\pi
=\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx>0.
\tag{20}
\]

Polynomial division verifies this identity directly. These displayed
substitutions are also transcribed in
`verify_hand_core_scalar_arithmetic.py`; the program is not needed to
interpret any premise or to discover any case.

## 7. Seven exterior rays cannot avoid a shallow central square

Suppose, contrary to the desired conclusion, that \(a\ge5/12\).
The central square is

\[
[a-1/2,a+1/2]\times[u-1/2,u+1/2].
\]

Write \(d=1/2-u\), so \(0<d\le1/2\).

If \(5/12\le a\le9/20\), this square contains
\([0,L]\times[-d,1-d]\). By (7) and (8), there is a connected
interval of center-ray directions of width greater than \(347/200\)
for which the corresponding rotated segment meets the central square.
No exterior center ray can belong to that interval. Indeed its
rotated segment is in the exterior square's open interior, so an
intersection even with the central square's boundary would force
intersection with the central square's open interior nearby.

Equation (2) gives the primary-coordinate bound \(A>107/200\) in
this band. Therefore each of the six gaps between the seven exterior
center rays, when ordered in the complementary arc, is greater than
\(19/25\). Their span is greater than \(114/25\). Adding the
forbidden interval would require a total angle greater than

\[
\frac{347}{200}+\frac{114}{25}
=\frac{1259}{200}
>\frac{44}{7}>2\pi,
\]

which is impossible. The exact reserve over \(44/7\) is \(13/1400\).

If \(9/20\le a<1/2\), the central square instead contains
\([0,19/20]\times[-d,1-d]\). The forbidden width is greater than
\(899/500\) by (9). The small reserve (1) gives the primary bound
\(A>5007/10000\), so the six gaps have total greater than
\(12(3741/10000)\). This time the required total angle is greater than

\[
\frac{899}{500}+12\frac{3741}{10000}
=\frac{7859}{1250}
>\frac{44}{7}>2\pi.
\]

The reserve over \(44/7\) is \(13/8750\). This is again impossible.

Both bands are excluded. Hence \(a<5/12\).

## 8. The strict core conclusion

Every point \(p\) of the closed disk \(|p|\le1/12\) has distance
less than \(1/2\) from the central center in each of its two coordinate
directions, since

\[
|p_x-a|\le\frac1{12}+a<\frac12,
\qquad
|p_y-u|\le\frac1{12}+u\le\frac1{12}+a<\frac12.
\]

Thus the entire closed disk lies in the central square's open interior.
No other closed square can meet this disk: any such common point is
approximated by interior points of that other square while staying
inside the central open square. Finally, compactness of every closed
square makes its distance from the origin attained. Its distance is
therefore strictly greater than \(1/12\), as claimed.

### Independent arithmetic check

The companion polynomial note's 19 displayed rows, comprising 115
positive Bernstein coefficients, were independently checked by exact
polynomial identities and direct Bernstein-basis evaluation. The
conversion formula of its generating script was not reused.
`verify_central_band_tables_independently.py` also checks the note-to-table
transcription and the two Taylor enclosures. The scalar calculations
above passed the separate 30-comparison transcription check.

These checks confirm the printed finite arithmetic. The proof itself is
the geometric deductions, the three elementary calculus partitions,
and the explicit polynomial and scalar identities in the two notes.
