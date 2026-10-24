# A radial D leaf and a radial S leaf cannot share a triangle articulation

**Status: complete exact hand proof; root and separate independent hand audits passed.**
Let a positive component consist of a triangle A,B,C and two pendant
unit squares, both attached to A. If one leaf is radial D and the other
is radial S, the core is impossible throughout

\[
             \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

The proof includes the whole articulation domain, every circle-corner
mask of B and C, and all positive weights and actual contact types.
It excludes the core itself, retaining all four completion squares.
The D/D branch and the distinct-articulation layout remain separate.

## 1. Common geometry and the acute-load obstruction

Put

\[
 r=R-\sqrt2,\qquad s=1-r,\qquad
 d=\sqrt{R^2-\tfrac14}-1,
 \qquad T=d+1.
\tag{2}
\]

We use the following exact uniform bounds:

\[
 0<r<1,\qquad r>\frac{67}{120},\qquad
 0<s<\frac9{20},\qquad d>\frac{91}{100},
 \qquad R<\frac{25}{12}.
\tag{3}
\]

The lower bound for r follows from R at least 79/40 and
\(\sqrt2<17/12\). The upper radius bound follows by squaring.
The bound for d is the lower-endpoint calculation in
`S_LEAF_TRIANGLE_EXCLUSION.md`: equivalently
\(R^2>1/4+(191/100)^2\). All inequalities in (3) are strict
even at the endpoints in (1).

Rotate the D leaf east. The selected nonradial point-normal convention
and the radial bridge theorem give the full aligned articulation
domain

\[
            A=[-s,r]\times[t-1/2,t+1/2],
            \qquad |t|<1/2.
\tag{4}
\]

The D application is \((r,0)\), in the relative interior of A's
right side. The S leaf has fixed radial application \(p=d n\),
where n is its unit circle-resultant direction, and p belongs to A's
support face with outward normal n. These are actual physical support
conditions, including side application means.

A is physically circle-clear. B and C are loaded degree-two triangle
vertices; an unloaded degree-two triangle vertex would be a normal
transmitter whose two neighbors touch, which is impossible by the
triangle transmitter exclusion. Their positive circle corners form a
pairwise acute collection, because B and C touch. Global equilibrium
therefore gives

\[
                 m_B+m_C=-\alpha e_x-\beta n,
                 \qquad \alpha,\beta>0.
\tag{5}
\]

The acute-arc observation of
`TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md`, Section 1, applies:
if a closed inaccessible circle arc has length at least 90 degrees
and less than 180 degrees, the positive sum in (5) cannot point
strictly inside it. Indeed all positive B,C corners lie in one open
angular interval shorter than 90 degrees. Their sum lies in that
interval, and such an interval with its endpoints outside the
inaccessible arc cannot cross the arc.

A circle corner at distance greater than \(\sqrt2\) from A is
inaccessible to every circle-touching neighbor of A, by the diameter
of a unit square. This criterion treats all corner masks at once.

## 2. The S application has exactly three possibilities

If p is on a side support face of A, n is a coordinate direction.
It cannot be east, since that would require d=r; it cannot be west,
since that would require d=s. Both equalities are excluded below or
by (3). After reflection across the horizontal axis, the remaining
side case is

\[
              n=e_y,\qquad
              A=[-s,r]\times[d-1,d],\qquad d<1.
\tag{6}
\]

The application on that side is \((0,d)\), and its side-interior
position follows from s,r positive. The strict upper bound d<1 is
the full D slider condition in (4).

Otherwise p is a unique supporting vertex. Its first coordinate is
either r or \(-s\). Its height cannot vanish, since its norm is d
and d differs from both r and s. Reflect vertically to make its
height positive. The radial support condition then puts it at the
top vertex of A. Thus the two remaining cases are

\[
 \begin{array}{lll}
 \text{NE:}&p=(r,Y),&Y=\sqrt{d^2-r^2},\\[2pt]
 \text{NW:}&p=(-s,Y),&Y=\sqrt{d^2-s^2},
 \end{array}
 \qquad
                   A=[-s,r]\times[Y-1,Y].
\tag{7}
\]

The D slider condition gives \(0<Y<1\). There are no other
support-face or vertex possibilities for the aligned A.

Here are uniform bounds that also justify the inequality d>r used
in this classification. Since

\[
 \begin{aligned}
 d^2-r^2
 &=2R(\sqrt2-1)-\frac54+2(R-T),\\
 2(R-T)&=\frac{1}{2(R+T)}>\frac1{4R}>\frac3{25},
 \end{aligned}
\]

and \(\sqrt2>24/17\), equations (1) and (3) imply

\[
        d^2-r^2>
        \frac{79}{20}\frac7{17}-\frac54+\frac3{25}
        =\frac{211}{425}>\frac{49}{100}.
\tag{8}
\]

Thus \(Y>7/10\) in the NE case, and in particular d>r.
In the NW case, (3) gives

\[
         Y^2>d^2-\left(\frac9{20}\right)^2
          >\left(\frac{91}{100}\right)^2
             -\left(\frac9{20}\right)^2
          =\frac{6256}{10000}>
             \left(\frac{79}{100}\right)^2.
\tag{9}
\]

Consequently \(Y>79/100\) in the NW case. These inequalities
do not assume symmetry or a particular circle corner of B or C.

## 3. The top-side and northeast-vertex cases

In either (6) or the NE case in (7), write the top height as Y and
put k=1-Y. The side case has Y=d>91/100; the NE case has
Y>7/10. Hence

\[
       0<k<\frac3{10},\qquad
       s^2+k^2<\left(\frac9{20}\right)^2+
                   \left(\frac3{10}\right)^2
                =\frac{117}{400}
                <\left(\frac{67}{120}\right)^2<r^2.
\tag{10}
\]

Every circle point z in the closed southwest quadrant is farther
than \(\sqrt2\) from A. To see this without any assumption on
its nearest feature, enlarge A to

\[
                    [-s,\infty)\times[-k,\infty).
\]

The nearest point v of this quadrant to z has coordinates in
\([-s,0]\times[-k,0]\), so (10) gives \(|v|<r\).
Therefore

\[
             \operatorname{dist}(z,A)
                \ge |z-v|\ge R-|v|>R-r=\sqrt2.
\tag{11}
\]

The entire closed 90-degree arc from west to south is consequently
inaccessible to every B,C circle corner. In the side case n points
north; in the NE case both its coordinates are positive. In either
case the right side of (5) lies strictly in the southwest quadrant.
This contradicts the acute-arc observation. Both cases are excluded.

## 4. The northwest-vertex case

Now \(n=(-s,Y)/d\), with \(Y>79/100\), and k=1-Y satisfies
\(0<k<21/100\). The southwest-quadrant argument still applies,
with the stronger bound

\[
 s^2+k^2<\left(\frac9{20}\right)^2+
                \left(\frac{21}{100}\right)^2
           =\frac{2466}{10000}<\frac14<r^2.
\tag{12}
\]

In addition every circle point with angle between 270 and 300 degrees
is inaccessible. Write it as

\[
           z=(R\sin\phi,-R\cos\phi),
           \qquad 0\le\phi\le\pi/6.
\]

Since every point of A has second coordinate at least \(-k\),
its vertical distance from A is at least

\[
 R\cos\phi-k
   \ge R\frac{\sqrt3}{2}-k
   >\frac{79}{40}\frac56-\frac{21}{100}
   =\frac{1723}{1200}
   >\frac{17}{12}>\sqrt2.
\tag{13}
\]

Thus the full closed 120-degree arc from 180 to 300 degrees is
inaccessible. On the other hand the angle eta of n lies strictly
between 90 and 120 degrees: the latter inequality is equivalent to
Y/s>\(\sqrt3\), and follows from

\[
                    \frac Ys>\frac{79}{45}>\sqrt3.
\tag{14}
\]

The direction of \(\alpha e_x+\beta n\), with both weights
positive, lies strictly between 0 and eta. Its negative therefore
lies strictly between 180 and \(180+\eta<300\) degrees,
inside the inaccessible arc. This again contradicts (5) and the
acute-arc observation.

All three physical support types have now been excluded. The entire
D/S same-articulation branch is impossible throughout (1). No bound
on a completion region, numerical search, Lean compilation, or CI
is used. \(\square\)
