# The entire exact S/S wall family has upper-pocket capacity at most three

**Status: complete hand capacity theorem; root and independent full hand audits passed.**

Use the complete wall family of
DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md:
\[
 \begin{gathered}
 x=(\sqrt{70}-8)/4,\quad \delta=x^2,\quad d=1+\delta,\quad
 R^2=(d+1)^2+1/4,\quad u=1-x^2,\\
 A=[\delta,d]\times[t-1,t],\\
 B=[-u,\delta]\times[2x-1,2x],\quad
 C=[-u,\delta]\times[2x-2,2x-1],\\
 x(1-2x)/(1-x)\le t<2x.
 \end{gathered}
\tag{1}
\]
The radial S leaves have directions
\[
        e_A=(1,0),\qquad e_B=(-u,2x)/d
\tag{2}
\]
and occupy \(S_d(e)=\{re+sJe:d\le r\le d+1,\ |s|\le1/2\}\).
All additional squares have arbitrary independent frames.

The two radial rays in (2) screen a genuine upper pocket, whose angle is
\[
                  \phi=\pi-2\arctan x<170^\circ.
\tag{3}
\]
**Theorem.** At most three additional unit squares lie in that upper
pocket, uniformly over the entire interval of t in (1).

This counts the whole upper region. The complementary lower regions are
excluded in DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md. The whole cell is assembled
in TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md.

## 1. Actual screening and the center-radius bound

The exact relation \(8x+2x^2=3/4\) gives
\[
                    \frac1{11}<x<\frac1{10},\qquad d<101/100.
\tag{4}
\]
For the lower bound, \(\sqrt{70}>92/11\) follows from \(8470>8464\).

For a unit square with center c and orthonormal side vectors v,w,
\[
 \max_{\text{corners }z}|z|^2
   =|c|^2+\tfrac12+|c\cdot v|+|c\cdot w|
   \ge |c|^2+\tfrac12+|c|.
\]
Since equality with \(R^2=(d+1)^2+1/4\) occurs at
\(|c|=d+1/2\), every center satisfies
\[
                          |c|\le d+\tfrac12<151/100.
\tag{5}
\]

The radial outer-face screen applies without change to \(S_d(e)\):
every point of a distinct packing square has e-projection strictly
less than d+1. Indeed its center has smaller e-projection by (5).
If a segment from the center crossed the line \(e\cdot z=d+1\)
at an interior disk point, that crossing would have transverse
coordinate of absolute value less than 1/2, and nearby interior
points would overlap the terminal. The two endpoints of that chord
are the terminal's circle vertices and cannot be shared by another
contained square.

B contains zero in its open interior. The segment from zero to
\(de_B=(-u,2x)\) belongs to B by convexity. The segment from zero
to \(de_A=(d,0)\) is covered by B for \(0\le X\le\delta\)
and A for \(\delta\le X\le d\), since \(0<t<2x<1\).
The remaining portions of the two positive rays are blocked by the
two radial leaves and their outer-face screens.

Every other square's connected open interior therefore avoids both
whole rays and lies entirely in one of the two intervening open
angular sectors. A square in the upper sector is contained in its
closed wedge, hence wholly in \(Y\ge0\). Its center angle is
strictly between 0 and \(\phi\). No center-only routing assumption
has been made.

For an exact verification of (3), put \(\alpha=\arctan(1/11)\).
Then \(3\alpha<\pi/2\) and
\[
 \tan(3\alpha)=\frac{181}{649}>2-\sqrt3=\tan(\pi/12).
\]
The strict comparison follows by squaring
\(\sqrt3>1117/649\), whose integer difference is
\(3\cdot649^2-1117^2=15914>0\).
Thus \(\alpha>\pi/36\), and (4) gives
\(\phi<17\pi/18\), exactly (3).

## 2. A universal point in every sufficiently central upper square

**Lemma 2.1.** If a unit square T is wholly in \(Y\ge0\) and its
center has norm at most 2/3, then
\[
                              p=(0,2/11)
\tag{6}
\]
lies in its open interior.

*Proof.* Write its center as \((X,Y)\), and put \(k=2/11\).
For either unit side axis n, let
\(a=|n_x|\), \(b=|n_y|\), so \(a^2+b^2=1\).
Its vertical halfwidth is \(h=(a+b)/2\), and
\[
             h\le Y\le2/3,\qquad |X|\le\sqrt{4/9-Y^2}.
\]
Since \(Y>k\),
\[
 |n\cdot((X,Y)-p)|
 \le a\sqrt{4/9-Y^2}+b(Y-k).
\tag{7}
\]
We prove that (7) is strictly less than 1/2 for each axis.

If \(b\le a\), the right side decreases for \(Y\ge h\):
its unconstrained maximum occurs at \(Y=(2/3)b<h\).
At \(Y=h\), replace \(4/9\) by \(1/2\) to obtain the strict bound
\[
 a\sqrt{4/9-h^2}+b(h-k)
 <a(a-b)/2+b(a+b)/2-bk
 =1/2-bk\le1/2.
\]
The equality \(a=b\) is infeasible because then \(h=1/\sqrt2>2/3\).

If \(b\ge11/12\), Cauchy's inequality gives the bound
\[
 |(X,Y)|-bk\le2/3-bk\le1/2.
\]
It is strict for \(b>11/12\). At \(b=11/12\), equality would
require \(Y=(2/3)b=11/18\), less than
\(h=(11+\sqrt{23})/24\), so it is strict there too.

The remaining case is \(a<b<11/12\). The floor \(h\le2/3\)
implies
\[
              a\le(4-\sqrt2)/6<4/9.
\]
Also \(a>b/3\), since \(b<11/12<3/\sqrt{10}\).
Thus the right side of (7) again decreases on \(Y\ge h\).
The function \(a+b=\sqrt{1-b^2}+b\) is decreasing for
\(b>1/\sqrt2\), so
\[
 h>(11+\sqrt{23})/24,\qquad h^2>35/81,
             \qquad \sqrt{4/9-h^2}<1/9.
\]
The middle exact inequality is equivalent to
\(\sqrt{23}>472/99\), whose squares compare as
\(225423>222784\). Therefore at \(Y=h\), (7) is less than
\[
                  \frac4{81}+\frac{11}{12}
                           \left(\frac23-\frac2{11}\right)
                    =\frac{40}{81}<\frac12.
\]
This proves both strict side-coordinate inequalities and puts p in
the open interior of T. \(\square\)

By (4), the point p lies in the open interior of B:
\(-u<0<\delta\) and \(2x-1<0<2/11<2x\).
Thus every upper-pocket extra avoids p and has
\[
                            |c|>2/3.
\tag{8}
\]

## 3. Forty degrees are excluded at both radial terminals

**Lemma 3.1.** A square center with radius in
\([2/3,151/100]\), belonging to a unit square disjoint in interior
from \(S_d(e)\), differs in angular direction from e by more than
\(2\pi/9\), whenever that difference is measured in
\([0,2\pi/9]\).

*Proof.* Rotate e east and write the center as
\(r(\cos\theta,\sin\theta)\), \(0\le\theta\le2\pi/9\);
reflection handles negative transverse sign.
The exact elementary bounds
\[
 \cos(2\pi/9)>153/200,\qquad \sin(2\pi/9)<13/20
\tag{9}
\]
suffice. For the first, the increasing polynomial
\(4z^3-3z+1/2\) on \(z>1/2\) vanishes at
\(\cos(2\pi/9)\) and equals \(-8423/2000000\) at \(153/200\).
The second follows by squaring from the first.

At \(r=2/3\), the transverse coordinate is below 1/2 and the
radial coordinate below d. Its distance to the terminal rectangle is
\[
       d-(2/3)\cos\theta
           <101/100-(2/3)(153/200)=1/2.
\]
At \(r=151/100\), the radial coordinate is between d and d+1,
while its transverse coordinate is below
\((151/100)(13/20)<1\). Its distance to the rectangle is again
strictly less than 1/2. Squared distance to a convex rectangle is
convex along this fixed radial segment, so every intermediate radius
also has distance strictly less than 1/2.

The square's open inscribed disk of radius 1/2 would then meet the
terminal's open interior, contradicting physical nonoverlap.
\(\square\)

Applying this to the two terminals and (5), (8), every upper extra
center angle satisfies
\[
                      2\pi/9<\theta<\phi-2\pi/9.
\tag{10}
\]

## 4. Every consecutive center angle is more than thirty degrees

If two centers have radii r,s in \([2/3,151/100]\) and minor
angular difference at most \(\pi/6\), their squared distance is at
most
\[
                            r^2+s^2-\sqrt3\,rs.
\]
This is separately convex in r,s, so its maximum is at a corner
of the radius rectangle. Using \(\sqrt3>12/7\), its three distinct
corner bounds are
\[
             \frac8{63},\qquad
             \frac{22801}{35000},\qquad
             \frac{629263}{630000},
\tag{11}
\]
all strictly less than one. But distinct square centers have distance
at least one, by their disjoint open inscribed half-radius disks.
Thus every consecutive center angle in (10) differs by more than
\(\pi/6\).

The interval (10) has length
\[
               \phi-\frac{4\pi}{9}
                    <\frac{17\pi}{18}-\frac{8\pi}{18}
                    =\frac{\pi}{2}.
\]
Four ordered center angles would require three consecutive gaps
strictly exceeding \(\pi/6\), whose sum exceeds \(\pi/2\).
This is impossible. The entire upper pocket has capacity at most
three, uniformly for every t in (1).

The theorem does not assume the extras' orientations, place their
centers by a grid, or replace a lower-region exclusion by a quadrant
assumption. No numerical search, Lean compilation or CI is a premise.
