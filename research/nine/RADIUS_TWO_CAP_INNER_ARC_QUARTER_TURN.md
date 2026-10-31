# Every unit in a radius-two cap of height greater than one quarter occupies more than a quarter-turn inner arc

Date: October 26, 2026.

**Status: strengthened complete hand theorem, accepted after full-source
and scope reviews of the height threshold H>1/4.** See
REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_ROOT_2026_10_26.md and the
separate nonauthor review
REVIEW_RADIUS_TWO_CAP_ARC_QUARTER_TURN_C6_2026_10_26.md. The earlier
version with threshold H>1/(2sqrt(2)) also passed
REVIEW_RADIUS_TWO_CAP_ARC_CERTIFICATE_REDUCTION_2026_10_26.md;
the two new reviews check the complete strengthened argument below.
The strengthened proof applies to every actual unit orientation and
uses convex endpoint bounds and one whole-interval derivative.

Let S be an actual closed unit square contained in the disk of radius
R<=2 about the origin. Suppose, for an actual unit vector n, that
\[
 S\subseteq\{p:n\cdot p\ge H\},\qquad H>\frac14.
\tag{1}
\]
Put r=5/4, and let c be the actual square center.

**Theorem.** The entire intersection of the open interior of S with
\(|p|=r\) is one connected open arc. It contains the point
\(r c/|c|\), and its angular length is strictly greater than \(\pi/4\).

Consequently two such interior-disjoint actual squares cannot both
be routed into one free interval of this circle of length at most
\(\pi/2\). That routing premise is separate; it is not inferred
merely from the outward half-plane in (1).

## 1. Exact own-frame geometry and the two complete cases

Choose signs and order of S's actual own axes so that its center
coordinates are \(x\ge y\ge0\). Put
\[
 a=x+\frac12,\quad b=y+\frac12,\quad A=a-1,\quad B=b-1,
 \qquad S=[A,a]\times[B,b].
\tag{2}
\]
Thus \(a\ge b\ge1/2\), and its farthest actual corner gives
\[
                         q=a^2+b^2\le4.
\tag{3}
\]
Every point of S has norm at least H, by the actual half-plane
premise. Its closest point to the origin is
\((\max(A,0),\max(B,0))\). We treat the complete alternatives
\(a>r\) and \(a\le r\) below. This is a geometric face case
split, not a partition into sampled square orientations.

## 2. A uniform convex estimate for the entire inner-face case a>r

Here \(A>1/4\), \(q>29/16\), and (3) gives
\[
 A<1,\qquad-\frac12\le B<\frac12,\qquad
                 A^2+B^2<\frac54<r^2.
\tag{4}
\]
Indeed \(a^2\le4-1/4=15/4<4\), and \(b\le\sqrt2<3/2\).
Set
\[
                         E=A^2+B^2+\sqrt2\,AB.
\tag{5}
\]
We prove the uniform bound
\[
                         E<\frac35<\frac{25}{32}=r^2/2.
\tag{6}
\]

For fixed q, put \(t=a+b\). Direct expansion gives
\[
 E=(1-1/\sqrt2)q+t^2/\sqrt2-(2+\sqrt2)t+2+\sqrt2.
\tag{7}
\]
This is convex in t. On the full fixed-q domain \(a\ge b\ge1/2\),
the endpoints of t occur at \(b=1/2\) and \(a=b\). Enlarging to
that interval preserves an upper bound, even if an auxiliary endpoint
fails the cap premise or the inner-face condition.

At \(b=1/2\), \(B=-1/2\) and
\(A=\sqrt{q-1/4}-1\in(1/4,1)\). Since \(1/\sqrt2>7/10\),
\[
 E=A^2+\frac14-\frac A{\sqrt2}
      <A^2+\frac14-\frac7{10}A\le\frac{11}{20}<\frac35.
\tag{8}
\]
The last polynomial is convex on \([1/4,1]\), with endpoint values
\(11/80\) and \(11/20\).

At \(a=b=v=\sqrt{q/2}\), the full possible range is contained
in \([3/4,\sqrt2]\), and
\[
                         E=(2+\sqrt2)(v-1)^2.
\tag{9}
\]
This is convex in v. Its endpoint values on that enlarged interval
are \((2+\sqrt2)/16<7/32\) and exactly \(2-\sqrt2<3/5\),
using \(7/5<\sqrt2<3/2\). Thus (9), then (7), prove (6)
on the entire original inner-face domain.

## 3. Exact connected arc and length in the inner-face case

Define principal angles
\[
 \alpha=\arccos(A/r),\qquad \beta=\arcsin(B/r),\qquad
 \gamma=\arcsin(\min(b/r,1)).
\tag{10}
\]
The square has positive first coordinate, its outer first face is
beyond r, and (4) gives \(\beta>-\alpha\). Hence its exact
closed intersection with the inner circle is the one interval
\[
                         [\beta,\min(\alpha,\gamma)].
\tag{11}
\]
The corresponding open interval satisfies all four square inequalities
strictly. At \(b=r\), the upper face would have angle \(\pi/2\),
whereas \(\alpha<\pi/2\); thus this endpoint gives no extra
component or exceptional open point.

The bound (6) is exactly
\[
                  (\sqrt2 A+B)^2<r^2-B^2.
\]
The right side is positive. Therefore, regardless of the sign of
\(\sqrt2 A+B\),
\[
 \sqrt2 A+B<\sqrt{r^2-B^2},\qquad
                         A<r\cos(\beta+\pi/4).
\tag{12}
\]
There is no extra positive-sign premise on the expression being
squared. The inequality \(|B|\le1/2\) gives \(|\beta|<\pi/4\);
both compared angles lie in the decreasing cosine interval. Thus
\[
                            \alpha-\beta>\pi/4.
\tag{13}
\]

If \(b\le r\), the opposite-face strip length satisfies
\[
 \gamma-\beta
 =\arcsin(b/r)-\arcsin((b-1)/r)
 \ge2\arcsin(2/5)>\pi/4.
\tag{14}
\]
The difference is nondecreasing on \([1/2,r)\), since
\(b\ge|b-1|\) gives that sign for its derivative. Continuity
includes \(b=r\). The strict final comparison is
\(\sin(\pi/8)<2/5\), from \(2-\sqrt2<16/25\).
If \(b>r\), then \(\gamma=\pi/2\) and \(\beta<\pi/4\)
give (14) directly. Both possible lengths in (11) exceed \(\pi/4\).

## 4. The full outer-face case a<=r also has a longer than quarter-turn arc

Here \(A,B\le1/4\). If \(B\le0\), the closest point's norm
would be \(\max(A,0)\le1/4\), contradicting (1). Consequently
\[
          0<B\le A\le\frac14,\qquad
          k^2:=A^2+B^2\ge H^2>\frac1{16},\qquad
                            k^2\le\frac18.
\tag{15}
\]
In particular the square lies in the open first quadrant, with
\(1<b\le a\le r\). Its exact closed inner-circle intersection
has angular interval
\[
 \left[
 \max\{\arccos(a/r),\arcsin(B/r)\},
 \min\{\arccos(A/r),\arcsin(b/r)\}
 \right].
\tag{16}
\]
We prove that each of its four possible upper-minus-lower differences
is strictly greater than \(\pi/4\). This also proves nonemptiness
and the exact connected open-interior interval.

Two differences are opposite-face strip lengths. Applying (14) to
\(z=a\) or \(z=b\) gives
\[
              \arcsin(z/r)-\arcsin((z-1)/r)>\pi/4.
\tag{17}
\]
The inner-inner difference obeys
\[
 \arccos(A/r)-\arcsin(B/r)
       \ge\pi/2-2\arcsin(1/5)>\pi/4.
\tag{18}
\]
For the last strict comparison,
\(\sin(\pi/8)>1/4>1/5\), since \(\sqrt2<7/4\).

It remains to treat the entire outer-outer difference
\[
 L(A,B)=\arcsin((1+A)/r)+\arcsin((1+B)/r)-\pi/2.
\tag{19}
\]
Fix the actual \(k^2=A^2+B^2>1/16\), put
\(B=\sqrt{k^2-A^2}\), and vary from \(A=B=k/\sqrt2\)
to the original ordered point. This is one connected interval
with \(B>0\) and \(A\le1/4\). In its interior, the sign of
\(dL/dA\) is the sign of
\[
 \begin{split}
 &B^2\{r^2-(1+B)^2\}-A^2\{r^2-(1+A)^2\}\\
 &\quad=(A-B)\big[(A+B)(k^2-9/16)+2(k^2+AB)\big]\\
 &\quad=(A-B)\left[(A+B-1/4)^2
                   +(k^2-1/16)(A+B+1)\right]\ge0.
 \end{split}
\tag{20}
\]
Both terms squared in comparing the derivative are positive on the
open interval. The bracket in the last line is strictly positive
throughout (15). Thus L is nondecreasing away from the diagonal.
Continuity includes \(a=r\) or \(b=r\), where an individual
arcsine derivative can be infinite. No extension across such a
point is needed.

The diagonal value increases with k. Since \(k>1/4\),
\[
 L\ge2\arcsin\left(\frac{1+k/\sqrt2}{5/4}\right)-\pi/2
    >2\arcsin\left(\frac{4+1/\sqrt2}{5}\right)-\pi/2
    >\pi/4.
\tag{21}
\]
The last comparison has the exact positive squared reserve
\[
 \left(\frac{4+1/\sqrt2}{5}\right)^2
          -\sin^2(3\pi/8)=\frac{16-9\sqrt2}{100}>0,
\tag{22}
\]
where \(16>9\sqrt2\) follows from \(256>162\). Both compared
arguments are positive and below one, so the principal arcsine
comparison has the stated direction.

Equations (17)--(21) prove all four possible differences in (16)
strictly larger than \(\pi/4\). This closes the complete outer-face
case, including its boundary with the inner-face case.

## 5. The actual radial-center point belongs to the unique open arc

The support half-width of every actual unit square in any unit
direction is at least \(1/2\). Hence its center norm \(k_c\)
satisfies
\[
               k_c=|c|\ge n\cdot c\ge H+1/2>3/4.
\tag{23}
\]
The actual farthest-corner formula is
\(q=k_c^2+x+y+1/2\ge k_c^2+k_c+1/2\). Since \(q\le4\),
\[
                 k_c\le(\sqrt{15}-1)/2<3/2.
\tag{24}
\]
It follows that \(|r-k_c|<1/2\). Thus \(r c/k_c\) lies strictly
inside the actual inscribed radius-\(1/2\) disk, and therefore in
S's open interior and in the unique open arc proved above. The
center is nonzero, as required for this expression.

## 6. Whole-cap consequence and retained physical scope

Different interior-disjoint actual squares have disjoint open arcs
on the same circle. Two arcs each longer than \(\pi/4\) cannot
both lie in one free interval of length at most \(\pi/2\). This
proves the conditional capacity consequence whenever an actual
crosscut or routing theorem supplies that one interval.

The theorem itself assumes no force, load, boundary-circle contact,
center box or preferred orientation. It supplies no routing or
endpoint-gap bound, and it does not assert the height premise
\(H>1/4\) for an unproved C6 pocket. Every original square,
contact mask, zero individual circle weight, mean, normal and
transmitter position remains unchanged. No sampled geometry,
new coefficient packet, Lean compilation or CI is used.
