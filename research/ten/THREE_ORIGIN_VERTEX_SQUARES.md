# Two or three origin-vertex squares give complete capacity bounds

**Status:** hand proof with independent mathematical audits of the arc lemma
and both capacity theorems. No Lean verification is claimed. The theorem
below is a complete physical capacity bound, with
arbitrary independent orientations of every additional square.

**Theorem.** For a packing in the origin-centered disk of squared radius 17/4:

- Three unit squares having the origin as a vertex force total capacity at
  most eight.
- Two unit squares having the origin as a vertex force total capacity at
  most nine.

The first statement closes the three-vertex-origin case TREE.03 of the n=9
tree inventory. Together they exclude ten-square completions of TREE.02 and
TREE.03. Their application to a stress classification is conditional on the
actual presence of the specified squares; this note does not assert that an
arbitrary packing has them.

The proof uses a circle of radius 11/10 and the following standalone lemma.

## 1. A circular-arc bound for squares whose centers are not too close to zero

Put

\[
 \rho=11/10,\qquad Q=17/4,\qquad
 \gamma=2\arcsin(10/11)-\pi/2.
\]

**Arc lemma.** A unit square contained in the disk D_Q, whose center has
squared norm at least 1/2, meets the circle of radius rho in an arc of angular
length at least gamma. Moreover gamma > 2 pi / 9.

Use the square's own orthonormal axes, reversing and exchanging them so the
center is (u,v), with u >= v >= 0. Set

\[
 a=u-1/2,\quad b=v-1/2,\quad U=u+1/2=a+1,\quad V=v+1/2=b+1.
\]

The hypotheses give

\[
 u^2+v^2\ge1/2,\qquad U^2+V^2\le17/4,
 \qquad u\ge1/2,\qquad u\le3/2.                            \tag{1}
\]

The square is the rectangle [a,U] x [b,V] in these axes, with a >= 0. Its
intersection with the test circle therefore lies in the right semicircle.

We will use the exact comparisons

\[
 \gamma<\pi/4,\qquad
 \arccos(10/11)>\pi/8,\qquad \arcsin(5/11)>\pi/8,          \tag{2}
\]

and

\[
 \arcsin(10/11)-\arcsin(1/11)>\pi/4.                       \tag{3}
\]

For example, (2) follows by squaring against the half-angle values at pi/8;
(3) follows from 10/11 > sqrt(3)/2 and 1/11 < sin(pi/12).

### 1.1 Centers with u >= 3/5

Here U >= rho, so the right edge does not cut the circle. Put

\[
 x_0=\arccos(a/\rho),\qquad y_0=\arcsin(b/\rho).
\]

The circle portion in the rectangle is the interval of angles

\[
 [-x_0,x_0]\ \cap\ [y_0,y_1],                              \tag{4}
\]

where y_1 = arcsin(V/rho) if V < rho, and y_1 = pi/2 otherwise.
Every possible choice of endpoints in (4) gives one of four width bounds.

- Both endpoints on the left edge: width 2 x_0 >= 2 arccos(10/11) > pi/4.
- Both endpoints on horizontal edges: width at least 2 arcsin(5/11) > pi/4.
  The difference arcsin((v+1/2)/rho) - arcsin((v-1/2)/rho) is minimized
  at v=0, because its derivative is nonnegative for v>=0.
- Lower endpoint on the left edge and upper endpoint on the top edge:
  width at least arccos(10/11) + arcsin(5/11) > pi/4.
- Lower endpoint on the bottom edge and upper endpoint on the left edge:
  the width is

  \[
                   \pi/2-\arcsin(a/\rho)-\arcsin(b/\rho).  \tag{5}
  \]

Only the last case needs a sharper bound. We claim

\[
 \arcsin(a/\rho)+\arcsin(b/\rho)
 \le2\arcsin\left(\frac{\sqrt{17/8}-1}{\rho}\right).       \tag{6}
\]

Both summands increase with their argument, so a maximum under
(a+1)^2+(b+1)^2 <= Q occurs on equality. On that boundary parameterize
a+1 = sqrt(Q) cos(theta), b+1 = sqrt(Q) sin(theta), with a >= b and
b >= -1/2. Write s=a+b and

\[
                      f(t)=(t+1)\sqrt{\rho^2-t^2}.
\]

All radicals are positive: -1/2 <= b <= a <= 1 < rho. Direct expansion
using the boundary equation gives

\[
 f(a)^2-f(b)^2
  =(a-b)\left(s^2-\frac{s}{25}+\frac{17}{100}\right)
  =(a-b)\left((s-1/50)^2+106/625\right).                   \tag{7}
\]

Thus f(a) >= f(b). The derivative of the left side of (6) as theta
increases toward pi/4 has the sign of f(a)-f(b), and is nonnegative.
Its maximum is at a=b=sqrt(17/8)-1, proving (6).

The lower bound for (5) supplied by (6) is strictly larger than gamma.
Indeed, with k=(sqrt(17/8)-1)/rho, this is equivalent to

\[
 k^2+(10/11)^2<1
 \quad\Longleftrightarrow\quad
 \sqrt{17/2}>583/200.
\]

The last inequality holds because

\[
                   17/2-(583/200)^2=111/40000>0.           \tag{8}
\]

All four widths are therefore at least gamma. These bounds also show that
the interval in (4) is nonempty, so its endpoint classification is legitimate.

### 1.2 Centers with 1/2 <= u <= 3/5

Here 0 <= a <= 1/10 and b <= 1/10. Consider just the first-quadrant circle
arc. Its potential lower and upper angles are

\[
 \ell=\max\{\arccos(U/\rho),\arcsin(\max(b,0)/\rho)\},
 \qquad
 h=\min\{\arcsin(V/\rho),\arccos(a/\rho)\}.             \tag{9}
\]

All arguments are in their specified domains because U,V <= rho. If the
upper endpoint in (9) comes from the left edge, then

\[
 h-\ell\ge\arccos(1/11)-\arccos(10/11)
          =\arcsin(10/11)-\arcsin(1/11)>\pi/4.
\]

Here arcsin(max(b,0)/rho) <= arcsin(1/11) < arccos(10/11), so the stated
upper bound on ell holds. If the lower endpoint instead comes from the
bottom edge, that edge has b >= 0, hence V >= 1. When b<0 and u=3/5, the
artificial first-quadrant lower bound zero ties the right-edge bound; assign
that tie to the outward-edge case below. Now h >= arcsin(10/11)
and ell <= arcsin(1/11), giving the same width bound. This also covers an
endpoint tie at u=3/5, b=0.

It remains to consider the two outward edges, with width

\[
                     \arcsin(U/\rho)+\arcsin(V/\rho)-\pi/2.\tag{10}
\]

Decrease (u,v) radially until u^2+v^2=1/2. This decreases both terms in
(10), preserves u>=v>=0, and leaves 1/2<=u<=3/5. On this smaller-radius
arc write v=sqrt(1/2-u^2). The function

\[
          \arcsin((u+1/2)/\rho)+\arcsin((v+1/2)/\rho)
\]

is nondecreasing as u increases from 1/2. To check the derivative sign,
observe that

\[
\begin{split}
 &u^2\bigl(\rho^2-(u+1/2)^2\bigr)
  -v^2\bigl(\rho^2-(v+1/2)^2\bigr)\\
 &\qquad=(u-v)\left(\frac{23}{50}(u+v)-(1/2+uv)\right)\le0,\tag{11}
\end{split}
\]

since u+v<=1. Thus (10) is minimized at u=v=1/2, where it equals gamma.
Any second circle component below the horizontal axis only increases the
total angular length. This finishes the arc bound.

### 1.3 The strict angular constant

Put t=arccos(10/11), so 0<t<pi/6 and gamma=pi/2-2t. The triple-angle identity
gives

\[
 \cos(3t)=370/1331>11/40>
                  (\sqrt6-\sqrt2)/4=\cos(5\pi/12).        \tag{12}
\]

The second strict comparison follows from sqrt(6)<5/2 and sqrt(2)>7/5.
Since 0<3t<pi/2, (12) gives 3t<5pi/12, hence t<5pi/36. Consequently

\[
                             \gamma>2\pi/9.               \tag{13}
\]

**Center-exclusion corollary.** A packing in D_(17/4) whose every square
center has norm at least 1/sqrt(2) contains at most eight squares.
Each square contributes an arc of length at least gamma. Apart from finitely
many points, each arc belongs to the square's interior, because a circle
cannot agree with one of its straight edges. Interior-disjoint squares
therefore have disjoint arcs up to sets of angular measure zero. Nine such
arcs would have total length at least 9 gamma > 2pi.

## 2. Three origin-vertex squares force the center exclusion

A unit square with the origin as a vertex contains the entire circular sector
of radius one in its right-angle tangent cone. Three interior-disjoint such
squares therefore cover sectors of the unit disk with total angle 3pi/2.
Every complementary angular gap has width at most pi/2.

Consider the center c of any other square and suppose r=||c||<1/sqrt(2).
Its open inscribed disk of radius 1/2 must avoid the three square interiors.
If the direction of c belongs to one of the occupied sectors, this already
fails because r<1. Otherwise that direction lies in a complementary gap.
Choose a bounding radial segment whose angular distance from c is at most
pi/4. The perpendicular projection of c onto that segment has parameter
r cos(delta)<1, so it belongs to the unit segment. Its distance from c is

\[
                          r\sin(\delta)<1/2.
\]

The open inscribed disk consequently meets the adjacent square's interior,
a contradiction. The origin case is immediate for the same reason. Thus
every additional center has norm at least 1/sqrt(2); the three specified
centers themselves have norm exactly 1/sqrt(2).

The center-exclusion corollary now proves that at most eight squares fit.
No common orientation, common separating-coordinate frame, or stress premise
was used for the additional squares.

## 3. Two origin-vertex squares allow at most one smaller center

Now suppose just two specified unit squares have a vertex at zero. Their
occupied sectors in the unit disk have total angle pi, and the complementary
angular gaps consequently have total width pi.

Let c be any other square center with r=||c||<1/sqrt(2). As in Section 2,
its direction must lie in a complementary gap. Its angular distance from
each bounding ray must be strictly greater than pi/4: otherwise its open
inscribed radius-1/2 disk meets the corresponding unit radial segment and
the adjacent square interior. Thus a gap hosting such a center has width
strictly greater than pi/2. At most one complementary gap can do so.

That gap has width at most pi. Each eligible center direction is more than
pi/4 from each endpoint. Thus any two actual eligible directions differ by
strictly less than pi/2, even when the gap has width exactly pi. If two
smaller centers c_1,c_2 existed, their radii would both be less than
1/sqrt(2) and their angular difference less than pi/2.
Therefore

\[
 \|c_1-c_2\|^2
 =r_1^2+r_2^2-2r_1r_2\cos(\theta)<1,
\]

contradicting the distance of at least one between centers of interior-
disjoint unit squares. There is at most one center of norm below 1/sqrt(2).

If ten squares were present, at least nine would therefore have center norm
at least 1/sqrt(2). Their nine arcs alone already exceed the test circle's
total angular length, by (13). Thus the total capacity is at most nine.

## 4. Scope within the tree research

The three-vertex-origin case is defined in
[the pinned n=9 tree inventory](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/TREE_RADIUS_QUANTIZATION.md).
This note supplies the previously open TREE.03 physical completion bound
directly at q=17/4, and excludes the entire TREE.02 case for ten squares.
Both statements retain all allowed relative angles and every unstressed
additional square. The nine-square TREE.02 completion problem is not excluded
by the weaker capacity-nine statement. These capacity bounds do not extend
the radius window or the graph classification of the source by themselves.
