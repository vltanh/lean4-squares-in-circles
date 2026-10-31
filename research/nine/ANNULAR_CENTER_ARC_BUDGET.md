# At most seven unit-square centers lie outside the open unit disk

**Status: complete hand necessary-condition theorem; root and separate independent
full audits passed.** Put Q=1105/256 and r=5/4.

**Theorem.** Every closed unit square S contained in D_(sqrt(Q)), whose
center c satisfies |c|>=1, contains in its open interior a connected
arc of the circle |x|=r of angular length strictly greater than pi/4.
The square need not touch the containing circle.

Consequently, in any packing of nine interior-disjoint unit squares in
D_(sqrt(Q)), at least **two centers have norm strictly less than one**.
The assertion also holds in every smaller concentric disk. It is a
uniform geometric necessary condition, not a completed nine-square
radius bound or a completion theorem for a particular positive graph.

## 1. Own-frame coordinates and the full parameter range

Choose signs and order of the square's own orthonormal axes so its
center has coordinates (x,y), with x>=y>=0. Then
\[
 S=[a-1,a]\times[b-1,b],\qquad
 a=x+\tfrac12,\quad b=y+\tfrac12,\qquad a\ge b\ge\tfrac12.
\tag{1}
\]
The center condition gives x^2+y^2>=1. Its farthest corner is (a,b),
so, writing q=a^2+b^2,
\[
 \frac52\le x^2+y^2+x+y+\frac12=q\le Q.
\tag{2}
\]
The lower bound uses x+y>=sqrt(x^2+y^2)>=1.

Put A=a-1 and B=b-1. The outer bound alone gives
\[
 a<81/40,\qquad b<3/2,\qquad
 A<41/40,\quad-1/2\le B<1/2.
\tag{3}
\]
For a, use a^2<=Q-1/4<589/144<(81/40)^2; for b use b^2<=Q/2<9/4.

## 2. When the outer first face is near the inner circle

Suppose a<=r. Then x<=3/4 and
\[
 y^2\ge1-x^2\ge7/16,
 \qquad x\ge y\ge\sqrt7/4.
\]
Therefore
\[
 a,b\ge\frac{2+\sqrt7}{4}>
                \frac54\cos\frac\pi8.
\tag{4}
\]
For an exact verification of the strict comparison, square the positive
quantities 2+sqrt(7) and 5 cos(pi/8). Their squared difference is
\[
 4\sqrt7-\frac32-\frac{25}{4}\sqrt2
 >\frac{21}{2}-\frac32-\frac{125}{14}
 =\frac1{14}>0,
\]
using sqrt(7)>21/8 and sqrt(2)<10/7.

Also A,B<=1/4, whereas
\[
                 \frac54\sin\frac\pi8>\frac5{16}>\frac14.
\tag{5}
\]
Here sin(pi/8)>1/4 follows from sqrt(2)<7/4.
For every angle phi in the closed interval [pi/8,3pi/8], both
coordinates of r(cos(phi),sin(phi)) are thus strictly between the
corresponding square faces. This entire closed arc is in the open
interior of S. Compactness, or the strict endpoint inequalities,
allows a small extension at both ends, yielding an open interior
arc strictly longer than pi/4. This includes the face endpoint a=r.

## 3. The inner-face estimate for a>r

We give the full parameter check for the extension of the boundary
arc argument in CYCLIC_GLOBAL_CONTINUATION.md, Sections 3--4. The
square's farthest corner need not be on the packing's outer circle;
its own squared norm q merely lies in the complete interval (2).

The required inequality is
\[
 E:=(a-1)^2+(b-1)^2+\sqrt2(a-1)(b-1)<25/32=r^2/2.
\tag{6}
\]
At fixed q, put t=a+b. Direct expansion gives
\[
 E=(1-1/\sqrt2)q+t^2/\sqrt2-(2+\sqrt2)t+2+\sqrt2.
\tag{7}
\]
This is convex in t. For a>=b>=1/2, a^2+b^2=q, its possible t
range has endpoints b=1/2 and a=b. It suffices to bound those two
values, even when one of those endpoint configurations does not itself
satisfy the center restriction.

At b=1/2, put A=sqrt(q-1/4)-1. By (2)--(3), 1/2<=A<41/40.
Thus sqrt(2)>7/5 and the increasing polynomial A^2+1/4-(7/10)A give
\[
 E=A^2+1/4-(\sqrt2/2)A
    <A^2+1/4-(7/10)A
    <933/1600<25/32.
\tag{8}
\]
At a=b=sqrt(q/2)>1, the value is increasing with q. Since
sqrt(Q)<25/12,
\[
 E=(2+\sqrt2)(\sqrt{q/2}-1)^2
 <\frac{626-287\sqrt2}{288}<25/32.
\tag{9}
\]
The last comparison follows from 401^2<2*287^2. Convexity now proves
(6) throughout the full range (2).

We also need
\[
                           \sqrt2 A+B>0.
\tag{10}
\]
Indeed x>=y>=0 implies
( sqrt(2)x+y )^2-2(x^2+y^2)=y(2sqrt(2)x-y)>=0. Consequently
\[
 \sqrt2 A+B
 =\sqrt2 x+y-\frac{\sqrt2+1}{2}
 \ge\frac{\sqrt2-1}{2}>0.
\]
This replaces the stronger boundary-only lower bound on a used in the
original boundary-square argument.

## 4. The actual open arc when a>r

In this case A>1/4. Every inner-circle point in S has positive first
coordinate. Put
\[
 \alpha=\arccos(A/r),\qquad
 \beta=\arcsin(B/r),\qquad
 \gamma=\arcsin(\min(b/r,1)).
\tag{11}
\]
By (3), A^2+B^2<2081/1600<r^2, so beta>-alpha. The upper first
face is strictly beyond the inner circle because a>r. Therefore
the actual closed angular interval in S is exactly
\[
                          [\beta,\min(\alpha,\gamma)].
\tag{12}
\]
Using (6),(10),
\[
 \sqrt2 A+B<\sqrt{r^2-B^2},\qquad
 A<r\cos(\beta+\pi/4),
\]
so alpha-beta>pi/4. Here |B|<=1/2 makes |beta|<pi/4, and
beta+pi/4 lies in (0,pi/2), justifying the cosine comparison.

For 1/2<=b<r, the strip length
\[
                \arcsin(b/r)-\arcsin((b-1)/r)
\]
is nondecreasing in b, since b>=|b-1|. Hence
\[
                   \gamma-\beta\ge2\arcsin(2/5)>\pi/4.
\tag{13}
\]
The strict last inequality is equivalent to sin(pi/8)<2/5.
Continuity includes b=r. If b>r, gamma=pi/2 and beta<pi/4,
which gives the same strict conclusion. Thus (12) has length
strictly greater than pi/4. Every point of its open interval satisfies
all four square inequalities strictly.

Sections 2 and 4 exhaust all possible farthest-face coordinates and
prove the theorem.

## 5. The global count and its precise scope

For interior-disjoint squares, the open arcs just furnished are
pairwise disjoint subsets of the same circle |x|=5/4. Eight centers
with norm at least one would therefore give total angular length
greater than 8*pi/4=2*pi, a contradiction. At most seven centers
lie outside the open unit disk, proving the asserted two-center
necessary condition for a nine-packing.

In the declared research window, every circle-touching unit has
center norm at least R-1/sqrt(2)>1. Thus the two units with centers
inside the unit disk are physically circle-clear, regardless of their
assigned multipliers. The new conclusion is spatial: it locates their
centers, rather than merely counting two non-boundary units.

The result does not show that these two units lie in any particular
positive cycle hole or exterior pocket. It does not make seven outer
units into a boundary C7, and it does not justify radially moving them
independently. Those further geometric implications require separate
proofs. No numerical optimization, Lean compilation or CI is used.
