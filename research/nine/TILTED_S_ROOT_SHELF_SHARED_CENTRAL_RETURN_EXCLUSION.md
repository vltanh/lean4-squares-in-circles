# A tilted S-root shelf with a shared central edge has no return unit

Date: October 27, 2026.
Author: rooted_final_review.
Comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

**Status: complete uniform analytic candidate, pending independent full
review.** A physical shelf theorem and the actual true B3 equation
exclude the entire H-owned HB singleton / shared HK feature of the
original S/S hub-tip diamond. Every remaining owner family stays open
unless separately excluded. No coefficient certificate is introduced.

## 1. A purely physical tilted-shelf theorem

Use fixed orthonormal coordinates with the original circle origin.
Let three actual contained unit squares have the full positions

\[
 \begin{aligned}
 H&=[h-1,h]\times[A-1,A],\\
 B&=P+[0,1]v+[0,1]w,\quad
       P=(h,A-\alpha),\\
 v&=(\alpha,-\beta),\qquad w=(\beta,\alpha),\\
 K&=[k,k+1]\times[A,A+1].
 \end{aligned}
 \tag{1}
\]

Assume their open interiors are disjoint and

\[
 \begin{gathered}
 R^2\le1105/256,\quad |h|<1/60,\quad 5/6<A<1,\\
 \alpha^2+\beta^2=1,\qquad 0<\beta<1/2,\quad \alpha>0,\\
 Q=P+w=(h+\beta,A)\in K,
              \qquad K\text{ physically touches the circle}.
 \end{gathered}
 \tag{2}
\]

**Theorem 1.1.** No further unit square T contained in the same disk,
with open interior disjoint from H,B,K, can physically touch both
H and K. T's frame, mask, degree, circle load and contact types are
arbitrary. There is no force premise in this theorem.

The same fixed rational reserve is used in both parts of the proof:

\[
 \left(\frac{59}{60}\right)^2+
       \left(\frac{11}{6}\right)^2-rac{1105}{256}
                         =\frac{671}{57600}>0.
 \tag{3}
\]

Containment of K's two actual upper corners and A>5/6 give

\[
 |k|,|k+1|<59/60,
 \qquad -59/60<k<-1/60.
 \tag{4}
\]

Since |h|<1/60, these imply

\[
       h-1<k<h<k+1,\qquad -1<k<0.
 \tag{5}
\]

Thus the H/K intersection is a positive shared top segment. Since
A>0, the actual physical circle contact of K has the exact equation

\[
 R^2=M^2+(A+1)^2,\qquad M=\max(-k,k+1)<59/60.
 \tag{6}
\]

Both possible far horizontal corners and their tied physical mask
are included. No circle-stress weight has been used.

## 2. The whole right-side contact cover at H

Write U=(h,A) for the upper-right H corner. The actual segments
PU, UQ and PQ belong respectively to the closed physical H, K
and B. They bound the closed triangle

\[
                         \Delta=\operatorname{conv}\{P,U,Q\}.
 \tag{7}
\]

Its horizontal width is beta<1. The open interior of another unit
cannot contain any point of a closed occupied square: an open
neighborhood of such a point would meet that square's open interior.
Consequently, if T's connected open interior entered Delta, it could
not leave across its three occupied boundary segments. The whole
closed T would be contained in Delta. This is impossible because
every unit square has width at least one in every unit direction,
whereas Delta has horizontal width beta<1.

At every point of H's right side strictly between P and U, any T
touching H from outside has interior points just to its right,
inside Delta. At U, H occupies the southwest tangent quadrant and
K the upper tangent half-plane, since U is in the relative interior
of K's bottom side by (5). A further unit at U would again have
interior points in Delta. Thus none of these points belongs to T.

The point P is also impossible. H has a side-interior tangent
half-plane at P, while B's two inward directions v,w both have
strictly positive horizontal component. The two remaining tangent
gaps each have angle below pi/2. No tangent sector of a unit square,
whose angle is at least pi/2, can fit into either gap.

It remains to cover the short portion of H's right side below P.
Suppose T contains S=(h,s), with

\[
                         A-1\le s<A-\alpha,
 \tag{8}
\]

and lies wholly in x>=h. This includes every side-interior H/T
contact there. Choose an actual T/K common point Z=(z_x,z_y).
Then z_y>=A and z_x>=h. If z_x=h, the segment SZ contained in
T contains P, already impossible. Therefore z_x>h.

The point W of SZ at height A-alpha has horizontal displacement

\[
 0<W_x-h
   =\frac{A-\alpha-s}{z_y-s}(z_x-h)
   \le(1-\alpha)\sqrt2<1.
 \tag{9}
\]

Here z_y-s>=A-s, alpha<A-s<=1, and |Z-S|<=sqrt(2), the
actual diameter of T. The final strict inequality follows from
alpha>sqrt(3)/2>3/4 and sqrt(2)<2.

At this same height the actual B cross-section contains every
point with 0<x-h<1/alpha in its open interior: its own coordinates
are xi=alpha(x-h) and eta=beta(x-h), both strictly between zero
and one. Since 1<1/alpha, (9) puts W in B's open interior.
But W belongs to T, contradicting disjoint open interiors. This
excludes all right-side contacts below P under (8), with the
lower-right endpoint retained whenever T lies in x>=h.

## 3. The remaining boundary cover routes T above H or through its upper-left side

We now cover every other actual H/T contact, including both types
of corner contact.

* At the relative interior of H's left side, T lies in x<=h-1,
  which cannot reach K because k>h-1.
* At the relative interior of its bottom side, T lies in y<=A-1,
  below K.
* At its bottom-left corner, a vertex tangent quadrant of T is
  wholly left of x=h-1 or below y=A-1. Neither reaches K. If
  this corner is a side-interior point of T, the inward unit side
  normal into T has both components nonpositive. When its vertical
  component is negative, the upward span from that side point is
  at most the absolute horizontal normal component, strictly below
  one. Hence max_T y<A. If its vertical component is zero, the
  whole T lies left of x=h-1, already excluded.
* At its bottom-right corner, a vertex tangent quadrant of T is
  wholly right of x=h or below y=A-1. The right case is exactly
  (8)--(9), and the below case cannot reach K. For a side-interior
  contact of T its inward normal has nonnegative horizontal and
  nonpositive vertical component. A strict negative vertical
  component again gives max_T y<A; the zero component puts all
  T in x>=h, covered by (8)--(9).
* The upper-right corner and the entire right side were exhausted
  in Section 2.
* At the upper-left corner V=(h-1,A), a vertex tangent quadrant
  of T is wholly left or wholly above. The left case cannot reach
  K. The above case puts the whole T in y>=A. If V is instead
  a side-interior point of T, its actual inward side normal is
  (-c,s), with c,s>=0 and c^2+s^2=1.
* A contact in the relative interior of H's top side puts the
  whole T in y>=A. If it is within the actual shared H/K segment,
  the two opposite occupied half-planes exclude a third unit
  there; retaining it in the above case does not weaken the result.

The elementary quadrant fact used here is that a right-angle sector
avoiding an open coordinate quadrant is contained in one of the two
opposite closed coordinate half-planes. Side-interior contacts were
covered separately by their half-plane and full unit-side span.

The entire actual boundary cover therefore leaves only these forms:

1. T lies wholly in y>=A, with min_T y=A at an H/T point.
2. The actual point V=(h-1,A) lies on a T side with its actual
   inward unit normal (-c,s), c,s>=0, c^2+s^2=1.

Every tilted frame, side endpoint and physical singleton has been
retained. This is routing of the whole actual square, not merely
of its center.

## 4. Both routed forms exceed the containing circle

In the first form, a lowest point of T belongs to H's top edge,
so its horizontal coordinate is at most h<k+1. We claim max_T x<=k.
For an aligned T this follows at once from the overlap of its
vertical interval [A,A+1] with K. For a tilted T, its unique
lowest vertex has an inward side leading to its rightmost vertex.
That side has positive horizontal increment and vertical increment
strictly between zero and one. If max_T x>k, a portion of that
side has k<x<k+1 and A<y<A+1, inside K's open interior. A small
move into T then contradicts open nonoverlap. Thus max_T x<=k.

Physical T/K contact gives equality, and the complete supports are
max_T x=k and min_T y=A. The orientation-free coordinate-minimum
point theorem, reflected horizontally, puts the actual point

\[
                                (k-1,A+1)\in T.
 \tag{10}
\]

For -1<k<0, one has 1-k>max(-k,k+1)=M. Equations (6),(10)
therefore give a point of T with squared norm above R^2.

In the second form the actual opposite-side point

\[
                         V+(-c,s)=(h-1-c,A+s)\in T
 \tag{11}
\]

is present for every original position of V on its side. Put
t=1-h>59/60. Since A>5/6 and c+s>=1,

\[
 \begin{aligned}
 |V+(-c,s)|^2
   &=t^2+A^2+1+2(tc+As)\\
   &>\left(\frac{59}{60}\right)^2+
          \left(\frac56\right)^2+1+2\frac56\\
   &=\left(\frac{59}{60}\right)^2+
          \left(\frac{11}{6}\right)^2>R^2.
 \end{aligned}
 \tag{12}
\]

The last inequality is the exact reserve (3). The two axis limits
c=0 and s=0 are included. This excludes the second form too,
and proves Theorem 1.1.

## 5. The complete original shared-HK / H-owned-HB domain

Retain the actual original positive graph

\[
                    HK,HB,BK,HC,CK,HL_H,BL_B
 \tag{13}
\]

with true H4,K3,B3,C2, genuine S leaves at H,B, positive circle
loads at K,C, and all three arbitrary additional physical units.
Assume the actual HB is singleton owned only by H and HK is
physically shared with positive length. The entire original
radius interval and common compatible certificate are used.

The complete owned-singleton adjacent-port normal form supplies

\[
 \begin{gathered}
 0<\delta=d-1<1/60,\quad |h|\le\delta,\qquad
 n=\alpha v+\beta w,\quad 0<\beta<1/2,\\
 P=xv-uw,\quad L=\beta x+\alpha u,\quad
 Q=P+w,\quad m_{BK}=\frac{w-rn}{|w-rn|}.
 \end{gathered}
 \tag{14}
\]

The real B leaf is precisely the adjacent-vertex or positive-side
feature, with both actual concurrence formulas retained. Its
whole original BK ownership join gives K as the sole owner of
the singleton BK; B's normal is strict at Q.

Since HK is shared, H and K have the same side frame. Use coordinates
e_x=n, e_y=Jn=-beta v+alpha w. K's actual BK side axis must be one
of +/-n,+/-Jn. The Jn-component of w-rn is the strict positive
number alpha. Consequently its only possible common-frame side
axis is +Jn, and

\[
                  m_{BK}=Jn,\qquad r=\beta,
                  \qquad A=\alpha-L=\min_K y.
 \tag{15}
\]

This is forced by actual side ownership and the original mean,
not a new choice of normal or application. We next show uniformly
that

\[
                              5/6<A<1.
 \tag{16}
\]

## 6. Both complete leaf features put the K shelf above 5/6

### 6.1. The actual positive-side B leaf

Here x=delta and r=u/beta. Equation (15) forces u=beta^2, so

\[
 h=\alpha\delta-\beta^3,\qquad
 L=\beta\delta+\alpha\beta^2>0,\qquad
 A=\alpha^3-\beta\delta<1.
 \tag{17}
\]

The actual lower H support h>=-delta gives
beta^3<=delta(1+alpha). Since alpha=sqrt(1-beta^2)
<=1-beta^2/2 and delta<1/60,

\[
                    \beta^3+\frac{\beta^2}{120}<\frac1{30}.
 \tag{18}
\]

The left side is strictly increasing for beta>0. At beta=8/25
its excess over 1/30 is exactly 9/31250>0. Thus beta<8/25.
Consequently alpha^2>561/625 and alpha>71/75; the latter squared
reserve is 561/625-(71/75)^2=8/5625>0. Therefore

\[
 A>\frac{71}{75}\frac{561}{625}-\frac2{375}
       =\frac{39581}{46875}
       =\frac56+\frac{1037}{93750}>\frac56.
 \tag{19}
\]

The entire original side slider was kept until its actual equation
r=beta forced u=beta^2. No shared mean or leaf endpoint was fixed.

### 6.2. The actual adjacent-vertex B leaf

Here r=u/(beta+L)=beta gives
u(1-alpha beta)=beta^2(1+x). Both sides have positive factors.
Put

\[
 N=\sqrt{(\alpha-\beta)^2+\beta^2},\qquad
 E=\frac{\alpha-\beta}{N}.
 \tag{20}
\]

The actual leaf direction in the H frame is (E,-beta/N), as
is seen by normalizing
(1-alpha beta)v-beta^2 w. In that frame its numerator is
(alpha-beta,-beta), with squared norm N^2. Thus

\[
                  h=dE-\alpha,\qquad
                  L=\beta(d/N-1)>0,
                  \qquad A=\alpha-L<1.
 \tag{21}
\]

On 0<beta<1/2 one has alpha>beta, N<1 and 0<E<alpha.
For the last strict inequality,

\[
          \alpha^2-E^2
                =\frac{\beta^3(2\alpha-\beta)}{N^2}>0.
 \tag{22}
\]

The actual owner bound h>=-delta is equivalent to

\[
           \delta\ge f(\beta)=\frac{\alpha-E}{1+E}.
 \tag{23}
\]

This single function is strictly increasing on the whole interval.
Indeed alpha'=-beta/alpha and E'=-beta/(alpha N^3), hence

\[
 f'(\beta)=\frac{\beta}{\alpha(1+E)^2}
           \left(\frac{1+\alpha}{N^3}-(1+E)\right)>0.
 \tag{24}
\]

Positivity follows from N<1 and E<alpha. At beta=7/25 one has
alpha=24/25, N=13sqrt(2)/25 and E=17/(13sqrt(2)). The exact
comparison f(7/25)>1/60 is equivalent to
3679sqrt(2)>5185. Both quantities are positive and their squared
reserve is

\[
                         2\,3679^2-5185^2=185857>0.
 \tag{25}
\]

Equations (23)--(25) and delta<1/60 force beta<7/25 and
alpha>24/25. The same exact concurrence gives

\[
                     L(\alpha-\beta)=\beta h+\beta^2.
 \tag{26}
\]

Using h<=delta<1/60 and the strict component bounds therefore yields

\[
 L<\frac{(7/25)(1/60+7/25)}{24/25-7/25}
      =\frac{623}{5100},\qquad
 A>\frac{24}{25}-\frac{623}{5100}
      =\frac{4273}{5100}=\frac56+\frac{23}{5100}>\frac56.
 \tag{27}
\]

This proves (16) for the whole actual vertex feature as well,
with one derivative comparison and exact fixed rational reserves.
There is no radius or orientation subdivision.

## 7. Every actual shared-HK placement is now excluded

The actual K has y-interval [A,A+1]. H's x-interval is [h-1,h],
and its whole y-coordinate range is in [-1,1] by the owner-direction
theorem. Because their actual frames agree and HK has positive
shared length, there are exactly four side placements.

* K cannot lie to the left of H: that would give max_K x=h-1,
  whereas its actual BK point Q has x-coordinate h+beta>h.
* K cannot lie below H: that would give min_H y=A+1>1,
  contradicting the whole H range.
* If K lies to the right of H, its actual corner (h+1,A+1)
  has squared norm strictly above
  (59/60)^2+(11/6)^2>R^2 by (3). It is not contained.
* Therefore K lies above H. Their full actual positions are
  exactly (1), with H=[h-1,h]x[A-1,A], K=[k,k+1]x[A,A+1],
  P=(h,A-alpha), and v,w as in (1). Its actual Q is on K's
  bottom side, and K is physically boundary.

Every hypothesis of the purely physical Theorem 1.1 now holds
for the original H,B,K. The original C is a distinct actual
contained square physically touching both H and K, with disjoint
open interiors from them and B. Theorem 1.1 excludes it.

**Corollary 7.1.** In the whole original S/S hub-tip diamond,

\[
 \boxed{\quad HB\text{ singleton owned by H}
                    \ \Longrightarrow\ HK\text{ is not shared}.\quad}
 \tag{28}
\]

This conclusion covers the entire surviving narrow-angle interval
and both real B leaf features in that ownership class. It preserves
H4,K3,B3,C2, all positive forces, all actual shared means and all
three arbitrary extra units. No degree-three equation was assigned
to H, no degree-two equation to K, and no C force was removed.
In fact, after the actual B3 and owner-frame reduction, the return
contradiction needs only C's physical contacts and containment.

If the whole original central HK is shared, the HB singleton must
therefore be owned only by B. The earlier full shared-contact normal
form already rules out a shared HB in that case. The B-owned shared-
central family, the remaining singleton HK features, and the whole
original S/S gate stay open unless separately excluded. No new
original checklist row or coarse cell is closed by (28) alone.

## 8. Exact frozen inputs and verification boundary

| Input | SHA256 | Actual scope used |
| --- | --- | --- |
| TWO_S_ROOT_TRIANGLE_OWNED_SINGLETON_ADJACENT_PORT_NORMAL_FORM.md | 2397a468e15cb7043a4774f4ce5bfc3dabb34b0d85937991f444819b4cf2ac88 | Entire original leaf/port cover, actual concurrence and K owner; arbitrary H/K degrees |
| UNIT_SQUARE_COORDINATE_MINIMUM_INTERIOR_POINT.md | 9011a40a6b811dd62069fb4f5336a04196746ca148845a8fce0e75e14763b938 | Full actual point (max x-1,min y+1) in every unit orientation |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | Actual H range, true owner support and all leaf sliders |
| SS_HUB_TIP_SHARED_CONTACT_NORMAL_FORM.md | 18d2f8f7cfc86f9521b68ed05f1450ad19e79ed8399065cffa0419acca687278 | Original whole side-owner join and exclusion of shared HB when HK is shared |

The full physical shelf proof is given in Sections 1--4; it does
not import the narrower aligned-shelf hypothesis of an earlier
wall theorem. All tangent half-planes, vertex quadrants, lower
corner contacts and triangle-pocket boundaries are covered there.
The actual circle origin is never translated. No new computational
certificate, pose sample, orientation table, normal selection,
force deletion, changed mask, gate ID, ledger mutation, Lean run,
CI workflow or remote write is introduced.
