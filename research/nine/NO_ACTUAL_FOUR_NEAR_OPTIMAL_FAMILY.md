# Nine squares without an actual four-chain, arbitrarily close to the target radius

This is an exact hand construction and an all-directions proof. It rules
out the proposed stronger claim that nine squares with no actual
projection four-chain must have squared containing radius at least
\(9/2\). More strongly, no lower bound strictly greater than
\(Q=1105/256\) can hold for that class.

The construction does **not** disprove the sharp target bound \(Q\).
Every member has squared radius strictly greater than \(Q\), tending
down to it. Thus a global proof based on the absence of actual
four-chains must handle this class sharply, including its approach to
the usual attaining packing. No numerical optimizer or table is a proof
input below.

## 1. One exact family of nine original squares

Choose \(0<t\le1/100\), and put

\[
 c=\frac{1-t^2}{1+t^2},\qquad s=\frac{2t}{1+t^2},\qquad
 u=(c,s),\quad v=(-s,c),
\]
\[
 h=\frac{c+s}{2},\qquad
 a=\frac{1+c+s}{2}=\frac{1+t}{1+t^2},\qquad
 b=\frac1c,\qquad X=a+\frac b2,\qquad y_0=\frac1{16}.
\tag{1}
\]

The frame \((u,v)\) is orthonormal. A square with this frame is
called tilted; aligned means the frame \((1,0),(0,1)\). Give the
nine original unit squares the following centers and frames:

| Originals | Centers | Frame |
|---|---|---|
| Outer pair \(A,D\) | \((-X,y_0),(X,y_0)\) | Aligned |
| Inner pair \(B,C\) | \((-b/2,y_0),(b/2,y_0)\) | Tilted |
| Lower triple \(L,M,N\) | \((-1,y_0-a),(0,y_0-a),(1,y_0-a)\) | Aligned |
| Upper pair \(U,V\) | \((-b/2,y_0+2h),(b/2,y_0+2h)\) | Tilted |

All centers and frames are rational whenever \(t\) is rational.
For example, \(t=1/100\) gives

\[
 (c,s)=\frac{(9999,200)}{10001},\quad
 a=\frac{10100}{10001},\quad
 b=\frac{10001}{9999},\quad
 X=\frac{301999801}{199999998}.
\tag{2}
\]

## 2. The whole physical packing is valid

The tilted square's horizontal and vertical halfwidth is \(h\),
and an aligned square's is \(1/2\). In particular
\(a=h+1/2>1\) and \(bc=1\). The following comparisons check
all 36 original pairs.

| Pair family | Physical separating projection |
|---|---|
| The outer pair | Horizontal center gap \(2X>3\) |
| Either outer versus any tilted square | Horizontal center gap at least \(a=h+1/2\) |
| Either outer versus any lower square | Vertical center gap \(a>1\) |
| Pairs within the lower triple | Horizontal center gap at least one |
| Lower squares versus inner or upper tilted squares | Vertical center gap at least \(a=h+1/2\) |
| Inner tilted squares versus upper tilted squares | Vertical center gap \(2h\) |
| The pair within either tilted row | Projection of their center difference on \(u\) equals \(bc=1\); each square has width one in this direction |

Equality is allowed in a physical separating projection, so all original
open interiors are disjoint. This verification does not replace the
tilted originals by aligned squares or by their insets.

## 3. Exact containing radii above \(Q\) and below \(9/2\)

On \(0<t\le1/100\), direct monotonicity in (1) gives

\[
 1<a<\frac{101}{100},\quad
 1<b<\frac{1001}{1000},\quad
 \frac12<h<\frac{51}{100},\quad
 \frac32<X<\frac{151}{100}.
\tag{3}
\]

For the last bound, \(a'(t)=(1-2t-t^2)/(1+t^2)^2>0\)
and \(b'(t)>0\), so evaluate \(X\) at the right endpoint
using (2). The integer comparison for \(X<151/100\) is

\[
 30199980100<30199999698.
\]

The outer pair has largest squared corner norm

\[
 q(t)=\left(X+\frac12\right)^2+\left(\frac9{16}\right)^2.
\tag{4}
\]

This exceeds \(Q\) because \(X>3/2\), and

\[
 q(t)<\left(\frac{201}{100}\right)^2+\frac{81}{256}
       =\frac92-\frac{22959}{160000}<\frac92.
\tag{5}
\]

The largest lower-square corner norm is
\(9/4+(a+7/16)^2\). Since \(b>1\), subtracting it from
(4) gives the strict bound

\[
 q(t)-\left[\frac94+\left(a+\frac7{16}\right)^2\right]
 > (a+1)^2+\frac{81}{256}-\frac94
                 -\left(a+\frac7{16}\right)^2
 =\frac98(a-1)>0.
\tag{6}
\]

Every tilted square is inside its centered coordinate bounding square
of halfwidth \(h\), so (3) bounds every tilted corner norm by

\[
 \left(\frac b2+h\right)^2+
 \left(y_0+3h\right)^2
 <\left(\frac{51}{50}\right)^2+\left(\frac85\right)^2
 =\frac{9001}{2500}<Q.
\tag{7}
\]

Here \(b/2<51/100\) and
\(y_0+3h<637/400<8/5\). Equations (4), (6), and (7)
therefore show that \(q(t)\) is exactly the largest squared corner
norm of this packing. Convexity gives containment of every whole square.
Finally \(a,b\to1\) as \(t\to0\), so

\[
 q(t)>Q,\qquad \lim_{t\downarrow0}q(t)=Q.
\tag{8}
\]

At \(t=0\) the construction becomes the usual aligned attaining
packing. The absence of an actual four-chain established next holds for
every positive parameter, however small.

Changing the containing disk's center cannot produce a counterexample
below \(Q\). Indeed, for a proposed center \((p,z)\) with
\(z\le0\), one of the two original outer corners
\((\pm(X+1/2),9/16)\) has squared distance at least \(q(t)>Q\).
For \(z\ge0\), one of the two original lower corners
\((\pm3/2,-a-7/16)\) has squared distance at least
\(9/4+(a+7/16)^2>Q\), since \(a>1\).
Thus the smallest enclosing radius is strictly above the target as
well. Formula (4) specifies the exact radius about the displayed origin;
it need not be the radius of the smallest enclosing disk.

## 4. Any actual four-chain would have the two outer endpoints

Subtract the common vector \((0,y_0)\) when comparing centers.
The outer centers become \((\pm X,0)\); every other center lies
in \([-1,1]\times[-a,2h]\).

Every center pair other than \(A,D\) has distance strictly less
than three. For an outer center and any other nonouter center, the
squared distance is less than

\[
 \left(\frac{251}{100}\right)^2+
 \left(\frac{51}{50}\right)^2
 =\frac{73405}{10000}<9.
\tag{9}
\]

For two nonouter centers it is less than

\[
 2^2+\left(\frac{203}{100}\right)^2
 =\frac{81209}{10000}<9,
\tag{10}
\]

using \(a+2h<203/100\).

In an actual projection four-chain, the extreme center projections
differ by at least three: sum its three separation inequalities and
use the minimum halfwidth \(1/2\). Thus the extreme center distance
is at least three. By (9)--(10), its endpoints must be \(A,D\).
Reverse the direction and chain if necessary, writing the projection
direction as \(e=(C,S)\) from \(A\) towards \(D\). Then

\[
 C^2+S^2=1,\qquad 2XC\ge3,\qquad
 C>\frac{150}{151}>\frac{99}{100},\qquad |S|<\frac17.
\tag{11}
\]

For the last comparison,
\(1-(99/100)^2=199/10000<1/49\).

## 5. Its intermediate squares would have to be one tilted square in each column

Let \(p_1,p_2\) be the two intermediate center projections after
the common translation. Consecutive center projection gaps are at least
one, while the endpoint projections are \(-XC,XC\). Therefore

\[
 -\frac{51}{100}<p_1<-\frac{49}{100},\qquad
 \frac{49}{100}<p_2<\frac{51}{100}.
\tag{12}
\]

Indeed \(p_1\ge-XC+1\), \(p_1\le XC-2\), and similarly
for \(p_2\), while \(XC\le X<151/100\).

The middle lower square has center projection \(-aS\), whose
absolute value is less than \(101/700<49/100\). Either outside
lower square has center projection \(\pm C-aS\), whose absolute
value exceeds

\[
 \frac{99}{100}-\frac{101}{700}
 =\frac{148}{175}>\frac{51}{100}.
\]

No lower original satisfies (12). The intermediate originals must thus
come from the four tilted squares.

A tilted center in the left column has negative projection, and one in
the right column has positive projection. Indeed its possible height
term has magnitude below \((51/50)/7\), whereas
\((b/2)C>99/200>(51/50)/7\). Consequently the first intermediate
is in the left column and the second is in the right. Their centers have
the forms

\[
 (-b/2,Y_L),\quad (b/2,Y_R),\qquad
 Y_L,Y_R\in\{0,2h\}.
\tag{13}
\]

## 6. No direction separates all three chain links

Let \(H(e)\) be the sum of the projection halfwidths of an aligned
square and a tilted square. The exact support formula is

\[
 H(e)=\frac{C+|S|+|cC+sS|+|-sC+cS|}{2}.
\tag{14}
\]

We prove \(H(e)>aC\) whenever \(S\ne0\) subject to (11).
The term \(cC+sS\) is positive: \(c>99/100\),
\(C>99/100\), and \(s|S|<1/350\).

If \(S<0\), then \(-sC+cS<0\), and (14) gives

\[
 H(e)=aC+\frac{s-c-1}{2}S>aC.
\tag{15}
\]

The first chain gap in (13), from \(A\), has projection
\(aC+Y_LS\le aC\). It cannot meet the separation threshold
\(H(e)\).

If \(S>0\) and \(cS\le sC\), then

\[
 H(e)=aC+\frac{1+s-c}{2}S>aC.
\tag{16}
\]

If \(S>0\) and \(cS\ge sC\), then instead

\[
 H(e)=(a-s)C+aS,\qquad
 H(e)-aC=aS-sC\ge sC\left(\frac ac-1\right)>0.
\tag{17}
\]

Here \(a>c\) follows from \(1+s>c\). In either positive case,
the last chain gap, from the tilted right intermediate to \(D\),
has projection \(aC-Y_RS\le aC\), so that link fails.

The only remaining direction has \(S=0,C=1\). The middle link
then has center projection gap \(b\), while the two tilted
halfwidths sum to \(2h=c+s\). But

\[
 c(c+s)-1=s(c-s)>0,
 \qquad b=\frac1c<c+s.
\tag{18}
\]

Thus the middle link fails in this direction too. Every possible
direction and every choice of intermediate originals has been covered.
There is no actual projection four-chain anywhere in the packing.

## 7. Precise consequence for the unrestricted proof

The family consists of nine physical original squares, with every pair
and corner checked, and no actual four-chain in any direction. Its
radius squares belong to \((Q,9/2)\) and approach \(Q\).
Consequently neither a \(9/2\) bound nor any other fixed improvement
above \(Q\) is valid under the no-actual-four hypothesis.

The proposed implication

> Nine squares with no actual four-chain in any direction still require
> squared radius at least \(Q\)

remains possible and unproved here. It must have a sharp argument near
this family. Rotating or relabeling a witness alone cannot give an actual
four-chain for the nearby packings above \(Q\). This is an obstruction
to a stronger global route, not a closure of any strict-subcritical mask.
