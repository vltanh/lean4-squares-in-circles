# Outer centers have private radial rays

## Theorem and scope

Let unit squares with pairwise disjoint open interiors lie in a closed disk
D_R centered at zero, where R<=2. Call a square outer if its center has norm
at least one. Then:

1. The entire positive center ray of any outer square misses every other
   outer square, including their boundaries.
2. For any packed square T, the segment from zero to its center misses
   every outer square other than T.
3. In circular order of the outer centers, only consecutive outer squares
   can touch. Thus their actual-contact graph is a subgraph of a cycle
   when there are at least three outer squares.
4. If that graph contains a cycle, it uses all outer squares. Its contact
   polygon winds once about zero and about the whole open interior of
   every noncycle square.

Unlike HUMAN_BOUNDARY_VISIBILITY.md, these assertions do not require the
blocking squares to meet the containing circle. All norms and contacts in
this note are geometric; no stress is chosen. The result is not the sharp
eight-square bound. It supplies a different, more restrictive contact
order for the outer squares while retaining all near-center squares.

## 1. Two elementary bounds

If a square has center p and orthonormal side frame e,f, its farthest
squared vertex norm is

    |p|^2+|p dot e|+|p dot f|+1/2.

Consequently every center has norm less than 3/2 when R<=2. Also, any
two square centers are at distance at least one, by their open inscribed
disks of radius 1/2.

For a square T centered at (a,0), put

    A=|e_x|+|f_x|,       1<=A<=sqrt(2).

Its horizontal and vertical widths are both A, and disk containment gives

    a^2+a A+1/2<=4.

When a>=1 this implies the strict bound

    a<1+1/(2A).                                           (1)

Indeed the left side at a=1+1/(2A) is

    2+A+1/A+1/(4A^2)>4,

using A+1/A>=2. It increases with nonnegative a.

If another square S has horizontal and vertical width B, and L is the
sum of the absolute cosine and sine of the relative frame angle, then

    B<=A L,       A<=B L.                                 (2)

For example express a side normal of S in the frame of T and apply the
triangle inequality for the sum of the absolute world coordinates. Each
of T's two unit frame vectors has that sum A. Interchange the squares for
the other inequality. On an axis owned by either square the sum of their
half-widths is (1+L)/2.

## 2. Assume an outer center ray meets another outer square

Rotate so that the center of T is (a,0), a>=1. Suppose the positive
horizontal ray meets S. Write p_S=(x,y), reflect in the horizontal axis
to make y>=0, and let B be S's width on each coordinate axis. Then

    0<=y<=B/2,       1<=B<=sqrt(2),       x^2+y^2>=1.

We have x>0. Otherwise x<=-sqrt(1-y^2)<=-B/2, so S is wholly in x<=0
and cannot meet the positive ray. The origin cannot belong to S either,
because its center norm is at least one and its circumradius is 1/sqrt(2).
Thus

    x>=sqrt(1-y^2).

Also a>x. If a<=x, then 0<=x-a<1/2, since x<3/2 and a>=1; together
with y<=1/sqrt(2), this would make the center distance less than one.

For any unit direction whose absolute coordinate components are c,s,
with c,s>=0 and c^2+s^2=1, the absolute center projection difference is
at most

    c(a-x)+s y
      <=c(a-sqrt(1-B^2/4))+s B/2
      <=c a+(s-c)B/2.                                    (3)

The first maximization uses the increase of
c(a-sqrt(1-y^2))+s y for y>=0. The second uses
sqrt(1-B^2/4)>=B/2, since B^2<=2.

We show (3) is strictly below the separating width for every axis of
both squares.

## 3. Axes owned by S

Here B=c+s. By (2), the required separating width is at least

    (1+B/A)/2.

If c=0, the projection is at most y<=1/2, strictly below this width.
If c>0, equations (1) and (3) give

    c a+(s-c)B/2
      =1/2+c a-c^2
      <1/2+c/(2A)+c(1-c)
      <=1/2+(c+s)/(2A).                                  (4)

For the last step, 2A c(1-c)<=s follows from A<=sqrt(2) and the identity

    s^2-8c^2(1-c)^2
      =(1-c)[8c(c-1/2)^2+(1-c)]>=0.

Both quantities compared before squaring are nonnegative. This excludes
both of S's axes, including their opposite signs.

## 4. Axes owned by T

Now A=c+s, and (2) bounds the separating width below by (1+A/B)/2.
The case c=0 follows immediately from y<=1/sqrt(2)<1 and the actual
half-width sum being at least one. For c>0, (1) and (3) show it suffices
to prove

    E(B):=B+A-2Bc-Bc/A+B^2(c-s)>=0,       1<=B<=sqrt(2).   (5)

The identity

    E(B)=(c-s)(B-1)^2+s[B/A-2(B-1)]                       (6)

proves this when c>=s: the first term is nonnegative and

    B/A-2(B-1)>=B/sqrt(2)-2(B-1)>=3-2sqrt(2)>0.

When c<=s, E is concave as a function of B. Its endpoint values are

    E(1)=s/A>=0,
    E(sqrt(2))=(3-2sqrt(2))c+s[sqrt(2)/A-1]>=0.

Concavity proves (5) on the full interval. The strict inequality in (1)
makes the projection strictly smaller than the separating width.

Every axis of both squares therefore has strict projection overlap.
The separating-axis theorem contradicts disjoint open interiors. This
proves the private-ray assertion, including at R=2.

## 5. Segments to centers of norm at most one

Let T have center p with |p|<=1, and let an outer square S have center q.
Then |q|>=1 and |q-p|>=1. We claim

    dist(q,[0,p])>=sqrt(3)/2.                              (7)

If the nearest point of the segment is an endpoint, its distance is at
least one. Otherwise write l=|p|<=1 and let the perpendicular foot have
distance t from zero along the segment, 0<t<l. If d is the perpendicular
distance, the two endpoint bounds give

    d^2>=1-t^2,       d^2>=1-(l-t)^2.

At least one of t,l-t is at most l/2<=1/2, yielding d^2>=3/4.
For p=0 the claim is immediate.

S lies in its circumdisk of radius 1/sqrt(2) about q. Since
sqrt(3)/2>1/sqrt(2), (7) makes [0,p] disjoint from S. For |p|>=1 use
the private-ray theorem instead. This proves assertion 2 for every T.

In particular all nonselected square interiors belong to the origin's
component of the open disk minus any selected outer squares: their center
segments provide paths, and their open interiors are connected and avoid
the selected closed squares. The assertion does not exclude empty pockets.

## 6. The cyclic order of outer contacts

An outer square's angular shadow is a closed arc containing its center
direction in its relative interior. Its length is at most pi/2: the square
is in its radius-1/sqrt(2) circumdisk and its center norm is at least one.
Distinct outer center directions are different, and no outer shadow contains
another outer center direction, by the private-ray theorem.

If two outer squares touch, their shadows meet at the direction of their
contact point, which is nonzero. Their union is a connected proper arc of
length at most pi. It contains both center directions and no other outer
center direction. Those two centers are consequently consecutive in the
circular order. The contact direction lies in their intervening empty gap:
it cannot lie beyond either center direction without putting that direction
in the other shadow.

For at least three outer squares, the resulting graph is a subgraph of
the cycle joining consecutive center directions. If it has a cycle, it is
that whole cycle.

## 7. All noncycle units lie inside an outer contact cycle

At each edge of such a cycle choose any common contact point. Inside each
cycle square join its incoming point to its center, then its center to the
outgoing point. Their lifted arguments are in increasing order: the two
contact points are in the empty gaps before and after the center direction.
All segments avoid zero. Traversing all the squares in circular order
therefore increases the argument by exactly 2pi. The resulting curve has
winding number one about zero.

For any noncycle square T, its segment from zero to its center misses all
cycle squares, by assertion 2. Winding stays one along that segment. Also
int(T) avoids every closed cycle square and is connected, so the winding
is one on all of int(T).

Replacing each two-segment path by its contact chord is a homotopy inside
the owning square. It avoids zero and every noncycle square interior.
Hence the contact polygon has the same winding assertions. Degenerate
contacts and repeated contact points cause no problem for this homotopy.

This yields a concrete new reduction: an outer actual-contact cycle cannot
leave any unused unit in a zero-winding pocket. It is not necessary to select
a physical stress or prove the cycle has positive contact moments.

## 8. Remaining sharp step

The theorem does not assert that every exterior square has center norm at
least one. Indeed the displayed sharp construction permits a near-center
exterior slider. Nor does it show that the outer graph must contain a cycle;
it may be a union of paths attached to near-center squares.

Thus the unresolved configurations are localized to those near-center
squares and their attachments, or to outer cycles enclosing the remaining
near-center units. A lower-bound proof still has to handle those configurations
quantitatively. The present result alone does not establish R8>=Rhat.
