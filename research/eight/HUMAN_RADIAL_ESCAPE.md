# Radial escape and the exclusion of two enclosed units

## Theorem

Let S be a unit square contained in the closed disk D_2 centered at zero.
Let B be a closed disk of radius 1/2 with center p, where |p|>=1/2.
If their open interiors are disjoint, then

    S intersection {t p : t>=1} is empty.                 (1)

The statement concerns the closed square and the entire outward ray.
It does not require a common frame, circle contact, a stress, or
radius minimality. The disk B itself need not lie in D_2.

In particular, in a packing of unit squares in D_2, the outward center ray
of every square whose center has norm at least 1/2 misses every other
closed square. This strengthens the boundary-only visibility statement,
but concerns the outward ray, not the segment from zero to that center.

A consequence is that a closed curve contained in the union of some of the
packed squares can have nonzero winding about at most one remaining whole
unit square. Every remaining unit with nonzero winding has center norm
strictly less than 1/2.

## 1. Normalize a putative ray intersection

Rotate coordinates so p=(a,0), a>=1/2. Suppose S meets the ray x>=a,y=0.
Disjointness of open interiors implies that the entire closed square S
avoids the open disk int(B). Indeed a point of S in that open disk could
be approximated by interior points of S, creating an open overlap.
Consequently a point of S on that ray has x coordinate at least a+1/2.

Write (x,y) for the center of S. Reflect in the horizontal axis to take
y>=0. Choose its unsigned frame difference theta in [0,pi/4], and put

    c=cos(theta), s=sin(theta),
    H=(c+s)/2, D=c-s, u=x-a.

The half-width of S on either coordinate axis is H, independent of the
sign of its frame angle. Ray intersection implies y<=H and

    u>=1/2-H.

The open inscribed disk of S has radius 1/2. Its disjointness from int(B)
therefore gives

    u^2+y^2>=1.                                          (2)

Since 1/2<=H<=1/sqrt(2), u cannot be nonpositive: otherwise

    u^2+y^2 <= (H-1/2)^2+H^2
             <=5/4-1/sqrt(2)<1.

The middle expression increases with H on the stated interval. From (2),

    u>=sqrt(1-y^2)>=sqrt(1-H^2)>=H>=y.                  (3)

In particular every point of S has x coordinate at least a, and x>=y.

## 2. The favorable sign of the frame angle

We may replace a negative frame angle by +theta, keeping the center fixed.
This replacement preserves the half-widths and the line intersection,
does not enlarge the farthest-vertex norm, and does not decrease the
distance from p to S. Here is a proof of both comparisons.

For any vector (v,w) with v>=w>=0, its first coordinate in the +theta
frame is vc+ws. This is at least the absolute value of either coordinate
in the -theta frame, since

    vc+ws >= |vc-ws|,
    vc+ws-(vs+wc)=(v-w)(c-s)>=0.

Thus reflection increases the largest absolute local coordinate, while
preserving the squared norm of the coordinate pair.

At fixed squared norm, the sum of the two nonnegative coordinates is
nonincreasing as their larger coordinate increases. This proves the
farthest-vertex comparison, using

    max_vertex |z|^2=|center|^2+1/2
                    +|center dot e|+|center dot f|,

and (x,y) with x>=y. At fixed squared norm, the function

    (v-1/2)_+^2+(w-1/2)_+^2

is nondecreasing as the larger coordinate increases. When both coordinates
exceed 1/2 this is squared norm minus their sum plus 1/2. When the smaller
coordinate is at most 1/2 it is just the increasing square of the larger
coordinate minus 1/2; the formulas agree at the transition. This is the
squared distance to a centered unit square. Applying it to (u,y), with
u>=y from (3), proves the disk-clearance comparison.

After the replacement the square is still in D_2 and still avoids int(B).
Its line intersection remains on the positive ray because every one of its
x coordinates is at least a. Henceforth its frame is

    e=(c,s), f=(-s,c), 0<=theta<=pi/4.

Translate S and p to the left by a-1/2. This preserves their separation
and the ray intersection. Every square vertex originally had x coordinate
at least a, so this translation only decreases its squared norm.
It suffices to treat a=1/2.

Now translate S alone to the left, keeping y and its frame fixed, until
its distance from p first equals 1/2. Such a first position exists: if its
center reached x=a, its inscribed disk would overlap B because y<=H<1.
Before that first contact (2)--(3) persist. Thus all square vertices retain
nonnegative x coordinates and their norms do not increase. The square
remains in D_2 and intersects the line y=0. At first contact it still
avoids int(B), so its line intersection is still on the right side of B.

We have reduced to exact tangency between B and S, with

    a=1/2, 0<=y<=H, and S contained in D_2.                (4)

## 3. Only one disk-square tangency branch can survive

Let z be the nearest point of S to p, and let n=2(z-p) be the unit normal
from the disk toward S. If v is the supporting point of the centered
square in direction n, tangency says

    (x,y)-p=v+n/2.                                       (5)

All points of S have x coordinate at least a. Thus n_x>=0. In fact n_x>0:
if n were vertical, (5) would force |y|=H+1/2, contradicting (4).
Write n=(cos(phi),sin(phi)), -pi/2<phi<pi/2.

The following is the complete support-face split for (5).

* If theta-pi/2<phi<theta, the support point is
  v=(e-f)/2=(H,-D/2). The condition y>=0 gives sin(phi)>=D>=0,
  hence 0<=phi<=theta and cos(phi)>=c. Therefore

      x=a+H+cos(phi)/2 >= a+c+s/2 >=3/2.                (6)

  The last inequality follows from c+s/2>=1 on [0,pi/4]: this concave
  function has endpoint values 1 and 3/(2sqrt(2)), both at least one.
  But every unit-square center in D_2 satisfies

      |center| <= (sqrt(15)-1)/2 <3/2,                  (7)

  by the farthest-vertex formula and
  |center dot e|+|center dot f|>=|center|. Thus (6) is impossible.

* If theta<phi<pi/2, the support point is v=(e+f)/2=(D/2,H).
  Then y=H+sin(phi)/2>H, impossible.

* If -pi/2<phi<theta-pi/2, the support point is
  v=(-e-f)/2=(-D/2,-H), giving y=-H+sin(phi)/2<0.

* At the side normal n=-f, equation (5) has the form
  (x,y)-p=-f+t e, |t|<=1/2. It gives y=-c+t s<0.

The only remaining side normal is n=e. Endpoints of the vertex branches
are included in these side-face cases; normals with n_x=0 were excluded
above. We must therefore have

    (x,y)=p+e+t f,      -1/2<=t<=1/2.                    (8)

## 4. Two elementary bounds contradict radius two

In (8), y=s+t c<=H, so

    t<=(c-s)/(2c).

The two local coordinates of the center are 1+c/2 and t-s/2.
Consequently the exact farthest squared vertex norm Q_S satisfies

    Q_S=(3/2+c/2)^2+(1/2+|t-s/2|)^2.

The second term's positive square root is both at least 1/2 and at least

    1/2+s/2-t >= (s/2)(1+1/c).

It follows that Q_S is at least both

    A(c)=((3+c)^2+1)/4,
    B(c)=9/4+c+1/(2c)+1/(4c^2).                         (9)

For B, expand (3+c)^2/4+s^2(1+1/c)^2/4 and use s^2=1-c^2.
On 0<c<=1,

    B'(c)=(c-1)(2c^2+2c+1)/(2c^3)<=0.                  (10)

If c>=7/8, the first bound in (9) gives

    Q_S>=A(7/8)=1025/256>4.

If c<=7/8, (10) and the second bound give

    Q_S>=B(7/8)=1577/392=4+9/392>4.

Both contradict (4). This proves the radial-escape theorem, including
all tangency and ray-endpoint cases. No numerical minimizer or interval
cover is used.

## 5. At most one whole unit can have nonzero winding

Let gamma be any closed curve contained in the union of some packed
squares in D_2. The open interior of every other packed square T avoids
gamma and is connected, so its winding number is constant there.

If |p_T|>=1/2, apply the theorem to the inscribed radius-1/2 disk of T
and to each square used by gamma. The ray {t p_T:t>=1} misses all of
them. It connects p_T to infinity without crossing gamma. Thus gamma
has winding zero about p_T and throughout int(T).

Every noncycle unit with nonzero winding therefore has center norm <1/2.
Two such centers would be at distance less than one by the triangle
inequality. That is impossible for interior-disjoint unit squares, whose
open inscribed radius-1/2 disks are disjoint. Hence there is at most one
such unit. This counts units, not winding multiplicities; a curve can
wind repeatedly about the same unit.

## 6. The six-outer-cycle case is excluded

Apply HUMAN_OUTER_GRAPH_REDUCTION.md to an eight-square packing below
its radius ceiling sqrt(98/25). If the induced graph of squares with
center norm at least one is a cycle, that note proves it has six or
seven vertices and that every remaining unit is inside its contact
polygon, with winding one.

The six-vertex alternative would enclose two whole units. Section 5
excludes it. Therefore the exhaustive alternatives sharpen to:

1. a seven-outer cycle enclosing only the central unit, whose center
   necessarily has norm <1/2; or
2. outer paths and isolated vertices, with the inner attachments already
   required by HUMAN_OUTER_GRAPH_REDUCTION.md.

This closes the six-outer-cycle case without replacing either enclosed
square by its convex hull with the other. The seven-cycle sharp inequality
and the path-with-inner-attachments alternatives are not settled by this
note. In particular (1) concerns a ray of points, not a collision-free
outward translation of an entire square.
