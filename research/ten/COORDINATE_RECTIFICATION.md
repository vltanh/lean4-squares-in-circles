# Rectifying squares separated along common coordinate axes

**Status:** the rectification lemma below is a complete hand proof for any
number of squares. Its ten-square corollaries use the all-parallel lower
bound and equality theorem in `ALL_PARALLEL_THEOREM.md`.

This allows independently rotated squares, provided every pair has a
horizontal or vertical separating line in one common orthonormal frame.
Physical interior-disjointness alone does not imply this hypothesis:
oblique separating axes remain the unrestricted problem.

## 1. The common-coordinate hypothesis

Use coordinates centered at the containing disk's center. A unit square
with center (x,y) and frame (c,s), c^2+s^2=1, has an axis-parallel bounding
box with halfwidth

    h = (|c|+|s|)/2.

The common-coordinate hypothesis says that these bounding boxes have
pairwise disjoint interiors. Equivalently, for each pair i!=j,

    |x_i-x_j| >= h_i+h_j
        or |y_i-y_j| >= h_i+h_j.

The choice between horizontal and vertical separation may vary with the
pair; only the two coordinate directions are fixed.

## 2. Rectification of one square

Put w=2h=|c|+|s|. Then 1<=w<=sqrt(2). Set

    m = h-1/2,
    d = 1-h,
    x' = sign(x)*max(|x|-m,0),
    y' = sign(y)*max(|y|-m,0).

Replace the square by the axis-parallel unit square centered at (x',y').
Its bounding box is contained in the original square's bounding box.
Indeed, x' is the point nearest zero in the interval
[x-h+1/2,x+h-1/2], and likewise for y'.

**Rectification lemma.** If the original square lies in the disk of
squared radius q, the replacement also lies in that disk. If the original
square is not axis-parallel and its center is not the disk center, the
replacement lies strictly inside the disk whenever q is the original
square's farthest-vertex squared norm.

### Proof

Write X=|x| and Y=|y|. The replacement's farthest-vertex squared norm is

    F' = max(X+d,1/2)^2 + max(Y+d,1/2)^2.

Since 0<=d<=1/2, for every Z>=0,

    max(Z+d,1/2)^2 <= Z^2+2*d*Z+1/4.

If Z+d>=1/2, this follows from d^2<=1/4; otherwise it follows from
Z^2+2*d*Z>=0. Consequently

    F' <= X^2+Y^2+1/2+2*d*(X+Y).                 (1)

Let u=c*x+s*y and v=-s*x+c*y be the center's coordinates in the
square's frame. The original farthest-vertex squared norm is exactly

    F = X^2+Y^2+1/2+|u|+|v|.

Reconstructing x=c*u-s*v and y=s*u+c*v and applying the triangle
inequality gives

    X+Y <= (|c|+|s|)*(|u|+|v|) = w*(|u|+|v|).

Also

    1/w-(2-w) = (w-1)^2/w >= 0,
    2*d = 2-w.

Therefore

    F >= X^2+Y^2+1/2+(X+Y)/w
      >= X^2+Y^2+1/2+2*d*(X+Y)
      >= F'.                                                (2)

This proves disk containment. When w>1 and X+Y>0, the second
inequality in (2) is strict. The only unit-square frames with w=1
are axis-parallel frames. QED.

## 3. Rectification of a packing

Apply the construction independently to every square. Because each
replacement's bounding box is a subset of the original bounding box,
common-coordinate separation is preserved. Thus the replacements are
pairwise interior-disjoint axis-parallel unit squares in the same disk.

This proves, for every n and every q, the implication

    independently rotated common-coordinate-separated n-packing in D_q
       => axis-parallel n-packing in D_q.

No claim is made that the replacement square lies in the original
rotated square itself. Bounding-box containment is the property that
preserves the stated separation hypothesis.

## 4. Ten-square lower bound

The all-parallel theorem gives q>=9/2 for ten axis-parallel unit squares.
Applying it to the rectified packing proves the same lower bound for ten
independently rotated squares under common-coordinate separation.

The construction already exhibited in `CONSTRUCTION.md` shows this
bound is attained in this class.

## 5. Equality preserves the entire parallel family

Suppose a common-coordinate-separated ten-packing has q=9/2. By the
all-parallel equality theorem, the rectified packing, after a rotation
of the common frame and relabeling, consists of

* the four anchor squares centered at (±1,±1);
* two side squares at (-u,0),(v,0), with 1<=u,v<=a;
* four central squares at (0,t_i), with
  -a<=t_1, t_(i+1)-t_i>=1 and t_4<=a;

where a=(sqrt(17)-1)/2<2.

First, the original squares corresponding to the four anchors are
axis-parallel. Their replacements have farthest squared norm 9/2;
strictness in (2) rules out w>1 unless the original center is zero.
A square centered at zero has farthest squared norm 1/2 and cannot
rectify to an anchor. Thus w=1, rectification leaves the square unchanged,
and all four original anchors are fixed.

The original packing now satisfies the hypotheses of
`ANCHORED_EQUALITY_CLASSIFICATION.md`: it has ten physically
interior-disjoint unit squares in the disk of squared radius 9/2 and
four exact anchors. That theorem permits arbitrary orientations of the
other six squares and proves that every one is axis-parallel, with
precisely the six-parameter family displayed above. Thus the equality
classification follows without any further assumption about their
pairwise separating directions.

## 6. Remaining unrestricted obligation

An arbitrary physical packing has separating lines, but their normals
can be axes of different squares. Their bounding boxes in a fixed frame
can overlap even when the squares do not. The rectification lemma cannot
be applied to such a packing without an additional theorem establishing
the common-coordinate hypothesis, or a separate argument handling the
oblique cases. No such implication is assumed here.

The one-square algebra and its strictness were independently checked by
two agents. This is a hand proof; Lean compilation and kernel verification
have not been performed.
