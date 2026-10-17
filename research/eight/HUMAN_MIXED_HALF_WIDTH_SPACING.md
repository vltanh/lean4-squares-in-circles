# Exact mixed-frame center spacing in a narrow column

## Theorem (one parallel, one arbitrary square)

Let Q be a horizontal/vertical unit square, and let S be
an independently rotated unit square, with pairwise disjoint
open interiors. Write their center difference as (dx,dy).
If

    |dx|<=1/2,

then

    |dy|>=1.                                          (1)

If equality |dy|=1 holds, the frame of S must also be
horizontal/vertical (modulo quarter-turn symmetry).
Conversely, two parallel unit squares at vertical center
distance one and arbitrary |dx|<=1/2 are disjoint in
their open interiors, so the bound is sharp.

This is stronger than the arbitrary-frame two-unit
*whole-projection-span* lemma in
HUMAN_TWO_ARBITRARY_TRANSVERSE_SPAN.md when one of
the two frames is known to be parallel to the
coordinate axes. Crucially, (1) gives an exact
**center-coordinate** separation, not merely a
combined support-width bound. No containing-circle
assumption is needed.

## Hand proof

Choose the unsigned angle theta of S modulo
square quarter turns and reflection in [0,pi/4],
and put

    c=cos(theta), s=sin(theta), L=c+s,
    W=(1+L)/2.

For Q and S, every side-axis separating projection
has required absolute center displacement at least W.
The separating-axis theorem gives only four
unoriented candidate axes: horizontal, vertical,
and the two side normals of S.

Suppose |dx|<=1/2 and |dy|<1. On the horizontal
or vertical axes, respectively,

    |dx|<=1/2<W,    |dy|<1<=W.                      (2)

For the first tilted axis with absolute coordinate
components (c,s),

    |n dot(p_S-p_Q)|
      <=c*|dx|+s*|dy|
       <c/2+s,

while

    W-(c/2+s)=(1-s)/2>0.                         (3)

For the second tilted axis with absolute components
(s,c),

    |m dot(p_S-p_Q)|
      <=s*|dx|+c*|dy|
       <s/2+c,

and

    W-(s/2+c)=(1-c)/2>=0.                         (4)

When theta=0, the second axis is vertical
and |dy|<1 already supplies strictness.
When theta>0, c<1 makes (4) strict.
Thus **no** side axis supplies a separating
projection, contradicting the separating-axis
theorem. This proves |dy|>=1.

For equality |dy|=1 with nonparallel theta>0,
(2) remains strict since W>1, while (3)--(4)
become non-strict upper bounds that are still
**strictly below W** because s<1 and c<1.
Again no separating axis exists. Therefore
theta=0 and S is parallel to Q.
The parallel equality construction is immediate.

Interchanging x and y proves the rotated
version: if |dy|<=1/2 then |dx|>=1,
with equality only when both frames align
with the specified coordinate axes.

## Relevance to the one-exterior-rotation branch

If seven squares including the central square
have one common frame, and the remaining
exterior square has an arbitrary frame, then
every aligned square whose center is within
a half-unit horizontal strip of the rotated
center must be separated vertically by at
least one full unit. Along any mixed
three-square column with two parallel
outer members and center abscissa differences
at most 1/2, the outer parallel pair's
vertical center gap is at least two. Thus
its two farthest vertical vertices span at
least three, exactly the four-point
obstruction used in
HUMAN_PARALLEL_EIGHT_OPTIMUM.md.

The theorem by itself does not show those
abscissa differences are <=1/2 in every
eight-square packing; the wider side-cell
and corner-owned separating-axis cases
remain the global gap. No unrestricted
R8>=Rhat conclusion is inferred.
