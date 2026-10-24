# n=9 TL.6: a complete eight-square capacity bound for every six-body two-column cage

**Status:** new all-orientation hand completion theorem. Independent full
mathematical audit and Lean verification pending. No numerical pose search
or angle grid is a proof premise.

Put q0=17/4 and Q=1105/256. This manuscript proves a complete physical
capacity bound for a six-square skeleton, including **all arbitrary
rotations and oblique separators of the remaining squares**. It closes
both six-body graph topologies in the two-loaded component inventory.
It does not close the four-body P family, the five-body two-loaded
component, the Y family, or all cyclic cells with three or more loads.

## 1. The exact six-square family

In the disk D={x^2+y^2<=17/4}, fix two aligned outer squares centered at

    (-3/2,0), (3/2,0),

and four aligned inner squares centered at

    (-1/2,a), (-1/2,b), (1/2,c), (1/2,d),

with

    -1<a<b<1,  b-a>=1,
    -1<c<d<1,  d-c>=1.                                  (1)

Assume the six physical square interiors are disjoint and lie in D.
The within-column conditions imply a,c<0<b,d. Across the vertical seam,
the lower two squares have a positive-length overlap of their vertical
projection intervals, as do the upper two, since |a-c|<1 and |b-d|<1.
They are of course physically disjoint because their horizontal interiors
lie on opposite sides of x=0.

**Theorem TL.6.** At most TWO other physical unit squares can be added to
this skeleton in D. Their individual orientations and separating axes
are unrestricted. Therefore every complete packing containing (1) has
at most EIGHT squares, never nine.

The strict center ranges in (1) are satisfied by all six-body components
of the selected strict-point-contact two-loaded stress certificate.
The theorem itself only needs the displayed geometric hypotheses, not
force or torque equilibrium.

## 2. A new all-angle cap-section lemma

**Lemma S.1 (central section).** Let a unit square T lie in D and in y>=1/2.
Either

    T = [-1/2,1/2] x [1,2] =: N,

or its intersection with y=1 has a nonempty **open interior section** I
such that

    length(I)>1/2,
    inf(I)<1/2,   sup(I)>-1/2.                            (2)

In particular I meets the open central segment (-1/2,1/2). No obstacle
squares or common orientation hypotheses are needed for this lemma.

### 2.1 The unique line-boundary exception

The exact farthest-corner bound implies |center(T)|<=3/2. If h is its
vertical halfwidth, then h>=1/2 and center height y>=h+1/2>=1. The top
height is at least 3/2, whereas the bottom height is <=3/2-h<=1.
Thus y=1 crosses the open interior except when the bottom is exactly one.
Equality then forces center=(0,3/2), h=1/2 and axis alignment, giving N.
This handles the full closed-boundary case rather than silently using an
interior section for the exceptional top square.

### 2.2 The open section has length greater than one half

By square quarter-turn equivalence and horizontal reflection, choose
side directions (A,B),(-B,A), with A>=B>=0 and A^2+B^2=1. Set

    h=(A+B)/2,  k=(A-B)/2.

For B=0 the nonexceptional section has length one. Suppose B>0.
Since y>=h+1/2>1, the line lies below the center. In the central strip
its chord length is 1/A>=1. Otherwise, near the bottom vertex, its length is

    ell=(1+h-y)/(A B).                                   (3)

We prove 1+h-y>AB/2 over the full angle range.

**Case A>=4B.** For fixed y>0, exact corner containment is

    F(x,y)=x^2+y^2+1/2+|A x+B y|+|-B x+A y|<=17/4.

Its minimum in x occurs in [-By/A,0]: outside this interval its derivative
points inward. Inside the interval both absolute-value arguments are
nonnegative, and minimization of the resulting quadratic gives

    min_x F = (y/A)^2+y/A+1/2,   if By/A <= k;
              (y+h)^2,           if By/A >= k.             (4)

Both pieces are strictly increasing with y>0 and agree at the transition.
For y0=3A/2, the inequality A>=4B gives By0/A<=k; its minimum value is
exactly 17/4. Therefore every feasible square has y<=3A/2. Consequently

    1+h-y-AB/2
      >= 1-A+B/2-AB/2
       = (1-A)(1+B/2)>0.

**Case A<=4B.** The top vertex height y+h is <=sqrt(17)/2. Put w=A+B.
The exact identity

    (A-4B)(4A-B)=4-17AB<=0

gives w^2=1+2AB>=25/17>36/25, hence w>6/5. Also w<=sqrt(2)<2. The function
5/4+w-w^2/4 is increasing on this interval, so

    1+w-AB/2 = 5/4+w-w^2/4
             > 209/100 > sqrt(17)/2.

(The last squared comparison is 43681>42500.) Thus
1+h-y-AB/2 >= 1+w-sqrt(17)/2-AB/2>0 again.
Equation (3) proves ell>1/2 in every nonexceptional orientation.

### 2.3 The right endpoint cannot lie at or left of -1/2

Suppose the right section endpoint is p=(x0,1) with x0<=-1/2. Because
this is an endpoint of an interior horizontal section, it lies on an
outward square side with unit normal n=(u,v), u>0. Put t=(-v,u).
For some 0<=lambda<=1, the four vertices are exactly

    p-lambda*t,  p+(1-lambda)*t,
    p-lambda*t-n, p+(1-lambda)*t-n.                         (5)

The argument includes an endpoint that happens to be a square vertex.
There is no generic-position assumption.

**Case v>=0.** The floor condition in y>=1/2 says
lambda*u+v<=1/2. Thus 0<=v<=1/2. The upper-left vertex in (5) has

    X=x0-u-(1-lambda)*v
      <= -[1/2+v+(1-v/2)/u],
    Y=1-v+(1-lambda)*u >= 1/2+u.

Since 1/u>=1, |X|>=3/2+v/2. Hence

    X^2+Y^2 >= (3/2+v/2)^2+(1/2+u)^2
             = 9/2+(u-1)+3v/2-3v^2/4
             >= 9/2+3v/2-7v^2/4 >= 9/2.

Here 1-u=v^2/(1+u)<=v^2, and v<=1/2. This exceeds 17/4.

**Case v=-w<0.** Now u^2+w^2=1 and the floor condition is lambda*u<=1/2.
The two vertices on the side opposite p have fixed n-coordinate

    n.p-1=u*x0-w-1 <= -(1+u/2+w)=:-K.

Their t-coordinates differ by one. Therefore at least one has squared norm
at least K^2+1/4.

If w>=3/5, then u/2+w>=1, so K>=2. For 3/5<w<1 this is strict, since
u^2-4(1-w)^2=(5w-3)(1-w)>0. At w=3/5, equality at squared radius 17/4
would require u=4/5, x0=-1/2 and the two t-coordinates to equal +/-1/2.
That forces lambda=t.p+1/2=1, contradicting lambda*u<=1/2.
Thus this whole range is impossible.

If 0<w<3/5, then u>4/5. The upper-left vertex has negative X and positive Y.
For fixed lambda its squared norm cannot decrease when x0 is moved to the
left of -1/2, so bound it at x0=-1/2. Its n-coordinate is -K and its
positive t-coordinate is at least

    V=1+u-w/2-1/(2u)>7/8.

The exact inequalities

    u >= 1-(5/9)w^2,
    1/u <= 1+(25/36)w^2

follow from u>4/5 and 1-u=w^2/(1+u). They give positive lower bounds

    K >= K0=3/2+w-(5/18)w^2,
    V >= V0=3/2-w/2-(65/72)w^2.

Their squared sum has the exact expansion

    K0^2+V0^2-9/2
      = (3/2)w-(55/24)w^2+(25/72)w^3+(4625/5184)w^4
      > w/8 > 0,                                       (6)

because w<3/5. Once again the vertex norm exceeds 17/4.

All right-side normal directions have been covered, so sup(I)>-1/2.
Horizontal reflection gives inf(I)<1/2. This completes Lemma S.1. QED.

## 3. Fill only holes that no additional unit square can occupy

Return to the six fixed squares of Section 1. In the left column, the
possible gap between the two inner squares is the vertical interval

    G_L=(a+1/2,b-1/2),

and in the right column it is G_R=(c+1/2,d-1/2). Empty intervals are ignored.
Both are contained strictly in (-1/2,1/2). Across x=0, any overlapping
parts of these intervals join; nonoverlapping parts are blocked by the
other column. The outside endpoints x=-1 and x=1 are blocked by the two
outer squares. The horizontal top/bottom boundaries are the fixed inner
squares. Thus every component of these gaps has boundary contained in
the closed fixed-square union and lies in a horizontal strip of height
STRICTLY less than one.

The open interior of another physical square is disjoint from the closed
fixed-square union: an interior ball centered at any point of a closed
fixed square would meet that fixed square's open interior. If the new
square interior entered one of the bounded gaps, connectedness would
confine its whole interior there. But every unit square has vertical
projection width at least one, whereas the gap's total height is <1.
This is impossible.

Therefore we may **fill these inaccessible gaps for a capacity argument**,
without moving any actual square and without excluding an admissible
additional square. The filled obstacle includes

    [-1,0] x [l_L,h_L],  [0,1] x [l_R,h_R],
    l_L=a-1/2, h_L=b+1/2,
    l_R=c-1/2, h_R=d+1/2.                                (7)

Each column has height h_i-l_i>=2, bottom l_i<-1/2 and top h_i>1/2.
Together with the two outer squares, it contains the solid band

    [-2,2] x [-1/2,1/2].                                 (8)

The outer-face screen for either fixed radial terminal says every point
of an additional square has -2<x<2; see RADIAL_SECTOR_POCKET_CAPACITY.md,
Lemma P1.1. Since its connected interior avoids (8), every additional
square lies wholly in y>=1/2 or wholly in y<=-1/2. This is derived from
physical obstacles, not assumed coordinate separability.

## 4. Count cap squares by the two column tests

Call an upper column slot *available* if h_i<1, and a lower slot available
if l_i>-1. Since h_i-l_i>=2, no one column has both slots available. Thus,
with a_U and a_D the numbers of available upper and lower slots,

    a_U+a_D <= 2.                                       (9)

First suppose no additional square is the exceptional north square N
from Lemma S.1 or its southern reflection S.

For every upper additional square, its **open** section at y=1 has
length >1/2 and meets (-1/2,1/2), by Lemma S.1. If a column has h_i>=1,
that column's closed interval at y=1 cannot meet this open section.
Consequently:

- If a_U=0, both columns block [-1,1] at y=1, so no upper square exists.
- If a_U=1, say only the left slot is available, every section must lie
  to the left of zero, yet end strictly to the right of -1/2. Its length
  >1/2 forces -1/2 to lie in its open interior. All such squares would
  contain the same point (-1/2,1) in their open interiors. At most one fits.
  The other side is symmetric.
- If a_U=2, at most two upper squares fit: three would contradict the
  unrestricted three-square cap theorem, since they lie in y>=1/2>7/16
  and q0<Q. This is UNRESTRICTED_THREE_SQUARE_CAP.md, not a common-frame
  or projection-separated theorem.

Thus the upper count is at most a_U. Reflection gives lower count at most
a_D. By (9) there are at most two additional squares.

## 5. Complete treatment of the exceptional north/south square

Suppose N=[-1/2,1/2]x[1,2] is present. A different upper square cannot be
N and therefore has an open y=1 section meeting (-1/2,1/2). That gives an
open-interior point on the closed bottom face of N, contradicting physical
nonoverlap. Thus N is the only upper square.

Physical avoidance of N also forces h_L,h_R<=1 in (7). Otherwise the
filled obstacle overlaps N above height one on the corresponding side of
x=0. Because each column's height is at least two, l_L,l_R<=-1. Both lower
slots are therefore blocked. The reflected section lemma excludes every
lower square except the unique possible exceptional southern S. Hence
at most two extras exist even in this boundary case.

The case where S is present first is its reflection. This handles all
exceptional line tangencies and completes Theorem TL.6. QED.

## 6. Gate impact: two of four two-loaded core topologies finished

For the selected strictly exposing point-contact certificate, the
universal two-loaded component reduction gives four graph types:

| Type | Component bodies | Full nine-square completion status |
|---|---:|---|
| P4 path | 4 | OPEN: existing P.ALL |
| C4 with one pendant bridge | 5 | OPEN: four unrestricted extra squares |
| Simple six-cycle | 6 | **CLOSED hand by TL.6** |
| Six-body seven-edge two-column graph | 6 | **CLOSED hand by TL.6** |

Every six-body type has two aligned bodies in each column with strict
heights in (-1,1), separation >=1, and the two outer radial terminals.
It therefore satisfies (1), and TL.6 includes all its unstressed-square
completions. The new conclusion is a whole-family physical capacity bound,
not a graph check on a representative core.

In particular, every remaining CYCLIC selected component with exactly two
loaded bodies must be the **five-body four-cycle-plus-bridge family** in
coarse cell C1.4.b1. Any other still-open cyclic cell needs at least THREE
loaded bodies to survive the present necessary conditions. Parent cells
with three-or-more-loaded configurations are not declared closed merely
because their two-loaded subfamilies are excluded.

## 7. Verification boundary and remaining proof

The new square-section estimates are symbolic over the complete angle
range. The short rational splits correspond to different support faces
and the exact circle bound, not an interval-cover computation. The hole
argument retains every unstressed square and explicitly treats inaccessible
bounded gaps; it is not a deformation that assumes collisions away.

The proof uses the previously written physical cap theorem for the two
available-slot case. Both that dependency and this manuscript require
independent review; no standard-kernel Lean proof or CI run is claimed.
A separate exact regression program checks the identities, boundary
controls and attainable eight-square examples, not the universal theorem.

P.ALL, Y.ALL, the five-body two-loaded completion, cyclic cores with three
or more loaded bodies, unrestricted equality, independent full audit and
Lean integration remain OPEN. This work is prepared as a local Git
continuation; no successful remote push is claimed.
