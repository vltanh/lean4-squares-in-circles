# Perpendicular triple caps require a shared double-side square at offset 7/50

## Main theorem (all frames, no contact assumptions)

Let eight pairwise interior-disjoint unit squares fit in a
disk D_R centered at zero, with

    R^2<=9789/2500,      R<99/50.

Let C be its unique origin-containing unit square,
with own horizontal/vertical side frame. Suppose
three exterior squares lie **wholly** beyond its
right side at signed positive offset h_R and
three lie wholly beyond its upper side at offset h_U,
where

    h_R>=7/50,      h_U>=7/50.                      (1)

Then at least one of the seven exterior squares
belongs to **both** of those central-owned
whole-square cap populations. In other words:

    triple R + triple U + (1)
       => an actual RU double-side separator status. (2)

Every orientation is permitted. The squares need
not touch C or one another. The assertion concerns
actual *entire-square* cap membership, not center
signs, an arbitrary choice of SAT separator, or
a physical stress.

By reflection and quarter turns, the same implication
holds for every pair of perpendicular central sides.

**Sharp n=8 branch consequence.** The all-seven-single-side
status type S1=(3+0,3+1), with two perpendicular triples,
has **no** double-side square. Therefore

    S1 => min(h_triple,1,h_triple,2)<7/50.        (3)

This improves the earlier 13/60 and 11/50
thresholds, and it holds **for every k**, the number
of outer-center squares, not just for k=3 or 4.
With p_C=(a,b) and its triple sides normalized
to R and U, it reads

    S1 => min(a,b)<-9/25,                          (4)

since h_R=1/2+a, h_U=1/2+b and
7/50-1/2=-9/25.

It does not exclude the entire S1 branch.
The surviving small-offset side has
0<h<7/50 and must be treated by a
different sharp geometry argument.

## 1. A narrower angular lane for the extreme center of a triple cap

We first prove an exact consequence of
HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md.

Take any three disjoint whole unit squares
in D_R intersect {x>=h} with
R<=99/50, h>=7/50.
Put L=c+s in [1,sqrt(2)] for the
actual frame of the **topmost** square
on the midpoint slice x=(R+h)/2.

The hand proof in that note establishes

    p_top.y>1281/1000-L/2,
    p_top.x>=h+L/2>=7/50+L/2.                  (5)

Disk containment also gives the independent
upper bound

    p_top.x<=R-L/2<=99/50-L/2,                  (6)

because the square's rightmost x point
is p_top.x+L/2<=R.

Subtract 9/20 times (6) from (5):

    p_top.y-(9/20)*p_top.x
      >1281/1000-L/2
         -(9/20)*(99/50-L/2)
      =39/100-(11/40)*L
      >=39/100-(11/40)*sqrt(2)>0.               (7)

For the final strict comparison,
sqrt(2)<78/55, because
2*55^2=6050<78^2=6084, and
(11/40)*(78/55)=39/100.

The same note proves |p_top|>1. Hence
the topmost square has an **outer**
center lying in the open northeast angular
lane

    p_top.x>0, p_top.y>0,
    angle(p_top) >alpha:=atan(9/20).              (8)

The square with the **lowest** chord is
analogously outer and has
p_bottom.y<-(9/20)*p_bottom.x.
These facts use only actual positions
and chord lengths, not assumed frame
alignments or center polar data.

After swapping coordinates, a triple cap
in {y>=h} produces a **rightmost** extremal
square whose center is outer and satisfies

    p_right.x>(9/20)*p_right.y>0,

so

    angle(p_right)<pi/2-alpha.                   (9)

## 2. The northeast angular lane is narrower than the outer-center exclusion gap

The pairwise outer-center theorem
HUMAN_STABLE_OUTER_ANGLE.md proves that,
throughout q<=9789/2500, **two distinct
disjoint unit squares whose centers have
norm at least one must have angular
center-ray separation strictly greater
than pi/4-1/500.**

We now show by hand that the lane
between (8) and (9) is **strictly
narrower**. Its width is

    beta=pi/2-2*atan(9/20).

We prove

    beta<pi/4-1/100<pi/4-1/500.                (10)

It suffices to show

    atan(9/20)>pi/8+1/200.                       (11)

The exact identity tan(pi/8)=sqrt(2)-1
and the rational square inequality
sqrt(2)<17/12 give

    tan(pi/8)<5/12.

Also tan(x)<2x for 0<x<=1/200,
because tan'(x)=sec^2(x)<2
on that interval. Hence

    tan(1/200)<1/100.

The positive-angle addition identity yields

    tan(pi/8+1/200)
       < [(5/12)+(1/100)]/
         [1-(5/12)*(1/100)]
       =512/1195<9/20,                            (12)

where 512*20=10240<10755=1195*9.
Both angles are in (0,pi/2), where
tangent increases, proving (11).
Subtract twice from pi/2 to obtain (10).

Consequently two **distinct outer centers**
cannot both lie between angular directions
alpha and pi/2-alpha: their ray gap would be
at most beta, violating the established
strict pairwise outer-center theorem.

## 3. Apply the angular lane to perpendicular triples

Apply section 1 to the three right-cap squares.
Their highest-slice square S_R has
|p_SR|>1 and its ray angle >alpha.

Apply section 1, with x,y interchanged, to
the three upper-cap squares. Their
rightmost-slice square S_U has
|p_SU|>1 and its ray angle <pi/2-alpha.

Both center directions have positive x,y
coordinates. Thus their ray angles lie in
the **same** interval (alpha,pi/2-alpha).

By (10) and the established outer-center
separation theorem, S_R and S_U cannot be
different packed squares. Hence

    S_R=S_U

as an actual square label. That square lies
wholly beyond both the right and upper
supporting sides of C, because it was selected
from each *whole-square cap population*.
Thus it has precisely the RU double-side
separator status. This proves (2).

If every exterior square has exactly one
central-owned separator status, as in S1,
there is no RU member. Therefore the
simultaneous assumptions (1) are impossible
and (3)--(4) follow. QED.

## 4. Consequences for the surviving central-side patterns

1. **S1 is now restricted for every outer count k.**
   With both perpendicular triples, some actual
   triple side lies within 7/50 of the
   disk center. No all-single-side S1 packing
   survives in the complementary closed
   rectangle h_R,h_U>=7/50.

2. **For Type A with a genuine RU double,**
   the same proof identifies RU uniquely as
   both the highest R-cap and rightmost U-cap
   extreme whenever the two triple offsets
   satisfy (1), since each double-side
   status has multiplicity at most one.
   This is a forced angular routing and
   slice-order fact, not an exclusion of
   the sharp equality candidate.

3. If S1's small-offset triple is on the
   3+1 axis, its opposite singleton
   has transverse center coordinate |z|<9/50
   by section 5 of
   HUMAN_TRIPLE_CAP_TWO_OUTER_CENTERS.md.
   If the small-offset triple is instead
   on the 3+0 axis, no opposite-singleton
   lane is asserted.

The theorem does **not** force a five-corner
chain or handle the remaining 0<h<7/50
triple offsets. It also does not treat
a center sign as equivalent to a
whole-square separator. The unrestricted
inequality R8>=Rhat remains OPEN.
