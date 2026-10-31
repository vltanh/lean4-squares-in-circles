# No actual unit in a nine-square packing can have six boundary neighbors

Date: October 27, 2026.

**Status: complete proposed whole-range geometric theorem, pending full
root and separate independent review. Mathematical text is frozen.**
No original graph gate, shared ledger or existing source is changed.

## 1. Statement and the exact same-packing inputs

Keep nine actual unit squares with pairwise disjoint open interiors in
the same containing disk D_R, with

    79/40<=R<=sqrt(Q), Q=1105/256.

A physical boundary neighbor of a unit H means a different actual unit
that physically touches H and physically touches the containing circle.
No positive contact multiplier is required at either contact.

**Theorem.** Every actual unit H has at most five distinct physical
boundary neighbors.

The theorem has no positive-graph, force, root, origin-containment,
common-frame or contact-mean premise. It applies in particular to a
higher-degree root without changing a single original force. Its
nine-unit hypothesis is used in two already accepted geometric inputs:

* NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md gives R>2 for these same
  nine physical units. Its inherited measure certificate is retained.
* CHORDED_HEXAGON_QUARTER_DISK_COMPLETION_OBSTRUCTION.md proves that
  no one of the nine units contains the closed disk D_(1/4).

The second theorem is equivalent, in the actual own frame of H, to

    max(|(c_H)_1|,|(c_H)_2|)>1/4.                     (1)

We also use the accepted force-free CENTERED_INNER_ARC.md. It proves
that any two physical boundary units in the stated radius window have
minor center-angle separation strictly greater than

    2pi/9 = 40 degrees.                              (2)

It therefore suffices to put every boundary-neighbor center direction
in one open angular interval of width at most 10pi/9, or 200 degrees.
Indeed six ordered lifts in such an interval have five consecutive
positive gaps, each greater than 2pi/9 by (2), so their total span
would exceed 10pi/9. A consecutive lift gap greater than pi also
exceeds 2pi/9; no minor/major ambiguity changes this conclusion.

Everything below is a direct whole-range geometric estimate proving
that interval bound. Numerical angular samples are not used.

## 2. Universal center and actual-contact bounds

Put

    s=1/sqrt(2), D=181/140, M=91/60.

The elementary strict comparisons

    s<99/140, 2-s>D                                  (3)

follow from (99/70)^2-2=1/4900>0.

Every contained unit center c has |c|<M. In fact its farthest corner
has squared norm at least |c|^2+|c|+1/2, and

    M^2+M+1/2-Q=31/57600>0.                          (4)

For every physical boundary unit B, its actual circle corner and unit
circumradius give

    r_B:=|c_B|>=R-s>2-s>D.                           (5)

If B touches H at an actual point p, both center-to-point distances
are at most s. Consequently

    |c_B-c_H|<=2s=sqrt(2),
    dist(c_B,H)<=s.                                 (6)

The second bound retains the actual shape and frame of H. In its
own frame it says c_B lies in the Euclidean s-neighborhood of the
actual unit square. The two estimates in (6) will be used separately.
No contact point is replaced by a center or an artificial application.

## 3. A center displacement of at least 2/5 already suffices

Suppose h:=|c_H|>=2/5. Let theta be the minor angle between c_H,c_B.
The first inequality in (6) yields

    cos(theta)>=(h^2+r_B^2-2)/(2h r_B)=:f(h,r_B).      (7)

For 2/5<=h<M and D<=r_B<M, f is strictly increasing in its second
variable: the numerator of that derivative is
r_B^2-h^2+2, which is at least D^2-M^2+2>0. After reducing to r_B=D,
it is strictly increasing in h, since h^2-D^2+2>0 and D^2<2.
Thus

    f(h,r_B)>=f(2/5,D)>-1/6,
    f(2/5,D)+1/6=227/60816>0.                        (8)

Here the first derivative reserve can be read exactly as

    D^2+2-M^2=6047/4410>0.

The elementary inequality sin(pi/18)>1/6 follows from

    3(1/6)-4(1/6)^3=13/27<1/2=sin(pi/6),

because 3x-4x^3 is strictly increasing for 0<=x<=1/2.
Hence -1/6>cos(5pi/9). Equations (7)--(8) put all neighbor directions
strictly within 5pi/9 of the direction of c_H. This is an open
interval of width 10pi/9, as required.

## 4. A smaller center retains a useful own-frame corner restriction

It remains to suppose

    |c_H|<2/5.

Reflect and exchange H's actual own axes, using (1), so that

    c_H=(x,y), 1/4<x<2/5, 0<=y<=x<2/5,
    H=[x-1/2,x+1/2] times [y-1/2,y+1/2].              (9)

These are merely coordinates in H's unchanged physical frame. In
particular O is inside H in this branch; this is a consequence of
the small center, not an additional premise.

No neighbor center belongs to the closed southwest quadrant

    { (X,Y): X<=0, Y<=0 }.                            (10)

To prove this, the nearest point in H to such a center has both
coordinates nonpositive, with absolute values at most 1/4 and 1/2
respectively. Its norm is therefore less than or equal to sqrt(5)/4.
The second inequality in (6) would imply

    |c_B|<=s+sqrt(5)/4<99/140+9/16<D,

contradicting (5). The exact final reserve is

    D-99/140-9/16=13/560>0,

and sqrt(5)/4<9/16 follows from 5<(9/4)^2.

All remaining neighbor directions consequently have consistent lifts
in (-pi/2,pi). We control the northwest and southeast portions of
that interval using the actual square neighborhood in (6).

## 5. The full branch y>=2/25

Assume first that y>=2/25. Write c_B=(X,Y). Coordinate projection of
the second bound in (6), together with (3),(9), gives

    X>x-1/2-99/140>-1/4-99/140=-67/70,
    Y>2/25-1/2-99/140=-789/700.                       (11)

For a northwest center, divide its negative X coordinate by r_B>D
to obtain

    arg(c_B)<pi/2+asin(a), a=134/181.

For a southeast center, the corresponding Y bound gives

    arg(c_B)>-asin(b), b=789/905.

Northeast centers already lie between these bounds, and (10) excluded
the other quadrant. Thus all directions lie in an open interval of
width

    pi/2+asin(a)+asin(b).                             (12)

Here is an exact whole-interval comparison of this width with 10pi/9.
The positive square-root factors satisfy

    sqrt(1-a^2)>2/3,
    sqrt(1-b^2)>12/25,
    ab<49/75.                                       (13)

Their exact squared/product reserves are respectively

    1-a^2-4/9=2201/294849>0,
    1-b^2-144/625=195016/20475625>0,
    49/75-ab=19399/2457075>0.

Consequently

    cos(asin(a)+asin(b))
       =sqrt(1-a^2)sqrt(1-b^2)-ab
       >8/25-49/75=-1/3.                            (14)

Also sin(pi/9)>1/3. Indeed 3x-4x^3 is increasing on [0,1/2],
and at x=1/3 it has value 23/27<sqrt(3)/2=sin(pi/3), with

    3/4-(23/27)^2=71/2916>0.

Thus -1/3>-sin(pi/9)=cos(11pi/18). The sum of the two inverse
sines in (14) lies in (0,pi), where cosine is decreasing, so

    asin(a)+asin(b)<11pi/18.

Equation (12) is strictly less than pi/2+11pi/18=10pi/9.
This finishes the full branch, with equality y=2/25 retained.

## 6. The full branch 0<=y<=2/25

Now assume 0<=y<=2/25. The second bound in (6) gives

    X>-67/70,
    Y>-1/2-99/140=-169/140.                           (15)

For a southeast center, (5),(15) yield Y/r_B>-169/181. The exact
centered-arc trigonometric estimate cos(pi/9)>15/16 and

    15/16-169/181=11/2896>0

therefore imply

    arg(c_B)>-7pi/18,                                (16)

or strictly greater than -70 degrees. For completeness the cited
cosine estimate follows because 4x^3-3x is increasing for x>1/2,
and its value at 15/16 is 495/1024<1/2=cos(pi/3).

We prove that every northwest neighbor has

    arg(c_B)<13pi/18,                                (17)

or strictly less than 130 degrees. Suppose instead theta=arg(c_B)
lies in [13pi/18,pi). Then

    X=r_B cos(theta)<-D/2<-1/4,

because sin(2pi/9)>1/2 and cos(13pi/18)=-sin(2pi/9).
The necessary contact bound X>-67/70 from (15), with r_B>D, also
gives

    Y>sqrt(D^2-(67/70)^2)>29/50.                      (18)

The last exact squared reserve is

    D^2-(67/70)^2-(29/50)^2=29327/70000>0.

Every point of the actual H has first coordinate greater than -1/4
and second coordinate at most 1/2+2/25=29/50. Hence its distance
from this putative c_B is at least the distance to the fixed corner

    P=(-1/4,29/50).

Write r=r_B and define

    F(r,theta)=|r(cos(theta),sin(theta))-P|^2
      =r^2+1/16+(29/50)^2
              +(r/2)cos(theta)-(29r/25)sin(theta).

On r>=D, 13pi/18<=theta<=pi, this function is increasing in both
variables. For its radial derivative,

    partial_r F>=2D-1/2-29/25=162/175>0.

For the angular derivative, sin(theta)<=1 and
-cos(theta)>=sin(2pi/9)>1/2 give

    partial_theta F
       =r[-sin(theta)/2-(29/25)cos(theta)]
       >r[29/50-1/2]=(2/25)r>0.                     (19)

Thus it suffices to evaluate F(D,13pi/18). The elementary strict
bounds needed for that value are

    sin(2pi/9)<9/14, cos(2pi/9)<23/30.                (20)

For the cosine bound, 4x^3-3x is increasing above 1/2 and

    4(23/30)^3-3(23/30)+1/2=17/6750>0,

whereas cos(2pi/3)=-1/2. For the sine bound,
sin(2pi/9)>1/2 and 3x-4x^3 is decreasing for x>1/2. At 9/14
it equals 297/343<sqrt(3)/2=sin(2pi/3), since

    3/4-(297/343)^2=111/470596>0.

This proves both comparisons in (20) without a decimal angle bound.
Consequently

    (1/2)sin(2pi/9)+(29/25)cos(2pi/9)
       <9/28+(29/25)(23/30)=12713/10500,

    F(D,13pi/18)-1/2
       >D^2+1/16+(29/50)^2-D(12713/10500)-1/2
        =1481/294000>0.                              (21)

Equations (18)--(21) force dist(c_B,H)>sqrt(1/2)=s, contradicting
the actual contact bound (6). This proves (17).

Together with (10),(16), all neighbor directions lie in the single
open interval

    (-7pi/18,13pi/18),

whose width is exactly 10pi/9. Every endpoint exclusion is strict.
This completes the full small-center branch.

## 7. Whole conclusion and graph-caller scope

Sections 3, 5 and 6 exhaust every possible actual center and frame of
H satisfying the same-nine obstruction (1). Every physical boundary
neighbor therefore lies in an open angular interval of width at most
10pi/9. Six such neighbor centers would have total ordered span
strictly greater than 5(2pi/9)=10pi/9 by (2), a contradiction.
The stated at-most-five-neighbor theorem follows.

All circle-contact masks, any zero individual or total circle weights,
all physical contact features and actual H orientations are included.
The conclusion applies equally to positive graph neighbors and to
unstressed physical neighbors. It does not use the complete physical
contact graph as a plane graph or alter a selected physical stress.

In a proposed original graph caller it is enough to exhibit six
distinct actual circle-touching neighbors of one unit in the same
nine-packing. The caller must establish their physical boundary
status and distinctness from its own full load/graph cover. This
source does not infer those labels for every six-body graph or
declare any original graph family closed by naming it.

The only inherited numerical certificate is that already present in
the same-nine radius-two lower-bound theorem. All new comparisons
here are explicit rational inequalities and elementary trigonometric
monotonicity on complete intervals. No sampled pose, new force
selection, Lean compilation, CI, remote action, shared-ledger edit or
deletion of historical certificates is used.
