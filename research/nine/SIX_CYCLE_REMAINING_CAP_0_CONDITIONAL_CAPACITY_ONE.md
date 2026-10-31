# A coarse-coordinate capacity-one criterion for remaining exterior pocket 0

Date: October 26, 2026.

**Status: accepted complete conditional hand geometric lemma after
independent review in REVIEW_C6_CAP_0_CONDITIONAL_CAPACITY_ROOT_2026_10_26.md.
The radius hypothesis is now supplied by
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md; the other coordinate
hypotheses have not yet been proved for the full remaining C6 orbit.**
This conditional source itself retires no allocation or gate. It remains
a separate whole-pocket criterion with a fixed rational diameter reserve.
The actual C6 completion is now excluded by the independent same-nine-square
R>2/R<2 join in SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md, without
requiring the unproved extra coordinate hypotheses of this criterion.

All physical squares and their original orientations remain arbitrary
except for the two actual loaded squares appearing explicitly below.
No square is moved to a chosen pose, and no transmitter slider, shared
mean, boundary mask, or individual circle weight is changed.

## 1. Geometric statement and exact intended join

Let \(3/2\le a\), \(6/5\le b\), and
\[
                    a^2+b^2=R^2\le4.
\tag{1}
\]
Let \(H\ge1/2\), and take an actual unit direction
\[
 u=(X,Y),\qquad X^2+Y^2=1,\qquad
              3/4\le X\le4/5,\quad Y>0.
\tag{2}
\]
In the disk \(D_R\), retain the two actual unit squares
\[
 S_0=[-a,1-a]\times[-b,1-b],
\]
\[
 S_1=(2-a,-H)+[0,1](X,Y)+[0,1](Y,-X).
\tag{3}
\]
They are the exact loaded-square coordinates obtained from actual
channel 0 in
SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md.

**Conditional capacity theorem.** There cannot be two additional unit
squares, of arbitrary independent orientations, with pairwise disjoint
open interiors and interior-disjoint from both squares in (3), all
contained in
\[
                          D_R\cap\{y\le-H\}.
\tag{4}
\]
Thus any actual exterior pocket 0 satisfying (1)--(3) has capacity at
most one. No condition on the actual position of its transmitter is
needed for this conditional estimate.

The existing physical channel-cap theorem puts every pocket-0 extra
in (4). To apply the present theorem to the entire surviving orbit,
the accepted common-point theorem already gives \(R<2\). One still
has to derive \(a\ge3/2\), \(b\ge6/5\), \(H_0\ge1/2\),
and \(3/4\le X\le4/5\) from the exact original equations and
restrictions. This source makes no such remaining derivation.

## 2. Every possible center lies in one small rectangle

Let \(E\) be any additional square in (4), and let its center be
\(e=(x,y)\). Circle containment gives the standard center bound
\[
 |e|\le\sqrt{R^2-1/4}-1/2
       \le(\sqrt{15}-1)/2<23/16=:M.
\tag{5}
\]
For completeness, in its own frame the farthest corner has squared
radius \(|e|^2+|e_1|+|e_2|+1/2\), which is at least
\(|e|^2+|e|+1/2\). Solving the resulting quadratic gives (5).
The final strict comparison is \(\sqrt{15}<31/8\), whose positive
squared reserve is \(1/64\).

The half-width of every unit in any direction is at least \(1/2\),
so (4) gives
\[
                   -23/16<y\le-H-1/2\le-1.
\tag{6}
\]
The open radius-\(1/2\) disk about \(e\) lies in the open square
\(E\). Its disjointness from either loaded unit therefore requires
\[
                   \operatorname{dist}(e,S_i)\ge1/2
                   \qquad(i=0,1).
\tag{7}
\]
This is only a necessary disk condition; the proof does not replace
the actual extra by a disk.

### 2.1. The axis-aligned loaded square bounds the center from the left

Equations (1) give
\[
                   3/2\le a\le8/5,\qquad 6/5\le b<2.
\tag{8}
\]
Since \(x>-M>-a\) and \(y\le-1<1-b\), the only possible
vertical distance from \(e\) to \(S_0\) is
\[
 d_y=(-b-y)_+<M-b\ \text{ if positive},\qquad
                         0\le d_y<19/80.
\tag{9}
\]
If \(x\le1-a\), the horizontal distance would be zero, and
(9) would contradict (7). Thus \(x>1-a\), and (7) gives
\[
 (x-(1-a))^2+d_y^2\ge1/4.
\]
Consequently
\[
 x-(1-a)>\sqrt{\,1/4-(19/80)^2\,}
          =\frac{\sqrt{1239}}{80}>\frac7{16},
\]
\[
                          x>-3/5+7/16=-13/80.
\tag{10}
\]
The last radical comparison uses \(1239>35^2=1225\).

### 2.2. The other loaded square bounds the center from the right

Put \(d=2-a\). Equations (2),(8) imply
\[
 2/5\le d\le1/2,\qquad
 3/5\le Y<2/3,\qquad
                    0<Y/X<8/9.
\tag{11}
\]
The upper bound for \(Y\) follows from
\(Y^2\le7/16<4/9\). Define the actual own coordinates of \(e\)
relative to the base of \(S_1\):
\[
 \xi=X(x-d)+Y(y+H),\qquad
 \zeta=Y(x-d)-X(y+H).
\tag{12}
\]
The loaded square \(S_1\) is exactly \(0\le\xi,\zeta\le1\).

First,
\[
 \zeta=Yx-Xy-(Yd+XH)
       <M-(6/25+3/8)<1.
\tag{13}
\]
This uses Cauchy's inequality \(Yx-Xy\le|e|\), and preserves
the correct signs of the positive \(d,H,X,Y\).
In the other direction, (6),(10)--(11) give
\[
 \zeta>-\frac23\frac{53}{80}+\frac12\frac34
                              =-\frac1{15}.
\tag{14}
\]
Also
\[
 \xi\le X(x-d)-Y/2
       <\frac45(M-2/5)-\frac3{10}
       =\frac{53}{100}<1.
\tag{15}
\]
If \(x-d<0\), the first term is already negative and the displayed
upper bound still holds; otherwise \(X\le4/5\) proves it directly.

If \(0\le\xi<1\), then (13)--(14) would give
\(\operatorname{dist}(e,S_1)<1/15<1/2\), contradicting (7).
Thus \(\xi<0\). Since \(\zeta<1\), the same distance formula gives
\[
 \xi^2+(-\zeta)_+^2\ge1/4,\qquad
 -\xi>\sqrt{1/4-1/225}=\frac{\sqrt{221}}{30}
                                     >\frac{49}{100}.
\tag{16}
\]
The final positive squared reserve is \(491/90000\).
Solve (12),(16) for \(x\), using \(X>0\):
\[
 x<d-\frac{49}{100X}-\frac YX(y+H)
   <\frac12-\frac{49}{80}
                     +\frac89\left(\frac{23}{16}-\frac12\right)
   =\frac{173}{240}.
\tag{17}
\]
Every substitution in the last inequality has a known sign:
\(y+H\le-1/2\), \(M-H>0\) for any existing \(E\), and
\(-y-H<M-H\). If \(M-H\le0\), (6) already contradicts (5),
so no extra exists and the theorem is immediate.

Combining (6),(10),(17), every possible center lies in the single
rectangle
\[
             -13/80<x<173/240,\qquad -23/16<y\le-1.
\tag{18}
\]

## 3. Two arbitrary extra squares cannot occupy the cap

The rectangle (18) has horizontal width \(53/60\) and vertical
width \(7/16\). Its squared diameter is
\[
                  \left(\frac{53}{60}\right)^2+
                  \left(\frac7{16}\right)^2
                      =\frac{55969}{57600}<1,
\tag{19}
\]
with fixed reserve \(1631/57600>0\).

If two unit squares had disjoint open interiors, their open
inscribed disks of radius \(1/2\) would also be disjoint, so their
center distance would be at least one. Equation (19) contradicts
this. Their independent orientations, boundary contacts and any
zero circle weights play no role in the contradiction.

This completes the stated conditional whole-cap theorem. Its additional
coordinate hypotheses remain unproved on the whole original exact
system. The later independent source SIX_CYCLE_REMAINING_CAP_0_CAPACITY_ONE.md
now proves complete pocket-0 capacity at most one without them, using
the original channel height, closure and actual full-square arc routing.
That separate theorem removes three of the former seven allocations;
(central,cap0,cap2)=(0,0,3),(0,1,2),(1,0,2),(1,1,1) remain open.
No numerical root box, sample, Lean compilation or CI is a premise.
