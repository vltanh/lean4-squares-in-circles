# Opposite central-side neighbors have center rays more than 94 degrees apart

**Research continuation 2026-10-12. Status: complete all-frame
analytic hand theorem.** This is a geometric bridge from **two
actual contacts of the origin-containing central square** to a
strict outer-center angular obstruction. It substantially
strengthens the simple projected-distance-two observation.
It does not depend on a chosen seven-square contact
graph or on a numerical angle mesh.

## Theorem (uniform angular separation across an origin-containing unit square)

Let three genuine unit squares C, A and B of
**arbitrary independent orientations** have
pairwise disjoint open interiors in
\[
D_R,\qquad R^2\le q_+:=9789/2500.
\]
Assume zero lies in the **open interior of C**.
Suppose there is a unit vector n such that
A lies wholly beyond C's positive-n supporting line,
and B lies wholly beyond C's negative-n supporting line:
\[
\begin{aligned}
A&\subseteq\{x:n\cdot x\ge h_+\},\\
B&\subseteq\{x:n\cdot x\le-h_-\},
\end{aligned}
\quad
h_+,h_->0,
\]
where \(h_+\) and \(h_-\) are the **actual**
positive and negative signed support distances
of C from the disk origin. (In particular this
holds when C has two *opposite* contact
force normals n and -n toward A and B.)

Then the centers \(p_A,p_B\) obey the strong
**universal dot-product and angular bounds**
\[
\boxed{p_A\cdot p_B<-4/25,}                   \tag{1}
\]
\[
\boxed{\angle(p_A,p_B)>\pi/2+1/13.}           \tag{2}
\]

The conclusion is for **true square centers**
and **true whole-square cap membership**,
not just the sign of the centers' projections.
The frames need not be parallel to n or
to one another. This theorem is independent
of stress: a pair of true opposite central-owned
whole-side separators suffices.

## 1. Normalize the complementary cap offsets

Rotate coordinates so n is the positive horizontal
unit vector; reflect across the vertical diameter
and interchange A,B if needed. We may suppose
\[
h:=h_+\ge h_-=k>0.
\]
Since C is a **unit square containing zero**,
its projection width in the direction n is
\[
h+k=2h_C(n)=|n\cdot e_C|+|n\cdot f_C|
\ge1.                                            \tag{3}
\]
Thus
\[
\boxed{h\ge1/2,\qquad k\ge1-h.}              \tag{4}
\]
For the two actual neighbor centers write
\[
p_A=(x,y),\qquad p_B=(-u,v),\qquad x,u>0.
\]
The whole-square cap projections (half-width
at least 1/2 in every normal) imply
\[
\boxed{x\ge h+1/2,\qquad
       u\ge k+1/2\ge3/2-h.}                    \tag{5}
\]

Every genuine unit square center p in the
search disk has radial norm strictly below
\[
r_0:=283/200,\qquad r_0^2=80089/40000,
\]
by the exact farthest-vertex inequality
\[
R^2\ge|p|^2+|p|+1/2,
\]
whose left side at r_0 exceeds q_+
by \(65/40000>0\).
Thus \(h+1/2\le x<r_0<3/2\),
and in particular
\[
\boxed{1/2\le h<1.}                           \tag{6}
\]

The exact *one-square cap envelope* in
[HUMAN_ONE_SQUARE_CAP_ENVELOPE.md](HUMAN_ONE_SQUARE_CAP_ENVELOPE.md)
has already been hand-proved at the present
radius ceiling for **every frame** when the
whole cap offset is at least 2/5:
\[
|y_\perp|+1/2
\le\sqrt{q_+-(1+h_{\rm cap})^2}.             \tag{7}
\]
We will apply it to A, always because h>=1/2,
and to B only when k>=2/5.
Elsewhere for B we use merely
\[
|v|<\sqrt{r_0^2-u^2}.                         \tag{8}
\]
No unproved extension of the sharp one-square
cap envelope below 2/5 enters the proof.

## 2. Four rational intervals force a negative dot-product gap

From (5),
\[
p_A\cdot p_B=-xu+yv
\le -(h+1/2)(3/2-h)+|y||v|.
\]
The normal-projection product is exactly
\[
(h+1/2)(3/2-h)
=1-(h-1/2)^2.                                 \tag{9}
\]

We bound the transverse product |y v| in
**four complete rational ranges of h**:

| Larger opposite-cap offset h | Strict upper bound on |y| | Strict upper bound on |v| | Lower bound on xu | Resulting strict bound on p_A·p_B |
| --- | ---: | ---: | ---: | ---: |
| \(1/2\le h\le3/5\) | \(4/5\) | \(9/10\) | \(99/100\) | \(<-27/100\) |
| \(3/5\le h\le7/10\) | \(2/3\) | \(6/5\) | \(24/25\) | \(<-4/25\) |
| \(7/10\le h\le4/5\) | \(13/25\) | \(5/4\) | \(91/100\) | \(<-13/50\) |
| \(4/5\le h<1\) | \(1/3\) | \(283/200\) | \(3/4\) | \(<-167/600\) |

All bounds in the table follow from (7)
or (8) by **elementary rational squaring**:

* h>=1/2: (7) gives
  \(|y|<4/5\), because
  \((13/10)^2-[q_+-(3/2)^2]
  =61/2500>0\).
* If h<=3/5, then k>=2/5 and
  (7) for B gives \(|v|<9/10\):
  \((7/5)^2-[q_+-(7/5)^2]
  =11/2500>0\).
* h>=3/5: (7) gives
  \(|y|<2/3\), as
  \((7/6)^2-[q_+-(8/5)^2]
  =31/5625>0\).
* If h<=7/10, then k>=3/10, so
  \(u\ge4/5\). The universal
  radial bound (8) gives \(|v|<6/5\),
  since
  \((6/5)^2-[r_0^2-(4/5)^2]
  =3111/40000>0\).
* h>=7/10: (7) gives
  \(|y|<13/25\), as
  \((51/50)^2-[q_+-(17/10)^2]
  =37/2500>0\).
* If h<=4/5, then k>=1/5 and
  \(u\ge7/10\). Bound (8) gives
  \(|v|<5/4\), as
  \((5/4)^2-[r_0^2-(7/10)^2]
  =2011/40000>0\).
* h>=4/5: (7) gives
  \(|y|<1/3\), from
  \((5/6)^2-[q_+-(9/5)^2]
  =106/5625>0\).
  For B use just \(|v|<r_0\).

The normal product column uses (9),
whose minimum over each interval is
at its upper h endpoint because h>=1/2.
The last column then follows by subtracting
the stated maximum transverse products:
\(99/100-(4/5)(9/10)=27/100\),
\(24/25-(2/3)(6/5)=4/25\),
\(91/100-(13/25)(5/4)=13/50\),
and \(3/4-(1/3)(283/200)=167/600\).
All four are **at least 4/25**,
with strictness supplied by the displayed
transverse estimates.

Thus in every actual allowed h interval
we obtain
\[
\boxed{p_A\cdot p_B<-4/25},
\]
proving (1).

## 3. Convert the exact dot-product deficit to an angle

Let \(\Delta\in[0,\pi]\) be the smaller
polar angle between the two true center
rays. Because both center radii are below
r_0, and their dot product is *negative*,
\[
\cos\Delta=\frac{p_A\cdot p_B}
{|p_A||p_B|}
<-\frac{4/25}{r_0^2}
=-\frac{6400}{80089}.
\]
The last rational fraction is strictly
larger than 1/13 in absolute value:
\[
\frac{6400}{80089}-\frac1{13}
=\frac{3111}{1041157}>0.
\]
Since \(\sin(1/13)<1/13\),
we have
\[
\cos\Delta<-\sin(1/13)
=\cos(\pi/2+1/13).
\]
Cosine is strictly decreasing on [0,pi],
so
\[
\boxed{\Delta>\pi/2+1/13}.
\]
This completes the proof. QED.

## Exact implications for the global proof architecture

If C has exactly **two positive-stress
contact neighbors**, the central force
equilibrium forces their contact normals
to be **opposite**. The actual support
conditions therefore satisfy the hypotheses
above, and their center-ray angular gap
exceeds \(\pi/2+1/13\), *regardless* of
their actual outer or inner radial classes.

This strong angular separation is the
key to a **whole stressed-cycle-size
exclusion** in
[HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md](HUMAN_SEVEN_OUTER_PATH_M7_EXCLUDED.md).

The theorem applies to any other two
true squares beyond C's opposed
support lines, even when no stress
was chosen. It does not assign a whole
quadrant to a center from its sign,
force frame parallelism, or prove
the full global radius lower bound.

[verify_opposite_central_neighbor_angle.py](verify_opposite_central_neighbor_angle.py)
checks all seven rational margin identities,
the four interval deficit bounds and
the final cosine threshold exactly.
The computer was used to *discover*
this four-band comparison; its proof
above is a finite, human-verifiable
analytic inequality for the entire
center/frame continuum.
