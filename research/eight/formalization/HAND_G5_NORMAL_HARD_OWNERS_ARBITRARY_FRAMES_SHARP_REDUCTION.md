# The normal hard-owner class is sharp without any original frame order

## 1. Original-candidate theorem and remaining entry hypotheses

Put
\[
 Q=\frac{9789}{2500},\qquad q_L=\frac{19577}{5000},\qquad
 Q_1=\frac{1957767069}{500000000}.
\tag{1}
\]
Retain the original normal signed tangents
\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
       =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),
       \qquad b_i\ge0,
\tag{2}
\]
the original sorted own-frame magnitudes and corner bounds
\[
 a_i\ge b_i,\qquad
                (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q,
\tag{3}
\]
and the true central exclusion. Assume only that the real
frames belong to one interval of length at most \(7/10\).
There is no original order condition among any of the frames.
The retained original witnesses are
\[
\begin{array}{c|rrrrrrr}
 \text{edge}&HG&GA&AB&BT&TD&DE&EH\\ \hline
 \text{axis}&0\text{ or }2&0&0\text{ or }2&2&
                         0\text{ or }2&2\text{ or }3&0\text{ or }1.
\end{array}
\tag{4}
\]
For E, retain the radial alternative
\[
                 a_E\le7/12
          \quad\hbox{or}\quad
                 a_E\ge\max\{b_H,b_D\}.
\tag{5}
\]
In particular (5) holds if the original E is a true core
boundary representative or a sorted point on the original
common containing circle. It remains valid when a working
ceiling is enlarged or middle/intermediate points change,
provided H,D,E remain fixed.

**Sharp original-class theorem.** Every system (2)--(5)
has \(q\ge q_*\). At equality its three original zero
differences vanish:
\[
 \theta_G=\theta_H,\qquad \theta_A=\theta_B,\qquad
 \theta_T=\theta_D.
\tag{6}
\]
Its original E frame equals D's frame, and its original
five anchors H,A,B,D,E are the unique stationary anchors
with the canonical hard split. For an original packing,
the unchanged remaining constraints then give the weak
five-parameter equality family and its converse, exactly
as in the aligned hard-class theorem.

This removes the original frame-order and all three
zero-error restrictions from the stated normal hard class.
The normal signs, hard GA0/BT2 owners, original mixed-owner
sets, and E radial alternative (5) remain explicit entry
hypotheses. No unrestricted capture into those hypotheses
is asserted here.

The stationary enclosure is \(q_L<q_*<Q_1<Q\).
If \(q>Q_1\), the strict conclusion is immediate. Otherwise
enlarge a ceiling below \(q_L\) to \(q_L\) without moving
the original centers. It suffices to work at
\[
                              q_L\le q\le Q_1.
\tag{7}
\]
All actual circle constructions below use this q. At
equality there is no enlargement.

## 2. Align AB between the actual intermediate frames

Apply
[global intermediate order with all mixed owners](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md).
Its hypotheses are exactly the normal signs, true core,
circles, frame spread and retained witness sets above;
it does not require (5). It gives
\[
                              \theta_G>\theta_T.
\tag{8}
\]
Now use
[direct AB alignment between those frames](HAND_G5_AB_ALIGNMENT_BETWEEN_ORDERED_INTERMEDIATE_FRAMES.md).
It supplies
\[
                 \theta_A=\theta_B=\rho\in[\theta_T,\theta_G],
                 \qquad b_A+b_B=1.
\tag{9}
\]
The actual G,T,H,D,E coordinates and frames stay fixed.
Any original nonzero AB difference creates a strict A/B
circle loss. An originally common frame outside the G/T
interval creates strict losses in both. Normalizing a
transverse sum strictly above one also strictly decreases
one middle corner. Earlier separate A and B losses are
retained by that theorem.

Every subsequent construction will keep H,D,E and all
their coordinates and frames fixed. Thus their mixed
witnesses and (5) remain available.

The later uses of (8) are legitimate on the constructed
necessary cycles. Its proof uses precisely their retained
neighboring inequalities, sorted circles, true core, and
frame interval. It does not require an omitted nonneighbor
constraint or a physical-gap claim about a replacement
intermediate.

## 3. Local processing when the outer frame is on the correct side

Consider the H side when \(\theta_H\ge\rho\), with
\(\theta_G\ge\rho\). The reflected statements below apply
to the D side when \(\theta_D\le\rho\) and
\(\theta_T\le\rho\).

### A side with middle tangent at least one half

If \(b_A\ge1/2\), the following local alternatives are
available without using E's frame or mixed-owner choice.

* An aligned HG edge already gives its aligned composite.
* A negative canceling HG2 error aligns by Section 3 of
  [the signed canceling transport](HAND_G4_SIGNED_THREE_ZERO_REDUCTION_FOR_CANCELING_OUTER_OWNERS.md).
  It keeps H,A fixed and gives composite slack greater
  than \(3|\theta_G-\theta_H|/20\).
* A positive canceling HG2 error aligns by Section 6 of
  the same note. Its threshold \(b_A\ge1/5\) is satisfied,
  and the unchanged H,A composite has slack greater than
  \((\theta_G-\theta_H)/20\).
* A positive noncanceling HG0 error aligns by Section 5
  of
  [the positive same-circle boundary theorem](HAND_G5_POSITIVE_HG_ZERO_OWNER_BOUNDARY_REDUCTION.md).
  Its primary lift and strict-loss restoration are part
  of that theorem. The aligned pair has strict slack for
  every positive error.
* A negative noncanceling HG0 error is retained as its
  true-core composite when \(b_A>1/2\). At \(b_A=1/2\),
  the small-transverse negative transport may align it.

The cited local proofs use only the stated outer/middle
order and their three actual points. Their older whole-chain
theorem statements need not be invoked with an E-order
hypothesis.

In every outcome the middle primary satisfies
\[
                             a_A>11/10.
\tag{10}
\]
For an aligned composite this follows from
\(b_H+a_A\ge2\) and \(b_H<.9\). For a retained negative
HG0 error, put \(e=\theta_H-\theta_G>0\) and
\(t=\theta_G-\rho\ge0\). Its exact-core cap is
\[
 V_A(t)\ge D(e),\qquad
 V_A(t)=(a_A-\tfrac12)\cos t-(b_A+\tfrac12)\sin t,
\]
\[
                 D(e)=1+(\tfrac12-b_H)\sec e+\frac{13}{12}\tan e
                              >\frac35.
\tag{11}
\]
Hence \(a_A\ge1/2+D(e)>1.1\).
Its circle and (9) consequently give
\[
                         b_A<.665,\qquad b_B>.335.
\tag{12}
\]
The tangent values and common frame have not changed in
this local processing.

### Concrete comparison intermediates

An aligned composite can be realized by
\[
        \theta_G'=\theta_H,\qquad a_G'=\frac7{12},
                              \qquad b_G'=1-b_H.
\tag{13}
\]
It has \( .1<b_G'<.415\): the lower bound follows from
\(b_H<.9\), while the aligned composite and
\(a_A<283/200\) give \(b_H>.585\).
Thus it is sorted, on the true flat core, and its corner
is strictly below \(q_L\), since
\[
             (13/12)^2+(.915)^2=\frac{723901}{360000}<q_L.
\tag{14}
\]
Both original zero owners are feasible at alignment,
and GA0 is precisely the retained aligned composite.

For a retained negative HG0 error, keep its frame and
choose
\[
                       a_G'=\frac7{12},\qquad b_G'=D(e)-\frac12.
\tag{15}
\]
Equations (11) and the actual hard cap give the same
strict tangent range \(.1<b_G'<.415\). HG0 is active,
GA0 is feasible, and (14) applies again.
This supplies an actual necessary cycle for any later
use of the global order barrier (8). In both cases
\[
                         \rho\le\theta_G'\le\theta_H.
\tag{16}
\]
The reflected construction puts T between D and the
common frame.

### A side with tangent between .335 and one half

Suppose instead \(.335<b_A\le1/2\).
The same canceling transports still apply. A negative
noncanceling error aligns by
[small-transverse core transport](HAND_G4_NEGATIVE_NONCANCELING_ZERO_CORE_TRANSPORT.md),
with unchanged H,A and slack greater than \(e/150\).

A positive noncanceling error first uses the positive
same-circle boundary theorem. Its only alternatives are
alignment or a transverse-zero G endpoint.
[The all-mixed small-tangent G-zero exclusion](HAND_G5_SMALL_TANGENT_G_ZERO_WITH_ALL_MIXED_OWNERS.md)
excludes the latter. Its hypotheses are exactly (9),
\(\theta_T\le\rho\le\theta_H\), the small tangent interval,
and the unchanged endpoint/TD inequalities. It permits
either E sign, every retained mixed owner, and any
opposite outer-error sign.

Thus every nonzero positive small-side error aligns with
strict pair slack. The boundary theorem recreates any
earlier strict A loss after its temporary primary lift.
Its auxiliary G-zero angle may extend the old G frame;
the endpoint exclusion uses only the unchanged H,D,E,T
frame intervals, so no new total-span assumption is made.
The selected aligned frame (13) lies in the original
interval.

Every small-side outcome is aligned and has the concrete
realization (13). H,D,E and the opposite intermediate stay
unchanged. Pair slacks become strict middle-circle losses
by a sufficiently small primary decrease, once needed.

## 4. Local processing of a crossed outer frame

Suppose \(\theta_H<\rho\), still with
\(\theta_G\ge\rho\ge\theta_T\).
The original HG error is then positive.

For \(b_A\ge1/2\), use the appropriate one of

* [large crossed HG0 alignment](HAND_G5_CROSSED_NONCANCELING_LARGE_TANGENT_GA_ALIGNMENT.md);
* [large crossed HG2-to-HG0 reduction](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md).

For \(.335<b_A\le1/2\), use the corresponding

* [small crossed HG0 alignment](HAND_G5_CROSSED_SMALL_TANGENT_NONCANCELING_GA_ALIGNMENT.md);
* [small crossed HG2-to-HG0 reduction](HAND_G5_CROSSED_SMALL_TANGENT_CANCELING_TO_NONCANCELING.md).

In every case the resulting actual HG0/GA0 system has
\[
 \theta_G'=\rho,\qquad 0<\rho-\theta_H<.04,\qquad b_H>.75.
\tag{17}
\]
H,B,T,D,E and their data are unchanged. The HG0 versions
retain a separate strict A loss through their primary
lift; the HG2 versions initially change only G.
All four statements permit either E sign.

Now apply
[the crossed common-frame clamp](HAND_G5_CROSSED_COMMON_FRAME_CLAMP.md).
It gives
\[
                   \theta_G''=\theta_A''=\theta_B''=\theta_H
                                         >\theta_T,
                  \qquad b_A''+b_B''=1.
\tag{18}
\]
H,T,D,E remain fixed, all required actual witnesses and
the frame interval are retained, and both A/B corners
are strictly below q. In particular the crossing itself
is incompatible with equality after a sharp terminal.

At the new aligned H side, \(a_A''>1.1\), so
\[
                         b_A''<.665,\qquad b_B''>.335.
\tag{19}
\]
It may be useful to replace G by (13) afterward; this
does not change any middle or endpoint data.

Every reflected use has the analogous conclusion with
T,D,B,A in place of G,H,A,B. Its E sign is allowed to
change in the algebraic reflection. Undo the labels after
the local comparison: the actual original E coordinates
and its original sign never change.

## 5. A finite procedure puts the common frame between H and D

Choose a side whose current middle tangent is at least
one half; such a side exists by (9). Describe the
procedure with that side named H--G--A. A reflected
description treats the other choice.

### 5.1 The chosen large side is not crossed

Suppose \(\theta_H\ge\rho\). Apply the large-side
processing of Section 3. It aligns that side or leaves
one negative noncanceling composite, with an actual
comparison G satisfying (16). Equation (12) gives
\(.335<b_B\le.5\).

If \(\theta_D\le\rho\), the opposite side is not crossed.
Its small-side processing in Section 3 aligns it. The
common frame is already between D and H; the resulting
system has two aligned composites or only the large
H-side negative composite.

If \(\theta_D>\rho\), use the reflected small crossed
reduction and clamp from Section 4. That clamp keeps the
processed G fixed and moves the common A/B/T frame up
to D. Its strict intermediate-order conclusion is
\[
                            \theta_D<\theta_G\le\theta_H.
\tag{20}
\]
Thus it finishes inside the outer interval. The new common
frame is D, the D side is aligned, and the unchanged
H-side G still lies between that new common frame and H.
Its hard inequality is retained by the clamp and its HG
contact stays fixed. Those two inequalities therefore
supply the same aligned or negative-core composite form
with the new A coordinates. Both middle circles now have
strict loss.
There is no need to preserve which current tangent is
larger: the terminal permits arbitrary tangents in its
negative composites.

### 5.2 The chosen large side is crossed

Suppose \(\theta_H<\rho\). Apply the large crossed
reduction and clamp first. The new common frame is H
and \(G=H>T\), while (19) gives \(b_B>.335\).

The opposite endpoint cannot lie above this new common
frame. If \(\theta_D>\theta_H\), its reflected crossed
reduction applies: use the large branch when \(b_B\ge.5\)
and the small branch when \(b_B<.5\).
The subsequent reflected clamp would keep the already
aligned G fixed and require
\[
                              \theta_D<\theta_G=\theta_H,
\]
a contradiction. This uses the strict G/T barrier built
into the clamp, not an assumed outer-frame order.

Therefore \(\theta_D\le\theta_H\). Process the opposite
noncrossed side by Section 3, using its actual current
tangent. A small tangent aligns; a large tangent aligns
or retains a negative noncanceling composite. The H
side remains aligned throughout.

These two cases finish after at most two crossed-side
comparisons. They produce
\[
                   \theta_D\le\rho\le\theta_H,\qquad
                              b_A+b_B=1,
\tag{21}
\]
with each outer path aligned or represented by a
negative noncanceling core composite. H,D,E and both
mixed constraints were fixed throughout.

## 6. Invoke the all-mixed arbitrary-E negative-composite terminal

In the original labels set
\[
 t=\theta_G-\rho,\quad e_H=\theta_H-\theta_G,\qquad
 u=\rho-\theta_T,\quad e_D=\theta_T-\theta_D.
\]
The preceding procedure makes these four quantities
nonnegative, with zero e on every aligned side. They
sum to the unchanged H/D span, at most \(7/10\).
The two exact necessary composites are
\[
\begin{aligned}
 b_H&\ge\frac12+C_A\cos e_H+\frac{13}{12}\sin e_H,\\
 C_A&=1-(a_A-\tfrac12)\cos t+(b_A+\tfrac12)\sin t,\\
 b_D&\ge\frac12+C_B\cos e_D+\frac{13}{12}\sin e_D,\\
 C_B&=1-(a_B-\tfrac12)\cos u+(b_B+\tfrac12)\sin u.
\end{aligned}
\tag{22}
\]
All actual five-anchor circles, normal signs, the AB sum,
the original mixed witnesses and the E radial alternative
(5) remain valid.

These are precisely the hypotheses of
[the nonpositive-composite all-mixed arbitrary-E terminal](HAND_G5_NONPOSITIVE_COMPOSITES_ALL_MIXED_E_FRAMES_SHARP_REDUCTION.md).
That theorem does not assume E is between D and H. It
allows both mixed owners at each endpoint and any
remaining negative outer composites. It gives
\(q\ge q_*\), and its sharp identities retain separate
strict A/B losses.

No large negative noncanceling error has been silently
aligned in this argument. Such an error is retained in
(22) until the exact negative terminal resolves it.
This completes the lower bound for every original
candidate in Section 1.

## 7. Strict losses and the original equality configuration

All equality statements concern original centers.
The reductions retain a separate indicator for each
middle anchor whose circle is strictly below q.
A comparison that keeps an anchor preserves its actual
loss. A positive same-circle reconstruction recreates
its loss by the strict endpoint comparison. A crossed
clamp creates strict losses in both, regardless of their
earlier values. The direct AB theorem has the same
separate-loss property.

At \(q=q_*\), the terminal's positive circle masses
therefore exclude every source of strictness listed
above. In particular:

1. The original AB frame difference was zero, its common
   frame already lay between the original G/T frames,
   and its original transverse sum was one. Otherwise
   Section 2 supplies strict middle loss.
2. Neither outer endpoint was crossed relative to that
   original common frame. Every such crossing would
   invoke Section 4 and create both strict middle losses.
3. Every original canceling outer error and every
   original positive noncanceling error was zero.
   Their local reductions have strict pair slack,
   convertible into strict circle loss; a temporary
   primary lift cannot erase it.
4. Every nonzero small-tangent negative noncanceling
   error is likewise excluded by its \(e/150\) slack.
   The only remaining possible error is the original
   large negative noncanceling one. Its frame has not
   moved: with no AB or crossed-frame change, the
   replacement (15) changes only its coordinates.
   The negative sharp terminal forces that retained
   error to zero.

Thus the three original zero differences satisfy (6).
The original A/B coordinates were not changed when AB
was already aligned and normalized; zero outer errors
require no primary lift. H,D,E were never changed by
the frame-order procedure.

Reapply the terminal directly to the original five
anchors, now with both errors zero. Its E-order and
mixed-owner argument excludes original outside E at
equality and forces the original \(\delta=0\) split.
The final identity fixes the original stationary anchor
vectors and canonical hard split. This reapplication
does not identify any constructed intermediate or E
state with an original one.

For an original packing, the remaining original
constraints are unchanged and yield exactly the weak
five-parameter equality family already proved from
those stationary anchors in the aligned hard-class
theorem. This proves the claimed original equality
statement as well as the lower bound.

The assembly uses analytic local transports, the exact
global intermediate-order barrier, intrinsic scalar
endpoint comparisons, and the positive circle masses
of the sharp terminal. No state enumeration, angular
mesh, numerical acceptance premise, Lean run, or CI
result is used.

