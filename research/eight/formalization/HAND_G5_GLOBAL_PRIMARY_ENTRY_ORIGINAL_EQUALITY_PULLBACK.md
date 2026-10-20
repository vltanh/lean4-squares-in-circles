# Original equality survives the complete primary-owner entry

## 1. Statement and the two equality interfaces

Let q* be the stationary sharp squared radius. Start at q=q* in
the original boundary-neighbor domain of
[the complete primary-owner entry theorem](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md).
In particular, H,A,B,D are the original outer anchors at this
same q, E has its original true-core or outer-q status and
normalized nonpositive sign, and the actual retained owners are
\[
 HG,AB,TD\in\{0,2\},\qquad GA,EH\in\{0,1\},
 \qquad BT,DE\in\{2,3\}.
\tag{1}
\]
Write \(W(d)=(1+\cos d+|\sin d|)/2\). A witness slack is
its actual signed projection minus this required width.
Keep the original implications HG2 => yG<0 and TD0 => yT>0.
The states are sorted, avoid the open true core, and have the
real-frame and variation bounds in that theorem. No initial
G/T sign, contact equality, or individual error sign is assumed.

**Original-owner equality theorem.** The actual GA0 and BT2
witnesses are already feasible on this original input. Applying
the hard-owner equality theorem to that input gives its own
stationary five anchors, normal G/T signs, and frame identities
\[
 \theta_G=\theta_H,\qquad
 \theta_A=\theta_B=\theta_T=\theta_D=\theta_E,
 \qquad \theta_H-\theta_A=t_*>0.
\tag{2}
\]
This conclusion does not identify a moved intermediate with its
ancestor.

There are two distinct transfers to check. First, the primary-pair
constructions may change G/T coordinates and frames. Sections 2--4
prove the theorem above by excluding every source in which an
original hard witness was unavailable. Second, a fixed-witness
radial-boundary reduction may change the centers of all seven
exterior squares while preserving their physical frames and
initially chosen signed separating axes. Sections 5--6 prove that
these initially chosen axes have exactly the stationary physical
directions, and then apply the stationary dual directly to the
original centers.

The second transfer is essential: availability of a new hard
witness at a boundary representative would not alone say that it
was one of the signed witnesses retained from the original packing.

## 2. Exhaustive source audit for the G pair

Write
\[
 x=\theta_A-\theta_G,\qquad
 \tau_G=\theta_A-\theta_H.
\tag{3}
\]
Every G-only construction fixes H,A and therefore fixes tauG.
It also fixes B,T,D,E and all of their data. Use the following
choices in the preprocessing of the complete entry theorem.

If actual GA0 is already available, select it and leave G
unchanged. Otherwise GA1 is retained and x is nonzero, since
x=0 gives exactly the actual GA0 tie. If HG is already aligned
and x<0, leave the genuine aligned-negative pair unchanged;
there is no need to normalize G's tangent before classifying it.

For all remaining sources the following table is exhaustive.
Here “hard endpoint” means an endpoint at which actual GA0 is
available, regardless of whether GA1 is also available. A
remaining aligned primary is classified by its actual error:
positive gives G+, negative and still genuine gives G-, and
zero gives the hard tie G0.

| Source with GA0 unavailable | Actual same-q construction | Information if a hard endpoint is reached |
|---|---|---|
| HG0, tauG>0; either G sign and either individual error sign | Positive-total uniform-radius pair transport | The unchanged anchors still have tauG>0. |
| HG0, tauG<=0, yG>=0 | Wrong-sign nonpositive-total construction | G aligns with A; actual HG0 slack is greater than 1/25. |
| HG0, tauG<=0, yG<0, x>0 | Positive-GA nonpositive-total construction | G aligns with A; actual HG0 slack is strictly positive. |
| HG0, tauG<=0, yG<0, x<0, HG nonaligned | Genuine-negative flat-core entry and noncanceling companion | A surviving actual HG0 witness has strictly positive slack. |
| HG2, x>0 | Retain the original positive primary | This is already G+; no hard endpoint is inferred. |
| HG2, x<0, HG nonaligned | Genuine-negative flat-core entry and canceling companion | A surviving actual HG0 or HG2 witness has strictly positive slack. |
| Either HG owner, HG aligned, x<0 | Retain the original genuine negative primary | This is already G-; no hard endpoint is inferred. |

For HG2 the original zero-owner implication gives yG<0, so
there is no omitted wrong-sign HG2 row. At an aligned HG edge,
its actual transverse inequality and bH<.9 also force yG<-.1.
Zero signed totals are included in the nonpositive rows. In the
second row the wrong-sign inequality itself forces the GA error
negative; no extra sign alternative needs to be added.

The precise inputs to the table are as follows.

* Section 6 of
  [the uniform-radius pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
  gives the first row for either original G radial kind, either
  signed tangent, and both individual-sign allocations. A
  nonhard endpoint is HG alignment with the positive remaining
  error tauG, hence G+.
* [The wrong-sign pair theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_WRONG_SIGN_PAIR_REDUCTION.md)
  gives the second row, including the strict HG0 reserve.
  Its nonpositive-total construction already uses the original q;
  the uniform-radius theorem supplies the positive-total join.
* [Positive GA with nonpositive total](HAND_G5_GLOBAL_PRIMARY_ENTRY_POSITIVE_GA_NONPOSITIVE_TOTAL.md)
  gives the third row, also at the original q and with strict HG0
  slack. It includes tauG=0.
* If a negative GA1 is actual but GA0 is unavailable, equation
  (26a) of the uniform-radius theorem rules out outer G at the
  actual q and forces the genuine flat core aG=7/12. The
  [noncanceling companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md)
  and
  [canceling companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md)
  then give the fourth and sixth rows. Their strict surviving
  transverse witness is part of their statements when the
  original HG error is nonzero. It is retained even when the
  surviving owner changes from HG2 to HG0.

The local endpoints keep every unchanged anchor, the other
intermediate, the actual q, and the necessary physical gap and
variation bounds. Section 6 of the uniform-radius theorem checks
the flat-core endpoint gaps as actual boundary-neighbor gaps.
Thus the table concerns actual necessary-cycle descendants,
rather than only scalar relaxations.

Every hard endpoint obtained from an original missing GA0
therefore carries at least one of the following obstructions:
\[
 \boxed{\quad \tau_G>0\quad\hbox{or}\quad
       \text{a retained strictly positive HG slack}.\quad}
\tag{4}
\]
Every other endpoint has a genuine positive or aligned-negative
primary and is one of the terminal types already in the complete
entry matrix. If a nominal aligned-negative endpoint also admits
GA0, select that actual hard witness immediately; the strict HG
information in the corresponding nonaligned source row remains.

## 3. The reflected source audit covers every T case

The exact local reflection and role reversal is
\[
 (H',G',A')=(D,T,B),\qquad
 \theta'=-\theta,\qquad y'=-y.
\tag{5}
\]
It transforms actual local projections, core and circle
conditions, and physical gaps. It does not involve or change E.
The correspondence is

| G-side datum in Section 2 | T-side datum |
|---|---|
| GA0, GA1 | BT2, BT3 |
| HG0, HG2 | TD2, TD0 |
| x=thetaA-thetaG | z=thetaT-thetaB |
| tauG=thetaA-thetaH | tauT=thetaD-thetaB |
| Normal yG<0 | Normal yT>0 |
| Wrong yG>=0 | Wrong yT<=0 |
| G aligned with A or H | T aligned with B or D |
| Strict surviving HG slack | Strict surviving TD slack |

Accordingly, start by leaving T unchanged whenever actual BT2
is available. A zero BT3 error is already that actual tie.
If BT2 is unavailable, the reflected seven rows cover:
positive BT3/TD2 total of either individual sign; wrong T sign
with nonpositive total; normal positive BT3 with nonpositive
total; normal negative BT3 with nonaligned TD2; positive BT3
with TD0; negative BT3 with nonaligned TD0; and an already
aligned genuine negative BT3. The original TD0 implication
supplies the normal sign in its two rows. Zero totals stay in
the nonpositive constructions.

Every hard endpoint obtained from an original missing BT2
therefore carries
\[
 \boxed{\quad \tau_T>0\quad\hbox{or}\quad
       \text{a retained strictly positive TD slack}.\quad}
\tag{6}
\]
The other endpoints are T+ or genuine T-. The G-only and
T-only preprocessing operations have disjoint changed vertices
and disjoint changed edge pairs. Each preserves a strict
transverse slack obtained on the opposite side. Both preserve
all five original anchors, including their frames and circles.

## 4. Apply the terminal matrix before pulling back equality

Run the source-aware preprocessing in Sections 2--3. The
[complete entry theorem](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md),
Sections 4--6, gives the following entire terminal list at q*.

| Terminal | Equality obstruction |
|---|---|
| At least one positive primary G+ or T+ | The sign-free positive-primary exclusion is strict at q<=q*. |
| G-/T0 | A genuine aligned-negative GA gives a strict H-anchor circle loss. |
| G0/T- | A genuine aligned-negative BT gives a strict D-anchor circle loss. |
| G-/T- | The first conversion gives strict H loss; the complete second conversion preserves it and adds strict D loss. |
| G0/T0 | Only the independent G/T preprocessing has occurred; all five source anchors remain unchanged. |

The negative rows use actual anchor losses, not circle loss at
a free intermediate. They are impossible at q* because the
hard-owner equality theorem puts each of its own five anchors
on the stationary q* circle. In the two-negative row the
complete second conversion permits the earlier H loss and
preserves H exactly, as recorded in the complete matrix.

Thus only G0/T0 remains. For this final hard input,
[retained-contact rigidity](HAND_G5_HARD_EQUALITY_RETAINED_CONTACT_RIGIDITY.md)
gives zero slack for every retained HG and TD witness and gives
the unchanged anchor-frame relations
\[
             \tau_G=-t_*<0,\qquad \tau_T=0.
\tag{7}
\]
Consequently neither alternative of (4) nor of (6) can occur.
The opposite intermediate's independent preprocessing preserved
the relevant strict witness, so it cannot disappear in this
G0/T0 row. An anchor-changing negative terminal has already
been excluded separately; no strict local contact is asserted
to survive an unchecked later anchor motion.

It follows that neither original hard witness was missing.
Both GA0 and BT2 were actual on the source before either
intermediate was changed. Now apply
[the arbitrary-sign hard-owner theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md)
directly to that untouched source. Its E radial alternative
holds because E is still the source's true-core or actual
outer-q state. Its original signs, zero-owner implications,
and actual neighboring inequalities are precisely the ones
assumed in Section 1. This proves the source's own stationary
anchor coordinates and (2).

The argument has not claimed that a comparison G or T equals
its ancestor. It has proved the hypotheses of a sharp theorem
on the ancestor itself.

## 5. The initially retained axes are stationary physical axes

We next distinguish actual hard-witness availability from the
initial selection retained by a radial-boundary deformation.
Suppose the source of Section 1 is such a boundary representative.
Every initially chosen signed axis is still an actual weak
witness there. The global owner restrictions apply to every
original weak witness, including ties, so these initial axes
also belong to (1). In particular this is the explicit scope of
[global GA rigidity](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md),
[global EH rigidity](HAND_G3_GLOBAL_EH_OWNER_RIGIDITY.md),
and
[global DE rigidity](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md).
Any subsequent chart recoding changes only its description;
the physical signed normal retained by the boundary deformation
is unchanged.

At the sharp source the five edges HG, AB, BT, TD, DE have
zero frame error by (2). Their two allowed owner alternatives
are the same physical signed separator at that alignment.
The only remaining issue is whether the initial nonaligned
GA or EH axis could be the other allowed owner. We exclude
both possibilities on the actual stationary coordinates.

Use the stationary notation and coarse bounds in Section 1 of
[the equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md):
\[
 \begin{gathered}
 .1<\tan t_*<.13,\qquad .916<u_*<.94,\\
 1.741<r<1.755,\quad 1.9<w<1.906,\quad .533<v<.549,\\
 1.338<k_1<1.39,\qquad 1.4<k_2<1.45.
 \end{gathered}
\tag{8}
\]
These are whole-function consequences of stationary existence
and two exact endpoint signs, not a numerical equality box.
The actual chart coordinates are
\[
 \begin{aligned}
 a_A&=r-1/2,& b_A&=u_*-1/2,\\
 a_H&=k_2-1/2,& b_H&=k_1-1/2,\\
 a_E&=w-1/2,& b_E&=v-1/2.
 \end{aligned}
\tag{9}
\]

### 5.1 GA1 is strictly unavailable

Put g=-yG>0. Retained-contact rigidity gives
\[
 b_H+g=1,\qquad
 P_{GA0}=a_A\cos t_*-b_A\sin t_*-g=W(t_*).
\tag{10}
\]
Thus (8)--(9) imply
\[
 b_A<.44,\qquad a_A+g<1.255+.162<1.42,
 \qquad \tan(t_*/2)<.065.
\tag{11}
\]
Sorting and true-core avoidance give, for this same source G,
\[
 a_G\ge\frac12+\frac1{12\sqrt2}>\frac{447}{800}.
\tag{12}
\]
Indeed the distance from the origin to a square with sorted
center magnitudes aG>=bG is at most
\(\sqrt2(a_G-1/2)_+\), and it is at least 1/12.
The last strict comparison in (12) follows from
2(141/200)^2<1.

At the actual GA error -t*, the other projection is
\[
 P_{GA1}=a_A-a_G\sin t_*-g\cos t_*.
\]
Consequently
\[
 \begin{aligned}
 P_{GA0}-P_{GA1}
 &=\sin t_*\left[a_G-b_A-(a_A+g)\tan(t_*/2)\right]\\
 &>\sin t_*\left[\frac{447}{800}-\frac{11}{25}
                     -\frac{71}{50}\frac{13}{200}\right]\\
 &=\frac{529}{20000}\sin t_*>0.
 \end{aligned}
\tag{13}
\]
Since GA0 is tight by (10), GA1 is strictly below its required
width. It cannot be one of the original retained weak axes.

### 5.2 EH0 is strictly unavailable

The stationary mixed contact, the last equality of (15) in
[the aligned five-anchor theorem](HAND_G5_ALIGNED_HARD_CLASS_SHARP_REDUCTION.md),
is
\[
 P_{EH1}=a_H+a_E\sin t_*-b_E\cos t_*=W(t_*).
\tag{14}
\]
The other actual EH projection is
\[
 P_{EH0}=a_H\cos t_*+b_H\sin t_*-b_E.
\]
Their difference is
\[
 P_{EH1}-P_{EH0}
 =(a_E-b_H)\sin t_*+(a_H+b_E)(1-\cos t_*)>0.
\tag{15}
\]
Here aE>1.4, bH<.89, aH>.9 and bE>.033 follow directly
from (8)--(9), and t*>0. Thus EH0 also cannot be an actual
retained weak axis at this sharp source.

The initially selected GA and EH axes are therefore GA0 and
EH1. On each other edge the allowed tied choices have the same
stationary signed normal. This establishes the physical-axis
interface required for a direct original-center dual argument.

## 6. Apply the positive stationary dual to the original packing

Let an original eight-square packing at squared radius q* have
the canonical fixed-witness boundary representative above.
The general recession translation in
[the radial-boundary reduction](../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
can retain any initially selected seven neighboring signed
SAT axes, every physical square frame and the cyclic order.
The strengthened fixed-witness argument is stated explicitly
in Section 1 of
[the original-square equality pullback](../EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md).
No preservation of the individual center rays or centers is
needed or asserted.

Sections 1--4 give the actual boundary source's frames (2).
Those are also the original physical square frames, modulo
the harmless quarter-turn chart choices. Section 5 gives the
stationary directions of the seven initially selected signed
normals. They were already separating axes for the original
packing, not only for a later comparison system.

Rotate the original packing so the A,B,T,D,E frames are zero,
and put e=(cos t*,sin t*) and f=(-sin t*,cos t*). Write
u=u*, and define the stationary radicals
\[
 \begin{gathered}
 r=\sqrt{q_*-u^2},\qquad U=\sqrt{q_*-(2-u)^2},\qquad V=3-U,\\
 Y=\sqrt{q_*-V^2},\qquad v=2-Y,\qquad w=\sqrt{q_*-v^2},\\
 k_1=2-\cos t_*(r-1)+u\sin t_*,\qquad
 k_2=1+v\cos t_*-(w-1)\sin t_*.
 \end{gathered}
\tag{16}
\]
The five stationary centers are
\[
 \begin{array}{c|l}
 A&(r-1/2,\ 1/2-u)\\
 B&(U-1/2,\ 3/2-u)\\
 D&(U-5/2,\ Y-1/2)\\
 E&(1/2-w,\ 1/2-v)\\
 H&(1/2-k_1)e+(1/2-k_2)f.
 \end{array}
\tag{17}
\]
Denote them by \(P_i\), and the original packing centers by \(p_i\).
The stationary positive disk weights \(\mu_i\) sum to one, and the
seven stationary contact weights \(\lambda_j\) are strictly positive.
Their table-free formulas, normalization, and positivity are proved
in Section 3 of
[the stationary force-weight proof](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md).
Use the original selected-corner offsets
\[
 \begin{gathered}
 o_A=(1/2,-1/2),\quad o_B=(1/2,1/2),\quad
 o_D=(-1/2,1/2),\quad o_E=(-1/2,-1/2),\\
 o_H=-e/2-f/2.
 \end{gathered}
\tag{18}
\]
For the original signed gap slacks \(g_j\ge0\) define
\[
 \mathcal D=
 \sum_{i\in\{A,B,D,E,H\}}\mu_i|p_i+o_i|^2
                       -\sum_{j=1}^7\lambda_jg_j.
\tag{19}
\]
All physical normals and frames now have their stationary
values. The stationary force equations give zero forces at
G,T and give \(F_i=-2\mu_i(P_i+o_i)\) at each of the five anchors.
Completing the five center squares yields the exact identity
\[
 \boxed{\quad
 \mathcal D=q_*+
      \sum_{i\in\{A,B,D,E,H\}}\mu_i|p_i-P_i|^2.
 \quad}
\tag{20}
\]
The constant is q*, since the stationary comparison has all
five selected vertices on that circle and every selected gap
equal to zero. This is the stationary identity in Section 2
of the equality-family proof; after the physical-axis check
above it applies to the original centers without any proximity
assumption.

Original containment and the original nonnegative gap slacks
also give
\[
 q_*-\mathcal D
 =\sum_i\mu_i\bigl(q_*-|p_i+o_i|^2\bigr)
                       +\sum_j\lambda_jg_j\ge0.
\tag{21}
\]
All weights are positive. Equations (20)--(21) force the five
original anchors to equal (17), and force all seven original
selected gaps to be zero. The two zero slider forces and
their actual incident contact equalities then give exactly
\[
                 p_T=(U-3/2,z),\qquad
                 p_G=P_H+e+\eta f,
\tag{22}
\]
with their original frames 0 and t*, respectively.

The original central square and all original pairwise
nonoverlap and containment constraints have not been weakened
in this conclusion. Sections 3--6 of
[the complete equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
now give the exact weak necessary-and-sufficient domain for
the five parameters z, eta, the central center's two coordinates,
and its orientation. They also give its converse and an explicit
five-dimensional box of pairwise noncongruent packings. These
claims concern the original eight squares, not transported
intermediates. The stationary dual equally prevents a feasible
configuration in that domain from having a smaller enclosing
circle after translating its center.

This completes the equality interface of the unrestricted
assembly once its original boundary capture has supplied the
domain of Section 1. No new local coordinate enclosure,
numerical equality test, or identification of old and new G/T
coordinates is used.
