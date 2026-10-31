# Complete one-share C6 orbit cover and its excluded physical residue

Date: October 26, 2026.

**Status: accepted exact four-orbit cover and complete nine-square
exclusion.** The finite symmetry cover and full unchanged scalar domain
were independently reviewed in REVIEW_C6_ONE_SHARE_COVER_ROOT_2026_10_26.md.
The final assembly SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md
and REVIEW_C6_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION_2026_10_26.md now
close every row: the last mixed110 outgoing-share0 core requires R<2,
whereas the same nine actual squares require R>2. The physical core
equations below remain recorded without deleting any original constraint.

This source closes only its original all-unique/shared obligation.
SIX_CYCLE_ONE_RADIAL_COMPLETE_EXCLUSION.md separately closes the complete
physical one-radial mask, and the reviewed sibling join closes the whole
alternating three-load orbit. Other load orbits and coarse parents remain open.
The two-share family has its complete separate three-orbit cover.

Retain all nine actual squares, the common selected certificate,
every original positive force, all actual application means and
their endpoints, the physical unique-corner masks, the true unloaded
degree-two transmitter equations, all three extra squares, and the
complete radius window
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
No Lean compilation or CI was run.

## 1. Exactly four whole one-share orbits

Use the proper cyclic labeling and the actual inner-side chart from
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md and
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md. The loaded bodies are
\(S_i\), the transmitter between \(S_i,S_{i+1}\) is \(W_i\),
and the actual far-corner bit is \(\chi_i\in\{0,1\}\).

The true shared-interface normal form implies:

* A genuine share at a bit-one loaded body is outgoing, on \(S_iW_i\).
* A genuine share at a bit-zero loaded body is incoming, on \(W_{i-1}S_i\).

The full mean-preserving symmetry operation is reflection of the
packing followed by reversal of its cyclic labeling. If \(T\)
is the reflection, the side direction reverses, and the side base
changes from \(b_i\) to \(T(b_i+u_i)\). Consequently
\[
                         \chi'_i=1-\chi_{-i}.
\tag{2}
\]
The actual incoming and outgoing means are interchanged under the
same operation; the actual chord length, every square, all force
weights and all additional units are carried along. This is the
operation derived in
SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md; its
derivation does not assume two shares.

For a constant word, (2) reduces 000 to 111. Cyclic relabeling
then places the sole outgoing share at unit 0. This is one orbit.

For a nonconstant word, first use (2) if needed to make the number
of one-bits equal to two. There is now a unique zero-bit. Exactly
one cyclic relabeling puts it at position 2, giving the canonical
word 110. The sole share can then be at position 0, 1, or 2.
There is no further allowed symmetry identifying these positions:
a cyclic symmetry preserving 110 is the identity, and a
reflection-plus-reversal changes the number of one-bits from two
to one. Thus these are exactly three distinct mixed orbits.

The complete cover is therefore:

| Canonical corner word | Sole shared loaded unit | Original genuine interface |
| --- | --- | --- |
| 111 | 0 | \(S_0W_0\), outgoing |
| 110 | 0 | \(S_0W_0\), outgoing |
| 110 | 1 | \(S_1W_1\), outgoing |
| 110 | 2 | \(W_1S_2\), incoming |

Every binary word and every allowed position of a sole genuine share
appears in exactly one of these four orbits. This is a contact-type
cover, with no subdivision of angles, force ratios, radius values,
transmitter positions, or share means.

## 2. Exact current one-share joins

| Whole orbit | Completed proof | Independent source and scope review | Consequence |
| --- | --- | --- | --- |
| Constant word, sole share | TRIANGLE_CONSTANT_CORNER_ALL_MEANS_RADIUS_TWO.md with NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | Root and separate block full-source reviews of the all-means theorem | Excluded by the same-nine-square R<2/R>2 contradiction; the old six-matrix proof remains historical |
| 110, sole outgoing share 1 | SIX_CYCLE_MIXED_ONE_SHARE_MIDDLE_EXCLUSION.md | REVIEW_C6_CONTACT_TYPE_CLOSURES_ROOT_2026_10_25.md | Already excluded by one strict vertical closure projection |
| 110, sole incoming share 2 | SIX_CYCLE_MIXED_ONE_SHARE_2_CLOSURE_EXCLUSION.md | REVIEW_C6_MIXED_ONE_SHARE_2_2026_10_26.md | Excluded by one strict diagonal closure projection |
| 110, sole outgoing share 0 | TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md with NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md | Full common-point reviews and REVIEW_C6_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION_2026_10_26.md | Excluded for all nine original squares; every three-extra allocation is covered |

The later source SIX_CYCLE_MIXED_ONE_SHARE_1_CLOSURE_EXCLUSION.md
is a valid shorter alternative proof of the already accepted
middle-share row. It is not an additional new orbit and must not
be counted as another closure.

The displayed proof-and-review joins close all four rows. The final
completion conclusion uses the independent global nine-square lower
bound, not the finite symmetry cover alone. Sections3--9 retain the
exact physical reduction and intermediate geometric results for the
formerly remaining second row of Section1; Section10 gives its final
complete contradiction.

## 3. Full unchanged scalar domain of the formerly remaining orbit

The remaining original contact type is
\[
           \chi=(1,1,0),\qquad S_0W_0
                     \text{ the sole genuine shared interface}.
\tag{3}
\]
Normalize only by the original positive \(\mu_0\), giving
\(\mu=(1,p,q)\), \(p,q>0\). Write
\[
 \alpha_i=\theta_i-\pi/2\in(0,\pi/4],\quad
 \sum_i\alpha_i=\pi/2,\quad
 c_i=\sin\alpha_i,\quad s_i=\cos\alpha_i,
\]
\[
 A_i=s_i-c_i,\qquad h_i=s_i+c_i,\qquad r=1/\sqrt2,
\]
\[
 n_0=(1,0),\qquad n_1=(-c_1,s_1),\qquad
 n_2=(-c_0,-s_0),\qquad f_i=\mu_i n_i.
\tag{4}
\]

### 3.1. Actual directions and means

The shared body retains
\[
 u_0=(0,-1),\qquad
 \ell_0=1-qA_0,\qquad 0<\ell_0\le1.
\tag{5}
\]
The two nonshared bodies have their actual chords one:
\[
 u_1=(X,Y)
       =\frac{(1+ps_1,1+pc_1)}{E_1},
 \qquad E_1=\sqrt{2+p^2+2ph_1},
\]
\[
 u_2=(-M,-N)
       =\frac{q(-h_0,-A_0)+p(-s_1,-c_1)}{E_2},
 \qquad E_2=\sqrt{p^2+2q^2+2pqh_2}.
\tag{6}
\]

The actual channel closure is precisely
\[
                  \sum_i(n_i+\ell_i u_i)=0,
                  \qquad \ell_1=\ell_2=1,
\tag{7}
\]
or, in these coordinates,
\[
 M=1-c_0-c_1+X,\qquad
 N=s_1-s_0-1+qA_0+Y.
\tag{8}
\]

The direction cones in the original normal form give
\[
 X\le s_1,\qquad Y\le r,\qquad
 M\ge s_1,\qquad N\ge rA_0\ge0.
\tag{9}
\]
For the first pair, \(u_1\) lies between directions
\(\alpha_1\) and \(\pi/4\). For the second, \(u_2\) lies
between \(\pi+(\pi/4-\alpha_0)\) and \(\pi+\alpha_1\);
the ordering follows from \(\alpha_2\le\pi/4\).

Equations (8)--(9) imply the useful necessary constraints
\[
 c_0+c_1\le1,\qquad X\ge h_1+c_0-1,
\]
\[
 qA_0\ge1+s_0-s_1-Y+rA_0,\qquad qA_0<1.
\tag{10}
\]
These are consequences of the original means, not substitute
equations defining a different core.

### 3.2. The sole shared chord is strictly shorter in this remaining orbit

The complete input (5) includes its endpoint \(\ell_0=1\).
Actual closure rules it out here. If \(A_0=0\), then
\(c_0=s_0=r\), and (8)--(9) give
\[
 N=s_1-r-1+Y\le s_1-1<0,
\]
contradicting \(N\ge0\). Thus
\[
                  A_0>0,\qquad 0<qA_0<1,
                  \qquad 0<\ell_0<1.
\tag{11}
\]
The endpoint is contradicted by an explicit original equation; it
has not been deleted from the scope of the orbit.

### 3.3. True virial and physical corner inequalities

Let \(F_i=f_{i-1}-f_i\), \(D_i=|F_i|\). The exact identities are
\[
 D_0=\sqrt{1+q^2+2qc_0},\quad
 D_1=\sqrt{1+p^2+2pc_1},\quad
 D_2=\sqrt{p^2+q^2+2pqc_2},
\]
\[
 E_0=1+qh_0,\qquad
 R\sum_iD_i=2+p+q(1+h_0)+E_1+E_2.
\tag{12}
\]
The original circle corner is \(z_i=RF_i/D_i\). With
\(v_i=-Ju_i\), its physical uniqueness gives
\[
                  z_i\cdot v_i>1/2,\qquad
                  (2\chi_i-1)z_i\cdot u_i>1/2.
\tag{13}
\]
These are the complete local corner inequalities of
SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md, applied
to the actual local type, independently of the number of shares.
In particular their full-radius force-ratio consequences include
\[
       p<27/10,\qquad p/q<27/10,\qquad q>20/81.
\tag{14}
\]
The first two use the nonshared bodies 1 and 2; the third uses the
outgoing share at body 0. All remain necessary weak relaxations of
the original physical constraints.

### 3.4. Full physical reconstruction constraints remain

For each original loaded square let
\[
 b_i=z_i-\chi_i u_i-v_i.
\]
The actual square and original ports are
\[
 S_i=b_i+[0,1]u_i+[0,1]v_i,\qquad p_i^-=b_i,
\]
\[
 p_0^+=b_0+\ell_0u_0,\qquad
 p_i^+=b_i+u_i\quad(i=1,2).
\tag{15}
\]
In addition to (7), the full actual channel equations remain
\[
                       p_{i+1}^- -p_i^+=n_i.
\tag{16}
\]
All four vertices of each actual square must lie in the same
circle, only \(z_i\) is its physical circle corner, every pair
of physical square interiors is disjoint, and all three extra
squares are present. The scalar identities above do not replace
any of these conditions.

## 4. Existing whole-family allocation restrictions for the three extras

SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md applies to this entire
remaining orbit. Its actual contact hexagon has side lengths
\[
             \ell_0,1,1,1,1,1,
             \qquad \operatorname{Per}(H)=5+\ell_0<6,
\]
where the final strictness also follows from (11). Every actual
central extra is contained in this one convex contact hexagon.
The accepted central-capacity theorem therefore gives at most one
extra in the entire central free union.

SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md places every other extra in
one of the three actual exterior channel caps. For channel \(i\),
put
\[
 j_i=Jn_i,\quad m_i=p_i^++n_i/2,\quad
 \alpha_i^{\rm ch}=n_i\cdot m_i,\quad
 h_i^{\rm ch}=-j_i\cdot m_i>0.
\]
Its outward unit normal is \(-j_i\), and the corresponding cap is
\[
        D_R\cap\{x:(-j_i)\cdot x\ge h_i^{\rm ch}\}.
\tag{17}
\]
The notation \(h_i^{\rm ch}\) distinguishes the actual channel
height from the trigonometric \(h_i=s_i+c_i\) in Section 3.

The full transmitter interval remains exactly that of Section 4 in
SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md. Its center is
\(m_i+\tau_i j_i\), with
\[
 B_i=\sqrt{R^2-(|\alpha_i^{\rm ch}|+1/2)^2}-1/2\ge0,
\]
\[
 \tau_i\in[-1/2,1/2]\cap
             [h_i^{\rm ch}-B_i,h_i^{\rm ch}+B_i].
\tag{18}
\]
The original genuine-overlap condition and every strict
singleton-side-interior condition remain in force. The displayed
closed interval is a necessary containment and port cover; it does
not permit changing the actual contact type at one of its endpoints.
Every allowed actual transmitter occupies the common rectangle
\[
 \alpha_i^{\rm ch}-1/2\le n_i\cdot x\le
                                      \alpha_i^{\rm ch}+1/2,
\]
\[
 -h_i^{\rm ch}\le j_i\cdot x\le
                  -h_i^{\rm ch}+w_i,\qquad
 w_i=\max(0,h_i^{\rm ch}+1/2-B_i).
\tag{19}
\]
Thus (19) is an occupied obstacle for every remaining completion,
without moving a transmitter to a preferred endpoint.

The exact contained-unit support threshold is
\[
                         d_R=\sqrt{R^2-1/4}-1.
\]
An exterior cap is empty whenever \(h_i^{\rm ch}>d_R\).
At the same time (19) gives \(w_i\ge h_i^{\rm ch}-d_R>0\).
The independently reviewed whole-family theorem
SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md now proves
\[
                  h_1^{\rm ch}>d_R+1/100.
\]
Its actual circle-corner chord argument retains the complete domain
above. Thus the entire actual exterior pocket 1 is empty, and
every original transmitter \(W_1\) occupies an inward rectangle
of width greater than \(1/100\). This is a uniform occupied
obstacle, not a selected slider position.

If \(k_{\rm cen}\) counts central extras and \(k_i\) counts extras
in exterior cap \(i\), the accepted complete location cover gives
\[
 k_{\rm cen}\in\{0,1\},\qquad k_i\in\mathbb Z_{\ge0},\qquad k_1=0,\quad k_0\le1,\quad k_2\le2,
 k_{\rm cen}+k_0+k_1+k_2=3.
\tag{20}
\]
Here the new bound on k_0 is the independently reviewed whole-domain
SIX_CYCLE_REMAINING_CAP_0_CAPACITY_ONE.md, summarized in Section 8.
The new bound on k_2 follows from the whole-domain actual H2>1/4
theorem SIX_CYCLE_REMAINING_CHANNEL_2_HEIGHT.md and
RADIUS_TWO_SIDE_CHANNEL_CAPACITY_TWO.md, summarized in Section 9.
Consequently at least two original extras lie in the union of
exterior caps 0 and 2. The complete remaining allocation counts are

| Central count | Ordered exterior counts \((k_0,k_2)\) |
| --- | --- |
| 0 | \((1,2)\) |
| 1 | \((1,1),(0,2)\) |

This table is an exhaustive count cover, not an assertion that a
listed allocation is feasible. In particular at most one central
extra does not imply that exterior extras occupy distinct caps:
that would require a further whole-cap bound for pocket 2. Nor can
one declare a central extra absent merely from a diagnostic contact
area or a chosen transmitter position.

## 5. Exact completion scope

The last original type(3) is now excluded for all nine physical
squares by Section10. Its original equations and every interval in(18)
remain part of the full retained domain. The cap restrictions are
independent necessary geometric consequences, and no contact-type
reduction alone implies a completion bound.

The strictly obtuse one-radial physical mask has its separate complete
assembly in SIX_CYCLE_ONE_RADIAL_COMPLETE_EXCLUSION.md. The unrestricted
sharp inequality, original equality classification and older prerequisite
audit remain open.

## 6. Further exact whole-orbit reductions and the earlier conditional criterion

SIX_CYCLE_REMAINING_ONE_SHARE_FIVE_SCALAR_COMPATIBILITY.md proves
that one actual channel, closure and virial are equivalent to all
six individual channel components, using the exact original torque
identity. It reconstructs the core in both directions from(R,p,c1),
retaining every physical mask, genuine contact set, mean, slider and
all nine-square nonoverlap constraints. Root and a separate full
source review passed; no numerical root-isolation premise is used.

SIX_CYCLE_REMAINING_ONE_SHARE_ANGLE_AND_FORCE_BOUNDS.md derives
from actual closure the strict q>1 and c0>3-2sqrt(2)>1/6, as well as
c1+(1+1/sqrt(2))c0+s0/sqrt(2)>=1+1/sqrt(2).
The original genuine ell0=1 endpoint is contradicted explicitly,
so1<q<1/(s0-c0) and c0<1/sqrt(2). The complete direction and
vertical bounds in that source remain available. Its independent
root review passed.

SIX_CYCLE_REMAINING_CAP_0_CONDITIONAL_CAPACITY_ONE.md proves an
entire-cap capacity-one criterion from specified coarse coordinates.
Its possible center rectangle has squared diameter55969/57600<1.
The radius premise is now supplied by the whole-orbit theorem below.
The other coordinate hypotheses have not been established for the full
original system. This conditional theorem itself retires no allocation;
the separate complete theorem in Section 8 removes three without those
hypotheses. The final radius contradiction in Section10 closes the
physical three-extra completion and exactly the original all-unique/shared
gate; radial and coarse parents stay open.

## 7. One common comparison point now proves the whole radius bound

TRIANGLE_MIXED_COLLAPSED_SHARE_FERMAT_BOUND.md and
TRIANGLE_MIXED_ONE_SHARE_COMMON_POINT_BOUND.md prove that every
nonconstant counterclockwise or collinear force triangle has one common
point where both endpoint functionals are strictly below twice its
perimeter. Norm convexity at that same point covers the entire original
shared-mean interval. The argument includes every Fermat-vertex,
collinear and coincident alternative; the constant zero exception is
absent from the actual positive force triangle.

The proof uses global convexity and Hessian estimates, one explicitly
displayed fixed rational witness, and one uniform comparison-point
displacement. It uses no angle grid or coefficient-sign packet. Root
and independent C6 reviews reconstructed all fixed radical comparisons
and the whole continuous-domain argument.

For the original actual ell0, closure makes the force-plane origin a
global minimum of its exact convex support functional. The unchanged
virial is R*P=Phi_delta(0), where P>0 and delta=1-ell0. The common
point therefore gives R*P<=Phi_delta(x)<2P, hence R<2 throughout
the entire remaining physical orbit. No force ratio, normal, original
mean, physical mask or transmitter slider is changed.

Any hypothetical original core in this orbit consequently has
79/40<=R<2. The radius theorem by itself is a necessary core bound.
Section10 joins it to the new R>2 theorem for all nine unchanged
squares, supplying the complete original-gate exclusion.

## 8. Whole cap-0 capacity removes three allocations

SIX_CYCLE_REMAINING_CAP_0_CAPACITY_ONE.md proves H0>21/50 from the
original physical channel, using a unimodal function over one complete
interval. Original closure bounds the actual endpoint-center distance
and its outward gap below127 degrees. Every cap extra has center norm
above23/25, so its full-square inner-circle arc is connected and longer
than43.5 degrees. Actual occupied-crosscut routing confines it between
the two endpoint blocked arcs of20 degrees each. Two extra arcs cannot
fit. Root and separate full-source and physical-scope reviews passed.

Thus k_0<=1 throughout the whole original orbit, independently of every
unproved coordinate-box premise. Exactly (central,cap0,cap2)=(0,3,0),
(0,2,1),(1,2,0) are removed from the previous cover. Before the
additional cap2 bound below, four allocations remained:
(0,0,3),(0,1,2),(1,0,2),(1,1,1). The current exhaustive cover is
the historical three-allocation table in Section4. Section9 further
reduces it to(1,1,1), and Section10 excludes that allocation as well.
Every original square, circle mask, force, actual mean and slider remains.

RADIUS_TWO_CAP_INNER_ARC_QUARTER_TURN.md additionally proves a general
orientation-independent tool for a radius-at-most-two cap of height>1/4:
each whole unit has one connected open arc longer than45 degrees on
the radius5/4 circle, containing its radial-center point. Its full
strengthened proof passed independent review.

## 9. Whole channel-2 height, opposite-port gap and capacity one

SIX_CYCLE_REMAINING_CHANNEL_2_HEIGHT.md proves H2>1/4 on the entire
original orbit. The side-channel capacity-two theorem first removed
the allocation(0,0,3). Its actual center, occupied-crosscut and arc
routing hypotheses all hold for the original simple alternating C6.

The reviewed RADIUS_TWO_CAP_INNER_ARC_SHARP_BOUND.md gives full-square
arc length at least2asin(2/5), with the complete equality case.
RADIUS_TWO_OPPOSITE_PORT_INNER_ARC_GAP.md now proves that the actual
two opposite-port endpoints leave a gap strictly below4asin(2/5).
SIX_CYCLE_REMAINING_CAP_2_CAPACITY_ONE.md establishes every actual
frame, face-order and occupied-crosscut hypothesis, retaining unequal
small-coordinate offsets and all transmitter sliders. Root and a
separate C6 reviewer audited both entire sources.

Hence k_2<=1 throughout the whole original domain. Together with
central<=1, k_1=0 and k_0<=1, the analytic cap route leaves only
(central,cap0,cap2)=(1,1,1). This removes exactly(0,1,2) and(1,0,2)
from the historical cover in Section4. It adds no computational packet.

## 10. The same-nine-square radius contradiction closes every allocation

NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md proves R>2 for every packing
of nine actual unit squares, without a graph, stress, contact or
orientation premise. Its one explicit uniform measure certificate
now has five fixed mass checks, one fixed derivative enclosure and
explicit analytic rational comparisons, with two exact integrated
evaluators. The complete current cover is
NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.
All nine original squares here are within that theorem's scope.

Section7 gives R<2 from the same actual force/mean configuration.
These conclusions contradict one another. Every possible placement
of the three original extras, including(1,1,1), is therefore excluded.
No square, force, original mean, physical mask or slider is changed.
This does not assert that the six-body core alone is impossible.

SIX_CYCLE_ALL_UNIQUE_SIDE_COMPLETE_EXCLUSION.md records the complete
zero/one/two/three-share matching cover and its independent gate audit.
Exactly M6.B6.C6.THREE_ALTERNATING.ZERO_DIAGONAL.UNIQUE_SHARED closes.
No radial parent, coarse cell, unrestricted sharp theorem, equality
classification or Lean integration is closed by this argument.
