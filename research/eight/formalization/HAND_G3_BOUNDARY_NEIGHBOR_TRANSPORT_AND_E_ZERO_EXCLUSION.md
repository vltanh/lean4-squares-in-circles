# Boundary-neighbor transport and the E-zero high-GA exclusion

## 1. Exact geometric domain

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 k=(0,1,0,1,0,1,1).
\tag{1}
\]
Use the cyclic roles \((H,G,A,B,T,D,E)\). A **boundary-neighbor
cycle** in this note consists of seven actual unit squares and
the following data:

* Each square is contained in the closed disk of squared radius Q
  and avoids the open radius-\(1/12\) disk.
* Each sorted own-frame center \((a_i,-y_i)\), with
  \(a_i\ge |y_i|\), is on the true core side/corner or the outer
  Q-circle. These are the full boundary curves used by G1.
* The centers have cyclic order of winding one. Consecutive squares
  have disjoint open interiors, witnessed by actual weak separating
  inequalities. Choose each retained witness and each boundary-chart
  label consistently at both incident edges.
* Their directed nearest axes have quarter increments k and real
  frame lifts \(\theta_i\) of spread less than h.

Only the seven consecutive pairs are required to be disjoint in this
definition. This is exactly the necessary relaxation already produced
by the fixed-axis radial-boundary reduction in Section 1 of
[the exterior-frame proof](../HAND_EXTERIOR_FRAME_CONCENTRATION.md).

**Boundary-domain lemma.** The G2 wrong-word exclusions and global
nearest-axis tie restrictions, as well as the zero-owner, quarter-sign,
DE-owner, and BT-owner conclusions proved from G0--G2, apply to every
boundary-neighbor cycle just defined. In particular, if \(y_E\le0\),
every feasible BT witness has owner 2 or 3, including tied witnesses.

**E-zero consequence.** In a boundary-neighbor cycle with
\(y_E=0\), every feasible GA witness has owner 0 or 1. Hence a
retained GA2 or GA3 witness excludes that boundary, independently of
the other original owners or transverse signs.

Sections 2--3 justify the exact boundary domain of the existing
theorems. Section 4 proves the consequence by a physical reflection.
Sections 5--6 give the eligibility criteria for continuous transports
and directly constructed boundary endpoints.

## 2. The physical gap and common-marker inputs are local

Avoidance of the open radius-\(1/12\) disk implies
\[
 a_i\ge\frac12+\frac1{12\sqrt2}>\frac{107}{200}.
\tag{2}
\]
Indeed the distance of the square from the origin is at most
\(\sqrt2\max(a_i-1/2,0)\). The strict last inequality follows
from \(1/(12\sqrt2)>7/200\).

The second central-depth band in Section 1 of
[the central-band proof](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md)
uses only the two contained squares, (2), and their disjoint open
interiors. Their smaller center angle is therefore greater than
\(19/25\). Each positive consecutive gap \(g_i\) is consequently
greater than \(19/25\). Since the gaps sum to \(2\pi\),
\[
 \frac{19}{25}<g_i<2\pi-6\frac{19}{25}<\frac{3\pi}{4}.
\tag{3}
\]
For the last comparison use \(\pi<22/7\), which gives
\(5\pi/4<55/14<114/25\). This also supplies the full physical
gap interval needed for the forward-axis geometry.

Every two-state hypothesis of the complete C/L/M/H inequalities
in Section 2 of
[the exterior-frame proof](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
is now present. Choose one signed marker \(\ell_i\) at each
vertex and use it in both incident estimates. With
\[
 w(t)=\frac{\sin t+\cos t-1}{2},\qquad
 d_i=\theta_{i+1}-\theta_i,
\]
the exact G1 inequality is
\[
 k_i\frac\pi2+d_i+\ell_i-\ell_{i+1}
       -\frac9{50}w(|d_i|)>\Gamma_{t_i t_{i+1}}.
\tag{4}
\]
The four-type constants, chart junctions, weak SAT contacts, and
nearest-axis ties have precisely the coverage proved there. No
nonconsecutive pair occurs in (4).

The common markers and real increments telescope around this
boundary-neighbor cycle. The seven-walk argument in Section 3 of
that proof thus gives the same global charge bound, and the
concavity argument in Section 2 of
[the BT0/DE2 path proof](HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md)
gives
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{5}
\]
One may derive (5) again at a transported endpoint from its actual
boundary data. This does not retain an old marker value at a moved
state: the marker is evaluated at the new actual state, once for
both adjacent edges.

## 3. The owner proofs retain exactly these inputs

The zero-primary exclusion in
[HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION](HAND_ZERO_PRIMARY_CYCLIC_EXCLUSION.md)
uses one original zero-edge projection, its two boundary states,
(3), and the six-edge return formed from (4). It therefore excludes
owners 1 and 3 on every zero edge of the present domain.

Likewise, Sections 4--9 and 11 of
[the global quarter-sign and DE theorem](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md)
use only the local quarter projection, the same boundary markers,
and the six unchanged inequalities (4). They supply both generic
quarter-sign implications and, when \(y_E\le0\), the DE2/3
restriction and negative D sign.

The zero--quarter propagation theorem
[HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER](HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER.md)
uses two consecutive edges and their five-edge G1 return. Its
positive endpoint signs are therefore also available here.
The complete
[global BT theorem](HAND_G3_GLOBAL_BT_OWNER_RIGIDITY.md)
then applies its three-edge return inequality and four-edge
complementary-path estimates. Their only global geometric inputs
are the consistent boundary markers, (3)--(5), and the sign/owner
implications just obtained. All supports concern the actual
consecutive shared states. Its original-axis comparisons and
both radial tails use no nonconsecutive nonoverlap condition.
Consequently its strict contradiction excludes every actual BT0
or BT1 witness on this boundary-neighbor domain.

This is an explicit extension of the stated domain, justified by
the displayed dependencies. It does not assume that a transported
seven-cycle can be completed to an eight-square packing. The central
square was used to obtain the initial core avoidance; core avoidance
itself is retained as a geometric input here.

### 3.1. Wrong words and nearest-axis ties have the same boundary domain

The integer classification and six strict wrong-word contradictions in
[the quarter-word selection proof](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md)
also use only (3), the real-frame bound, the canonical boundary states,
and their actual consecutive witnesses. Each wrong-word proof adds
its seven two-state estimates with the same vertex label at shared
ends. Its core adjacency restriction, when used, is the
[core-cycle gap lemma](HAND_GLOBAL_CORE_CYCLE.md), whose proof needs
disjointness only on the indicated neighboring pairs. Thus none of
these strict word exclusions requires nonconsecutive separation.

At an actual nearest-axis tie one may change that square's nearest
axis by a quarter turn, without changing the physical square or any
neighboring separation. The same real lifts modulo a quarter turn,
physical gaps, circles and core states are retained. The integer
argument and wrong-word exclusions therefore apply to the changed
representation on the present boundary-neighbor domain. The proof of
[the nearest-axis tie theorem](HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md)
then gives strict sorting at G,A,B,T,E; only positive H or negative D
may be diagonal.

In particular, a positive T diagonal changes the quarter word to
\(0100111\), in the excluded \(0010111\) class. A negative T diagonal
creates a negative increment on its outgoing zero edge, which would
give a physical gap below \(h<19/25\). Both are impossible. These
conclusions remain valid for an actually feasible boundary endpoint
constructed independently of a continuous path.

## 4. Reflect the E-zero cycle

Assume \(y_E=0\). Reflect all seven physical squares and reverse
their cyclic order, with the new roles
\[
 (H',G',A',B',T',D',E')=(D,T,B,A,G,H,E).
\tag{6}
\]
Reflection negates the signed transverse coordinate. The reflected
E' therefore still satisfies \(y_{E'}=0\le0\). The edge word remains
\((0,1,0,1,0,1,1)\). The real frame lifts are negatives of the old
lifts in the order (6); their spread is unchanged. The new increment
on each reversed edge equals its old increment, rather than its
negative. Every containing circle, core distance, boundary kind,
physical gap, and weak neighboring separation is preserved.

The new BT edge is the reverse of the old GA edge. For a quarter
edge with signed states \((a,y),(A,Y)\), write
\[
 \begin{aligned}
 P_0&=y+A\cos d+Y\sin d,&
 P_1&=A+a\sin d+y\cos d,\\
 P_2&=a\cos d-y\sin d-Y,&
 P_3&=a+A\sin d-Y\cos d.
 \end{aligned}
\tag{7}
\]
The reflected reversed states are \((A,-Y),(a,-y)\), at the
same d. Direct substitution gives
\[
 (P'_0,P'_1,P'_2,P'_3)=(P_2,P_3,P_0,P_1).
\tag{8}
\]
The support width is unchanged. An old feasible GA2 or GA3 is
therefore respectively a new feasible BT0 or BT1, with exactly
the same weak inequality. Section 3 excludes it. This proves the
E-zero consequence, including all original ties.

## 5. Continuous transport keeps a boundary-neighbor cycle eligible

Start from a boundary-neighbor cycle and continuously move one square,
keeping it contained, sorted and outside the open true core, both
of its adjacent squares disjoint from it, and its real frame within
the original global frame interval. Keep the other six physical
squares and their labels fixed. Let its own-frame
coordinates and directed frame vary continuously without changing
the prescribed quarter offsets. Its center never reaches the origin
by (2).

Choose continuous lifts of the center arguments from the initial
cyclic order. The seven lifted consecutive gaps have constant sum
\(2\pi\). No changing gap can reach zero: at such a first event
the two adjacent centers would have smaller angular distance zero,
contradicting the strict two-square band bound. Thus all gaps remain
positive, including a limiting endpoint of the transport. Equation
(3) holds throughout and gives the same one-winding cyclic order.
In particular a nonconsecutive collision of center rays cannot
destroy this order while every consecutive gap is positive and
their sum is \(2\pi\).

At every attained endpoint lying on the canonical radial boundary,
all the remaining boundary-neighbor hypotheses are present.
Consequently Sections 2--4 apply there. Intermediate states during a
radial push need not themselves be boundary states: the two-square
band and the continuity argument above require only containment,
sorting, core avoidance and actual neighboring separation. In
particular, for a flat-core E-only motion retaining an original high
GA witness, the path cannot reach \(y_E=0\).

The assertion also applies when a limiting weak contact first makes
a secondary DE or EH projection feasible. The original primary and
new secondary are both actual witnesses at that same state; a
subsequent argument may select either. No assertion about a virtual
angle substitution inside a stress is made here: Section 5 requires
an actual continuous path of contained, consecutive-disjoint squares.

## 6. Directly constructed endpoints

A scalar concavity argument may select a feasible endpoint without
providing a feasible path to it. For such a construction, verify the
new state's actual containment, core avoidance, canonical radial
boundary, neighboring SAT inequalities, frame interval, and the two
positive physical gaps directly. The other five gaps are unchanged,
and the two new gaps must have their old total. These facts supply
one-winding cyclic order and every hypothesis of Section 1 at the
endpoint. Sections 2--4 and the nearest-axis conclusion of Section 3.1
then apply to that endpoint itself. No connectedness of the set of
feasible comparison states is asserted or needed.

This proof uses the established whole-domain two-square band and
common-marker inequalities, a finite dependency check, continuity,
and the exact reflection identities (6)--(8). It introduces no state
mesh, scalar positivity table, Lean compilation, or CI premise.
