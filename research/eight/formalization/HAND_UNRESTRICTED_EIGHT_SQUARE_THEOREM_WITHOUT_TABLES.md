# The unrestricted eight-square theorem without numerical lookup tables

## 1. The theorem and its exact constant

Let eight closed unit squares, with arbitrary centers and orientations
and pairwise disjoint open interiors, lie in a closed disk of radius R.
Then
\[
                              R^2\ge q_*.
\tag{1}
\]
The bound is attained. Up to an isometry of the plane and relabeling,
every equality packing is exactly a member of the five-parameter family
in Section 5, and every member of that domain is an equality packing.
Reflection is included in the allowed isometries.

Here q* is an exact stationary constant, not a decimal input. Set
\[
 q_L=\frac{19577}{5000},\qquad
 Q_1=\frac{1957767069}{500000000},\qquad
 Q=\frac{9789}{2500}.
\tag{2}
\]
For positive radicals define
\[
\begin{aligned}
 r&=\sqrt{q-u^2},& U&=\sqrt{q-(2-u)^2},&V&=3-U,\\
 Y&=\sqrt{q-V^2},&v&=2-Y,&w&=\sqrt{q-v^2},\\
 k_1&=2-\cos t\,(r-1)+\sin t\,u,&&&
 k_2&=1+\cos t\,v-\sin t\,(w-1),\\
 F(q,u,t)&=k_1^2+k_2^2-q.
\end{aligned}
\tag{3}
\]
The unique admissible stationary zero satisfies
\[
 F(q_*,u_*,t_*)=F_u(q_*,u_*,t_*)=F_t(q_*,u_*,t_*)=0,
\tag{4}
\]
\[
 q_L<q_*<Q_1<Q,\qquad .87<u_*<1.1,
                   \qquad0<t_*<\arctan(1/5).
\tag{5}
\]
[Stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md)
constructs this zero by compact minimization and the intermediate
value theorem. Its actual-envelope uniqueness input identifies it
uniquely. The refined bounds and exact radicals used for the family
are proved in
[the table-free equality-family theorem](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).
No narrow numerical root box is a premise of the present theorem.

This document assembles the completed continuous hand proofs. It makes
no Lean elaboration, kernel-verification, source-table-removal, or build
claim. The historical uncompiled Lean draft is a separate artifact.

## 2. From an arbitrary packing to the original-radius boundary domain

Translate the containing disk's center to the origin. If its squared
radius q is greater than q*, (1) is immediate. Thus suppose q<=q* and
choose the working ceiling
\[
                            \bar q=\max(q,q_L).
\tag{6}
\]
The original squares are unchanged and qL<=qbar<=q*<Q.

### 2.1. Central core and the two distinct boundary operations

The central-core input of
[the exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
gives a unique central square whose open interior contains the closed
radius-1/12 disk. Its table-free dependencies are the
[central-band identities](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md),
the analytic central-existence argument in
[the global geometry proof](../HUMAN_GLOBAL_GEOMETRY_CLOSURE.md), and
[the transverse-segment forbidden-width proof](../HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md).
The other seven squares avoid the open central disk. Put their centers
in cyclic polar order and choose one actual signed separating axis
on each neighboring pair. Weak contacts and simultaneous-axis ties
are permitted; make one choice and retain it.

Apply
[the cyclic boundary reduction](../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
at qbar, as justified for a variable actual ceiling in Section 3 of
[the fixed-ceiling transfer theorem](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md).
At each step the two previously selected incident inequalities define
fixed halfplanes. A common recession direction moves that center to
its first true-core or containing-circle boundary. This preserves
the physical frames, all seven selected signed witnesses, core
avoidance, and cyclic order. It need not preserve individual center
rays or nonneighbor separation. After seven steps every exterior
square is core or outer at the actual ceiling qbar.

For the fixed-Q geometric classifications, expand just the outer
centers of this boundary cycle along their fixed rays from qbar to Q;
leave core centers fixed. Section 2 of the fixed-ceiling transfer
theorem proves this operation unconditionally for boundary radii in
[5/2,4]. It preserves every initially feasible signed axis, not merely
the selected seven, and preserves frames, rays, signed tangent ratios,
radial kinds, and cyclic gaps. It is a different operation from the
preceding recession translation. In particular, it is the valid bridge
when an auxiliary Q argument must retain a diagonal or a nearest-axis
representative.

### 2.2. Apply the global classification, then return to the known cycle

First apply the whole-pair inequalities, odd-walk budget, and orientation
lift argument of the
[exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
to the expanded Q-boundary cycle. These arguments use only core avoidance,
containment and consecutive nonoverlap, as verified in Section 2 of
[the boundary-neighbor bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
They give real frame spread less than 7/10 before any word or owner
selection. No completion of the relaxed cycle to an eight-square packing
is assumed.

Next the
[quarter-word theorem](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md)
leaves precisely the word 0101011. Choose cyclic roles
(H,G,A,B,T,D,E), and use its remaining physical reflection to normalize
E's signed tangent nonpositive.

The cycle now satisfies the full stated domain of the boundary-neighbor
bridge. Its variation argument gives
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<7/10.
\tag{7}
\]
The completed
[global owner theorem](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md), together
with the zero-, BT-, DE-, and EH-owner conclusions it records, gives
\[
 HG,AB,TD\in\{0,2\},\qquad
 GA,EH\in\{0,1\},\qquad BT,DE\in\{2,3\}.
\tag{8}
\]
These restrictions quantify every feasible actual witness, including
ties. H,A are positive outer anchors and B,D negative outer anchors.
The zero-owner implications include
\[
                        HG2\Rightarrow y_G<0,
               \qquad  TD0\Rightarrow y_T>0.
\tag{9}
\]
There is no G/T sign or frame-order assumption beyond these implications.

Now return to the qbar-boundary cycle constructed in Section 2.1.
This is recovery of known feasible states, not an inward-monotonicity
claim. All its initially selected witnesses survived the expansion,
so each belongs to (8). All its frames, directed nearest-axis choices,
signed ratios, quarter word, and errors are the same as those at Q.
Consequently (7), (9), the signs, and the four outer radial kinds
hold at qbar. The actual outer coordinates are those on qbar, not
those on Q. All hypotheses of the complete same-radius entry theorem
are now present.

## 3. Exhaustive same-radius primary-owner entry and the lower bound

Apply
[complete global primary-owner entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md)
to the qbar-boundary cycle. Its proof has the following finite order.

1. G-only and T-only pair reductions retain all five anchors and the
   actual radius. Each side ends with a hard owner, a positive primary,
   or a genuine negative primary with its adjacent transverse edge
   aligned. Both signs, both radial kinds, all signed pair totals,
   and weak zero-angle ties are covered.
2. Every positive-GA terminal is excluded with either E sign, every
   DE/EH owner and signed error, and all four terminal T regimes.
   Core E, both secondaries, either sole primary, and paired primaries
   have complete proofs. The arbitrary-angle EH0 contact extensions
   cover the positive-E sole-DE endpoint without changing its original
   circle. Physical reflection then excludes every positive-BT terminal.
3. The four remaining hard/negative terminal cells are exhaustive.
   Hard/hard enters the sharp theorem directly. A genuine negative
   GA primary produces a strict H-anchor circle loss, and a genuine
   negative BT primary a strict D-anchor loss. With both genuine
   negatives, the first loss is retained through the second conversion.
   The equality statement of the hard theorem excludes every such loss
   at q<=q*.

The only surviving route reaches the hard GA0/BT2 class at the same
qbar by changing G and T alone. Its five original boundary anchors
and their frames are identical. E still has the required radial
alternative
\[
 a_E\le7/12\quad\hbox{or}\quad
 a_E\ge\sqrt{\bar q/2}-1/2\ge\max\{b_H,b_D\}.
\tag{10}
\]
The
[arbitrary-sign, arbitrary-frame hard-owner theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md)
therefore gives qbar>=q*. Thus qbar=q*.

If the original q were below qL, this would contradict qL<q*.
Otherwise qbar=q, and hence q=q*. This proves (1) for every original
packing. At no point is an outer state at one ceiling merely relabeled
as outer at another. The auxiliary Q states are used only to transfer
classification facts; every sharp transport uses qbar itself.

## 4. Equality for the original squares

Assume the original packing has q=q*. Use the construction above with
qbar=q*, retaining the initially selected physical signed witnesses
through its recession translations and fixed-ray expansion.

The
[complete original-equality pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md)
handles the two necessary interfaces separately.

First it examines the source of every G/T preprocessing alternative.
If a hard owner was originally unavailable, the construction retains
either a positive invariant pair total incompatible with the stationary
frames, a strict actual HG/TD slack, or a genuine positive/negative
terminal already excluded in Section 3. The
[retained-contact rigidity lemma](HAND_G5_HARD_EQUALITY_RETAINED_CONTACT_RIGIDITY.md)
makes the strict-slack test exact. It follows that the untouched
q*-boundary source itself has actual GA0 and BT2. Reapply the hard
theorem to that source; do not identify transported G/T coordinates
with their ancestors.

Second, at this stationary boundary source the pullback proves that
the originally selected GA1 and EH0 quarter witnesses are infeasible.
All other allowed selected alternatives coincide with the stationary
physical normals at their zero frame errors. Hence the selected axes
retained from the original packing have exactly the directions needed
by the stationary positive dual.

Reapply that dual directly to the untouched original centers, as in
[the original-center equality identity](../EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md).
Containment bounds each selected anchor vertex by q*. The seven
original separating inequalities have nonnegative gaps. The dual
identity has strictly positive anchor masses and contact weights,
proved without tables in Section 3 of
[the stationary force-weight and square-completion proof](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md):
\[
 \sum_i\mu_i|p_i+o_i|^2-\sum_j\lambda_j g_j
       =q_*+\sum_i\mu_i|p_i-P_i|^2,
 \qquad\mu_i>0,\quad\sum_i\mu_i=1,\quad\lambda_j>0.
\tag{11}
\]
Here i runs over H,A,B,D,E and j over the seven cycle contacts.
Its left side is at most q*, so all five original anchor centers
are P_i and every original contact gap is zero. The forces on the
two intermediate squares vanish, leaving their actual translation
sliders free. The original central square remains subject to its
actual containment and seven original nonoverlap constraints.

Thus equality is recovered for the original eight squares. Strict
circle loss at a free intermediate was never treated as an anchor
loss, and no preservation of omitted nonneighbor constraints was
assumed during the necessary-system transports.

## 5. Complete explicit equality family and attainment

Evaluate (3) at the unique triple (q*,u*,t*), and put
\[
 c=\cos t_*,\qquad s=\sin t_*,\qquad
                    e=(c,s),\quad f=(-s,c).
\tag{12}
\]
After a common isometry the five fixed exterior centers are
\[
\begin{aligned}
 P_A&=(r-1/2,\;1/2-u_*),&
 P_B&=(U-1/2,\;3/2-u_*),\\
 P_D&=(U-5/2,\;Y-1/2),&
 P_E&=(1/2-w,\;1/2-v),\\
 P_H&=(1/2-k_1)e+(1/2-k_2)f.
\end{aligned}
\tag{13}
\]
The remaining exterior centers are
\[
                 P_T=(U-3/2,z),\qquad
                 P_G=P_H+e+\eta f.
\tag{14}
\]
The frames of A,B,T,D,E are zero, and those of H,G are t*.
Set
\[
 z_+=\sqrt{q_*-(U-1)^2}-1/2,\qquad
 \eta_-=k_2-\sqrt{q_*-(2-k_1)^2},\qquad
 \eta_+=k_2-13/12.
\tag{15}
\]

Let the central center be (x,y) and its frame be
theta=2 arctan kappa, with
\[
 1-\sqrt2\le\kappa<\sqrt2-1,\qquad
 C=\frac{1-\kappa^2}{1+\kappa^2},\qquad
 \Sigma=\frac{2\kappa}{1+\kappa^2}.
\tag{16}
\]
For d=(d_x,d_y), define the explicit support maxima
\[
\begin{aligned}
 M_0(d)&=\max\{|d_x|,|d_y|,|Cd_x+\Sigma d_y|,
                                    |-\Sigma d_x+Cd_y|\},\\
 M_t(d)&=\max\{|cd_x+sd_y|,|-sd_x+cd_y|,
                       |Cd_x+\Sigma d_y|,|-\Sigma d_x+Cd_y|\},\\
 W_0&=(1+C+|\Sigma|)/2,\\
 W_t&=(1+cC+s\Sigma+|c\Sigma-sC|)/2.
\end{aligned}
\tag{17}
\]
The complete parameter domain is
\[
\boxed{\begin{gathered}
 1-\sqrt2\le\kappa<\sqrt2-1,\qquad
 7/12\le z\le z_+,\qquad\eta_-\le\eta\le\eta_+,\\
 |Cx+\Sigma y|<5/12,\qquad|-\Sigma x+Cy|<5/12,\\
 M_0(P_i-(x,y))\ge W_0\quad(i=A,B,D,E,T),\\
 M_t(P_i-(x,y))\ge W_t\quad(i=H,G).
\end{gathered}}
\tag{18}
\]
Every quantity is an explicit radical, rational expression, absolute
value, or maximum. In particular the domain contains no unchosen
separating-axis witness.

Sections 3--4 of the
[table-free equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
prove all 21 exterior pair separations and exterior containment over
the full slider ranges in (18). The last two lines of (18) are exactly
the seven central/exterior separating-axis conditions. The strict core
conditions also imply central containment, since its farthest squared
vertex norm is less than 121/72<q*. Thus (18) is sufficient. Section 4
of the present theorem and the same pair geometry prove necessity.

The domain is nonempty and has five independent freedoms. Section 5
of the equality-family proof gives the entire closed box
\[
\begin{gathered}
 .139\le x\le.141,\qquad -.001\le y\le.001,
                 \qquad .099\le\kappa\le.101,\\
 1.349\le z\le1.351,\qquad -.321\le\eta\le-.319,
\end{gathered}
\tag{19}
\]
with direct geometric reserves on its whole domain. This proves
attainment as well as the full family, rather than an isolated
stationary picture.

## 6. Dependency boundary and proof status

The dependency order is central core and actual boundary reduction;
continuous frame and word classification; every-witness owner
rigidity; same-radius exhaustive primary entry; the hard sharp
theorem; original-center equality; and the explicit family converse.
Each global implication is supplied above. No coarse mismatch
capture, S<=3/200 assumption, or unproved primary-conversion premise
remains in this route.

The scalar proofs used in these dependencies are symbolic inequalities
on whole intervals or rectangles, with explicit rational Taylor and
polynomial bounds. Exact arithmetic audits check those displayed
constructions. Sampled minima, angle/state meshes, optimizer output,
large retained numerical lookup tables, and historical generated
certificate imports are not acceptance premises of this hand proof.
The finite owner matrix and intrinsic contact cases enumerate
geometric alternatives; they are not a numerical cover of the state
space.

The unrestricted lower bound, attainment, necessity of (18), and its
converse are therefore complete on the stated hand-proof dependency
chain. The current reading map is
[the table-free roadmap](TABLE_FREE_GEOMETRIC_HAND_ROADMAP.md); the
[handoff](HANDOFF_2026_10_20.md) records the delivered scope and the
unchanged deferred Lean-verification boundary.
