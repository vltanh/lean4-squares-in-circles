# Assemble the unrestricted theorem at the exact sharp ceiling

## 1. The sharp ceiling suffices for the entire global argument

Let \((q_*,u_*,t_*)\) be the stationary triple constructed in
[the stationary existence theorem](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md).
The internal radius and capture constants are recorded in
[the auxiliary-bound interface](HAND_AUXILIARY_RADIUS_BOUNDS.md).
In particular, q* lies strictly inside the domains of every
same-radius entry theorem and below the fixed geometric ceiling.

The following formulation avoids a lower working cutoff.

**Sharp-ceiling rigidity.** Suppose eight closed unit squares with
pairwise disjoint open interiors are contained in a disk of squared
radius at most q*. Their five rigid exterior anchors, after a common
isometry and relabeling, are the stationary anchors. Their physical
frames, seven retained contact directions, and remaining freedoms
are exactly those of the complete equality family.

Consequently every containing disk of every eight-square packing
has squared radius at least q*. The stationary construction attains
this value, with the full five-parameter equality domain.

The proof constructs its necessary boundary cycle freshly at the
ceiling q*. It does not first construct an outer state at a smaller
ceiling and then declare that state outer at q*. The original
packing centers are used only after their stationary physical
frames and initially retained signed normals have been recovered.

## 2. Independent inputs and absence of circularity

The inputs are the following completed conditional statements.

| Input | Result used here |
|---|---|
| [Stationary existence and uniqueness](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md) | The actual stationary triple and its certified branch exist independently of unrestricted packing capture. |
| [Stationary force weights and square completion](HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md), Section 3 and the zero-error identity | Positive normalized anchor masses, positive contact weights, and exact stationary force balance. |
| [Exterior-frame concentration](../HAND_EXTERIOR_FRAME_CONCENTRATION.md), [quarter-word selection](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md), and [global owner rigidity](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md) | Classification of actual boundary-neighbor cycles at the fixed geometric ceiling, with every feasible weak witness covered. |
| [Complete same-radius primary entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md) and the [conditional hard-owner theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md) | Every necessary cycle at q* reaches the hard class or an actual contradiction; the hard class has exact stationary equality data. |
| [Original-owner and physical-axis pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md), Sections 2--5 | At q*, hard witnesses already hold on the untouched boundary source, and its initially selected physical signed normals are stationary. |

The conditional hard-owner equality theorem is a theorem about a
necessary seven-cycle at a specified ceiling. Its proof uses the
stationary minimum and actual local transports. It does not assume
the unrestricted eight-square lower bound.

Likewise, Sections 2--5 of the pullback note concern the source of
those conditional transports and exact stationary projections.
They do not assume that the original packing's least containing
radius equals q*. The original-center dual below proves that
conclusion. The complete original equality domain is invoked only
after this step.

## 3. Construct the actual boundary cycle at q*

Take an arbitrary containing disk with center O and radius R.
Translate O to the origin and put
\[
                         q_{\mathrm{orig}}=R^2.
\tag{1}
\]
If \(q_{\mathrm{orig}}>q_*\), the required lower bound already
holds. Otherwise regard the unchanged packing as contained in
the concentric disk of squared radius q*.

Let \(\rho_{\mathrm{core}}\), \(\vartheta_{\mathrm{cap}}\), and
\(q_{\mathrm{cap}}\) denote the core radius, real-frame bound,
and fixed geometric ceiling in the auxiliary-bound interface.
The central-core theorem applies because the original packing
is contained at q* and \(q_*<q_{\mathrm{cap}}\). It supplies the
unique central square whose open interior contains the closed
radius-\(\rho_{\mathrm{core}}\) disk. The other seven squares
avoid that disk.

Order their centers cyclically and choose one actual physical
signed SAT witness on each neighboring pair. Keep this choice,
including any weak owner tie, throughout the following first
construction.

### 3.1. Recession boundary reduction at the sharp ceiling

Apply
[the cyclic radial-boundary reduction](../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
with the containing ceiling q*. Its two retained incident
inequalities define fixed halfplanes for each moved center.
A common recession direction keeps those inequalities valid
until the state first reaches its true-core boundary or the
containing-square boundary at q*.

This operation preserves all seven chosen signed inequalities,
every physical square frame, true-core avoidance, and cyclic
order. The fixed-witness strengthening is proved in Section 1 of
[the original-square pullback](../EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md).
No individual center ray is required to remain fixed. Omitted
nonneighbor constraints need not survive in this necessary system.

Call the resulting actual seven-cycle \(C_*\). Every one of its
outer states is outer at q*, by the construction itself. Nothing
in this step requires a lower bound for \(q_{\mathrm{orig}}\).

### 3.2. Classify at the fixed ceiling and recover the known cycle

Expand only the outer centers of \(C_*\), along their fixed rays,
from q* to \(q_{\mathrm{cap}}\), and leave core centers fixed.
The unconditional monotonicity theorem in Section 2 of
[the fixed-ceiling transfer](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md)
applies on the certified interval containing these two values.

This second operation preserves every initially feasible signed
axis, physical frames, center rays, signed tangent ratios, radial
kinds and cyclic gaps. It is distinct from the preceding recession
translation. The expanded cycle therefore satisfies the domain
of the fixed-ceiling geometric classification, including its
requirements at a nearest-axis tie or a diagonal.

Apply the exterior-frame theorem and the quarter-word theorem,
using their boundary-neighbor scope established in
[the boundary-domain bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
They give the canonical word 0101011 and roles
\[
                            (H,G,A,B,T,D,E).
\tag{2}
\]
Choose the permitted physical reflection so E's signed tangent
is nonpositive. The real-frame spread and each captured error
variation are below \(\vartheta_{\mathrm{cap}}\). The global
owner theorems give
\[
 HG,AB,TD\in\{0,2\},\qquad
 GA,EH\in\{0,1\},\qquad BT,DE\in\{2,3\},
\tag{3}
\]
with H,A positive outer and B,D negative outer. The original
zero-owner implications include
\[
                     HG2\Longrightarrow y_G<0,\qquad
                     TD0\Longrightarrow y_T>0.
\tag{4}
\]

Return to the already constructed states of \(C_*\), carrying
these labels and chart choices. This is recovery of known
feasible states; no assertion about monotonicity during inward
motion is needed. Its original selected axes survived the
outward expansion, so the all-witness restrictions (3) apply
to them. All the data used in (2)--(4), the quarter word, and
the frame variations are unchanged. The actual outer anchor
coordinates are once again those of \(C_*\) at q*.

Thus the complete same-radius entry theorem applies to \(C_*\)
at q*. Every outer state used in that entry proof has the actual
circle specified by its individual construction.

## 4. Conditional equality fixes the boundary source and initial axes

At q* the complete entry theorem excludes every positive
terminal. Each genuine aligned-negative terminal produces a
strict H- or D-anchor circle loss; the conditional hard-owner
equality theorem excludes those losses. Only the independent
G/T preprocessing route to the hard/hard class can survive.

Sections 2--4 of the
[original equality pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md)
then examine the source of that route. If original GA0 or BT2
was missing, a hard endpoint retains either a positive invariant
anchor-frame total or a strict actual transverse HG/TD slack.
Both contradict the sharp hard-class equality data. The
nonhard endpoints were already excluded. This covers both
transverse owners, all signs and totals, and all weak ties.

Hence actual GA0 and BT2 hold on \(C_*\) before either
intermediate was changed. Reapply the hard theorem directly
to \(C_*\). It gives its own stationary five anchors and
\[
 \theta_G=\theta_H,\qquad
 \theta_A=\theta_B=\theta_T=\theta_D=\theta_E,\qquad
 \theta_H-\theta_A=t_*.
\tag{5}
\]

These physical frames are also those of the original packing.
Their initially retained signed normals still need to be
identified: a newly available hard witness alone would not
provide that identification. Section 5 of the pullback note
proves that GA1 and EH0 are strictly infeasible on the sharp
boundary source. Its initial GA and EH witnesses must therefore
be GA0 and EH1. On the five aligned edges, both allowed owners
give the same signed normal. Thus all seven initially selected
physical axes have exactly their stationary directions.

This step uses only the conditional boundary-source equality.
It has made no assumption that \(q_{\mathrm{orig}}=q_*\).

## 5. The original-circle dual proves the radius inequality

Rotate the original packing so its five standard frames are
zero. Write
\[
             e=(\cos t_*,\sin t_*),\qquad
             f=(-\sin t_*,\cos t_*).
\tag{6}
\]
Let \(P_i\), for \(i\in\{A,B,D,E,H\}\), be the explicit
stationary anchors in equation (13) of
[the equality-family theorem](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).
The original centers relative to O are \(p_i\). Use the actual
corner offsets
\[
 \begin{gathered}
 o_A=(1/2,-1/2),\quad o_B=(1/2,1/2),\quad
 o_D=(-1/2,1/2),\quad o_E=(-1/2,-1/2),\\
 o_H=-e/2-f/2.
 \end{gathered}
\tag{7}
\]

Let \(g_j\ge0\) be the slacks of the seven physical signed
witnesses selected on the original packing. The stationary
force theorem supplies
\[
 \mu_i>0,\qquad \sum_i\mu_i=1,\qquad \lambda_j>0,
\tag{8}
\]
and zero forces at G,T. Define, on the original centers,
\[
 \mathcal D=
       \sum_{i\in\{A,B,D,E,H\}}\mu_i|p_i+o_i|^2
                       -\sum_{j=1}^7\lambda_jg_j.
\tag{9}
\]
Because the physical normals and frames have the stationary
values, force balance and completion of the five center squares
give the exact identity
\[
 \mathcal D=q_*+
       \sum_{i\in\{A,B,D,E,H\}}\mu_i|p_i-P_i|^2
                          \ \ge q_*.
\tag{10}
\]
This identity is algebraic for arbitrary original centers
with these fixed physical normals and frames. It requires
neither an original radial-boundary condition nor any original
center-proximity bound.

Each \(p_i+o_i\) is an actual vertex of an original square.
Consequently its squared distance from O is at most the
original ceiling \(q_{\mathrm{orig}}\), even if that ceiling
is much smaller than an auxiliary proof cutoff. Original
separation gives \(g_j\ge0\). Therefore
\[
 \begin{aligned}
 \mathcal D
 &\le \sum_i\mu_i|p_i+o_i|^2\\
 &\le q_{\mathrm{orig}}\sum_i\mu_i
   =q_{\mathrm{orig}}.
 \end{aligned}
\tag{11}
\]
Equations (10)--(11) prove
\[
                            q_{\mathrm{orig}}\ge q_*.
\tag{12}
\]

The central square has no disk mass in this identity. It was
needed for the geometric capture, and its original containment
and nonoverlap remain actual constraints. Likewise G,T have
zero disk masses and zero stationary forces. No comparison
circle loss at either free intermediate enters (10)--(12).

The original containing center O was arbitrary. Hence (12)
applies to every disk containing the packing, and in particular
to a least containing disk if one is chosen.

## 6. Equality, attainment and the scope of the simplification

If \(q_{\mathrm{orig}}\le q_*\), the argument has shown equality
throughout
\[
                         q_*\le\mathcal D
                              \le q_{\mathrm{orig}}\le q_*.
\]
Thus every anchor displacement in (10) vanishes. The exact
nonnegative decomposition
\[
 q_{\mathrm{orig}}-\mathcal D
 =\sum_i\mu_i\bigl(q_{\mathrm{orig}}-|p_i+o_i|^2\bigr)
                    +\sum_j\lambda_jg_j
\tag{13}
\]
also forces all seven original selected contacts to be tight.
The actual incident equalities give the two original sliders
\[
                   p_T=(U-3/2,z),\qquad
                   p_G=P_H+e+\eta f.
\tag{14}
\]
Their frames are zero and t*, respectively. All remaining
original packing inequalities still hold. The established
complete weak five-parameter domain is therefore necessary.

The direct construction in Sections 3--6 of
[the equality-family theorem](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md)
proves that domain sufficient and nonempty, including a
five-dimensional box of pairwise noncongruent configurations.
This construction is a check of actual containment and all
pairwise nonoverlap; it does not assume the unrestricted lower
bound. Equation (12), or the same stationary identity after a
common translation, shows that these configurations have least
containing squared radius q*. This proves attainment and the
complete equality statement.

Only the global radius interface has been simplified. The main
argument no longer needs a floor \(\max(q_{\mathrm{orig}},q_L)\),
a separate case below that floor, or a moving comparison ceiling.
The supporting existence, owner, transport and scalar proofs
retain their original exact rational bounds. Those constants
certify that the single actual working ceiling q* lies in their
proved domains.
