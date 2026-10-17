# The unrestricted eight-square radius: complete computer-assisted proof

**Proof status, 2026-10-17.** The exact lower-bound argument is complete,
with all continuous certificate branches and all global covering interfaces
checked. Together with the existing exact construction, it proves the sharp
radius. It still contains computer-assisted premises. The user's requested
hand-proof closure requires their analytic replacement; that work remains
active in the [gated roadmap](GATED_ROADMAP_2026_10_16.md). This distinction
applies to the whole document, including its theorem statement.

## 1. The theorem and exact target

Let \(R_8\) be the least radius of a disk containing eight unit squares
whose open interiors are pairwise disjoint. Their orientations are arbitrary.
Let \((q_*,y_*,t_*)\) be the unique admissible stationary solution selected
by [HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md), with the radical
definitions below. Then

\[
\boxed{R_8=\sqrt{q_*}.}
\]

For orientation, \(q_*\approx3.91553413751747532652\) and
\(R_8\approx1.97877086534\). The decimals do not define the target.
[ANALYTIC_EXACT_CONSTRUCTION.md](ANALYTIC_EXACT_CONSTRUCTION.md) supplies
an actual eight-square packing at this exact radius. The task here is the
unrestricted lower bound.

For \(c=\cos t\), \(s=\sin t\), define

\[
\begin{aligned}
x_1&=\sqrt{q-y^2},&x_2&=\sqrt{q-(y+2)^2},&x_3&=x_2-3,\\
y_3&=\sqrt{q-x_3^2},&y_4&=y_3-2,&x_4&=-\sqrt{q-y_4^2},\\
h_1&=cx_1+sy-2-c,&h_2&=-sx_4+cy_4-1-s,\\
F(q,y,t)&=h_1^2+h_2^2-q.
\end{aligned}
\]

The selected exact solution satisfies \(F=F_y=F_t=0\) with the stated
radical signs. The existing family proof proves its existence, uniqueness
in the admissible strip, and conditional optimality. The new
[hand sharp-ceiling bracket](HUMAN_SHARP_CEILING_BRACKET.md) supplies the
rational-ceiling comparison below by eight explicit square-root brackets
and strong convexity, without relying on a numerical root isolation.

## 2. The two global geometric reductions

Assume for contradiction that an actual eight-square packing has squared
radius \(q<q_*\), with the disk centered at the origin. Put

\[
\begin{aligned}
q_c&=3.91553413751747532652,\\
q_-&=q_c-2\cdot10^{-16},\qquad
Q_\sharp=q_c+10^{-16},\\
\widetilde q&=\max(q,q_-).
\end{aligned}
\]

These terminating decimals are exact rational numbers. The hand bracket gives

\[
q_-\le\widetilde q<q_*\le Q_\sharp,
\qquad Q_\sharp-q_-=3\cdot10^{-16}.
\tag{1}
\]

The same packing lies in the \(\widetilde q\) disk. The
[central-core hand theorem](HUMAN_CENTRAL_CORE_FROM_TRANSVERSE_SEGMENT.md),
valid at the ceiling \(9789/2500\), gives one square whose open interior contains the closed
disk of radius \(\rho=1/12\). The other seven squares avoid that disk.

Order those seven centers cyclically. Their radii lie between \(7/12\)
and \(71/50\), and nonoverlap implies that neighboring centers have
distance at least 1. The elementary cosine bound in
[CYCLIC_RADIAL_BOUNDARY_REDUCTION.md](CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
therefore gives center-angle gaps

\[
3/5<\delta_i<\pi,\qquad \sum_{i=0}^6\delta_i=2\pi.
\tag{2}
\]

Keep the seven actual square frames fixed and relax nonneighbor constraints.
The radial-boundary theorem moves centers to the outer-center boundary or
the core-avoidance boundary, retaining every adjacent true SAT disjunction
and (2). This is a theorem about actual squares and their actual side axes.
It does not replace squares by sampled orientations or by independent
incompatible pair states.

Write a center in its canonical square chart as \((a,-au)\), with
\(-1\le u\le1\). Thus the square frame is rotated by \(\arctan u\)
from the center ray; consecutive canonical frames differ by
\(\delta_i+\arctan u_{i+1}-\arctan u_i\). The two
boundary types are:

\[
\begin{array}{ll}
O:&(1+u^2)a^2+(1+|u|)a+1/2=\widetilde q,\\[2pt]
C:&a=7/12\quad\text{if }|u|\le6/7,\\
 & (1+u^2)a^2-(1+|u|)a+71/144=0
    \quad\text{otherwise, with the larger root.}
\end{array}
\tag{3}
\]

Every label thus has one continuous relative-frame parameter and one of
two boundary types. Only the seven adjacent pair conditions are needed
from this point onward.

## 3. Passing to the fixed rational ceiling is legitimate

The [outer-radius monotonicity theorem](OUTER_RADIUS_MONOTONICITY_AND_SHARP_PULLBACK.md)
allows every O radius to be expanded from \(\widetilde q\) to
\(Q_\sharp\), retaining each center ray, each actual frame, each C center,
each canonical u parameter, and every initially valid signed separating
axis. Each moved center travels at most \(10^{-16}\).

The reason is elementary. An outer radius satisfies
\(r^2+Br+1/2=q\), with \(1\le B\le\sqrt2\). For
\(5/2\le q\le4\),

\[
4/5<r<3/2,\qquad 1/4\le r_q\le1/3.
\]

For any active outer--outer signed projection \(ur_A+vr_B\ge1\), the
derivative with respect to q is strictly positive; the proof gives the
uniform bound \(>1/24\). For a core--outer active projection its outer
coefficient is \(>2/15\), so its derivative is \(>1/30\). The support
width is unchanged because the frames are fixed. Thus no valid selected
separator is lost during expansion.

This also transfers every exclusion proved at the coarser
\(Q=9789/2500\) to \(Q_\sharp\) without changing a boundary word or
its parameters.

## 4. Exhaustive reduction to three boundary words

The completed [four-type pair theorem](FOUR_TYPE_BOUNDARY_PAIR_CERTIFICATE.md),
followed by the hand odd-cycle and frame-lifting arguments, proves that all
seven exterior frames fit in one open 45-degree window. In particular all
former M5 and M6 branches are excluded. Its complete input consists of all
40 closed pair branches, not only a finite set of sampled orientations.

The [no-adjacent-core lemma](NO_ADJACENT_CORE_BOUNDARY_STATES.md) excludes
every word with neighboring C states. The remaining binary necklaces are
exactly

\[
O^7,\quad CO^6,\quad COCOOOO,\quad COOCOOO,\quad COCOCOO.
\]

The complete [three-core certificate](THREE_CORE_BOUNDARY_EXCLUSION.md)
excludes \(COCOCOO\): its telescoped gap sum is at least
\(3929/625>2\pi\). The complete
[short-two-core certificate](SHORT_TWO_CORE_BOUNDARY_EXCLUSION.md)
excludes \(COCOOOO\): its telescoped gap sum is at least
\(125709/20000>2\pi\). Thus every hypothetical packing reaches one of
the three full continuous domains

\[
\boxed{OOOOOOO,\qquad COOOOOO,\qquad COOCOOO.}
\tag{4}
\]

## 5. The entire surviving domain has a completed finite capture

The previously open global implication is now supplied by the following
complete covers. Their branch meanings and reflection conventions are
recorded in the respective proof notes.

| Word | Closed ordinary exclusions | Retained terminal cases | Cover and interface |
|---|---:|---|---|
| OOOOOOO | 45 | Both sliders outer | [ALL_OUTER_CAPTURE_ROADMAP.md](ALL_OUTER_CAPTURE_ROADMAP.md) |
| COOOOOO | 46 | T core or G core | [ONE_CORE_CAPTURE_LEDGER.md](ONE_CORE_CAPTURE_LEDGER.md); [terminal interface](ONE_CORE_TERMINAL_INTERFACE.md) |
| COOCOOO | 32 | Both sliders core | [LONG_TWO_CORE_CAPTURE_LEDGER.md](LONG_TWO_CORE_CAPTURE_LEDGER.md); [terminal interface](LONG_TWO_CORE_TERMINAL_INTERFACE.md) |

Each exclusion is a directed seven-role pair-potential argument. Its
continuous pair inequalities telescope around the physical cycle, giving a
strict lower gap sum above a proved rational upper bound for \(2\pi\).
The symbolic cover audits verify the closed complements of every retained
interval, the exact inclusion in each certificate's declared domain, and
all sequential and symmetry hypotheses. All 123 required exclusions have
complete exact manifests and independent binding/coverage audits.

For all O, a maximum absolute parameter is made the nonpositive role-0
parameter by reflection and cyclic relabeling. All later maximum caps
come from that actual canonical choice. For one C, its unique core is
role 0 and reflection makes its parameter nonpositive; both remaining
core phases are retained. For the long two-C word, the explicit
reflection \(i\mapsto3-i\pmod7\), with parameter signs reversed,
preserves the word. Its use and its maximum-core selection are checked
only under invariant preceding hypotheses.

These are exhaustive continuous covers. The computer-assisted premises
are the full pair inequalities, not optimizer convergence or a conjectured
contact graph. Their exact data and all completed evidence are preserved in
the [capture package](certificates/sharp_capture/README.md).

## 6. Terminal budgets force the actual frames and signed owners

For each of the four retained cases there are exact role potentials
\(\psi_i\), constants \(\gamma_i\), and charges \(\beta_i\). Set

\[
h(d)=\frac{\cos d+\sin d-1}{2},\qquad
e_i=\delta_i-\beta_i h(d_i)+\psi_{i+1}(u_{i+1})-\psi_i(u_i)-\gamma_i,
\]

where \(d_i\in[0,\pi/4]\) is the distance between the two actual
square frames modulo a quarter turn. The charge is 1/50 on the five
candidate aligned edges and zero on the two mixed edges.

The exact selected-axis and complementary-axis certificates first prove
\(e_i\ge0\) for **every** actual SAT alternative. The complementary
axes satisfy the stronger lower bound \(e_i\ge\varepsilon\).
Only after this full union is established do we sum the inequalities.
It gives

\[
\sum_i e_i+\frac1{50}\sum_{\text{five aligned edges}}h(d_i)
=2\pi-\sum_i\gamma_i<\varepsilon,
\tag{5}
\]

with \(\varepsilon=7/10^7\) for the all-O and two-C cases, and
\(\varepsilon=9/10^7\) for either one-C case. Hence all complementary
owners are impossible. This inference is not circular: their independent
pair bounds are part of the initial full-SAT union.

Concavity gives \(h(d)\ge d/4\). Equation (5) first makes the aligned
sum \(S<1/1000\). The elementary sine and cosine Taylor bounds then give
\(h(d)>49d/100\), whence

\[
S<1/14000\quad\text{or}\quad S<9/98000;
\qquad\boxed{S<1/10000}
\tag{6}
\]

in every terminal case. Exact piecewise-linear/arctangent range bounds
fix the required quarter-turn representatives and the actual common tilt
\(1/10<t<4/25\). After the stated possible reflection, normalize A's
actual frame to zero and take G's actual frame to be t. The remaining
five frame deviations have magnitude at most S.

The surviving directed pair normals are exactly

| Pair | Allowed true axis |
|---|---|
| A to B | Positive vertical axis of A or B |
| T to B | Positive horizontal axis of T or B |
| D to T | Positive horizontal axis of D or T |
| E to D | Positive vertical axis of E or D |
| G to A | G's positive tilted e-axis |
| H to G | Positive tilted e-axis of H or G |
| H to E | H's positive tilted f-axis |

There are exactly 32 owner assignments. They are precisely the ones used
in the sharp dual below. No parallelism or exact contacts have yet been
assumed of the actual squares.

## 7. A sharp inequality with no center-proximity hypothesis

The [hand broad stationary graph](HUMAN_BROAD_TERMINAL_ARITHMETIC.md)
gives one analytic position \(y(t)\) with \(F_y(q_*,y(t),t)=0\) on the
entire captured tilt interval. It contains \((y_*,t_*)\), satisfies
\(-29/20<h_2<-7/5\), and has

\[
F(q_*,y(t),t)\ge\frac38(t-t_*)^2.
\tag{7}
\]

The existing adaptive construction supplies five comparison centers
\(p_A^0,p_B^0,p_D^0,p_E^0,p_H^0\), positive circle weights \(\mu_i\)
with sum 1, and positive contact weights \(\lambda_e\). They balance
all center forces exactly. Choose the two comparison sliders from the
actual transverse projections:

\[
z_T=(p_T)_y,\qquad
\eta=(p_G-p_H^0-e_t)\cdot f_t,
\]

and put \(p_T^0=(x_2-3/2,z_T)\),
\(p_G^0=p_H^0+e_t+\eta f_t\). The terminal state and sector bounds give

\[
z_T\in[29/50,7/5],\qquad \eta\in[-1/2,37/100].
\tag{8}
\]

The outer-coordinate polynomial in (3), the core coordinate 7/12, and
\(\eta=-a_G-h_2-1/2\) prove (8) throughout the original radius interval
in (1). No closeness of the five anchored centers is required.

For each actual selected signed separator let \(g_e\ge0\) be its true
gap. For the five actual corresponding square vertices define

\[
\mathcal D=\sum_i\mu_i|p_i+o_i(\theta_i)|^2-\sum_e\lambda_e g_e.
\]

Disk containment gives \(R^2\ge\mathcal D\). At the comparison pose,
\(\mathcal D^0=q_*+\mu_HF\). Exact force balance cancels every center
linear term. For every one of the 32 owner branches the angular term
is at least \((9/500)S\), uniformly over (8) and the whole tilt chart.

The [projected-slider remainder proof](CENTER_FREE_PROJECTED_SLIDER_REMAINDER.md)
is elementary and explicit. Put \(d_i=p_i-p_i^0\). The pure angular
loss is at most \(12S^2\). Young's inequality absorbs the five anchored
center/angle terms into half the positive center squares and at most
\(110S^2\). The free-slider displacements satisfy

\[
d_T=\tau e_0,\qquad d_G=\upsilon e_t.
\]

Thus their remaining terms are quadratic, by the exact identity

\[
(R(a)n-n)\cdot(\xi n)=\xi(\cos a-1).
\]

The actual and reference slider centers all have norm below 2, so the
displacement magnitudes are below 4 and their total loss is at most
\(8S^2\). Consequently

\[
\begin{aligned}
R^2&\ge q_*+\mu_HF
+\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2
+\left(\frac9{500}-130S\right)S\\
&\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2
+\frac12\sum_{i=A,B,D,E,H}\mu_i|d_i|^2
+\frac1{200}S\ge q_*.
\end{aligned}
\tag{9}
\]

The exact coefficient and stationary bounds invoked here now have an
explicit hand derivation: nine rational position brackets, four fixed
rectangles, and nine scalar mean-value estimates. The 32 owner assignments
reduce algebraically to those nine scalars. The independent review is
[HAND_TERMINAL_AND_CEILING_INDEPENDENT_AUDIT.md](HAND_TERMINAL_AND_CEILING_INDEPENDENT_AUDIT.md).
The analytic expansion does not require a small-center assumption.

## 8. Apply the inequality before expansion

The captures in sections 5--6 were made at \(Q_\sharp\), whereas (9)
must be applied at \(\widetilde q<q_*\). The monotonicity in section 3
closes this interface exactly.

All rays, parameters, frames, angular distances, and quarter-turn lifts
are unchanged by expansion. If a forbidden owner were a feasible axis
before expansion, it would remain a feasible forbidden axis afterward,
contrary to the completed owner theorem. Hence the allowed-owner
conclusion also holds before expansion. The projected-slider bounds in
(8) were proved directly for that lower-radius interval, including the
maximum \(10^{-16}\) radius transfer.

The boundary ring at \(\widetilde q\) therefore satisfies every
hypothesis of (9). It yields \(\widetilde q\ge q_*\), contradicting
(1). This proves the unrestricted lower bound. The existing exact
construction proves equality of the least radius with \(\sqrt{q_*}\).

## 9. What is closed, and what remains

The **unrestricted radius theorem is closed with exact computer
assistance**. No global capture or terminal-owner gate remains unproved
within this proof standard. All proofs concern full continuous domains.

The central core, sharp rational ceiling, and finite local arithmetic now
have complete hand proofs. The **unrestricted hand-proof requirement remains
open** until analytic replacements are supplied for the global pair/capture
premises. The new [seven-quarter-word reduction](SEVEN_QUARTER_WORDS.md)
is exhaustive conditional on frame concentration, and its smaller global
list is an active route. Numerical marker fits do not prove its remaining
word exclusions or the candidate capture.

Equation (9) also identifies equality inside a captured exterior ring:
the common tilt, both orientation clusters, and five anchored centers
are exact, while T and G retain slider freedoms. A complete description
of all original eight-square equality poses additionally requires
tracing the radial deformation and the eighth central square. That
separate classification is not asserted here.
