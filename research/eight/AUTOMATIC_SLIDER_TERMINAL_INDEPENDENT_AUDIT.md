# Independent audit: the terminal with automatic slider bounds

**Result: PASS.** I independently reviewed the continuous proof in
**HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md**, its exact arithmetic, and the
specific interfaces to the two earlier terminal notes. This is a review of
the stated conditional terminal; it does not count the remaining global
owner, tilt, or mismatch budget as proved.

The companion **verify_automatic_slider_terminal_independently.py**
reconstructs all nine enlarged owner reserves from the original midpoint
and derivative table, reconstructs both remainder constants from their
individual force/support/slider terms, and checks the two mismatch-budget
steps. Its 21 independent strict comparisons pass. It also executes the
author's 20-comparison checker and verifies byte-identical arithmetic
output. The JSON record binds the exact manuscript, both earlier source
notes, the capture-interface note, the author checker, and its output by
SHA-256.

## Geometric and frame-coordinate checks

For a canonical center with \(0\le b\le a\), avoidance of the open
radius-\(1/12\) disk gives
\[
 \frac1{12}\le
 \sqrt{(a-\tfrac12)_+^2+(b-\tfrac12)_+^2}
 \le\sqrt2(a-\tfrac12)_+.
\]
The resulting lower primary bound \(a>.55875\) is valid for every
original exterior square, including side/corner transitions and boundary
contact. It does not require radial deformation. The farthest-corner
formula independently gives \(a<1.415\). The contained radius-\(1/2\)
center disk gives \(|p|<3/2\).

I checked the quarter-offset signs against
**CANDIDATE_WORD_HAND_CAPTURE_INTERFACES.md**. T's offset \(+1\)
gives its center as the actual-frame rotation of \((u_Ta_T,a_T)\);
therefore \(|T_y-a_T|\le(3/2)S\). G's offset \(-1\) gives
\(p_G=-u_Ga_G e_t-a_G f_t\), so its exact comparison projection is
\(\eta=-a_G-h_2-1/2\). These formulas hold for both tangent signs,
both radial boundary kinds, and all undeformed intermediate centers.
They prove the closed enlarged rectangle
\[
 Z\in[.557,1.417],\qquad \eta\in[-.515,.392]
\]
with strict geometric containment in its interior.

## Owner-reserve checks

I compared the proposed four changes with the entire smooth coefficient
table in **HUMAN_BROAD_TERMINAL_ARITHMETIC.md**, Section 5.

The varying T coefficient is \(-\beta(Z+J)\). Its two cusp reserves
therefore decrease by at most \(.017w\) and \(.023w\) at the new upper
and lower endpoints. The varying G coefficient is
\(-\omega/2+N-\omega\eta\). Its two cusp reserves decrease by
\(.022w\) at the new upper endpoint and \(.015w\) at the new lower
endpoint. All five other scalar reserves and all other owner
coefficients are unchanged. The original nine-scalar reduction still
covers all 32 owner assignments.

Reconstruction directly from the old midpoint/derivative table yields
the displayed new minimum
\[
 \rho=.0113586=\frac{56793}{5000000}.
\]
The comparison slider centers need not form a packing or be contained in
the disk. Their forces vanish at zero error, and the earlier exact
force cancellation uses their transverse coordinates only in the first
derivative. Thus enlarging this rectangle introduces no additional
geometric premise.

## Exact remainder and equality checks

I rechecked the two actual-slider remainders from the force identities
in **HAND_EXACT_CENTER_SQUARE_COMPLETION.md**. For T, the single
cosine range gives \(3\beta S_C^2/4\). The actual bound
\(|Z|\le3/2\) gives the cubic term \(\beta S_C^3/2\). The G term
remains \(3\omega S_H^2/4+\omega S_H^3/4\), or zero for its other
owner. Since \(S_C+S_H=S\), the new aggregate slider term is
\(3wS^2/4+wS^3/2\).

No force-norm or support cancellation changes. Consequently the
quadratic constant is unchanged, and the cubic constant increases by
exactly \(w/30\). Independent reconstruction gives
\[
 C_2=\frac{26453303561590200213}{2850910772000000000}<9.28,
 \qquad
 C_3=\frac{5176729803}{3455440000}<1.5.
\]
For \(S\le.001\), the total loss is less than \(9.3S^2\), and the
remaining linear coefficient is
\[
 \rho-.0093=\frac{10293}{5000000}>0.
\]
This proves the asserted terminal inequality. Its equality consequences
are unchanged: \(S=0\), \(t=t_*\), and the five completed center
squares vanish. Enlarging the comparison rectangle contributes no new
equality configurations.

Finally, I checked the conditional budget arithmetic with charge \(1/25\).
The full-SAT baseline and complementary-owner bounds imply
\(S<.0019<.004\); the Taylor slope \(h(d)\ge.49d\) then improves this
to \(S<19/19600<.001\). The note correctly retains those whole-domain
pair inequalities and the tilt bound as outstanding premises.

