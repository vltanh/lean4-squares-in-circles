# Candidate capture and the sharp terminal at total mismatch 1/1000

## 1. A single current interface

The current conditional capture threshold is

\[
                         S\le\frac1{1000}.
\tag{1}
\]

At this threshold the hand arguments below force every required separator
owner and the common-tilt interval. The automatic-slider terminal then
gives the sharp radius inequality and its equality conditions. The older
mixed-owner threshold \(1/10000\) and tilt threshold \(1/100000\) in
`HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md` are superseded for this
application; its geometric notation, cone inequalities and circle-dual
identity remain useful shared definitions.

This is a conditional theorem. The global cyclic mismatch argument must
establish (1) on a representative satisfying the hypotheses below. The
present theorem introduces no additional local capture requirement after
(1).

## 2. Precise hypotheses and conclusion

Let seven unit squares have cyclic roles

\[
             (H,G,A,B,T,D,E)=(0,1,2,3,4,5,6)
\]

and the candidate quarter increments \(k=(0,1,0,1,0,1,1)\).
Every square avoids the open disk of radius \(1/12\) centered at the
origin and is contained in a centered disk of squared radius \(q\), where

\[
q\le Q_1=\frac{1957767069}{500000000}=3.915534138
   <Q_0=\frac{9789}{2500}.
\tag{2}
\]

Each cyclic pair is nonoverlapping and admits one of the four retained
forward canonical SAT axes supplied by the preceding angular theorem:
source \(+f\), target \(+e\), target \(+f\), source \(-e\),
respectively numbered 1, 2, 3 and 4.

Choose the real frame lifts with range less than \(7/10\), normalize
\(\theta_A=0\), and set

\[
\begin{split}
t&=\theta_G-\theta_A,\qquad I=\{0,2,3,4,5\},\\
d_i&=\theta_{i+1}-\theta_i,\qquad
S=\sum_{i\in I}|d_i|.
\end{split}
\tag{3}
\]

Thus \(|t|<7/10\). Assume (1), and the following closed tangent
domains in the canonical own frames:

| Role | Signed tangent domain |
|---|---|
| H | \([1/2,1]\) |
| G | \([-4/5,-1/20]\) |
| A | \([0,1]\) |
| B | \([-1,0]\) |
| T | \([1/20,4/5]\) |
| D | \([-1,-1/2]\) |
| E | \([-1,0]\) |

These are explicit hypotheses here. In the intended global assembly the
G/T/H/D exclusion theorems, the E reflection normalization and the
zero-quarter sign implication discharge them. The center coordinates need
not satisfy a radial-boundary equality.

**Conditional capture theorem.** Every feasible retained canonical
separator lies in the following sets, in cyclic order:

\[
\boxed{
\{1,3\},\ \{1\},\ \{1,3\},\ \{3,4\},\
\{1,3\},\ \{3,4\},\ \{2\}.}
\tag{4}
\]

Moreover,

\[
                         \frac1{10}<t<\frac4{25}.
\tag{5}
\]

Consequently, with the positive terminal weights and actual center-force
notation of `HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md`,

\[
q\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+
\sum_{i=A,B,D,E,H}\mu_i
\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2+
\frac{10293}{5000000}S\ge q_*.
\tag{6}
\]

No new bound on centers, slider coordinates, or radial kinds is a
hypothesis of (6).

## 3. Proof of the separator and tilt conclusions

The zero-quarter argument in Section 3 of
`HAND_CANDIDATE_MISMATCH_BOOTSTRAP.md` applies whenever
\(S\le2/5\). It proves that H→G, A→B and T→D have only axes
1 and 3. The implication is strict: a forbidden axis is impossible even
if another axis on the same pair also separates.

The remaining three finite hand steps are as follows.

| Step | Radius and mismatch hypotheses | Consequence | Quartics |
|---|---|---|---:|
| Quarter owners | \(q\le Q_0,\ S\le3/200\) | B→T and D→E allow only axes 3 and 4 | 1,545 |
| Mixed owners | \(q\le Q_0,\ S\le1/1000\), quarter owners | G→A allows only axis 1; E→H only axis 2 | 729 |
| Common tilt | \(q\le Q_1,\ S\le1/1000\), all owners in (4) | \(1/10<t<4/25\) | 1,239 |

The first step is the large-mismatch quarter theorem in
`HAND_CANDIDATE_MIXED_OWNERS_AND_TILT.md`, with the frozen input
`candidate_quarter_owner_large_mismatch_dual_data.json`.
The second is
`HAND_CANDIDATE_MIXED_OWNERS_WITH_TOTAL_MISMATCH.md`, with input
`candidate_mixed_owner_shared_mismatch_hand_data.json`.
The third is
`HAND_CANDIDATE_TILT_FROM_SIGNED_ERROR_VERTICES.md`, with input
`candidate_tilt_signed_error_hand_data.json`.

All three hypotheses are supplied in the stated order by (1)–(3), since
\(Q_1<Q_0\) and \(1/1000<3/200<2/5\). No owner conclusion is
assumed in a table whose purpose is to prove that same conclusion.

For clarity about completeness, the quarter table covers all 48 nominal
patterns with at least one wrong quarter owner, including all four choices
on both mixed edges. After it has been applied, the mixed table covers all
15 remaining nominal patterns other than the desired mixed pair \((1,2)\).
Each pattern has a complete closed half-angle cover, so separator ties and
zero half-angle values are included.

The tilt theorem fixes one common nonnegative seven-edge weight vector on
each angle interval. Its necessary signed-error inequality is maximized
over \(\sum_{i\in I}|d_i|\le1/1000\). Its maximum occurs either at
zero or with the entire error on one of the five edges, in one of two
signs. Only that edge's derivative depends on its two possible owners.
Thus the necessary disjunction has exactly
\(1+5\cdot2\cdot2=21\) alternatives. The common weight vector is
chosen before that disjunction; it is not changed between its alternatives.

The 59 closed angle intervals and their 21 alternatives cover exactly

\[
\left[-\frac38,\frac{1001}{20000}\right]
\ \cup\
\left[\frac2{25},\frac38\right]
\quad\text{in }z=\tan(t/2).
\]

Every alternative is excluded by its positive quartic. The elementary
arctangent comparisons in the tilt theorem turn the remaining open
half-angle interval into (5).

The three tables contain 3,513 quartics and 17,565 positive rational
Bernstein coefficient bounds. Their smallest printed bounds are,
respectively,

\[
\frac{2539981}{10^{12}},\qquad
\frac{231527}{10^{12}},\qquad
\frac{40703}{500000000000}.
\]

Each row proves a whole closed interval inequality for all center
coordinates using the circle completion; no sampled-center premise is
used. The exact standalone companions reconstruct every polynomial and
closed union. The associated independent audits bind the mathematical
derivation and the fixed arithmetic separately.

## 4. The terminal and equality interfaces

After the common normalization at A, the canonical quarter offsets are
\((-1,-1,0,0,1,1,2)\), as in the automatic-slider terminal. They give
the same seven quarter increments and the same five differences in (3).
The owner sets (4) are exactly that theorem's 32 allowed assignments.
The strict interval (5) is contained in its closed interval
\([1/10,4/25]\). The same total mismatch bound (1), the core avoidance,
and \(q\le Q_1<Q_0\) supply its remaining hypotheses.

Its transverse projections therefore automatically satisfy

\[
\frac{557}{1000}\le Z\le\frac{1417}{1000},\qquad
-\frac{103}{200}\le\eta\le\frac{49}{125}.
\]

These are conclusions of containment and core avoidance; they are not
additional global capture gates. Its completed-square calculation gives
(6). In particular the angular coefficient is positive because

\[
\frac{56793}{5000000}-\frac{93}{10}\frac1{1000}
=\frac{10293}{5000000}>0.
\]

Equality in (6) forces \(S=0\), \(t=t_*\), and the five anchored
centers A, B, D, E and H. It leaves exactly the freedom subsequently
classified in `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md`; the present
capture theorem adds no equality branch. For a radially deformed
representative, the original-center equality argument remains the
separate lemma `EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md`.

The proof here applies directly to original exterior centers whenever
they already satisfy (1)–(3). If a global argument obtains the tangent
cuts only after radial reduction, that reduction and the radius-transfer
step must remain explicit in the overall assembly. No preservation of a
signed tangent by radial deformation is asserted here.

## 5. Audit boundary

The manifest `CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH_HAND_MANIFEST.json`
records the exact files and independent-review status of this conditional
package. The active global obligation outside this package is to derive
\(S\le1/1000\) under its declared coarse hypotheses. Completion of
this conditional package alone does not assert that obligation proved.
