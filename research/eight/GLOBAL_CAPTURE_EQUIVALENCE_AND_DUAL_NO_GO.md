# Why strict global capture is equivalent to n=8 optimality; exact failure of a globalized candidate dual

**Research audit 2026-10-13.** This note keeps the proof objective
focused and prevents a logical restatement from masquerading as
a global geometric reduction. The sharp conjecture
\(R_8\ge\widehat R\) remains **OPEN**.

## 1. A capture statement without constructive content is exactly the desired theorem

Let \(\mathcal F\) be the space of **genuine eight-unit-square
packings** modulo simultaneous rigid symmetries and relabeling.
Let \(q(P)\) be the squared radius of the smallest centered disk
containing packing P, and \(q_*=\widehat R^2\).
Let \(\mathcal U\subset\mathcal F\) be a neighborhood of the
known attaining construction on which
[HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md](HUMAN_LOCAL_TRUE_SAT_SEVEN_SQUARE_SHARPNESS.md)
proves the local theorem
\[
\boxed{P\in\mathcal U\Longrightarrow q(P)\ge q_*.}
\tag{L}
\]

A proposed "global capture theorem" has sometimes been phrased as
\[
\boxed{\{P\in\mathcal F:q(P)<q_*\}\subseteq\mathcal U.}
\tag{C}
\]

**Elementary exact equivalence lemma.** Under (L), assertion (C)
holds **if and only if** the unrestricted sharp lower bound
\[
\boxed{\forall P\in\mathcal F,\quad q(P)\ge q_*}
\tag{G}
\]
is true.

**Proof.** If (C) holds and a packing P had \(q(P)<q_*\),
capture would put P in \(\mathcal U\), contradicting (L).
Thus (G). Conversely, if (G) holds, the set on the left
of (C) is empty, so (C) holds vacuously. QED.

**Interpretation:** A bare theorem that "every hypothetical
better packing is near the candidate" is *not an easier
intermediate claim*: once local sharpness is known, it is
logically equivalent to proving global optimality.
An **actual proof method** must instead supply a concrete,
independently justified geometric mechanism, such as a
complete finite interval/marker cover in which every
excluded cell is rigorously infeasible, or a sharp inequality
for the complement of the candidate neighborhood.

The analogous global marker/ownership reduction in
11SquaresOptimal is a concrete finite computation plus
analytic lemmas. Merely naming a "capture theorem" does not
reproduce it.

## 2. A short exact certificate: the candidate's adaptive support dual is NOT angle-global

The positive seven-support/five-circle adaptive dual in
[HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md](HUMAN_ADAPTIVE_DUAL_SEVEN_SQUARE_SHARPNESS.md)
is proved for a **small frame-angle box**. Its exact
angle-potential contribution for the aligned-end square E,
at the attaining common tilt t*, is
\[
\Phi_E(\delta)-\Phi_E(0)
=A_E(\cos\delta-1)+B_E\sin\delta
 +\Gamma_E|\sin\delta| ,
\tag{1}
\]
with A_E, B_E and Γ_E explicit algebraic expressions in
the isolated candidate parameters.

The independent exact rational interval checker
[verify_globalized_dual_angle_failure.py](verify_globalized_dual_angle_failure.py)
establishes, across the FULL rigorously certified sharp
stationary root box,
\[
\boxed{A_E>\frac{22}{25},\qquad
       B_E+\Gamma_E<\frac3{100}.}
\tag{2}
\]
In fact the values are approximately
\(A_E=0.89087665,\ B_E=-0.37034647,\
\Gamma_E=0.39771450\).

Set \(\delta=1/10\) radians, with **positive sign**.
Use the standard true trigonometric bounds
\[
0<\sin\delta<\delta,\qquad
1-\cos\delta\ge
\frac{\delta^2}{2}-\frac{\delta^4}{24}.
\]
Combining (1) and (2) gives the **strict exact rational bound**
\[
\begin{aligned}
\Phi_E(1/10)-\Phi_E(0)
&<
-\frac{22}{25}\left(\frac1{200}
                       -\frac1{240000}\right)
 +\frac3{100}\frac1{10}\\
&=\boxed{-\frac{4189}{3000000}<0.}
\end{aligned}
\tag{3}
\]

Therefore the existing **specific candidate-derived adaptive
dual weights** cannot be used, unchanged, to prove the
radius lower bound for an arbitrary \(0.1\)-radian
independent E rotation. A new dual adapted to E's
angle or a *geometrically proved capture into a small
angle box* would be needed.

**Crucial scope warning:** this is a NEGATIVE RESULT
ABOUT A PARTICULAR DUAL CERTIFICATE, **not**
a smaller-radius genuine packing. The true directed
seven-square support system optimized with E rotated by
0.1 radian numerically gave squared radius
approximately \(3.9163341>q_*\approx3.9155341\).
That optimization is a diagnostic without proof status.
One must not infer a counterexample or an inequality
from this optimizer.

The exact checker of (2) has no numerical search:
it uses the existing dyadic interval arithmetic of
verify_adaptive_seven_square_dual.py, with rational
candidate isolation input. Equation (3) is then a
four-line strict hand inequality.

## 3. The attempted complete-packing numerical falsification did not succeed

I also implemented the true eight-square geometry in
a separate exploratory SLSQP calculation, with all
32 real vertex-circle constraints and all 28 genuine
square-square SAT disjunctions. The explicit historical
rational eight-square construction served as a feasible
starting point, at squared radius approximately 3.9155994.
One bounded minimization run terminated at its iteration
limit near \(q\approx3.9167904\), with minimum constraint
residual about \(-6.8\cdot10^{-6}\).

**The solver's output is INFEASIBLE and proves NOTHING**
about the existence or absence of a better packing.
It is specifically not evidence of a completed global
pose-capture certificate.

The repository's earlier exact lower-bound audit
[GLOBAL_LOWER_BOUND.md](GLOBAL_LOWER_BOUND.md) already
records that direct 23-variable exact interval searches
exceeded node budgets even at \(q=37/10\), while a
low-dimensional exterior pair-marker theorem
successfully certified the weaker \(q>19/5\) bound.
This is why a bare instruction to search the full
pose box is not a plausible global proof by itself.

## 4. The single nonvacuous next proof requirement

Retain the exact local theorem (L). To obtain global
optimality one must **actually construct** at least
one of:

**(A) An exhaustive geometric/interval cover** of
the complement of \(\mathcal U\) in all eight-square
poses up to symmetries, where every box at
\(q<q_*\) is rejected by a **proved exact**
disk/SAT/marker inequality, and all remaining
boxes lie in \(\mathcal U\). The cover must have
a fully auditable finite, terminating certificate.
An over-budget search is NOT such a certificate.

**(B) A universal sharp support-force inequality**
valid on the complement of \(\mathcal U\), without
assuming the candidate contact topology. It must
retain all true independent frames and all eight
square labels.

**(C) A rigorous orientation-robust, complete
separator-capture theorem** whose hypotheses are
established for **every** relevant global
radius-minimizer, not simply by the radius bound
or a numerical optimizer.

These are **alternative sufficient proof methods**,
not a completed case enumeration. Current local
first-order duals, exact cap lemmas and the conditional
five-corner theorem do not yet supply any of A--C.

The 2019 published **Rigorous packing of unit squares
into a circle** by Montanher et al. (Journal of Global
Optimization 73, 547–565) supplies a precedent for
full-geometry interval CSP certificate proof at n=3,
using center tiling/subproblem decomposition; its
generalization to n=8 has **not** been executed here.

**Final mathematical status:** the exact Cantrell
candidate is locally sharp in the separately proved
true-SAT neighborhood; unrestricted
\(R_8\ge\widehat R\), complete equality, and Lean 4
formalization remain OPEN. Do not claim otherwise.
