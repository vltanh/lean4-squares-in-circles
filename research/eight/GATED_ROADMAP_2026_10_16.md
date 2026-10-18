# Gated roadmap: the unrestricted eight-square theorem is closed

Research started 2026-10-16 and continued through 2026-10-18 UTC.
Scope: PR #9, `research/eight/**`, a hand proof with supplied fixed rational
arithmetic tables and independent continuous and arithmetic reviews.

**The unrestricted sharp radius theorem and the complete equality
classification have a complete hand proof.** The main argument is
[UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md).
Every retained global premise now has a hand derivation. The proof keeps
all 128 core/outer boundary assignments and uses frame and quarter-word
inequalities to reach the candidate; it does not inherit the older
three-necklace or 123-box computer-assisted capture.

Let \(q_*\) be the unique admissible stationary root defined by the
radical equations in
[HUMAN_FAMILY_CLOSURE.md](HUMAN_FAMILY_CLOSURE.md). Then every packing
of eight unit squares in a circle has squared containing radius
\(q\ge q_*\), and an actual packing exists at that radius. The
hand sharp bracket is

\[
3.91553413751747532652-2\cdot10^{-16}
<q_*<3.91553413751747532652+10^{-16}.
\]

Thus \(R_*=\sqrt{q_*}\simeq1.97877086534\). The decimal is
descriptive; the stationary equations and unique admissible-root theorem
define the constant.

The equality conclusion is an exact classification, including the
central square. Up to isometry and relabeling, five exterior squares and
the two outer orientation groups are fixed. Two exterior squares slide
in prescribed directions; the central square can translate and rotate.
[COMPLETE_EQUALITY_PARAMETER_DOMAIN.md](COMPLETE_EQUALITY_PARAMETER_DOMAIN.md)
gives the necessary and sufficient domain in five real parameters by
explicit radical, rational and separating-axis inequalities. It contains
a full five-dimensional box of noncongruent packings. Consequently the
stationary root and five-anchor structure are unique, while an isolated
optimal pose is not.

## 1. Completed gate ledger

| Gate | Exact exit | Status and proof |
|---|---|---|
| G0: constant and attainment | Select the unique stationary root and construct eight actual unit squares at it | **Passed.** Global family convexity/uniqueness, exact construction, and the explicit equality-domain box |
| G1: central square and core | Exactly one square contains the closed radius-\(1/12\) disk in its open interior at \(q\le9789/2500\) | **Passed.** Two-circle angular measure, a universal transverse segment, and two complete forbidden-angle estimates |
| G2: radial reduction | Preserve true frames, physical cyclic order and one original signed separator per edge while moving each exterior center to a core or outer boundary | **Passed.** Two fixed incident halfplanes always have a common recession direction; all 128 radial assignments remain covered |
| G3: frame concentration | Every exterior frame lies in a common real interval of width less than .7 | **Passed.** Ten whole-pair hand theorems cover all 128 ordered source-axis branches, followed by the seven-walk and orientation-lift arguments |
| G4: quarter words | Exclude every word except 0101011 | **Passed.** Exact seven-word enumeration; the common table excludes four jump-two words; complete independent assemblies exclude 0010111 and 0011011 |
| G5: coarse candidate position | Normalize E; obtain \(-.8<u_G<-.05\), \(.05<u_T<.8\), \(u_H>.5\), \(u_D<-.5\) | **Passed.** Six full-SAT fixed affine-arc tables with independent closed-domain reviews |
| G6: initial mismatch | \(S<13/50\) | **Passed.** 129,031 full-domain fixed rows; the original cyclic chord bound and seven retained printed reserves use the same table |
| G7: middle mismatch | \(S\le13/50\Rightarrow S<1/10\) | **Passed.** 131,255 fixed rows and 123,168 independently covered angle chains; all four original axes are retained |
| G8: zero-edge signs and next contraction | H/A/T positive, G/B/D negative; \(S\le1/10\Rightarrow S<3/200\) | **Passed.** Strict elementary SAT bounds, then 107,196 fixed rows and 101,280 independently covered angle chains |
| G9: quarter owners | At \(S\le3/200\), B→T and D→E have only axes 3 and 4 | **Passed.** All 48 wrong-owner pattern unions and 1,545 independently reconstructed quartics |
| G10: final mismatch | \(S\le3/200\Rightarrow S<1/1000\) | **Passed.** 144,709 fixed rows and 129,368 independently covered angle chains; mixed edges still retain all four axes |
| G11: mixed owners and tilt | G→A has only axis 1; E→H only axis 2; \(.1<t<.16\) | **Passed.** Shared-error owner bounds and signed-error tilt vertices, with 729 and 1,239 independently reconstructed quartics |
| G12: sharp terminal | \(q\ge q_*\), with positive tilt, center-square and mismatch terms | **Passed.** Exact center-square completion applies to arbitrary centers; both slider bounds follow automatically |
| G13: radius and original equality transfer | Apply the terminal at the original subsharp boundary radius, then recover every original equality pose | **Passed.** Every initially valid signed separator survives outer-radius expansion; the stationary dual is reapplied directly to original centers |

## 2. The completed mismatch chain

Use cyclic roles \((H,G,A,B,T,D,E)\), quarter word
\((0,1,0,1,0,1,1)\), and

\[
I=\{0,2,3,4,5\},\qquad
S=\sum_{i\in I}|\theta_{i+1}-\theta_i|.
\]

Here \(\theta_i\) are the common real frame lifts, with the nominal
quarter-turn offsets removed, so \(d_i=\theta_{i+1}-\theta_i\).
The four stages now give the finite chain

\[
S<\frac{13}{50}\ \Longrightarrow\ S<\frac1{10}
\ \Longrightarrow\ S<\frac3{200}
\ \Longrightarrow\ S<\frac1{1000}.
\]

Every stage covers both radial kinds at every vertex. A marker is selected
once per vertex and used on both incident edges, including shared arc
endpoints, so the cyclic cancellation is exact. No stage assumes an owner
or sign that it is meant to prove.

| Stage | Charge on the five aligned edges | Sum of lower constants | Exact contradiction reserve |
|---|---:|---:|---:|
| Middle, .26 to .1 | \(1/400\) | \(7(.897582)\) | \(18173/2712000000\), above \(710/113\) after the hand lower bound for \(h(.1)\) |
| Narrow, .1 to .015 | \(1/200\) | \(125662969/20000000\) | \(2287/6400000000\), above 6.28318531 after the hand lower bound for \(h(.015)\) |
| Final, .015 to .001 | \(1/20\) | \(502653/80000\) | \(522599/240000000000\), above 6.28318531 after the hand lower bound for \(h(.001)\) |

Here \(h(x)=(\sin x+\cos x-1)/2\) on the indicated positive
interval. The strict pair sums and concavity give
\(2\pi>\Gamma+\beta\sum h(|d_i|)\ge\Gamma+\beta h(S)\).
The table's rational reserves contradict each proposed threshold.

The original coarse stage uses only G/T/E cuts and all four axes. The
middle stage also keeps all four axes. The .1 sign implication is used
only after the middle conclusion. The quarter-owner theorem is used
only after the .015 conclusion. The final table retains all four mixed
axes, so the later mixed-owner and tilt theorems are not circular inputs.

## 3. The sharp terminal and equality

After the final contraction, the owner sets in cyclic order are

\[
\{1,3\},\{1\},\{1,3\},\{3,4\},\{1,3\},\{3,4\},\{2\}.
\]

The [unified one-thousandth capture](HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md)
binds all 3,513 owner/tilt quartics and 17,565 positive coefficient
bounds. It supplies exactly the hypotheses of
[HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md](HAND_TERMINAL_WITH_AUTOMATIC_SLIDERS.md).
That theorem gives

\[
q\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2
+\sum_{i=A,B,D,E,H}\mu_i
\left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2
+\frac{10293}{5000000}S.
\]

All weights are positive. Equality forces the actual outer frames to
have \(S=0\), \(t=t_*\), and fixes the five anchor squares.
Reapplying the stationary dual directly to the original centers fixes
the original anchors and all seven selected contact gaps, with zero
forces on the two slider coordinates. This avoids any inference that
a radially moved center must already have been in the same position.

The [fixed-ceiling transfer](HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md)
handles the distinct radius levels explicitly. A hypothetical packing
below \(q_*\) is reduced at
\(\bar q=\max(q,7831/2000)<q_*\), then its outer boundary radii
are expanded to \(Q_1=3.915534138\). A further temporary expansion
to \(Q_0=9789/2500\) supplies the coarse frame/word results. Every
initially valid signed witness survives expansion, and the relevant
rays, frames and tangents stay fixed. The terminal is applied to the
already feasible \(\bar q\) representative recovered before
expansion, yielding \(\bar q\ge q_*\), a contradiction. No
arbitrary inward monotonicity or center-proximity claim is made.

## 4. What the hand arithmetic contains

Each candidate row proves an explicit continuous support inequality with
a nonnegative rational SAT multiplier. Endpoint monotonicity, concavity
or a full-circle support eliminates the two state coordinates. A supplied
global radical majorant and alternating Taylor bounds leave a fixed
one-variable rational polynomial. Its printed Bernstein coefficient
bounds prove that polynomial on its entire closed interval. The exact
arc and angle unions cover every retained case, including ties.

The completed proof is therefore a long finite tabular hand proof with
independently checked arithmetic. The full source tables are part of the
deliverable. Discovery fits, failed rows, numerical minima and adaptive
state-subdivision certificates are excluded as proof premises. No Lean
formalization or CI run is used to claim this closure.

For the main assembly, the companion fixed-interface checker additionally
reconstructs 44 exact scalar comparisons, all 16,384 four-type seven-walk
weights, and the 70 admissible quarter words before their seven-class
dihedral quotient. Those checks supplement the proved continuous lemmas;
they do not replace them.

## 5. Closure records and historical material

The current theorem is
[UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md](UNRESTRICTED_EIGHT_SQUARE_HAND_PROOF.md),
with the final hand-assembly manifest. Its ledger binds the completed
middle and final mismatch manifests, the four-type inventory, both wrong
word assemblies, all candidate cut and contraction tables, the unified
owner/tilt capture, and the exact original-equality domain.

Frozen component notes may retain the earlier statement that a global
capture input was pending or supplied by computer assistance. The current
assembly explicitly replaces that input with the completed hand chain.
Their mathematical statements and independent-review hashes are kept
unchanged. The older computer-assisted unrestricted proof remains a
separate historical result; its central-core subdivision, radial-necklace
exclusions and 123-box capture are not dependencies of the final hand
proof.

There is no remaining mathematical gate in the unrestricted radius or
equality target. Any later work on shortening the tables or formalizing
the argument is a separate project.
