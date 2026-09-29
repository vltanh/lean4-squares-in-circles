# Six unit squares in a disk — current proof assembly

## Status and source boundaries

The supplied normalization argument is now integrated as
[NORMALIZATION_PROOF.md](NORMALIZATION_PROOF.md). It replaces the former
§2.3, including its dependency order and the statements of (N16)–(N27).
The 78 scalar inequalities and all 23 direct certificate groups have been
replayed locally with an independent exact-dyadic interval backend. This is
not a python-flint/Arb execution and is not a Lean kernel proof. Execution
provenance is recorded in
[NORMALIZATION_INTEGRATION.md](NORMALIZATION_INTEGRATION.md).

The existing candidate, Seven reductions, Appendix A and downstream A2/survivor
calculations are preserved **byte-for-byte**, rather than rewritten during
normalization integration, in
[HAND_PROOF_PRE_NORMALIZATION.md](HAND_PROOF_PRE_NORMALIZATION.md). Its Git
blob is `1a59a55ac5f79c923b4935de96384b6b350bcf09`, identical to HAND_PROOF.md
at `4d9754c79c90df8b103e7b218dc316bec58dc43e`.

The source hierarchy is:

1. This file specifies the current theorem assembly and corrected interfaces.
2. NORMALIZATION_PROOF.md supplies the complete normalization argument.
3. HAND_PROOF_PRE_NORMALIZATION.md supplies the retained detailed calculations,
   except its former §2.3 and historical proof-status paragraphs, which are
   superseded. Its concise normalization sketches must not be used instead of
   the new manuscript.
4. The certificate programs are arithmetic checks; they are not axioms or
   imports into a Lean theorem.

This integration does not claim a new independent audit of the retained A1/A2
proof, does not merge PR #6, and does not change the formal library's theorem
statements. The unrestricted Lean theorem remains to be formalized.

## 1. Candidate and intended unrestricted theorem

Put
\[
 h=1/\sqrt2,\qquad A=(1466+1940h)/267,\qquad B=(327+432h)/712,
\]
\[
 s_*={2B\over A+\sqrt{A^2-4B}},\qquad
 t_*=(-20+30h)s_*+7/2-9h/2,
\]
\[
 d_*=1/2+h-t_*,\qquad q_*=2s_*^2+4s_*+5/2.
\]
The candidate centers are
\[
 C=(s_*,s_*),\quad N=(s_*,s_*+1),\quad E=(s_*+1,s_*),
\]
\[
 W=(s_*-1,t_*),\quad S=(t_*,s_*-1),\quad D=(-d_*,-d_*).
\]
The first five frames are parallel and D has rotation \(\pi/4\). Its active
containment identities and attainment argument are those of retained §1.
The intended unrestricted conclusion is \(R^2\ge q_*\), with the equality
classification in retained §7. Candidate parameters \(s_*,t_*,d_*\) are
not the angular variables \(s,d\) used in the stress lemmas.

## 2. Proven input to normalization

For a hypothetical packing with \(R^2\le q_*<Q_0=142559/50000\), use retained
§§2.1–2.2: the Seven exterior theorem forces a unique square C containing the
disk center in its open interior. Translate the disk center to zero, use C's
frame, and make its center coordinates nonnegative.

The other five squares have genuine admissible Seven charts. Their genuine
markers, not prematurely substituted affine markers, have successive cyclic
gaps in \((\pi/3,2\pi/3)\), by (N7). These are the N0 inputs. No A2 pattern,
fixed pin, small central box, or separator bit is assumed here.

## 2.3. Replacement normalization package

All details and scalar labels in this section refer to NORMALIZATION_PROOF.md.
Define
\[
 \rho_0=\sqrt{Q_0-1/4}-1/2,\qquad c_0=\rho_0-1,
 \qquad U_0=\sqrt{Q_0-(5/2-\rho_0)^2}-1/2.
\]
The dependency order is
\[
 \text{N0 and cap lemma K}
 \longrightarrow \text{Proposition A (N23, N16)}
 \longrightarrow \text{Lemma B}
 \longrightarrow \text{pin covering C}
 \longrightarrow \text{windows/order D}.
\]
Cap piercing and Lemma G supply the moving pins and one-helper-per-side
statement. Only after those results is Appendix A applied to obtain (N27).

| Output | Precise statement / proof source |
|---|---|
| N23, then N16 | Proposition A: \(0\le c_x,c_y\le c_0<23/200\), from the forbidden-marker arcs and N7 alone. No sector assumption. |
| N17 | Lemma B: \(a\ge2-\rho_0\), \(a\le\rho_0\), \(|b|\le U_0<1/2\), hence \(177/200<a<223/200\), \(|b|<117/250\), and side-nearestness. |
| N20 | B5: \(9a+11|b|<2\pi+7\), so the genuine label is axial and \(m=\phi+5b/4\). |
| N19 | Lemma C: each exterior square contains exactly one of the five open radius-9/10 pins at \(0,\pi/2,11\pi/12,5\pi/4,19\pi/12\). Labels are assigned by pins. |
| N18 | D2, D4 and S52: lifted primary directions have order E,N,W,D,S. |
| N21 | D1–D3 and B6: only the matching cardinal separator or OWN remains; prefer cardinal on ties. D's matching side is west after the diagonal normalization. |
| N22 | K4: two squares using one central cardinal side would contain the same piercing point in their open interiors. |
| N24 | K4 for cardinal helpers and Lemma G for OWN: \((1+c_x,0)\in E^\circ\), \((0,1+c_y)\in N^\circ\). |
| N25 | K3: every cardinal helper has angular deviation \(<2/5\) in absolute value. |
| N26 | K5, **only when both opposite helpers are cardinal**; precise statement below. |
| N27 | Retained Appendix A with the complete, noncircular interface below. |

### Strong box before sectors

If \(c_x>c_0\), after a temporary symmetry in the proof of this symmetric
bound, Lemma A excludes a marker arc whose length exceeds \(2\pi/3\).
For \(c_y\le c_0\) its endpoints are determined by
\(\pi/2-5X_0/4\) and \(\pi/2-5U_0/4\); for \(c_y>c_0\), they are
\(\pi/2\) and \(27/50\). This contradicts N7. The statement excludes the
strict region \(c_x>c_0\), **not the boundary** \(c_x=c_0\).
Consequently N23 is available before any pin or sector construction.

### Reflection budget

After pin labeling and the windows, use the diagonal reflection once, only
when needed to arrange \(\phi_D\le5\pi/4\). It preserves \(c\ge0\),
the strong box, and the pin set. It gives
\[
 \phi_D=\pi+d,\qquad -2/5<d\le\pi/4.
\]
No horizontal reflection is used. No later survivor transfer may spend an
additional global diagonal reflection while assuming the same D-angle range.
The direct survivor arguments in the retained manuscript are used instead.

### N26 — corrected opposite-cardinal-pair statement

Let \(K_X\ge0\) mean that X admits the corresponding cardinal central
separator. Then
\[
 (K_E\ge0\ \land\ K_W\ge0)
 \ \Longrightarrow\ |\theta_E|+|\theta_W|<4c_0,
\]
\[
 (K_N\ge0\ \land\ K_S\ge0)
 \ \Longrightarrow\ |\theta_N|+|\theta_S|<4c_0.
\]
There is no such assertion for arbitrary OWN/cardinal opposite pairs. The
retained uses are P26-1, with E and W cardinal, and P16, with N and S
cardinal. Read the unqualified historical display (N26) only with these
explicit hypotheses. The proof adds the opposite cap-depth inequalities and
uses the strict tilt budget K5, treating the two-zero-angle case separately.

### Appendix A — complete interface for N27

The Appendix A argument retained in HAND_PROOF_PRE_NORMALIZATION.md is invoked
only in the following strengthened form. Assume:

- \(R^2\le Q_0\), \(O=0\), C axis-parallel and
  **\(c\in[0,c_0]^2\)**, already established by Proposition A;
- the fixed pin labels and D2 windows;
- D is west-cardinal, so its deviation satisfies \(|d|<2/5\), by K3;
- W is OWN, by N22 and D3 under that assumption on D;
- W's deviation satisfies \(w>-2/3\), by D2/S42;
- \(w<d\), by D4; and each radial chart coordinate satisfies
  \(a\le\rho_0\), by B3.

Appendix A's three-separator stresses exclude this west-cardinal D case.
D3 then leaves only OWN, proving N27. The full central box is a hypothesis of
this invocation, not merely the older appendix's abbreviated \(c\ge0\).
Neither N27 itself nor any A2 classification is used to establish that box,
the pins, order, or N22. This removes the former circularity.

## 3. Assembly with the retained downstream argument

The normalization output now provides the actual hypotheses of the retained
A1/A2 stress calculations, rather than seeding a verifier with unproved
normalization conclusions. Apply the detailed A2.1, A2.2 and A2.3 lemmas in
the preserved manuscript, and then the direct survivor arguments for
9, 11, 15, 24, 25 and 27. The retained Pattern-8 calculation and equality
analysis supply the final candidate bound and its equality case.

This is an assembly of those retained arguments with the supplied normalization
proof. The local normalization replay is **not** a new independent verification
of every retained downstream scalar inequality. Its scope is explicitly the
normalization predicates and the dependency interface above.

## 4. Verification and formalization boundary

The local normalization record distinguishes:

- 78 scalar interval inequalities from four identity sanity checks;
- 23 direct certificate groups, all with zero unresolved boxes;
- 14 positive/negative sharpness controls;
- tests of rounding, critical points, interval-cover completeness, failure
  behavior, and the \(c_x=c_0\) boundary witness.

The executed backend is the separately named 96-bit exact-dyadic implementation.
The native python-flint/Arb entry point is retained, but was not executed in
this environment. No GitHub runner, Lean build, axiom audit, theorem merge,
or publication action is part of this integration.

The manuscript-level normalization package is supplied with explicit scalar
leaves and a successful independent replay. The next formalization step is to
translate those leaves and the dependency chain into Lean and verify the final
kernel dependency graph. Do not replace that work with a Python success flag.
