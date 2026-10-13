# Computer-assisted attack roadmap for the unrestricted n=8 lower bound

**Research continuation: 2026-10-12.**
**Target:** prove the unrestricted sharp inequality
\[
R_8\ge\widehat R
\]
against the exact already-constructed five-corner packing,
classify equality, and only then transfer the result to Lean 4.
**Status:** OPEN. This is a work program, not a claim of completion.
All proposals below must preserve the genuine S4/k=7 seven-outer
contact-ring equality construction and its admissible slider variants.

## 1. One complete computer-to-hand example, accomplished

We used
[computer_two_square_cap_probe.py](computer_two_square_cap_probe.py)
to investigate a **standalone, fully rotated two-square cap**
subproblem: an inner-center square P and an outer-center square Q,
both with nonnegative transverse x centers, whole-cap offset h,
true vertex containment, and *one of all eight signed exact
separating axes*.

The numerical program is **discovery only**. It minimizes the
squared containing radius by local, nonconvex SLSQP, independently
for all eight signed separator choices. Its objective variable
bounds the squared norms of **all eight true vertices**, and its
other inequalities include both center radial classes and both
whole-square cap minima.

Reproduce the exploratory baseline (requires NumPy and SciPy):
\`\`\`bash
OPENBLAS_NUM_THREADS=1 python research/eight/computer_two_square_cap_probe.py --starts 5
\`\`\`

An actual deterministic run with seed 20261012 produced:

| Shared cap offset | Best exploratory squared radius | Exact axis-aligned candidate |
| --- | ---: | ---: |
| \(7/24\) | 3.9184027691 | \(2257/576=3.9184027778\) |
| \(1/3\) | 4.0277777466 | \(145/36=4.0277777778\) |
| \(37/100\) | 4.1268999686 | \(41269/10000=4.1269\) |

**Critical caveat:** the numerical best entries have small *negative*
constraint residuals of magnitude \(5\cdot10^{-9}\) to
\(1.4\cdot10^{-8}\), and SLSQP did not report successful termination.
Do **not** call these certified feasible points, proven minima,
or a global exclusion. The exact axis-aligned candidates in
the final column, by contrast, are genuine geometric constructions.

The exact control packing for each h in \([7/24,37/100]\) is
\[
P=[-1/2,1/2]\times[9/20,29/20],\qquad
Q=[1/2,3/2]\times[h,h+1].
\]
P has inner center \((0,19/20)\),
Q has outer center \((1,h+1/2)\), both x centers
are *weakly nonnegative*, and their open interiors
are disjoint (touching only along the line \(x=1/2\)).
Their maximum vertex squared radius is
\[
q_{\rm axis}(h)=(h+1)^2+9/4.
\]
At \(h=7/24\), this is \(2257/576\), strictly
*above* the allowed ceiling \(q_+=9789/2500\) by
\[
2257/576-9789/2500=1009/360000>0.
\]

**The productive computer clue** was that local search repeatedly
moved toward parallel frames, transverse inner center \(p_x=0\),
outer center \(q_x=1\), and a whole-cap side-contact normal.
This motivated checking the old *single-square*
cap-envelope proof, rather than trying to certify
a nonconvex two-square minimum numerically.

The resulting **fully proved hand theorem** is
[HUMAN_CAP_ENVELOPE_37_100.md](HUMAN_CAP_ENVELOPE_37_100.md).
It improves the cap-offset domain of the sharp
arbitrary-orientation one-square center envelope from
\(h\ge2/5\) to \(h\ge37/100\) **at \(q\le q_+\)**.
The proof uses a two-sign vertex concavity reduction
and **four exact affine-polynomial positivity certificates**.
Its independent rational audit is
[verify_cap_envelope_37_100.py](verify_cap_envelope_37_100.py).

That exact lemma then yields
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md):
an inner/outer two-square whole-cap pair at
\(h\ge37/100\) **cannot** have same weak transverse
center signs, because its center distance would satisfy
\[
|p-q|^2<1989/2000<1.
\]
This is a strict, continuous, arbitrary-frame handproof.
The arithmetic replay is
[verify_mixed_high_cap_37_100.py](verify_mixed_high_cap_37_100.py).

### What was actually removed

The still-open exclusive S2/k=4 **same-weak-sign cell C**
previously had
\[
7/24<h_U<2/5.
\]
It is now restricted to
\[
\boxed{7/24<h_U<37/100.}
\]
Cells with **opposite** near-U center signs remain.
The exact standalone rational counterexample
[RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md](RATIONAL_SAME_SIGN_ROTATED_CAP_PAIR.md)
has **two outer centers**, so it does not invalidate
the new *mixed inner/outer* theorem. No eight-square
feasibility claim was made from the two-square search.

## 2. Priority A: finish the remaining S2/k=4 local mixed-pair obstruction

This is the most promising **hand-proof-first** target.

**Computer conjecture, emphatically not established:**

> Two distinct whole unit squares in \(y\ge h\ge7/24\),
> with one inner and one outer center and
> nonnegative transverse center x signs, require
> \[
> R^2\ge(h+1)^2+9/4.
> \]
> Equivalently, the aligned two-square arrangement above
> attains the minimum under those *mixed radial-class*
> hypotheses.

If true, this single local theorem would eliminate the
**entire remaining S2/k=4 same-sign cell C**, since its
right side at \(h=7/24\) is \(2257/576>q_+\).
The local optimization strongly **suggests** this conjecture,
but does not certify it. Search for a rotated actual-square
counterexample first; if one is found, keep the rational witness
and abandon the false theorem rather than patch assumptions
post hoc.

**Recommended algebraic conversion:**

1. Normalize both transverse centers to nonnegative x,
   use the already proved inner/outer polar gap \(>3/4\)
   to get \(0\le p_x<1/4\), \(q_x>7/10\).
2. Retain the *actual* separating-axis disjunction:
   one of \(\pm e_P,\pm f_P,\pm e_Q,\pm f_Q\) must separate
   the two true squares. Do not replace it with
   center distance \(\ge1\).
3. Split by which square owns the SAT axis and by frame
   signs, and transform \(z_i=\tan(\theta_i/2)\)
   to polynomial inequalities. Computer algebra may
   suggest a few exact monotonicity or convexity identities.
4. Prove the minimal vertex norm is at least
   \((h+1)^2+9/4\) in each surviving **continuous**
   axis/angle case, or isolate a concise weaker
   rational obstruction sufficient when \(h>7/24\).
5. Check equality/slack and the cap-offset boundary
   analytically. The exact two-square all-outer
   counterexample shows the **inner radial assumption
   cannot be dropped**.

**Deliverable:** one stand-alone 2-square mixed-cap hand lemma,
a small exact-fraction symbolic verifier, and a genuine
elimination of cell C. If the conjecture fails, replace it
with the strongest true per-SAT-owner inequality.

## 3. Priority B: S2/k=4 opposite-center-sign cells A and B

The complete necessary S2/k4 classification is in
[HUMAN_S2_K4_THREE_CELL_QUEUE.md](HUMAN_S2_K4_THREE_CELL_QUEUE.md).
The **updated** cells are:

| Cell | Remaining h_U | Near-U inner/outer x signs |
| --- | --- | --- |
| A | \(37/100\le h_U<97/200\) | Opposite |
| B | \(7/24<h_U<37/100\) | Opposite |
| C | \(7/24<h_U<37/100\) | Same weak sign, nontrivial frame defect |

The far-D 2+2 pair has two outer centers;
the R triple has exactly one outer and two inner
centers; the near-U pair has one outer and one inner
center. Every square has independent frame freedom.

**Computational experiment:** optimize *all four U/D squares*
with genuine whole-side membership, true square vertices,
and all six pairwise SAT disjunctions, initially
holding the central-coordinate \(t\) fixed. Add the
right triple only after measuring which far-side
corner/angle inequalities are active. No center-only
proxy should be accepted as an actual packing certificate.

**Hand route:** prove a precise *far-D pair versus near-U pair*
radial-cap or cross-chord inequality. Existing
[HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md](HUMAN_TWO_CAP_SHARED_MIDSLICE_CHORDS.md)
ensures the two near-U squares have disjoint, true
unit-length horizontal chords at a common slice
for all frames. Preserve the possible oblique
overlap of their **full projections**.
The outer-center angle bound
\(>\pi/4-1/500\) and exact signed cap envelope
give supplementary global constraints.

**Deliverable:** eliminate A and B by actual-square
support inequalities, or prove a sharp lower bound
for the entire S2/k4 class. A locally feasible 4-square
subassembly would not imply an 8-square packing.



### Exact opposite-sign negative control

[RATIONAL_OPPOSITE_SIGN_MIXED_CAP_PAIR.md](RATIONAL_OPPOSITE_SIGN_MIXED_CAP_PAIR.md)
exhibits two axis-parallel, actual unit squares
with one inner and one outer center in
**strictly opposite transverse half-planes**,
both wholly in \(y\ge2/5\).
Their true square-square SAT reserve is
\(1/10>0\), all eight vertices fit in the disk
with squared radius \(73/20<q_+\), and
the exact n=8 ceiling margin is \(166/625>0\).

Thus **cell A's opposite-sign mixed near-U pair
is locally possible** under the pair-only conditions;
one must use its **far-D outer pair, right triple and/or
central square** to prove a global S2/k4 exclusion.
This local two-square packing is not a valid
eight-square configuration. The full rational
vertex proof and its verifier are in the linked files.

## 4. Priority C: exclusive S1/k=3 tiny-offset geometry

The already proved S1/k3 necessary region, in
R=3,L=1,U=3,D=0 normalization, is
\[
17/200<h_{31}<13/100,\qquad
0<h_{30}<1/16,\qquad
-3/20<y_L<-1/75.
\]
This places the 3+0 triple almost through the
origin and the 3+1 far singleton in a strict
negative transverse lane. The four inner-center
rays are already ordered with pairwise
gaps \(>\pi/3\).

**Computer attack:** retain all **seven exterior**
actual square frames and SAT axes (the seven
single-side assignments are disjoint), but enumerate
only the small, already-proved polar-sector
alternatives. Record the first square pair whose
signed support inequality must saturate near
\(R=\widehat R\), not just a sampled minimum.

**Hand route:** show the near-origin triple plus
far singleton requires either an impossible
outer-center angular gap or a consistent
five-corner projected chain with
\(R\ge\widehat R\).
Do not assert the far singleton is wholly
in an origin quadrant merely from \(y_L<0\).
**Deliverable:** entire S1/k3 elimination or
the required sharp radius bound (not another
arbitrarily tiny threshold improvement).

## 5. Priority D: the equality-preserving global branches

This cannot be replaced by S1/S2 pruning.

* **S1 k=4..6; S2 k=5..6; S3 k=4..7; S4 k=4..7.**
  Cross-reference the current
  [SINGLE_SIDE_SEVEN_BRANCHES.md](SINGLE_SIDE_SEVEN_BRANCHES.md).
  S4/k7 contains the actual optimized construction,
  so an unconditional S4 impossibility would be false.
* **D0 with corner-only separators.**
  These are not wholly beyond a central side:
  do not insert fake side-cap hypotheses.
  Enumerate at most one corner-only square per
  quadrant and use actual own-frame separators.
* **D1, D2 double-side statuses.**
  D2 has two adjacent double-side members and a
  **forced corner-only exception**. Its double
  members share a central signed side;
  the actual corner-only square cannot be replaced
  by an invented central-side member.
* **Outer-center paths and full seven-cycle.**
  Noncentral inner units may connect outer paths;
  the **full seven-outer actual-contact ring occurs
  at equality** with central spokes and must be retained.

A computer's best role here is proposing a
**coherent five-corner support inequality**:
a single assignment of five actual square labels,
their true frame directions and compatible
oblique contacts, proved forced by the global
separating-axis/contact topology. An exterior
ring-only bound is insufficient: the central
square must still fit inside.

**Deliverable:** either derive the true
five-corner structural hypotheses for *every*
remaining configuration and apply the already
proved conditional optimum, or prove a different
universal sharp inequality preserving equality.

## 6. Certification and stopping gates

Every computation must be classified as one of:
**(i) a diagnostic**, **(ii) an exact rational
geometric counterexample**, or **(iii) a human
proof with an optional arithmetic audit**.

A computational attack is ready for promotion only after:

1. **Correct geometry.** All 32 actual square vertices
   lie in the proposed disk; every one of the 28
   pairwise nonoverlap constraints has a genuine SAT
   axis; assigned whole-side/corner statuses and
   inner/outer norms are literal and correctly counted.
2. **Exact proof.** Replace numerical constants with
   rational/radical bounds. Prove every continuous
   orientation/position range via monotonicity,
   concavity, convex vertex reductions or a
   finite *hand-understandable* geometric case split.
3. **Counterexample search.** Test the claim's
   hypotheses against tilted 2-, 3-, 4-, and
   7-square rational witnesses already in the repo.
   A strict rational counterexample invalidates
   the proposed statement immediately.
4. **Dependency hygiene.** Separate new full-domain
   theorems from earlier weaker, superseded
   offset-strip necessary conditions; do not
   count a square twice when adjacent cap
   populations share a double-side status.
5. **Equality guard.** Check the S4/k7 exact
   candidate/slider family against the new
   inequalities before declaring any global
   region impossible.
6. **Global exit.** Only after **all** remaining
   status/contact classes satisfy
   \(R\ge\widehat R\), with equality characterized,
   should the PR move past draft toward an
   independent Lean 4 proof. Arithmetic-only
   Python checks do not fulfill this gate.

### Current outcome

**Completed in this continuation:** a real local
nonconvex search, an analytically strengthened
sharp cap theorem at \(h\ge37/100\), a corresponding
full-frame mixed same-sign exclusion, and
a reproducible proof/discovery separation.

**Not completed:** the lower-offset \(7/24<h<37/100\)
same-sign cell C, S2/k4 opposite-sign cells A/B,
the tiny-offset S1/k3 continuum, all higher-k
and D1/D2/corner-only branches, the unrestricted
sharp n=8 lower bound, equality classification,
or Lean formalization. These remain the
explicit proof obligations.
