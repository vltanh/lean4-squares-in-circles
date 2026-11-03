# A is the unique leftmost original in the weak-outer caller

Complete hand proof. No Lean, Lake, or CI. This is a necessary geometric
consequence, not a whole-mask closure. The argument uses only the original
actual AB and BC links, the original CD cone and physical nonoverlap,
containment in the closed disk with squared radius Q=1105/256, and the
already proved left-main inset barrier. It does not need a D tilt sign,
an E/A height order, or a placement assumption on either extra original.

Let rho=91/60. Every original center has norm strictly below rho, and
every two distinct original centers have distance at least one. The latter
follows from the disjoint open radius-1/2 disks contained in the two unit
squares. The complete argument in `WEAK_OUTER_LEFT_MAIN_INSET_BARRIER.md`
gives, for the unchanged original A,

\[
 -x_A>91/64,\qquad |y_A|<g_A-3/40\le17/40.
\]

**Theorem.** Every other original X satisfies x_X>x_A.

**Proof.** Suppose x_X<=x_A. Both x coordinates then lie strictly between
-rho and -91/64, so

\[
 |x_X-x_A|<\rho-91/64=91/960.
\]

The same original center-disk bound gives

\[
 |y_X|^2<\rho^2-(91/64)^2<(8/15)^2.
\]

The last strict rational comparison has reserve

\[
 (8/15)^2-[(91/60)^2-(91/64)^2]=1811/307200>0.
\]

Consequently |y_X-y_A|<8/15+17/40=23/24. Hence

\[
 |c_X-c_A|^2<(91/960)^2+(23/24)^2<1,
\]

where the final reserve is

\[
 1-(91/960)^2-(23/24)^2=66919/921600>0.
\]

This contradicts the unit lower bound on the distance between distinct
original centers. It also excludes the equality face x_X=x_A. QED.

All nine originals remain present. In particular the conclusion applies
to both unselected originals, independently of their frames, and removes
the left-of-A escape branch from every alternate row that keeps A as its
left endpoint. The argument does not assert that D is the rightmost
original and does not change the accepted whole-mask count.
