# 11SquaresOptimal → eight-square sharp disk proof: one transferable global strategy

**Research note, 2026-10-13. Primary external reference:**
https://github.com/Queuingtheorydotcom/11SquaresOptimal

Read:
* paper/eleven-squares-synthesis.tex, especially
  "The argument in three ideas",
  "Two squares can cast the shadow of a straight row",
  "A mixed support inequality with independent angles",
  and "One principle for the global reduction";
* paper/eleven-squares-geometric-foundations.tex;
* PROOF.md and paper/README.md for the verification/trust scope.

The eleven-square problem is **unit squares in a square
container**, not eight unit squares in a circle.
None of its global ownership geometry or its numerical
thresholds transfers automatically.

## The main idea we SHOULD import

**Do not prove equal square orientations in every sharp
minimizer. Prove that deviations from the useful
candidate orientation clusters are PAID FOR by genuine
pairwise separating-axis inequalities.**

The 11-square paper's central analytic comparison is:
\[
\max\{v_{\theta_p}\cdot d,v_{\theta_q}\cdot d\}
\ge\frac{1+\cos(\theta_q-\theta_p)+
|\sin(\theta_q-\theta_p)|}{2}.
\]
Let m be the mean angle and
\(\delta=(\theta_q-\theta_p)/2\).
In midpoint-frame coordinates X,Y, this gives
\[
X-\cos\delta
\ge(\cos\delta-|Y|)|\tan\delta|
\ge\frac\eta2|\theta_q-\theta_p|,
\quad
\eta=1-D^2/2-B>0
\]
whenever \(|\delta|\le D,|Y|\le B\).

They then form a **positive weighted sum of true
support gaps**, prove that it has enough
mismatch penalties along a spanning tree of
angle variables, and compare its VALUE at
common angles through a sequence of analytic
tree contractions. **No physical packing is
rotated** during this comparison. A scalar
convexity/critical-point estimate finishes
their conditional optimum.

This is potentially exactly what our
five-corner proof is missing: its existing
seven-square directed-separator theorem
[HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md](HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md)
requires aligned A/E end frames. We should
try to replace that assumption with a robust
**orientation-mismatch support inequality**,
not treat exact alignment as a global
minimizer property to establish first.

## We have already proved a concrete local transfer

[HUMAN_LOCAL_ANGLE_MISMATCH_BACKBONE.md](HUMAN_LOCAL_ANGLE_MISMATCH_BACKBONE.md)
is a standalone **true-square hand theorem**
for the five actual separator edges in our
rational eight-square packing:

\[
AB,\quad TB,\quad DT,\quad ED,\quad HG.
\]

Their exact nominal signed transverse center
displacements are
\[
\frac{24441}{250000},\
-\frac{23}{30},\
\frac{397767}{1000000},\
-\frac{111471}{200000},\
0.
\]
All have magnitude below one.

If each square center is allowed an independent
Euclidean perturbation \(\le1/50\), and each
square frame an independent angular deviation
\(\le1/50\) radians from its nominal frame,
the **actual genuine SAT theorem** excludes
all wrong owner-axis directions. The correct
positively directed two-owner disjunction is forced.
The exact midpoint-frame support gaps then obey,
for **every** of those five physical pairs,
\[
\boxed{
g_{ij}\ge\frac7{100}|\theta_i-\theta_j|.
}
\]
Here the angle differences are within the
two nominal frame clusters: standard
A--B--T--D--E and tilted H--G.
Their **relative** nominal standard/tilted
orientation difference is left free and
must be optimized, as in the sharp candidate.

The local theorem is proved on an ENTIRE
continuous true-square pose neighborhood,
not from numerical sampling, and its
arithmetic is independently audited in
[verify_eight_angle_mismatch_backbone.py](verify_eight_angle_mismatch_backbone.py).

This does **NOT** prove a sharp local radius
bound. It proves only the mismatch penalties
for five actual pairs under strong locality
hypotheses.

## Next mathematical test: can a positive dual pay for these penalties?

**Do this before any new global contact-case enumeration.**

Take the exact seven directed
separator inequalities of
HUMAN_SHARP_SEVEN_RING_SEPARATOR_CLASS.md.
Allow every square frame to vary independently
but choose the two useful nominal
orientation clusters:

* the five standard-chain frames
  \(A,B,T,D,E\);
* the tilted-pair frames \(H,G\).

The correct **one** next experiment is to:

1. Derive one positive weighted sum \(S\) of
   those **true** seven-square support gaps.
   At internally equal standard and tilted
   frames, it should yield the already
   proved sharp five-corner scalar inequality.
2. Calculate the **actual exact derivatives**
   of S when leaf clusters of frame angles
   are pulled together along the tree
   A--B--T--D--E and edge H--G.
   Seek rational interval bounds
   \[
   |\partial_{\rm cluster}S|\le\beta_e
   \quad\text{and}\quad
   \beta_e\le\lambda_e\eta_e/2.
   \]
   Our local exact
   \(\eta_e/2>7/100\) is an
   available starting margin per relevant
   pair **before weighting**.
3. If these inequalities succeed, apply
   the elementary **tree-contraction
   lemma** to scalar angle arguments.
   The comparison yields the sharp bound
   even when A/E frames differ physically.
   The independent **relative tilt**
   remains for the already established
   HUMAN_FAMILY_CLOSURE.md optimum.
4. If these inequalities **fail on the
   real candidate neighborhood**, keep
   the failure certificate and reject
   this proposed dual rather than adding
   small case-specific adjustments.

This is testable without solving the
full arbitrary eight-square topology.
Its output would be a useful
**orientation-robust conditional
seven-square sharp theorem** and would
remove a major rigidity assumption
from the current global bridge.

## But one global extraction problem would remain

The 11-square paper DOES NOT prove
globality from angle penalties alone.
It first uses a **12-point ownership
cover**, compulsory convex cores and
full-domain interval/SAT exclusions to
force every potential improvement
into a small pose envelope.
Only *then* does its mixed-angle
analytic theorem finish.

For our disk, the analogous remaining
step is to force the **genuine directed
seven-square support owner families**,
or prove a different universal sharp
bound for other families.
The 11-square 12-marker cover depends
on a **square container's walls**;
it does not give a circular disk
marker cover. The analogous disk
ownership/capture theorem must be
newly proved. We already have a
unique origin-containing square and
angular exterior marker facts, which
are reasonable ingredients but do not
by themselves select the five-corner
separator directions.

The 11-square paper also has a
directional **two-square strip-shadow**
lemma: two squares in a sufficiently
shallow straight strip dominate the
support of a virtual two-square row.
It is potentially useful for replacing
actual disk-cap chains by **necessary
support inequalities**. However it
requires a **common separator normal
in a specified cone**; pairwise
disjointness from the two real
squares alone does NOT justify a
virtual row. Do not use it as
an unproved geometric occupancy fact.

## Proof status / software trust

The 11SquaresOptimal README describes
a computer-assisted certificate
proof, **not a completed Lean proof
or independently refereed result**.
Its paper/README.md reports
completed component checks but
explicitly says the *portable full
replay of the revised supplement*
has not yet been executed end to end.
The earlier PROOF.md follows a
different, larger certificate
reduction and states its own
software trust premises.

Accordingly the transferable
mathematical ideas above are
rederived locally; no unverified
global 11-square proof claim is
imported as an axiom.

**Bottom line:** prioritize ONE
"mixed-angle sharp seven-separator"
positive-dual test. If it works,
the global remaining problem becomes
**capturing the genuine separators**,
not **forcing parallel end squares**.
The unconditional eight-square
\(R_8\ge\widehat R\), global
equality classification and Lean 4
proof are still OPEN.
