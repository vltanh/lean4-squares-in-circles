# Nine squares: pen-and-paper proof in progress

The target is to prove that nine independently oriented unit squares with
disjoint interiors require a containing radius of at least
\(\sqrt{1105}/16\). An exact packing attains this radius. **The unrestricted
lower bound and the classification of all equality packings remain open.**

The present task is a pen-and-paper proof, with explicit finite tables where
useful. Lean work is deferred. Numerical searches, certificate replay and
archived success reports are not steps in the proposed paper proof.

Read these documents in order:

1. [Proof draft](PROOF.md): the physical model, attaining construction,
   weighted endpoint inequality, and the exact missing implication.
2. [Proof plan](PROOF_PLAN.md): complete mathematical milestones and the
   standard for a usable table.
3. [Physical-and-cap foundation](FOUNDATION.md): the complete physical
   preliminaries, weighted two-square cap, endpoint criterion, directional
   center capture and sharp three-square half-plane cap, including their
   scalar tables and terminal equality arguments.
4. [Exhaustive extraction](EXTRACTION.md): the complete cone-chain height
   bound, precise Greene input, rotating-rank proof and all-nine diagonal
   event cover, including persistent height four and simultaneous ties.
5. [Actual-four-chain analysis](ACTUAL_FOUR_CHAIN.md): the fixed all-nine
   domain, a stronger endpoint budget, the common central band, and the
   precise surviving geometric implication.
6. [Review of the earlier work](AUDIT.md): what to reuse, what failed, and
   what the old completion counts mean.
7. [Mathematical sources](sources/README.md): the retained arguments and
   exact examples. Dated status remarks in these sources describe their
   original checkpoints; this page and the proof plan describe current work.
8. [Archive and recovery](ARCHIVE.md): the immutable snapshot containing
   the old graph campaign, computational certificates, scripts and handoffs.

The most useful existing argument is the
[physical two-square cap](sources/PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md).
Applying it at two ends bounds a weighted span of four original squares.
Actual projection chains of lengths four and three reach that bound, but
they are only one possible way to do so. The new draft makes the more general
endpoint criterion explicit.

The main difficulty is to connect **all nine original squares** to a sharp
criterion. The existing rotating-frame argument supplies center-cone chains,
whose consecutive links need not be projection-separated. The two omitted
squares cannot both be discarded: an
[explicit rational table](sources/SEVEN_ORIGINAL_ALL_OPEN_MASKS_OBSTRUCTION.md)
realizes every remaining historical mask with seven squares strictly below
the proposed radius.

The foundation and extraction gates G1–G2 are complete at the manuscript
level and have received independent reading. Greene's finite-poset theorem
is stated exactly and remains an explicit classical dependency. These
chapters settle the proof inputs and coverage; the unrestricted geometric
closure is still open. Earlier computational results remain available in
Git history; they are not silently promoted to self-contained paper proofs.
