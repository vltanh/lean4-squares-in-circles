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
3. [Review of the earlier work](AUDIT.md): what to reuse, what failed, and
   what the old completion counts mean.
4. [Mathematical sources](sources/README.md): the retained arguments and
   exact examples. Dated status remarks in these sources describe their
   original checkpoints; this page and the proof plan describe current work.
5. [Archive and recovery](ARCHIVE.md): the immutable snapshot containing
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

This cleanup changes the organization and proof strategy, not the status of
the unrestricted theorem. Earlier computational results remain available in
Git history; they are not silently promoted to self-contained paper proofs.
