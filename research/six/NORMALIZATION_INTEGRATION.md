# Supplied normalization proof: integration record

Base reviewed: `4d9754c79c90df8b103e7b218dc316bec58dc43e` (PR #6).

The user supplied `NORMALIZATION_PROOF.md` and `normalization_cert.zip` as the
basis for replacing the normalization package in HAND_PROOF.md. This integration
preserves the supplied proof's terminology and dependency direction.

## Dependency changes to apply

1. Prove the stronger central box (N23) directly from the genuine Seven marker
   gaps by Proposition A / Lemma A, before using any sector or fixed-pin theorem.
   Then derive the coarse bound (N16).
2. Derive chart bounds and axial markers by Lemma B; obtain fixed pins by
   Lemma C and label squares by the bijective pin assignment.
3. Use Lemma D for windows, the single diagonal normalization, separator
   alternatives, and W/D order. Do not reintroduce horizontal reflection.
4. Use cap piercing (K4) for one helper per side and cardinal moving pins;
   Lemma G covers own-primary moving pins.
5. State (N26) only for opposite pairs whose two central separators are both
   cardinal. State the full central box explicitly in Appendix A before using
   that appendix for (N27).

## Verification boundary

The supplied scalar and direct certificates will be retained separately from
the mathematical text. Their supplied log is evidence from the author, not a
fresh local run. A local run is reported only after actual execution, with its
runtime/dependency versions, exit status, and output preserved.

No GitHub Actions or remote runner is used for this work. Source commits are
checkpoints, not proof-completion claims. This initial checkpoint does not
change the global proof status or claim that normalization has been verified.
