# Normalization certificates and independent replay

These programs accompany `../NORMALIZATION_PROOF.md`, based on the user-supplied
normalization manuscript and certificate package. The hand proof, its scalar
obligations, direct numerical certificates, and Lean formalization are distinct
layers. A successful executable audit is not a Lean kernel proof.

## Local execution

Run from this directory in a fresh Python process:

```sh
python test_replay.py
python replay_rational.py --log RATIONAL_REPLAY_LOG.md
```

`replay_rational.py` selects `rational_arb_compat.py`: an independent,
standard-library-only interval implementation with endpoints in units of
`2^-96`. It does **not** import or execute python-flint/Arb. Integer-directed
rounding, integer square roots, Taylor polynomials with explicit remainders,
and critical-point inclusion are implemented in that file.

The native entry point requires the supplied package's `python-flint`
dependency and is separate:

```sh
python run_all.py --log ARB_REPLAY_LOG.md
```

Do not label a rational replay as an Arb run. Use separate log filenames.
The runner records the selected backend, Python version, source SHA-256 hashes,
counts, closure reasons, and unresolved boxes. An unresolved box or failed
scalar obligation results in failure, not acceptance.

The optional sharpness controls can also run with the independent backend:

```sh
python -c "import sys; import rational_arb_compat as r; sys.modules['flint'] = r; import sharpness; sys.exit(0 if sharpness.main() else 1)"
```

A control returning 'not certified' is evidence about checker sensitivity,
not by itself a certified counterexample or a proof of a sharp optimum.

## Verification inventory

- 78 scalar inequalities, carrying the manuscript's S-labels. The numbering
  has sublabels and gaps; it does not mean 54 scalar tests.
- Four identity sanity checks, I1–I4. Their exact justification is algebraic
  in the manuscript; numerical near-zero checks are not proofs of identities.
- 23 direct certificate groups: L1, L2, five L3 windows, eleven L3-prime
  windows, L6, L7, W/D order, and the A1 and A2 cone groups. A2 combines 36
  central-coordinate boxes.
- 14 positive/negative sharpness controls in `sharpness.py`.
- Regression tests for arithmetic enclosure, interval coverage, critical
  points, fail-closed traversal, and the `cx=c0` boundary witness.

The scalar table's sampled diagnostic minima are **not certified lower
bounds**. Acceptance is determined only by the interval comparisons. Direct
acceptance requires an empty unresolved-box list.

## Important logical boundaries

Lemma A concerns **cx > c0**, not cx = c0. The cone predicate uses the hand
CE/OWN exclusions from Proposition A on this restricted domain; it is not an
unconditional theorem about every point of its enclosing closed central box.
The regression test retains an explicit feasible east-square witness at
cx = c0 with marker zero.

N23 is proved before sectors and pins. The sector-first derivation in the
preserved historical manuscript is superseded. N26 requires **both opposite
helpers to be cardinal**. N27 uses the existing Appendix A only after its
full central-box, ordering, chart, and separator hypotheses are established.

The supplied direct branch-and-bound checks supplement the hand argument;
no multidimensional certificate is imported as a Lean axiom. This package
does not independently re-audit the retained A1/A2 argument.

## Integration changes relative to the supplied package

The repository version adds explicit backend identification, source hashing,
fixed inventory checks, nonzero failure exits, traversal validation, and a
separate rational replay. Float interval endpoints are conservatively enlarged
before conversion; theorem margins are supplied as exact rational balls in
the runner. These implementation changes are separate from the supplied
mathematical argument and are documented in `../NORMALIZATION_INTEGRATION.md`.

The supplied manuscript's timing, box counts, and Arb log describe its author's
run. Only a separately recorded actual execution supports a local-run claim.
No GitHub runner is needed or used by these commands.
