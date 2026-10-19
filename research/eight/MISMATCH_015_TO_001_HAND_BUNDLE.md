# Final candidate mismatch: the complete proof bundle

The theorem is

\[
S\le3/200\quad\Longrightarrow\quad S<1/1000
\]

under the exact candidate boundary, tangent and original-axis hypotheses
in `MISMATCH_015_TO_001_AFFINE_HAND_THEOREM.md`. Its complete exact
replay and independent continuous/domain audit both pass.

The two large logical inputs are stored as ordered raw UTF-8 parts.
They are neither compressed nor reserialized. Reconstruct their exact
original bytes before running the proof checks:

```sh
python restore_mismatch_015_to_001_hand_inputs.py
python audit_mismatch_015_to_001_hand_assembly.py
python audit_mismatch_015_to_001_independently.py
python replay_mismatch_015_to_001_hand.py
```

The restore script verifies every part's length and hash, the ordered
concatenation, and the two independently bound complete-input hashes.
It refuses to overwrite a differing existing file. The optional complete
coefficient output can be retained with

```sh
python replay_mismatch_015_to_001_hand.py --save-full
```

That large replay artifact is not needed in the repository: its exact
hash and every compact polynomial record are part of the committed
proof bundle. There is no optimizer or adaptive search in a replay.

The final table has 456 closed arcs, 129,368 complete original-axis
angle chains, 144,709 fixed rows, 399,773 polynomials and 3,183,184
rational coefficient lower bounds. The smallest strict cost bound is
\(3986139/10^{14}>0\). The exact charged cyclic reserve is
\(522599/240000000000>0\).

This result supplies the input of
`HAND_CANDIDATE_CAPTURE_AT_ONE_THOUSANDTH.md`; the mixed-owner, tilt,
automatic-slider terminal and equality-transfer proofs then apply.
