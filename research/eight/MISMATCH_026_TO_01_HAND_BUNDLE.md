# Middle candidate mismatch: the complete proof bundle

The proved implication is

\[
S\le13/50\quad\Longrightarrow\quad S<1/10.
\]

Its full hypothesis is the candidate boundary cycle at
`Q = 3.915534138`, the previously proved G/T/H/D tangent cuts, and
the reflection normalization of E. Both signs of A and B and all four
original separating axes are retained. The charge is `1/400` on
edges 0, 2, 3, 4 and 5. The two mixed edges have their full angle ranges.

The continuous proof is in
`MISMATCH_026_TO_01_AFFINE_HAND_THEOREM.md`. Every one of its
131,255 fixed rows passes exact arithmetic; all 123,168 original-axis
angle chains and all 18 state domains have complete closed covers.
The table uses 401 arcs, 354,398 polynomials and 2,903,573 coefficient
lower bounds. The minimum strict cost bound is
`76173/20000000000000`. The exact cyclic contradiction has reserve
`18173/2712000000` over `710/113 > 2*pi`.

## Reproduce the supplied fixed arithmetic

The two large logical inputs are supplied as ordered raw UTF-8 parts.
Reconstruct their exact original bytes before running the checks:

```sh
python restore_mismatch_026_to_01_hand_inputs.py
python audit_mismatch_026_to_01_hand_assembly.py
python audit_mismatch_026_to_01_independently.py
python replay_mismatch_026_to_01_hand.py
```

The restore script checks every part and the two complete-file hashes.
It refuses to overwrite a differing input. An isolated reconstruction
and a second idempotent invocation have both passed. Reproduction uses
no optimizer or adaptive domain subdivision.

The optional full coefficient output can be retained with

```sh
python replay_mismatch_026_to_01_hand.py --save-full
python compact_mismatch_026_to_01_report_independently.py
```

The second command independently scans every explicit coefficient list,
its printed minimum and its ordered result index. If a compact file
already exists, it checks mathematical equality without modifying it.
The full output is optional in the repository because its hash and every
compact polynomial record are bound by the supplied input and kernel.

The manifest binds the complete theorem, all fixed inputs, author
assembly, independent review, and this byte-exact storage arrangement.
The conclusion supplies the sign bootstrap and the next contraction
`MISMATCH_01_TO_015_AFFINE_HAND_THEOREM.md` without assuming either
conclusion in its own premise.
