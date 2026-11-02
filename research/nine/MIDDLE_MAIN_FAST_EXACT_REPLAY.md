# Fast exact replay of the complete middle-main low-floor certificate

November 2, 2026. The completed low-floor certificate has been replayed
with a separate exact C++ implementation. No floating producer bound,
numerical tolerance, external solver, Lean, or CI is trusted.

## 1. Completed result and exact boundary of the claim

The replay passed all **2,821,264 leaves**, **5,642,527 nodes**, and
maximum depth **52**, with an empty final frontier. Its least positive
exclusion reserve was

    360606 / 281474976710656 > 0.

The run took 229,535 milliseconds. Its complete record is
`middle_main_low_floor_cpp_replay.json`.

The certificate proves the low-floor contrary root in
`MIDDLE_MAIN_SIDE_CONE_TRIPLE_HAND_TABLE.md`. The physical hand reduction
and complete occupancy caller are separate necessary parts of the proof.
In particular this root consumes the independently proved high-right
conclusion and the original lower-side main-height bound -17/50. The
complete root and all hand-excluded complements are stated in that
manuscript. This replay does not infer a whole mask from an arbitrary
conditional position cell.

The canonical certificate is `middle_main_low_floor_candidate.json`, with
SHA256

    faf9cc6967ce02412024f0fe90db6298931d0c243bce6cf345ad78dda2785a9c.

The complete certificate is also distributed in the deterministic
695,692-byte archive `middle_main_low_floor_candidate.json.gz`. Its
decompressed bytes are exactly that canonical JSON. The archive SHA256 is

    ad5275e67b28a15d86cea564cd6221149a9c7cf7e4470dfe4762c296e4f8e76e.

The checker source is `verify_middle_main_low_floor_exact.cpp`, SHA256

    96ac00e7069e20dcbf39dfb6e092349773300edc3689549f791f32c6c557bd00.

The independently implemented Python reference retained alongside it is
`verify_middle_main_side_triple.py`, SHA256

    c1e26b7c6184c2636c3eb66c1f267b076f84b852a9c7fe39e6c26e7a2029fe29.

## 2. Arithmetic and complete root coverage

The C++ checker uses signed 64-bit interval endpoints over the fixed
denominator 2^48. Products and division numerators use signed 128-bit
integers. Every interval operation rounds outward by exact integer floor
or ceiling; conversion to an endpoint rejects out-of-range values.
Radicals use an integer Newton iteration, followed by the exact
postcondition r^2 <= n < (r+1)^2. No floating approximation supplies a
radical bound or a leaf decision.

The original seven root intervals are hardcoded independently of the
certificate. Each coordinate cell is represented by its integer dyadic
level and index inside the original rational interval. For example, the
P tangent starts at the rational 1/27 and the left endpoint height starts
at 4421/12000. Their exact rational cells are converted outward to the
48-bit evaluation grid only after tree subdivision. Thus rounding never
defines a split or leaves a gap between children, even at depths beyond
48. The explicit depth budget 60 keeps every rational numerator product
within the checked signed 128-bit range; the actual tree has depth 52.

The parser accepts only the advertised low-floor certificate schema and
the one common leaf rule used by this certificate. It rejects duplicate,
missing, unknown, or trailing fields, unknown split and leaf tags, and
inconsistent counts. A preorder stack reconstructs both children of every
split. At the end it requires an empty frontier, the exact advertised
node/leaf/depth counts, and nodes = 2*leaves-1. The certificate supplies
only split and leaf decisions; all scalar bounds are recomputed.

## 3. Relation to the independent Python mathematical evaluator

The C++ evaluator was written from the separately reviewed mathematical
inequalities and the independent exact Python implementation, without
reading or importing the floating producer kernel. It retains all signed
original frame charts, the shared P-frame owner matrix, exact endpoint
resources, the two proved orientation tolls, the one original main tilt,
and the finite necessary-set contractions.

Several already required contradictions are checked earlier to keep
irrelevant large reciprocals out of the fixed-point implementation:

- A negative upper bound for the nonnegative main tilt rejects that
  branch immediately.
- An upper bound for g1 below 15/31, or a lower bound for e above its
  previously established upper bound, rejects before further resources
  are evaluated.
- A negative endpoint-circle radicand or a lower endpoint inset height
  above 1/2 rejects the same impossible branch immediately.
- A positive lower quotient can be capped at 1000. This only weakens
  that lower bound and is above every relevant physical gap or retained
  halfwidth.
- In a physical cone-gap lower bound, a nonpositive numerator may use
  the necessary bound zero. The actual gap is nonnegative. This avoids
  an unbounded negative quotient without removing any physical case.

These are consequences of the same original necessary inequalities.
They do not impose extra hypotheses or change the root. Their use is
documented in the C++ source. The independent Python implementation uses
80-bit directed dyadics and retains its own complete replay path.

## 4. Reproduction and damaged controls

The source needs a C++17 compiler supporting signed 128-bit integers and
the standard library. A representative build and replay are:

```sh
g++ -O3 -std=c++17 -Wall -Wextra -pedantic verify_middle_main_low_floor_exact.cpp -o /tmp/middle_main_exact
gzip -dc middle_main_low_floor_candidate.json.gz > /tmp/middle_main_low_floor_candidate.json
/tmp/middle_main_exact /tmp/middle_main_low_floor_candidate.json 0 100000
```

The ordinary JSON can also be passed directly if it is already available.
The independent Python checker accepts the same decompressed path through
its `--certificate` option.

The second numeric argument is a benchmark node limit; zero requests the
complete proof. Any positive limit ends with the explicitly incomplete
status `BENCHMARK_ONLY_INCOMPLETE`, never with an acceptance claim. The
third argument controls progress reporting. Acceptance requires the final
`EXACT_REPLAY_PASSED` record and a successful process exit.

Four deliberate damaged controls were rejected: the wrong root family,
an unknown leaf tag, a split missing both children, and a forged single
leaf claiming to exclude the whole root. The last control reached the
mathematical evaluator and failed its strict exclusion test. The complete
control record is `middle_main_low_floor_cpp_negative_controls.json`.

The `recover_low_floor` agent independently reviewed the signed rounding,
integer square root, product ranges, exact root-cell conversion and full
parser/tree skeleton. The `whole_mask` agent independently reviewed the
complete formula parity, all signed coefficients, the same-P-axis
shortcut, exact main-support monotonicity, all 16 owner pairs, the three
linear sweeps, the three chirality-union-hull repetitions, and every
intentional early-cut difference. It found no gap and separately
reconstructed the full JSON tree and compressed-archive identity. These
are agent reviews; no human review or proof-kernel certification is
claimed.

The complete separate review is
`MIDDLE_MAIN_LOW_FLOOR_CPP_INDEPENDENT_AUDIT.md`. Its supporting records
are `middle_main_low_floor_independent_structure_audit.json`,
`lower_side_main_17_50_independent_replay.json`, and
`lower_side_main_17_50_printed_table_audit.json`. The latter two also
independently check the complete physical reduction and every printed
row of the supporting -17/50 theorem.
