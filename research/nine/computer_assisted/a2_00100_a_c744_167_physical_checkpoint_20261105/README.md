# A-c744 physical continuation: complete retained cover

The fresh original-to-leaf replay passes all 167 current records, their original
initial states and old round prefixes, and every complete finite union. The
cover has 124 excluded leaves and nine OPEN leaves. It replaces the prior
118-excluded/14-OPEN frontier without closing the whole original or mask.

Four retained leaf domains (145, 149, 152, 163) exclude directly. Leaf 146
excludes by both closed I-slope intervals meeting at 1/2. Nine other leaves
receive one exact physical bound round each. The full run checks 28,709
deductions and 49,707 printed premises. All nine physical originals, all
corners, all physical pairs, the original path and the old component-3
threshold -3/5 remain in the caller.

The new accepted suffixes use only existing physical row families. An early
numerical screen experimented with a height row whose guard was not valid
on every screened lower interval. That row has no weighted occurrence in
any accepted certificate and is omitted from every accepted payload. The
independent physical reader rejects unrecognized row literals. The actual
accepted half-interval union at leaf 146 uses physical rows alone.

`CHECKPOINT167_FULL_REPLAY.json` records the fresh complete consumer replay.
Historical A1 and endpoint-provider proofs are explicitly reused by identity;
their arithmetic is not claimed freshly repeated. This is a native checkpoint,
not a cold standalone proof. No Lean, Lake, compilation, or CI ran. Original
and mask closure counts are unchanged.

The thin archive ships 15 changed/new payloads and the complete manifest;
152 prior payloads are reused byte-for-byte from the preceding accepted A165
tree in `a_c744_finite_existing_correlations_v2`. `TREE_ASSEMBLY.json` binds
every one of the 167 payloads. `COPY_PROVENANCE.json` binds the new native
source aliases; the existing A1/base, I64 and correlation native dependencies
remain required.

After checking the archive and extracting to a fresh directory, assemble with:

    python -B -S materialize_a167.py --delta EXTRACTED --base PRIOR_A165 --output NEW_A167

With the exact native aliases present, replay with:

    python -B -S EXTRACTED/sources/replay_full.py NEW_A167 NEW_REPORT.json

All old source bytes and prior proof artifacts remain unchanged.
