# Non-author review of the B16a 75-node and 203-node checkpoints

Review date: 2026-11-05. Result: **PASS_SCOPED_NONAUTHOR_REVIEW**.

I reviewed the manuscripts, source bindings, complete finite covers, newly
added terminal arguments and native transport of the two checkpoints below.
I did not author either checkpoint. No defect was found in their stated
partial results. This accepts a reusable partial proof for the merged I21/I22
rectangle of original `negative-16a2fc93c8d133f0`; it grants **zero original-cell
or mask closures**. It is not a standalone cold proof or a whole-proof audit.

The reviewed committed files were read at `faf4aed` and copied from Git into
this review's `published/` directory because the active sparse checkout did
not contain them. `REVIEW_IDENTITIES.json` gives the full commit ID and exact
SHA256 and byte size of every reviewed published file, every indexed native
input and every source pin in the two existing full replay reports.

## Exact subjects

Paths below are relative to `research/nine/computer_assisted/`.

| Subject | 75-node checkpoint | 203-node checkpoint |
| --- | --- | --- |
| Directory | `a2_00100_b16a_75_native_checkpoint_20261105` | `a2_00100_b16a_hi_cover_native_checkpoint_20261105` |
| README SHA256 | `91bd358a4e4d2de783f24ddf5345ddeeb21b0825b78fe778f2a552eb157ab30a` | `0f7d114a510bdfa545844d320ef927baa724d8c7649f3f2787a490c9ec166b1b` |
| MANIFEST SHA256 | `752f33cec22aceed6b9c10bd57bc428b3d3b2d5bd1238a0926433af03b612e3c` | `b789f6441da3eda321454b7f98cebcfcdcbd16ba8cf87c045936956cedc63be4` |
| INPUTS SHA256 | `e34a99bd6c8eb8bd8426895864ebb4f92db0e9e510518c12d4809f5ff54afc94` | `5a91d029da8526f1e1f107fb0e66a12e96814ec90bb597aef3f19fc1cba18797` |
| Archive SHA256 | `a6089f712ff8107dd58222d43b9869cc607aa4017e9e3b9fb91a3e69a36c043c` | `f34dbf2278d05692a1b0f8bba015042b693c32f8c268bfa44a3ddb5c137ebabb` |
| Archive bytes | 6,248,776 | 6,556,440 |
| Fresh full replay JSON SHA256 | `6f7e6a4d5dfa53304b0800868d343a1efe9d4d4a6c63164d55330737abe79cdb` | `c1131fd11525fa929d85ce44188b2354dfbce748d44b92bea0846e49f6edde89` |
| Native manifest SHA256 | `70ecc3432ebd9606af902fcb03c9ebafe9123a5b01ed2a5ab3d248c28ff83210` | `0a6cba31b7b94b40267fe0a2fa0b295acaa3b345602ddcd79eee17700f5f13b7` |

The native manifests are respectively
`/workspace/scratch/f9f48fcfb253/b_work/b16_broad_phase_20261105/manifest.json`
and `b16_hi_cover_v2_20261105/manifest.json` under the same `b_work` root.
The preceding 45-node manifest is
`b16_fresh_interval45_20261105/manifest.json`, SHA256
`941243cf54bde2070916a29c95c1a2bdba7b5c5e8651ec690c1f482788c210db`.
All three use the identical parent `B16A_MERGED_I21_I22_RESTRICTION.json`,
SHA256 `142b74254b59e00267298ea59fa27bef68b392a220f9509aa4a88221f514d5cc`.

## Coverage and newly completed arguments

I wrote a separate exact structural walk. It checks every indexed node is
reachable exactly once; all parent/depth/choice fields agree; all node payload
hashes agree; a proxy split contains all four axis/sign choices; a physical
SAT split contains all eight owner/axis/sign choices; and a slope split
contains both closed halves at a strict interior rational cut. Child states
are reconstructed from parent final states without calling the producer's
child constructors. All other coordinates, premises and path prefixes remain
unchanged. Closed cover status is accepted only when every child is closed.

| Tree | Nodes | Excluded terminal domains | OPEN terminal domains | Complete unions |
| --- | ---: | ---: | ---: | --- |
| Prior checkpoint | 45 | 16 | 14 | 7 proxy, 8 slope |
| First reviewed checkpoint | 75 | 34 | 16 | 12 proxy, 13 slope |
| Second reviewed checkpoint | 203 | 115 | 47 | 12 proxy, 13 slope, 16 physical SAT |

In the 75-node checkpoint the newly completed inherited regions are precisely
1, 5 and 13. Regions 1 and 13 have positive-reserve terminals. Region 5 has
20 new descendants and 16 terminal descendants, all excluded:
45, 49, 50, 53, 54, 55, 56, 52, 47, 57, 58, 61, 62, 63, 64 and 60.
Together these account for 18 new exclusions: eight positive-reserve
arguments, nine accepted center interval contradictions and one empty
difference interval. Region 18's continuation remains OPEN.

The 203-node checkpoint retains every earlier record literally. It adds all
eight H/I alternatives at each of the 16 earlier OPEN leaves, giving 128 new
children, 81 excluded and 47 OPEN. Every earlier parent retains at least one
OPEN child. Thus none of those 16 earlier regions becomes completely excluded.
The complete child accounting agrees with the manuscript's per-parent table.
All 81 new exclusions are exact positive-reserve arguments.

## Arithmetic and physical premises

I read the independent replay and cover code, including row validation,
round propagation, weighted terminal checks, physical child construction and
the accepted universal-center row binding and hand proof. The same original
nine squares, original corner and pair constraints, marked cones and links,
and strict weak CD are retained from the accepted parent. The subject remains
the closed rectangle
`x_I in [-163627/2097152,2457813/4194304]`,
`y_I in [-91/120,91/120]`, with strict `q < 1105/256`.

The eight physical H/I alternatives are justified by the separating-axis
theorem for two squares with disjoint interiors: either original supplies one
of its two frame-axis normals, and either sign is possible. Each case uses
the physical support widths and a closed separating inequality. Every owner,
axis, sign and contact face is retained.

For each new positive-reserve terminal, my separate Fraction calculation
recomputed every positive integer-over-2^40 weight, exact weighted RHS and
coefficient, absolute-bound residual and strictly positive reserve. The
necessary rows `c*z <= b` and `|z_j| <= M_j` imply
`c*z >= -sum(M_j*abs(c_j))`; therefore
`-b-sum(M_j*abs(c_j)) > 0` is a contradiction. No numerical feasibility status
or saved LP point is used in this reasoning.

I also freshly ran the existing independent physical row/replay engine on all
44 changed records in the 75-node extension and all 128 new H/I records. This
checks 4,109 and 1,260 printed-row occurrences respectively and validates all
18 plus 81 new terminal arguments. It reconstructs printed rows independently
of the numerical producer and checks propagated bounds, including the
nonweighted interval terminals. The engine's 159 retained premise pins were
rechecked at the end. NumPy, SciPy and HiGHS were not imported by this run.

The accepted universal-center premise is physically valid for each original:
maximizing its four corner norms gives
`r^2 + 1/2 + |c.u| + |c.v| <= 1105/256`, hence
`r^2+r+1/2 <= 1105/256`. At `rho=91/60` the excess is `31/57600 > 0`.
Consequently `r < rho`; rational supporting rows are valid when their
nonnegative RHS `s` satisfies
`3600*s^2 >= 8281*(a^2+b^2)`. The independent checker reconstructs precisely
the two original center columns and checks this inequality. Its accepted
binding and source hashes were retained, rather than replacing this premise
by a numerical initializer.

The already completed full arithmetic reports are reused for the unchanged
original-parent ancestry. Their respective totals are 28 rounds, 3,299
deductions and 11,974/13,234 printed-row occurrences. I verified exact root
identity, all old initial states, preservation of old round prefixes from
45 to 75 nodes, and literal preservation of every already closed old payload.
Every earlier record is identical from 75 to 203 nodes. I did not repeat
those full ancestral computations or re-prove all previously accepted row
families. This is a non-author manuscript/continuation review plus fresh
conditional arithmetic, not a second implementation of every physical row
checker.

## Transport, dependencies and limits

I verified every outer-manifest file hash and read every compressed member.
Every archive member is a regular `sources/<sha256>` blob of the declared
length and digest; there are no duplicate or extra members. The 75-node bundle
has 346 native paths/337 unique blobs and the 203-node bundle has 476/467.
All current indexed native paths were rehashed; the union of the two source
inventories contains 552 paths. Every source pin in the existing full reports
was also rehashed and matched. Their complete identities are recorded in
`REVIEW_IDENTITIES.json`.

These are native recovery bundles. Their source indexes do not purport to
enumerate all transitive files opened by ancestral loaders, and this review
does not certify a fresh isolated installation. The earlier published
ancestry remains required. The manuscripts state that dependency accurately.
The discovery source outside the scratch root in the H/I bundle is retained
as an indexed content blob. Discovery is not a physical premise.

Both full reports explicitly say `PASS_PARTIAL_PHYSICAL_TREE`,
`complete=false`, `whole_original_proved=false` and
`entire_registered_original_domain_retained=false`. The manuscripts agree.
No equality conclusion follows. Completing the surviving domains would still
require joining this restricted rectangle to B16a's other 14 proved I
rectangles before any whole-original credit. The register remains 224/231
originals and 8/32 masks CLOSED. No Lean, Lake, compilation or CI was run.

No mathematical, coverage or byte-binding defect was found within this
scope. The manuscripts' statements that no independent manuscript review
existed were historically accurate for the exact versions reviewed; this
separate report now supplies that limited review. Changing those manuscripts
would create new file identities and must not be described as the exact bytes
identified above.

## Review artifacts

The review command, run from the repository root, was:

```sh
python -B -S research/nine/.runs/review_continue/review_b16_checkpoints.py
```

The script is SHA256
`fb78dac04f3b9177f97a5d78e731b3d0ffb683c63f23b54ea1e2d89587d5b5c8`.
Its structured result `B16_CHECKPOINTS_NONAUTHOR_REVIEW.json` is SHA256
`0cf2119730030a434e6b10ba720ff1da48eb21bb1024b04a63b03f191827e79a`.
The complete file/source inventory `REVIEW_IDENTITIES.json` is SHA256
`12646a5081941351670fa9640f178c3e734501a218ac8dacf08108ae62c0cd06`.
The JSON result includes every changed-record audit and literal rational
terminal reserve. Execution took about 74 seconds. The command assumes the
already restored native ancestry and the exact published files in its local
`published/` directory; it is not a cold-install command.
