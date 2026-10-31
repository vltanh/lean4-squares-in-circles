# Current d579 adoption review of the analytic certificate package

Date: October 27, 2026.
Reviewer: `side_return_review`, a noncontributor to the three analytic
replacement proofs and to the eight proposed caller updates.
Repository: `vltanh/lean4-squares-in-circles`, PR11.
Authoritative comparison:
`d579c05a9ba866b568295adef81e3ad7638f003c`.
Earlier complete reconciliation:
`89554b3a6e85aeae2bc56ad3b7a949045a0c1e22`.

**Verdict: PASS for carrying forward the complete accepted 18-file
mathematical package and its eight exact source-specific adoption
updates to d579.** Every frozen package byte and every existing file
reference is accounted for below. The earlier full mathematical and
original-domain acceptances remain applicable because their exact
proof objects and original callers are unchanged. This is a current
adoption review, not a fresh reproof of every earlier prerequisite.
The package has not been published by this reviewer.

The accompanying machine-readable record is
`ANALYTIC_CERTIFICATE_CURRENT_D579_LOGICAL_PUBLICATION_MANIFEST_2026_10_27.json`.
It contains all 18 exact publication objects, their current preimages,
all 62 literal file-reference resolutions, the current bookkeeping
pins, and an acyclic section-level logical join. It separates active
mathematical inputs, prior acceptance records, and historical alternatives;
cross-citations between whole filenames are not mistaken for circular
mathematical dependencies.

## 1. Current source identity and the exact publication boundary

I compared the complete current Git tree with the retained exact tree
at 8955. I independently hashed the full local bytes of all 18 retained
package files and all eight original caller preimages. The following
checks hold simultaneously:

* Every retained package file matches its frozen byte count, SHA256 and
  Git blob in the earlier 20-file manifest.
* Ten retained files are genuinely new at d579. None has silently been
  integrated by an interrupted earlier write or a later graph checkpoint.
* The other eight files have exactly the same original Git blobs at
  d579 and 8955. Their complete retained original bytes hash to those
  current Git blobs.
* The 18 package texts contain 62 distinct explicit references ending
  in `.md`, `.json`, `.js` or `.py`. Of these, 52 are existing remote
  files, all byte-identical by Git blob between 8955 and d579. The
  other ten are precisely the new package files. Every reference
  resolves after publication; no changed or missing file was found.
* The eight proposed updates were read as complete diffs against those
  exact current originals. They change dependency/status/accounting
  prose, retain all old mathematical text and data, and introduce no
  altered hypothesis, geometry, force law, parameter domain or mean.

The eight current preimages are:

| Original caller or assembly | Exact current Git blob |
| --- | --- |
| `SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md` | `41dfa63a4207082eca3a5f33149938d1edf1db23` |
| `FOUR_C6_DIAGONAL_CHANNEL_CAP_EMPTY.md` | `1c11c422358cc3892b09e73f1fefe6b64c28c1ce` |
| `GENERAL_SIDE_CHANNEL_CAP_CENTRAL_INJECTION_BOUND.md` | `9abdde4e5f58b3918e55dc3a209d38c0013956ac` |
| `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` | `453091c80f23e0e1630f3351f139c7f50418c03d` |
| `NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` | `ecf79060dee88a377a248f27fdb182cd10c11f12` |
| `NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md` | `278924e9cde3087e52b67bdad6ccdb2cfd53c917` |
| `NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md` | `eb92e320d141bc00dd1aa2d30d9759e7e3c43a3e` |
| `NINE_RADIUS_TWO_MEASURE_RECTANGLES_ANALYTIC_REDUCTION.md` | `30e2cd8f1a576bc60d608acef8f2c24fc9504cd0` |

There is consequently no changed dependency or caller requiring a fresh
mathematical re-review at this head. The immutable-blob comparison is
the bridge from the earlier full reviews; it is not an assumption that
the intervening branch history left mathematical files untouched.

The old `HANDOFF_PR11_2026_10_25.md` and `TWO_LOAD_PROGRESS.md` in
`cert_8955` are explicitly excluded. They contain stale bookkeeping and
must not overwrite the current versions. The existing frozen
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md` remains unchanged: its
8955 inventory is a dated historical statement. This review supplies
the current d579 inventory instead of changing accepted source pins.

## 2. Exact accepted proof and review objects

I read the complete earlier reconciliation, the complete shared-T
caller audit, all four full source-specific mathematical reviews, the
accepted checkpoint, and the complete staged central-injection caller.
I read all eight adoption diffs. The full proofs and source-specific
reconstructions below are inherited at their exact frozen hashes;
I do not describe a hash match as a new mathematical reconstruction.

| Object | SHA256 |
| --- | --- |
| Three analytic diagonal-cap targets I--III | `1fd224603a90dbeb14c021a4deea53e90c1dd33596b9d6baec3e00f0b9672f5d` |
| Analytic vertical target IV | `d482c3a17acbc0b33a6fff9da5fbabc437b628929cca24965c583108b9934728` |
| Analytic same-nine fixed values | `9a4656cc90ab81200847c8b6958fc6e089fc4b807b401705663304be4f782c4b` |
| Full diagonal-cap root review | `c999c093ae3b9668f3dae1a3c01b94de94c8d1ade3a116eea81ac4c56671157c` |
| Independent full 202/1080 review | `93d899027713aea4ec29cd9b71e4df83bdb10030e7467823aab01503df559da5` |
| Full same-nine fixed-values root review | `cffa5e27f65722aded9ea872279569fbd77eb320d0b8412c6bf53277bcfe0fd9` |
| Independent full fixed-values and same-nine join review | `f6348d01f97f7c237c234976dabbb06327fa69153bcc7cda86c7c851a3cf7864` |

Those earlier full reviews reconstruct the mathematical proofs and
their complete original domains independently of the authors. The
8955 review separately read the eight complete originals, three new
proofs, caller audit and all four reviews, checked the whole caller
joins, and accepted the eight adoption patches. Its exact hash is in
the manifest. The present comparison preserves that complete chain.

## 3. All four original diagonal-cap inequalities: 202 to zero

The original balanced diagonal-cap proof is still the complete geometric
SAT argument, with its positive-denominator reductions, monotonicity,
safe unsquaring and the auxiliary tuple in its Section 6. The analytic
proofs replace exactly its original four scalar obligations:

| Original target | Former coefficient comparisons | Active proof |
| --- | ---: | --- |
| I, complete first angular rectangle | 20 | Endpoint bounds, whole-interval concavity and a positive affine comparison |
| II, complete second angular rectangle | 20 | Whole-angle monotonicity to the same endpoint |
| III, complete W-owned sector | 36 | Exact comparison to the 45-degree endpoint and one completed-square bound |
| IV, complete vertical rectangle and its auxiliary tuple | 126 | Monotonicity, strong convexity of boundary values and a curvature bound on the full strip |
| **Complete balanced packet** | **202** | **Zero Bernstein coefficient comparisons required** |

The original closed angular and height endpoints are included. The
vertical source adds no `R>=2` or `h<b` hypothesis to its scalar
theorem. Consequently it covers the auxiliary original tuple as well
as the actual geometric tuple. The original positive quantities are
established before division or unsquaring.

The full-mask local diagonal cap uses this exact balanced input in
Section 2. Its physical radial endpoints, including `b=1/2` or
`d=1/2` and either individual circle weight zero, lie in the same
closed analytic domains. Its complete asymmetric branches are
unchanged. Thus this is a complete original-domain replacement,
not only a scalar fact with an unproved physical caller.

The first manuscript's historical intermediate accounting removed 76
and retained 126. The vertical manuscript supplies those 126. The
accepted total is 202, counted once; the intermediate numbers are
not additional retirements. The old coefficient appendix remains a
valid historical alternative and is not deleted.

## 4. The 1080 packet is bypassed by the current whole bare-C6 caller

The separate shared-T packet has exactly
`209+91+375+405=1080` coefficient comparisons. Its exact torque is
`F=S[A-(1-ell)B]+ell*C*A=0`, with F itself rather than F/S.
The complete earlier audit checks both old bare-C6 uses: the all-unique
side-capacity path and the incident-radial high-angle transfer,
including its `alpha=pi/4` endpoint and unequal actual circle weights.
Every original source on those paths is unchanged at d579.

The current full caller is the central-injection source, Sections 1--4.
It is still explicitly named by the accepted current `M6.B6.C6.ALL`
gate. Its six unchanged actual load orbits are exhaustive. The long
three-load orbit and adjacent-zero four-load orbit use their complete
long-channel exits. The alternating three-load orbit, the two other
four-load orbits and the five-load orbit use the one capacity-two
injection, with all three original extras retained.

For that injection, a central extra maps to itself; an exterior extra
maps to the actual side transmitter of its occupied pocket. The local
cap-one theorem makes the assignment injective. Actual inner-square
restrictions, transmitter proximity and port margins put every image
in the complete near-origin angular obstruction. Diagonal pockets
are empty by the full-mask local cap. All physical masks, individual
weights, true degrees, selected normals, genuine means and physical
zero-stress contacts remain unchanged.

The manifest records the important section boundary: the proximity
input is `FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md`,
Sections 1--4. Its older Section 6 whole-C6 mask assembly is not used.
Neither of the two old shared-T callers is on this active route.
The resulting zero required comparisons are scoped to the **current
whole bare-C6 caller**, not to every possible rooted or unfinished
caller in the repository.

This caller requires the entire selected positive component to be a
simple cycle. No positive chord, root leaf, attached force or extra
unit is deleted to obtain that premise. The old rooted C5 reference
drift identified by the independent audit remains historical and is
not silently promoted into a new rooted-family acceptance here.

## 5. The same nine squares have R>2 without external fixed-value checks

The measure, total mass `8997/1000`, five positive weights, full
own-frame normalization and six-region cover are unchanged. All
original open-interior and origin-atom conventions remain. The new
fixed-values proof supplies exactly the two actual line minima,
three actual outer values and the derivative value required by the
existing continuous reductions.

The line source's complete minimization arguments are used before
the new values: the left minimum lies in `(927/1000,928/1000)` and
the right one is exactly `324943/298110`. The atom-free right domain
includes the actual origin-boundary square. The outer source retains
its entire clipping cover and `M''>1/30` on the whole middle interval.
The new value and derivative at `13/12` give `M>3013/3000` over
that entire interval; the initial and final ranges use their actual
endpoint values. No common-rectangle margin is assumed as a premise.

The unchanged analytic rectangle source covers the two remaining
full-region families. Its **fourteen displayed Taylor comparisons
are already transparent analytic arithmetic**, with written rational
reserves. They are not fourteen external computational certificates.
The new source's thirteen displayed Taylor comparisons likewise
follow from one signed Taylor lemma. Radical brackets, positive
squared reserves, rational sums and explicit coefficient identities
remain ordinary visible parts of these proofs.

After adopting the package, the radius-two route needs no external
fixed inverse-angle mass checker, no external derivative checker,
no stored charge margin and no adaptive subdivision. The historical
five-charge and 208-charge checkers remain valid alternatives. Exact
arithmetic used by earlier reviewers checked the printed identities;
execution of those review aids is not a theorem premise.

The conclusion is `R>2` for the **same nine physical units**, because
their disjoint open interiors would otherwise have measure at least
nine. It is not asserted for an isolated six-square core. The current
bare-C6 application uses exactly this same-nine premise before its
cycle/channel arguments, with its original three completion squares.

## 6. Logical joins, accounting and unchanged inventory

The manifest has separate mathematical nodes for the unchanged line
minimization, unchanged outer branch/convexity formulas, the new fixed
values, the complete continuous measure assembly, the balanced scalar
replacement, the original geometric cap, the full-mask cap, and the
uniform C6 completion argument. This prevents misleading file-level
cycles: a fixed-value proof uses an old formula, while the updated
old caller uses the new value. It does not require the old caller's
historical checker to prove that formula.

All 18 retained package objects may be staged at their recorded paths
against d579. The eight modified files have exact preimage hashes;
the ten added files have verified absent paths. This report and its
manifest are the two additional current adoption records. They make
the package reviewable without changing any shared ledger or forcing
new graph accounting.

| Exact scope | Former required external packet/check | Adopted route |
| --- | --- | --- |
| Whole balanced diagonal cap, including the auxiliary tuple | 202 Bernstein comparisons | Complete analytic inequalities |
| Current entire bare-C6 caller | One shared 1080-comparison packet | Both old callers bypassed |
| Same-nine R>2 fixed mass targets | Five mass-checker calls | Five direct analytic lower bounds |
| Same-nine R>2 derivative target | One derivative-checker call | Printed radical/rational proof |

The two distinct Bernstein packets comprise 1282 comparisons on this
scoped C6 route. The six fixed-value checker dependencies are a
different type of obligation and are not added to that coefficient
count. Earlier retired 1559/45/209/288 packets and twelve matrix
certificates are not recounted. No repository-wide certificate-free
claim follows, and unrelated packets and explicit analytic arithmetic
remain under their original scopes.

I counted the original named roadmap rows with
`^- \[([ x])\] \*\*([^*]+)\*\*`: there are exactly 2513 unique
original IDs, 2319 checked and 194 unchecked. The current authoritative
coarse inventory remains 32 closed and 26 open among 58. The exact
current roadmap, ledger, progress and handoff byte/hash records are
in the manifest. This review changed none of them and earns no new
fine ID, original placement or coarse-cell closure.

The unrestricted `R^2>=1105/256` theorem, original equality packings,
older full prerequisite/canonicalization audit and Lean integration
remain open. No Lean run, CI, workflow dispatch, merge, remote write,
normal reselection or physical/certificate modification was performed.
