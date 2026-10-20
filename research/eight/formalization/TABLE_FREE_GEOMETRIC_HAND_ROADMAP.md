# Completed table-free hand proof of the unrestricted eight-square theorem

**PR #10:** `formalize/eight-uncompiled-draft`.
**Status, 20 October 2026 UTC:** the mathematical hand-proof chain is complete.
**Scope:** unrestricted sharp radius, attainment, and the complete original
five-parameter equality family. This pass changes hand-proof documentation;
Lean compilation, CI, kernel verification, and further Lean source replacement
remain outside the authorized work.

## 1. Start with the complete theorem

[HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md](HAND_UNRESTRICTED_EIGHT_SQUARE_THEOREM_WITHOUT_TABLES.md)
contains the unrestricted statement, exact stationary definition of q*,
packing-to-boundary reduction, exhaustive primary-owner entry, original-center
equality, and the complete explicit parameter domain with its converse.

The final two joins are

* [Complete same-radius global primary-owner entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md).
* [Original equality through complete entry](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md).

There is no remaining outer-E sign branch, opposite positive-primary branch,
one-negative-BT branch, or original-equality gate. No bound of the form
`S<=3/200` is assumed in this route. The older small-mismatch route remains
an independently proved conditional route and is not needed for this assembly.

Every packing of eight unit squares with disjoint open interiors satisfies
`R^2>=q*`. The exact q* is the unique admissible stationary zero of the actual
five-circle defect. The table-free bracket used here is

\[
 19577/5000<q_*<1957767069/500000000<9789/2500.
\]

At equality five exterior anchors and two orientation groups are fixed, while
two exterior translation sliders and the central square's two translations
and rotation give the complete five-parameter family. The weak domain retains
all contacts and simultaneous separating-axis ties. A whole five-dimensional
box proves attainment and the independent freedoms.

## 2. The forward dependency chain

| Gate | Completed mathematical content | Main proof |
|---|---|---|
| Central core and actual boundary reduction | A unique central square contains the closed radius-1/12 disk in its open interior. Seven exterior squares admit a core/outer neighbor-cycle representative retaining initially selected physical signed axes and frames. | [Central bands](HAND_CENTRAL_BANDS_WITHOUT_TABLES.md), [exterior-frame proof, Section 1](../HAND_EXTERIOR_FRAME_CONCENTRATION.md), [cyclic boundary reduction](../CYCLIC_RADIAL_BOUNDARY_REDUCTION.md) |
| Fixed-ceiling classification transfer | Expand only outer boundary centers along fixed rays. Every initially feasible signed axis, sign, ratio, frame, gap and radial kind survives; recover the already feasible original-radius boundary cycle afterward. | [Fixed-ceiling transfer, Sections 2–3](../HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md) |
| G1: frame and variation capture | Ten whole-domain pair inequalities and a finite odd-walk budget give frame spread below 7/10; the boundary bridge gives both signed variations below 7/10. | [Exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md), [boundary-neighbor bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md) |
| G2: quarter word | A direct seven-word enumeration and six strict continuous exclusions leave exactly 0101011; physical reflection normalizes E. | [Quarter-word theorem](HAND_QUARTER_WORD_SELECTION_WITHOUT_TABLES.md) |
| G3: every-witness owner rigidity | Zero owners are 0/2; GA/EH owners are 0/1 and BT/DE owners 2/3. H,A are positive outer anchors and B,D negative outer anchors. G/T remain arbitrary except for the actual zero-owner implications. | [Global GA-owner rigidity and its completed dependencies](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md) |
| Complete normal-primary entry | Independent G/T preprocessing, sign-free positive-primary exclusion, and all four remaining hard/negative cells reach the hard class at the original radius or give a strict contradiction. | [Complete owner entry](HAND_G5_GLOBAL_PRIMARY_OWNER_ENTRY_COMPLETE.md) |
| Sharp hard class | GA0/BT2 is sharp with arbitrary G/T signs, frame orders, zero owners, E position and mixed owners, under the explicit core/outer E radial alternative. | [Arbitrary-sign, arbitrary-frame hard theorem](HAND_G5_ARBITRARY_SIGNS_AND_FRAMES_HARD_OWNERS_SHARP_REDUCTION.md) |
| Exact constant | Actual circle convexity and continuous minimization give existence and uniqueness of the stationary zero, without a local root-cover premise. | [Stationary existence](HAND_STATIONARY_EXISTENCE_WITHOUT_LOCAL_BOXES.md) |
| Original-center equality | Exhaust every preprocessing source, reapply the hard theorem to untouched boundary states, identify the originally selected physical axes, then apply the positive stationary dual to the original centers. | [Complete original equality pullback](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md) |
| Converse and five freedoms | Explicit anchors, both full slider intervals, seven central SAT conditions, all 21 exterior separations, and an admissible five-dimensional box. | [Equality family without bracket tables](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md) |

These are hand-proof statuses. They do not certify that the historical Lean
import graph now follows this mathematical chain.

## 3. Exact exhaustive normal-entry matrix

Work at one actual ceiling `qL<=q<=q*`. The boundary input has normal H,A,B,D
outer anchors, normalized nonpositive E, arbitrary G/T signs, all original
weak owners, frame spread and both variations below .7, and core or actual
q-outer representatives.

The [uniform-radius primary-pair theorem](HAND_G5_UNIFORM_RADIUS_PRIMARY_PAIR_TRANSPORT.md)
handles HG0/GA1 and the reflected BT3/TD2 pair for every signed total. Its
canceling/noncanceling companions cover genuine negative GA1 with HG2 and
the reflected negative-BT case. They alter only G or T. All five anchors
and the opposite intermediate stay fixed.

Each side has exactly three terminal types:

| G type | Data | T type | Data |
|---|---|---|---|
| G0 | Actual GA0; either HG owner and arbitrary HG error. | T0 | Actual BT2; either TD owner and arbitrary TD error. |
| G+ | GA1 at positive error, HG2. | T+ | BT3 at positive error, TD0. |
| G− | Genuine negative GA1, HG aligned. | T− | Genuine negative BT3, TD aligned. |

Every G+ terminal is excluded for all T types with either E sign. The
checked physical reflection exchanges G and T and therefore excludes every
T+ terminal as well. The remaining four cells are

| Cell | Completed same-radius conclusion |
|---|---|
| G0/T0 | Apply the hard theorem directly. |
| G−/T0 | [Complete negative-GA entry](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_NEGATIVE_ENDPOINT_COMPLETE.md) creates a strict H-anchor circle loss if GA0 was unavailable. |
| G0/T− | [Complete negative-BT entry](HAND_G5_GLOBAL_PRIMARY_ENTRY_ONE_NEGATIVE_BT_COMPLETE.md) creates a strict D-anchor circle loss if BT2 was unavailable. |
| G−/T− | The [two-negative short span](HAND_G5_GLOBAL_PRIMARY_ENTRY_BOTH_NEGATIVE_ALIGNED_SHORT_SPAN.md) permits the first H/G conversion; the complete negative-BT theorem preserves its strict H loss while converting the second side. |

At q<=q*, the hard equality theorem excludes every genuine negative row.
The surviving G0/T0 route uses only the earlier intermediate-only changes.

### The positive-primary proof covers every E branch

| E alternative | Completed obstruction or reduction |
|---|---|
| Core, either sign and all owners/totals | [Sign-symmetric core-E theorem](HAND_G5_COUPLED_CORE_E_SIGN_SYMMETRIC_POSITIVE_ENTRY.md) |
| Outer, nonpositive selected primary error | [Same-state reselection for either E sign](HAND_G5_POSITIVE_GA_OUTER_E_SIGNED_NONPOSITIVE_PRIMARY_RESELECTION.md) |
| Both E secondaries | [All terminal T-owner theorem](HAND_G5_POSITIVE_GA_OUTER_E_SECONDARY_E_ALL_T_OWNERS.md) |
| Sole EH1, either E sign | [Signed-coordinate extension](HAND_G5_SOLE_E_POSITIVE_GA_SIGNED_COORDINATE_EXTENSIONS.md), [positive T](HAND_G5_POSITIVE_GA1_SOLE_E_PRIMARY_POSITIVE_T_EXCLUSION.md), [negative T](HAND_G5_POSITIVE_GA_SOLE_E_NEGATIVE_T_EXCLUSION.md) |
| Sole DE3, nonpositive E | [BT2/TD0 theorem](HAND_G5_POSITIVE_GA_OUTER_E_SOLE_DE_AND_SECONDARY_EXCLUSION.md), the same positive-T and negative-T theorems |
| Sole DE3, positive E | Normalize E on its actual q-circle to E=0 or exact EH0 contact at its existing signed angle. Apply [BT2/TD0 sign-free entry](HAND_G5_COUPLED_OUTER_E_SIGN_FREE_BT2_TD0_ENTRY.md), [positive-T contact extension](HAND_G5_COUPLED_OUTER_E_POSITIVE_T_UNALIGNED_CONTACT.md), or [negative-T contact extension](HAND_G5_EXCEPTIONAL_E_NEGATIVE_T_ARBITRARY_EH_CONTACT_EXTENSION.md). |
| Both E primaries positive | [Same-radius paired-E endpoint reduction](HAND_G5_COUPLED_POSITIVE_E_PAIR_SAME_RADIUS_ENDPOINTS.md) reaches an actual alignment; the sign-free sole-E results cover its output. |

The four T regimes are BT2/TD0, BT2/TD2, positive BT3/TD0, and negative
BT3 with TD aligned. Each ordinary error keeps its actual sign. In the
exceptional positive-E contact argument the EH0 angle stays in H's actual
two-angle force. The exact zero contact residual preserves the sharp split;
the coefficient `max(p,n)` is handled on its whole domain. No E reflection
silently invokes a theorem restricted to the other signed coordinate.

## 4. Original equality and exact radius discipline

The [original-equality theorem](HAND_G5_GLOBAL_PRIMARY_ENTRY_ORIGINAL_EQUALITY_PULLBACK.md)
first proves that actual GA0 and BT2 were already available at the untouched
boundary source. A source with an unavailable hard owner would leave a
positive invariant pair total, a retained strict HG/TD slack, or an excluded
genuine terminal. The [retained-contact rigidity lemma](HAND_G5_HARD_EQUALITY_RETAINED_CONTACT_RIGIDITY.md)
then rules it out at q*. A strict loss at free G/T alone is never used as
an equality contradiction.

Reapplying the hard theorem to the source fixes its anchors and frames.
The selected GA1 and EH0 alternatives are then explicitly infeasible;
zero-frame alternatives share the stationary physical normals. Those are
the initially selected original axes, retained throughout the boundary
recession translations. The positive stationary dual applies directly to
the original centers, fixes five anchors and seven contact gaps, and
leaves the two genuine exterior sliders free.

The two boundary operations must remain distinct:

* Recession translation constructs a boundary cycle from original squares.
  It preserves selected signed witnesses, frames and cyclic order. It need
  not preserve individual center rays or canonical tangent ratios.
* Fixed-ray expansion starts with a boundary cycle. It preserves every
  initially feasible signed witness, rays, ratios, signs and radial kinds.
  Its unconditional monotonicity is the bridge to the auxiliary Q theorems.

For an original radius below qL, first choose the containing ceiling qL
and construct the boundary representative there from the original
witnesses. The resulting anchors are actually outer at qL. Do not merely
relabel earlier outer coordinates as qL-outer. Sharp transports, contact
circles and equality losses always use the actual working q.

## 5. What was completed in the final entry pass

The final pass closes the sole-negative-BT anchor-order and transport gap;
the sole-DE, secondary-E and remaining positive/negative T stress domains;
the paired-E original-radius endpoints; and the reflected E-sign gap.
It joins them in a finite terminal matrix, proves original-center equality
through every entry source, and assembles the unrestricted theorem.

The decisive positive-E extension replaces an unnecessary EH alignment
by its actual exact contact. Its extra H rotation requires the valid
coefficient `max(p,n)`. The base and negative-T rows reuse their existing
whole-domain bounds; the positive-T row adds sixteen explicit H polynomial
constructions, independently checked with 32 exact rational assertions.
All sixteen have margin greater than .002 and enclosure error less than
.000053. These conservative proof bounds are the printed certificate
claims, not sampled numerical minima.

The final interface audit also corrects old attributions of center-ray
preservation to the general boundary translation. The fixed-ray expansion
supplies every needed auxiliary-Q transfer. Stronger pre-boundary diagonal
claims are not assumed by this proof.

## 6. Validation and the separate source-verification boundary

The continuous arguments retain actual weak witnesses, either allowed sign,
shared states, all intrinsic endpoint alternatives, and the original-radius
circle equations. Their scalar appendices use whole-domain rational,
Taylor, coefficient-norm, and polynomial positivity arguments. Exact
arithmetic audits reproduce the displayed constructions; no sampled mesh,
optimizer result, large lookup table, or opaque checker acceptance is a
mathematical premise.

Independent reviews checked the new exceptional-contact H blocks, all sixteen
additional positive-T scalar constructions, the terminal-owner matrix, the
radius-transfer interface, and the final unrestricted/equality assembly.
Documentation checks verify referenced local files and mathematical delimiters.

The historical Lean draft, its generated files, and its remaining import
counts are described separately in [STATUS.md](STATUS.md). No Lean file was
changed in this completion pass. No Lean compilation, lake build, CI,
axiom inspection, or performance measurement was run. The mathematical
removal of a dependency does not claim its old source import was removed.
The PR remains a reviewable hand-proof delivery; it is not a verified
formalization claim.
