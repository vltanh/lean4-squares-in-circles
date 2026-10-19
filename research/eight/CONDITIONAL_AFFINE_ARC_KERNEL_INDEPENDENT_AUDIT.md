# Independent audit: conditional affine-arc frame and axis domains

**Result: PASS for the stated conditional interface.** The new range and
axis restrictions are explicit hypotheses; the checker does not prove
that an arbitrary packing satisfies them.

The reviewed sources are:

| Source | SHA-256 |
|---|---|
| `candidate_hand/verify_affine_arc_hand.js` | `1bd04b7b8890f7008108489da6fdf24b947e472eb4873f7523994ce4b81b85ee` |
| `candidate_hand/verify_conditional_affine_arc_hand.js` | `6af3d41fe7d404da7dd286c46644160f5444edd3028d864701266e9a4cd18697` |

The first is the previously independently approved full-domain kernel.
I compared the complete sources. The rational arithmetic, circular/core
support rules, SAT normalization, radical majorant, polynomial construction
and Bernstein acceptance are unchanged. The only mathematical additions
are intersection with declared signed frame-difference intervals and
restriction to declared original forward axes. Input validation and an
explicit hypothesis record accompany those changes.

## 1. The signed range intersection

For an original directed edge `i`, write

\[
 \phi_i=k_i\pi/2+\epsilon_i,
 \qquad \epsilon_i\in[d_i^-,d_i^+]\subseteq[-.7,.7].
\]

A scalar row uses `phi_i=k_i*pi/2+r*x`, where `r` is `+1` or `-1` and
`0<=x<=.7`. Therefore the declared extra interval for x is exactly

\[
 [d_i^-,d_i^+]\quad(r=1),\qquad
 [-d_i^+,-d_i^-]\quad(r=-1).
 \tag{1}
\]

The code implements (1) before any source/target exchange. It takes the
maximum of the three lower bounds and the minimum of the three upper
bounds: zero/.7, the existing physical-gap interval, and (1).
All endpoints of the new declaration are exact rationals.

The existing physical interval comes from

\[
 19/25<\delta_i<710/113-114/25,
 \qquad \phi_i=\delta_i-\alpha_s+\alpha_t.
\]

Its lower endpoint uses the largest source angle and smallest target
angle; the upper endpoint uses the opposite extrema. The old outward
enclosures and the negative-r transformation remain unchanged. Intersection
with (1) therefore covers every actual pair satisfying the declared
signed range. The cache is keyed by the original source/target identifiers,
quarter and r; ranges are fixed per original source role, so no incompatible
restricted domain can reuse a cache entry.

A declared point range, including `[0,0]`, is retained. A required interval
is discarded only when its lower endpoint is strictly greater than its
upper endpoint. The closed-chain routine still requires a row covering
each nonempty isolated endpoint.

## 2. Original axes remain the coverage indices

The declaration `axis_domains[i]` is a nonempty subset of the original
four forward axes. The coverage loop uses exactly those original axes,
and row groups keep the original edge, source, target, axis and r.
Only the separate row-proof routine normalizes target axes by reflecting
and reversing the two states. Thus a declaration for original axis 2
cannot accidentally certify only a row originally indexed by axis 4.
The analogous statement holds for axes 3 and 1.

If a preceding theorem restricts the actual separating axis to the stated
set, one of those rows supplies the pair bound. If an axis set instead
defines a wrong-owner exclusion theorem, the resulting statement is only
for those specified wrong axes; an independent full-SAT baseline or the
appropriate union is still required for a cyclic budget. The checker does
not infer either owner premise from the restricted cover itself.

The new validator rejects an empty axis list, duplicate or unknown axes,
unknown edge keys, reversed difference ranges and ranges extending beyond
the hand frame interval. Omitted declarations default to the full range
and all four axes. The seven edge targets and optional nonnegative width
charges are also checked explicitly.

## 3. Independent interface reconstruction

The companion `audit_conditional_affine_arc_kernel.py` uses a deliberately
empty pair-row fixture with positive-length tangent cuts, both boundary
kinds, positive and negative state signs, asymmetric signed difference
ranges, and differing original axis sets. It independently reconstructs
the necessary angles with direct rational arctangent series, rather than
the production half-angle formula.

All **56 required chains** agree with the independent list. All **112
displayed outward endpoint comparisons** pass, including **16 isolated
zero-angle chains**. The empty-row table correctly reports `INCOMPLETE`;
it is not treated as a proved pair table. With the extra declarations
omitted, the complete old and new coverage/error outputs are identical.
Six invalid declaration fixtures are all rejected. The two source hashes
are checked both before and after this reconstruction.

The exact record is `conditional_affine_arc_kernel_independent_audit.json`.
This exercise verifies the newly introduced indexing/intersection logic;
the approved base proof continues to justify each scalar row's arithmetic
and continuous support theorem.

## 4. Calling conditions for a completed theorem

The calling assembly must supply the same valid geometric state interface
as the approved base kernel: actual outer/core boundary pieces, exact
nonempty tangent cut intervals, the physical gap hypotheses, and a
complete closed state/angle cover. A successful collection of scalar rows
without `cuts` is only a collection of conditional row inequalities;
whole-domain use requires `cover.status = PASS` and the independent
state-domain assembly. Degenerate state-cut declarations are outside this
calling interface; point **angle** ranges are included as proved above.

The additional signed frame ranges and axis-domain hypotheses must come
from previously proved hand gates with matching roles, orientation signs
and radial scope. Subject to those stated premises, the conditional source
is a sound extension of the frozen base. This audit supplies no numerical
discovery premise and does not claim the later D-tangent exclusion or the
final candidate capture.
