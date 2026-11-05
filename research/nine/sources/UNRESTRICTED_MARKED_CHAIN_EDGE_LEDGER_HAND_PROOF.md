# Marked completed chains: exact weak-edge ledger

Hand lemma and finite *structural bookkeeping*, 2026-11-01 America/Chicago.
No Lean, CI, proof script, or numerical search. These elementary deductions
use the already-published rotating-frame extraction; they do not close A.2.

## 1. Definitions and a weak-edge theorem

Fix any orthonormal coordinate frame. For a physical unit square S write

\[
 h_S=\tfrac12(|e_x\cdot u_S|+|e_x\cdot v_S|)
     =\tfrac12(|e_y\cdot u_S|+|e_y\cdot v_S|),
 \qquad \tfrac12\le h_S\le\tfrac1{\sqrt2},
 \qquad g_S=\frac1{4h_S}.
\]

The centered axis-aligned square of halfwidth g_S is contained in the
physical S. Thus g_S<=h_S. Distinct physical squares S,T in the packing
have disjoint open interiors, hence their contained g-squares do also.

Write d=x_T-x_S>0 and v=y_T-y_S. The closed-tie completed x-order is

\[
 S<_{P_x}T
 \iff \bigl(d\ge h_S+h_T\bigr)\ \lor\ \bigl(d\ge|v|\bigr).
\]

Call the edge **weak** when it belongs to this completed order but is not
an actual x-projection comparison, i.e. d<h_S+h_T.

**Lemma 1 (all conditions on a weak edge).** Every weak edge satisfies

\[
 \boxed{g_S+g_T\le d<h_S+h_T,\qquad
        |v|\le d<h_S+h_T.}                          \tag{1}
\]

It is exceptional for both physical coordinate projection orders. Moreover
a physical separating normal for this pair cannot be parallel to either
coordinate axis. In particular the two squares cannot both be aligned to
the chosen coordinate frame.

**Proof.** Since the actual comparison fails, the completed comparison
must have come from d>=|v|. If d<g_S+g_T, then also |v|<g_S+g_T,
making the contained aligned g-squares overlap with positive area, a
contradiction. This proves (1). Both actual coordinate projections overlap
because d and |v| are strictly smaller than h_S+h_T. A physical axis-parallel
separating normal would require one of those two inequalities to reverse.
Finally, if both physical squares are aligned, h_S=g_S=h_T=g_T=1/2,
so the strict interval for d in (1) is empty. QED.

The owner of an oblique separating normal, its sign, and its slope remain
unrestricted; equation (1) does **not** make d a physical x-separation.

## 2. Nonconsecutive comparisons are always physical

**Lemma 2.** If S<_{P_x}T<_{P_x}U, then S<_x U is an *actual*
x-projection comparison.

**Proof.** Every completed comparison is also a comparison between
the contained g-squares, so

\[
 x_U-x_S\ge g_S+2g_T+g_U
          \ge\frac4{2\sqrt2}=\sqrt2
          \ge h_S+h_U.
\]

The same argument applies to completed y-chains. By transitivity,
every comparison between nonconsecutive members of any completed chain
is an actual projection comparison. QED.

The lemma applies at coordinate-gap ties and at weak physical contacts.

## 3. Exhaustive marked-edge masks, but not a geometric proof

The already-published rotating-frame argument guarantees, for every
nine-square packing in the closed Q-disk, two vertex-disjoint completed
chains of lengths four and three along one coordinate direction.
Their three plus two consecutive links may be marked actual (0) or
weak (1). Lemma 2 makes every other within-chain link actual.

Hence there are at most 2^5=32 formal binary masks before equivalence.
The all-actual mask (000,00) is settled by the published sharp physical
4+3-chain theorem. The new
[middle-link terminal](COMPLETED_MIDDLE_LINK_SHARP_TERMINAL_HAND_PROOF.md)
also excludes the entire nonzero mask (010,00), even at q=Q: its two
actual outer links and the middle maximal-coordinate inequality recover
the sharp long span with a strictly positive orientation reserve.
Thus at most 30 other masks remain as a *bookkeeping universe*.
Many may be geometrically impossible, and the masks do not
replace the continuous orientation, center and physical-separator
constraints. No distribution of masks by canonical root, and no
exclusion count, is asserted.

A weak edge is a genuinely coordinate-exceptional physical pair, but
one marked weak edge in the selected seven squares does **not** imply
that the entire nine-square packing has at most one exceptional pair.
The complete one-exception theorem may be invoked only after checking
all original pairs.

## 4. Exact outsider-distribution ledger for an actual four-chain

Suppose the four-chain is already physically x-separated and q<Q.
The two published unrestricted four-chain theorems give all five outsiders
|x|<13/12, and bound the number in each side column

\[
 L=\{x\le-29/60\},\quad
 C=\{|x|<29/60\},\quad
 R=\{x\ge29/60\}
\]

by |L|<=2 and |R|<=2. The complete arithmetical list of possible
occupancies (|L|,|C|,|R|) is

| Left | Center | Right |
|---:|---:|---:|
| 0 | 5 | 0 |
| 0 | 4 | 1 |
| 0 | 3 | 2 |
| 1 | 4 | 0 |
| 1 | 3 | 1 |
| 1 | 2 | 2 |
| 2 | 3 | 0 |
| 2 | 2 | 1 |
| 2 | 1 | 2 |

The new
[outer-link endpoint reserve](OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md)
extends this same nine-row occupancy cover to a completed four-chain
whose two outer links are actual, even if its middle link is weak.
It proves the outsider strip and both side capacities afresh from an
endpoint budget retaining the middle orientation excess; the internal
square consumes its marker without an assumed side-band center.

This is only a finite occupancy cover. It does **not** imply y-ordering,
coordinate separability, or a physical 4+3 terminal, and does not count as
any newly excluded nine-body configuration. Every row retains all nine
physical squares and all 36 original pairwise disjointness predicates.

## 5. Closure obligations

To close A.2 via this ledger, prove for **each remaining physically realizable
marked mask**, retaining both unselected squares, either an exact
contradiction at q<Q or a derived caller to an already-proved sharp terminal.
In the actual-four mask, complete the nine occupancy possibilities above
with all oblique and mixed-sign separating normals. No unproved “row
alignment,” no replacement of a physical square by only its inset for
the final sharp terminal, and no imported coordinate cover is permitted.

The sharper [pure center-cone extraction](CENTER_CONE_ROTATION_AND_ADJACENT_FIRST_BIRTH_HAND_PROOF.md)
can now be used: every selected edge, including an actual edge, has a
maximal coordinate center gap. At a first-birth frame the entering tie
joins adjacent old rows. This strengthens the edge data, not a physical
separator or a proof of the remaining masks.

The sharp target is Q=1105/256. A.2 remains OPEN.
