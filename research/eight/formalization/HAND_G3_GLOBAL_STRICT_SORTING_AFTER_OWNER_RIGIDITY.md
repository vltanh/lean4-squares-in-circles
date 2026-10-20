# Every exterior nearest-axis representative is strictly sorted

## 1. Statement and dependency order

Put \(Q=9789/2500\). Retain an actual G0--G2 seven-cycle
at a common squared circle ceiling \(q\le Q\), with cyclic roles
\((H,G,A,B,T,D,E)\), word \(0101011\), true-core avoidance,
the captured real frames, and actual weak neighboring witnesses.
The same statement holds on the boundary-neighbor domain of
[the boundary bridge](HAND_G3_BOUNDARY_NEIGHBOR_TRANSPORT_AND_E_ZERO_EXCLUSION.md).
Write each sorted own-frame center as \((a_i,-y_i)\), with
\(a_i\ge |y_i|\).

**Strict-sorting theorem.** After the global quarter-owner
restrictions have been proved, every exterior role satisfies
\[
                         a_i>|y_i|.
\tag{1}
\]
There is no assumption about the signs of G or T, the E sign,
the individual errors, their allocation among owners, or entry
into the hard GA0/BT2 class. In particular an actual H or D
diagonal is no longer an admissible stopping endpoint of a
boundary-neighbor transport.

This is a consequence of the **completed**
[global GA-owner rigidity theorem](HAND_G3_GLOBAL_GA_OWNER_RIGIDITY.md)
and the earlier global BT-owner rigidity theorem. It must not be
used as an input to either of those proofs. The earlier
[nearest-axis tie theorem](HAND_G3_GLOBAL_NEAREST_AXIS_TIE_LOCATIONS.md)
left positive H and negative D as possible locations; the
argument below removes exactly those two locations.

All operations used in the proof are physical reflections or
changes of representative at an actual diagonal. They preserve
the original centers, circles, core distances and weak contacts.

## 2. Normalize E and state the owner information precisely

For \(y_E\le0\), the established restrictions say that **every**
actual quarter witness belongs to
\[
 GA,EH\in\{0,1\},\qquad BT,DE\in\{2,3\}.
\tag{2}
\]
For \(y_E>0\), physically reflect the cycle and reverse the
roles by
\[
 (H',G',A',B',T',D',E')=(D,T,B,A,G,H,E).
\tag{3}
\]
This negates every signed tangent and every real frame lift.
On each reversed edge its new error equals the old error.
Quarter projections transform by
\[
                       0\leftrightarrow2,
                 \qquad1\leftrightarrow3.
\tag{4}
\]
The new E is nonpositive, so (2) holds there. Since GA and BT
exchange, as do DE and EH, undoing (3)--(4) gives (2) for the
original cycle as well. Thus (2) is available for either E
sign, provided it is interpreted with the same cyclic roles.

For a boundary-neighbor cycle at an actual \(q<Q\), the global
owner exclusions are still valid. If needed in their proof,
apply the fixed-witness radial-boundary reduction at Q, as in
the global GA theorem. It preserves the selected forbidden
witness and the center rays. This is an auxiliary impossibility
argument; it is not a same-radius transport used in the sharp
or equality proof.

## 3. An actual negative D diagonal would create a forbidden owner

Suppose \(a_D=-y_D>0\). Apply the exact representative change
and role permutation from
[the diagonal-D recoding](HAND_G3_DIAGONAL_D_NEAREST_AXIS_RECODING.md),
Sections 2--3. Increase D's directed nearest-axis representative
by \(\pi/2\), and use the new cyclic roles
\[
       (\widetilde H,\widetilde G,\widetilde A,
        \widetilde B,\widetilde T,\widetilde D,\widetilde E)
                         =(D,E,H,G,A,B,T).
\tag{5}
\]
The same physical configuration is canonically sorted at this
actual tie, has the same surviving word and frame spread, and
retains every physical separation. The recoding sends
\[
                    \text{old GA}\longmapsto
                               \text{new BT}
\tag{6}
\]
with its owner number unchanged. Choose any actual old GA
witness. By (2), its owner is 0 or 1. Consequently the recoded
cycle has an actual low BT witness.

There are exactly two normalization cases:

| New E tangent | Contradiction |
| --- | --- |
| \(y_{\widetilde E}=y_T\le0\) | The actual BT0/BT1 witness contradicts global BT-owner rigidity directly. |
| \(y_{\widetilde E}=y_T>0\) | Apply (3)--(4) to the recoded cycle. Its low BT witness becomes an actual GA2/GA3 witness in an E-nonpositive cycle, contradicting global GA-owner rigidity. |

All hypotheses of those owner theorems are retained: the actual
squares, core avoidance, cyclic physical gaps, word, real lifts,
and weak separators. They do not require the old names of the
four outer anchors to remain fixed. Their own fixed-witness
boundary reduction supplies any boundary-anchor hypotheses.
No unsupported sorted extension away from the diagonal is used.

The zero value \(y_T=0\) is in the first row. A tie between
several actual GA witnesses does not avoid the contradiction:
every low witness is forbidden after this recoding. Thus no
negative D diagonal is possible.

## 4. Positive H and all other roles

Suppose positive H is diagonal. Apply the physical reflection
(3). It becomes a negative D diagonal, and an old BT witness
becomes a low GA witness by (2)--(4). Section 3 was proved for
either E sign and therefore applies to this reflected cycle.
This excludes the positive H diagonal as well.

The earlier nearest-axis tie theorem already excludes both
diagonals at G,A,B,T,E, the negative H diagonal and the positive
D diagonal, using the original wrong-word exclusions and the
physical gap bound. Together with Sections 3--4, this proves
(1) for all seven roles.

For an original packing before boundary reduction, a diagonal
would survive that reduction because each original center ray
and physical square frame are retained. Its boundary descendant
would contradict (1). Thus the conclusion also applies to the
original exterior centers.

## 5. Use in the remaining entry problem

A proposed transport may invoke (1) at a terminal state only
after proving that the terminal state is an actual eligible
boundary-neighbor cycle: its circles, true core, neighboring
witnesses, cyclic order and frames must all remain valid.
An algebraic diagonal candidate without those properties is
not excluded by this theorem.

The theorem removes diagonal stopping events globally. It does
not prove that any remaining primary can be transported to such
an event, or that GA1/BT3 are already globally convertible to
GA0/BT2. Those entry and original-equality obligations remain
separate. No scalar approximation, numerical mesh, new lookup
table, Lean compilation or CI is used in this proof.
