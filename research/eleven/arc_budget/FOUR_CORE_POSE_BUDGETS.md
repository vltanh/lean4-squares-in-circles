# Necessary individual pose budgets in the four-core case

Assume the four-core branch at \(q\le49013/10000\): exactly four centers
have radius at most \(41/40\), and the other seven are ring centers. Let
\(W\) denote the three-circle weight in `WEIGHTED_ARC_EXCLUSION.md`, and
\(V\) the six-circle weight in `FOUR_CORE_EMPTY_SHELL.md`.

The certified per-square lower bounds and total circle budgets imply the
following upper bounds for each individual pose:

| Square class | Three-circle budget | Six-circle budget |
| --- | --- | --- |
| Core | \(W<132319/100000\) | \(V<118319/100000\) |
| Ring | \(W<80319/100000\) | \(V<73319/100000\) |

These are necessary conditions on arbitrary orientations, not sufficient
conditions for a pose to occur in a packing. They remain valid after any
other ring-radius refinement.

For the three-circle profile, every other square contributes at least
\(3(43/50)+7(17/50)=124/25\) when the selected square is core, and at least
\(4(43/50)+6(17/50)=137/25\) when it is ring. Since the total is at most
\(2\pi<628319/100000\), subtraction gives the displayed strict bounds.
The six-circle profile gives other-square totals
\(3(33/40)+7(3/8)=51/10\) and
\(4(33/40)+6(3/8)=111/20\), respectively. The rational pi inequality follows
from the already audited Machin-series upper bound in `exact_arcs.py`.

Consequently, for either class, any canonical own-frame center box whose
shared contained rectangle has weighted circle measure at least one of
its corresponding upper bounds is impossible. This is a sound additional
box-discard predicate. It uses the same outward exact arc lower bounds as
the existing cover checkers; no estimate at the box center suffices.

More generally, any collection of selected pose boxes can be discarded
when the sum of their certified weighted lower bounds, plus the existing
class lower bounds for all unselected squares, reaches the rational total
upper bound \(628319/100000\). This is a coupled pruning rule even when no
one selected pose violates its individual budget.

The statement supplies certified pruning predicates. It does not claim
that a complete packing-domain search using these predicates has closed.
