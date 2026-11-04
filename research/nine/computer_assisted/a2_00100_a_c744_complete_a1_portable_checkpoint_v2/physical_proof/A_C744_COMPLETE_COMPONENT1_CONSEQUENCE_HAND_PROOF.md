# Complete A component 1 and its necessary height inequality

## Scope and completed source

Fix the unchanged original cell `positive-c744bc031d40ee64` of mask `001/00`
at squared radius `1105/256`. Its registered path is

```text
[['angle',3,1], ['angle_cut',[0,'0'],0], ['inward_row_escape',[7,8],[4]]]
```

All nine original squares, all 36 original corner predicates, all 36
physical pair predicates, the five marked center cones, actual AB, BC, EF
and FG links, the strict weak CD link, and all shared equality faces remain
in the source and in every consumer. There is no relabeling, selected SAT
case, child orientation interval, or child bound transported to the whole
original.

The source is the entire closed component 1 of the accepted actual-AB
five-member complement:

\[
 y_B-y_D\le-\frac35.                                      \tag{1}
\]

Its complete tree has 757 nodes and 566 terminal leaves. The frozen
bounded-memory independent checker passed all 566 leaves, with zero OPEN
domains, 74,846 exact bound deductions and 134,855 checked premises. The
native replay took 669.11 seconds. The proof record is
`A_C744_COMPONENT1_COMPLETE_EXACT_REPLAY.json`, SHA256
`1f69c94f0028cabd28817b351553be0a5e4f3a30d790472255ea7ff556979240`.

The complete tree manifest has SHA256
`cfa406d4df6aaf9ac2d52b7b0ef9a4d9edf30819fddb7991406441914bbfbec7`.
The source checker is the older
`verify_ac_two_link_consequence_four_lazy_tree.py`, SHA256
`6cb9e209b3285e4fcc522cb4ffa93eff95b63f13281040464dc22eeea10092e6`.
It cannot consume the new consequence prefix introduced below. Each actual
consumer repeats this complete source in a fresh process; a saved PASS
report is not used as a replacement for the source arithmetic.

## Complete-cover assembly

The main search excluded every branch except one broad sibling, numbered
572 in its then-current manifest. A separate worker searched that sibling
from an exact copied proof path. Its complete closed subtree has 43 nodes
and 30 terminal leaves. All off-path alternatives in that auxiliary cover
remain explicitly OPEN.

The main search was stopped after it had started a small duplicate subtree
at 572. Every record in that duplicate subtree had zero bound rounds. A
separate restoration verified all its closed union and child-state
identities, restored the exact byte-identical frozen OPEN seed, and copied
every other main proof record unchanged. All 17 retired zero-round records
remain archived and hash-bound; the stopped main folder was not modified.

The graft required the restored seed's exact initial state and record hash
to match the delegated seed. Every ancestor proof record matched
byte-for-byte. It checked every delegated four-way proxy, eight-way SAT or
two-way angle cover and every child initial state, then copied the completed
subtree into a fresh complete main tree. The ordinary frozen full-tree
checker subsequently verified the assembled 757-node proof. No special
graft acceptance rule replaced that arithmetic replay.

## Original-wide consequence

Let a physical configuration satisfy the complete unchanged original-cell
hypotheses. If it also satisfied (1), it would belong to the completely
excluded source domain. Therefore

\[
 y_B-y_D>-\frac35,
 \qquad\text{hence}\qquad y_D-y_B<\frac35.
\]

Weakening the strict conclusion gives the necessary closed inequality

\[
 \boxed{y_D-y_B\le\frac35}.                               \tag{2}
\]

The row is valid on the whole original and on each of its descendants.
The producer emits only (2), with original coordinate indices 3 and 7.
It does not export any source-child predicate, SAT auxiliary, or source
interval box. The binding checks the original ID and exact registered path,
the literal excluded halfspace, the whole-original parent, the exact
component-1 parent, the complete source manifest and every source-node
hash, and the frozen older checker.

The binding is `A_C744_COMPONENT1_CLOSED_CONSEQUENCE_BINDING.json`, SHA256
`5c46eb3c5e3c60e9e776dd52db041cff92d0718c12feb040b9ada0fc745a801a`.
The independent literal implementation reconstructs the coefficients and
right-hand side directly. Literal/domain controls passed four positive
original or descendant cases and rejected 17 damaged originals, paths,
coefficients, bounds, names and binding domains. Those controls do not
replace the source proof.

## A component 3 only

Component 3 retains its own closed domain

\[
 y_B+y_D-2y_I\le-\frac35.                                \tag{3}
\]

Adding one half of (2) to one half of (3) yields

\[
 y_D-y_I\le0.
\]

This last inequality requires (3), so it is conditional on component 3.
It is not emitted as an original-wide row. The new A3 runtime retains its
existing separately proved component-3 root bounds and appends (2). The
independent A3 consumer first repeats the complete component-1 source,
then checks each new literal row, every earlier conditional source and the
entire consuming cover. Its node payloads are read with bounded memory.

## Status

Component 1 is completely excluded. The original A cell remains OPEN until
component 3 and the complete five-member composition pass their own gates.
This checkpoint grants zero new original cells and zero new masks. The
frozen whole-A3 probe retains its four earlier rounds and adds three rounds
using (2). Fresh independent replay passed all seven rounds: 565 exact
deductions, 1,436 checked premises, two weighted occurrences of (2), and
204 four-product corner occurrences. Its one unsplit domain remains OPEN.
The receipt is
`A_C744_COMPONENT3_FIRST_COMPLETE_A1_CONSEQUENCE_EXACT_REPLAY.json`, SHA256
`5c14a5ee853378adf31fcb56665bafa0c98656eec9bab0ca27ba596c03dc826d`.
That consumer freshly repeated the full 757-node A1 source and its older
conditional A3 bound source before checking the new record. The portable
checkpoint repeats that same dependency chain with inventoried inputs.
No Lean, Lake or CI run is claimed.
