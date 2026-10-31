# Full-cut excess and finite three-port degree signatures (hand proof)

Date: 2026-10-31. PR #11, hand-only research.

**Status:** elementary, independently checkable hand-counting lemma and necessary degree-signature census. No force/torque geometry or nine-square exclusion beyond the stated budget is claimed. No original canonical fine/coarse row is thereby closed.

## The original physical setting

Take nine actual unit squares with disjoint open interiors in a disk of squared radius at most (Q=1105/256), equipped with one unchanged, complete positive body-pair contact-force certificate. Let (K) be a connected nonempty set of **selected circle-unloaded** actual bodies. Let

- (n=|K|), (e=|E(K)|), and (b=e-n+1\ge0) be the internal edge count and cycle rank of the **induced original positive graph**;
- (p\ge1) be the number of **original positive cut edges**, counting each body-pair edge across (K\mid K^c) once, even if external endpoints repeat;
- (d(v)) be the **full original positive degree** of (v\in K), internal edges and cut edges both included.

An unloaded body cannot have full positive degree one: its sole nonzero force would violate its complete translational balance. Because it belongs to a positive connected set here, every (d(v)\ge2). Zero-weight geometric contacts do not alter these degrees or the cut.

### Lemma 1. Exact full-degree excess

For every such (K),
\[
\boxed{\sum_{v\in K}(d(v)-2)=2b+p-2.}\tag{1}
\]
**Proof.** The complete degree sum on (K) is (\sum d(v)=2e+p); each internal positive edge contributes two, and each original cut edge one. Thus
\[
\sum(d(v)-2)=2e+p-2n=2(e-n+1)+p-2=2b+p-2.
\]
No degree-two transmitter, cut-edge incidence, original side mean, or actual completion square was erased.

### Lemma 2. A uniform *finite* nine-square envelope

Every positive connected component has at least two **distinct positively circle-loaded actual bodies** (the standard total-force and center-dot-work physical stress fact; see PHYSICAL_CONTACT_STRESS.md). Both lie outside an unloaded (K), so
\[
1\le n\le7.
\]
The complete original positive body-pair graph is simple (at most one edge per unordered pair of actual bodies). Hence
\[
0\le b=e-n+1\le\binom n2-n+1
 =\frac{(n-1)(n-2)}2\le15,
\]
and
\[
1\le p\le n(9-n)\le20.
\]
These are **finite upper bounds, not a geometrically sharp classification**. In particular the previous three-port *subcubic* theorem's (b\le3) cannot be extended to arbitrary positive degrees: (1) allows much larger cycle ranks when high-degree hubs occur.

### Lemma 3. Exactly seven necessary full-degree signatures when (p=3,b=2)

In this branch (1) gives
\[
\sum_{v\in K}(d(v)-2)=5.
\]
Discard the zero contributions from true full-degree-two transmitters. The positive contributions are an unordered integer partition of five. There are exactly the following seven possibilities (entries in the middle column are **original full degrees**, not internal degrees after deletion of exits).

| Excess partition | Original full-degree multiset at branching hubs | Number of hubs |
|---|---|---:|
| \(5\) | \(7\) | 1 |
| \(4+1\) | \(6,3\) | 2 |
| \(3+2\) | \(5,4\) | 2 |
| \(3+1+1\) | \(5,3,3\) | 3 |
| \(2+2+1\) | \(4,4,3\) | 3 |
| \(2+1+1+1\) | \(4,3,3,3\) | 4 |
| \(1+1+1+1+1\) | \(3,3,3,3,3\) | 5 |

**Proof of completeness.** The largest positive excess is one of 5,4,3,2,1. For 5 the remainder is zero; for 4 it is (1); for 3 it is either (2) or (1+1); for 2 it is either (2+1) or (1+1+1); for 1 all five summands are ones. This gives precisely the displayed seven integer partitions, with no orientation, pose, or force-magnitude branching. Substituting (d=2+\text{excess}) gives the original full-degree signatures.

Every degree-two transmitter contributes zero and is **not** deleted physically. The two-loaded-outside condition limits the total number of those transmitters to (7-h), where (h) is the hub count in the chosen row. Other graph-theoretic, contact, force/torque and nine-square-completion constraints may eliminate further rows; **this table does not assert any row is realizable**.

### Corollary. The earlier subcubic rank-two module has at most two transmitters

If all original full positive degrees in (K) are at most three, only the last partition is possible. Thus five full-degree-three hubs occur, and (n\le7) leaves zero, one, or two actual full-degree-two bodies, including ones on transmitted **exit arms**. This recovers the pure counting portion of THREE_PORT_MULTICYCLE_SUBCUBIC_REDUCTION_2026_10_31.md without claiming its still-open house, subdivided-(K_{2,3}) or rank-three exclusions.

For (p=3,b=3) the excess is seven, so the subcubic case has seven hubs, no room for transmitters, and precisely two external positively circle-loaded bodies. For (p=4), (1) reads (\sum(d-2)=2b+2); for (p\ge5) it remains (2b+p-2). These keep the eventual larger-cut census finite while leaving its physical exclusions open.

## Scope and review

This is a necessary **topological integer census**, not a universal physical theorem (R^2\ge Q). It does not assert that original cut-size classes (p=4,5,\dots,20) are resolved. The earlier three-port theorem additionally assumes **at most one reduced exit arm per branching hub**, which is *not* assumed in Lemmas 1–3. Independent review of the broader channel/force lemmas is still outstanding.

No Lean/Lake, CI, numerical exclusion, external mathematical script, or graph enumeration program was used. The table is exhaustively obtained by the displayed hand partition argument.
