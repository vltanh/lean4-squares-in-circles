# A hand reduction of the seven-cell \`001/00\` frontier

**Status: one dependency removed from the critical path; zero new whole
original cells certified closed.** This is a genuinely finite reduction of
the frozen November 5 frontier. It neither changes the 231-cell register
nor proves the full mask. No Lean compilation, CI, numerical search or
certificate replay was used.

## 1. Exact existing problem

The original nine-square strict-radius predicate is
\`D_001/00^lt\` in the archived
[A.2 contract](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/A2_COVERAGE_AND_CLOSURE_CONTRACT.md).
The main original squares A,B,C,D form a center-cone chain, with actual
horizontal links AB and BC and strictly weak horizontal link CD.
The other original chain E,F,G has both links actual. The extra originals
H,I remain independently oriented, present, and pairwise physically
disjoint from every other original. Every original corner has squared
norm strictly less than Q=1105/256.

The previously accepted low-gap theorem excludes
\`|y_D-y_C|<=2/3\`. In its complement, one common vertical reflection
gives \`y_D-y_C>2/3\`, and the extra labels are sorted so \`x_H<=x_I\`.
For the C prefix, D has nonpositive canonical tangent and A has
nonnegative canonical tangent. Both zero-angle faces are retained.

The frozen register contains the seven open IDs below, grouped by
their **exact three or four initial path choices**:

| Prefix class | Original ID | Status |
|---|---|---|
| Positive D, inward A,H,I,D variation | \`positive-c744bc031d40ee64\` | OPEN |
| Negative D, alternate A,B,H,D branch 1 | \`negative-887236b78100baf3\` | OPEN |
| Negative D, alternate A,B,H,D branch 2 | \`negative-d4021ade840b985c\` | OPEN |
| Negative D, alternate A,B,H,D branch 3 | \`negative-b882d8ade0cf9ea0\` | OPEN |
| Negative D, F/H side branch 2 | \`negative-7c60be8b07a358e9\` | OPEN |
| Negative D, F/H side branch 1 | \`negative-462e78d2e2d8be05\` | OPEN |
| Negative D, F/H side branch 3 | \`negative-16a2fc93c8d133f0\` | OPEN |

All original IDs and paths are unchanged. The old current-mask handoff
has detailed, independently replayed partial evidence for each.
No count of internal OPEN leaves is interpreted as a new original ID.

## 2. Strict-interiorization lemma for the unchanged physical mask

**Lemma.** Suppose a physical packing at squared corner radius
\`q<Q\` satisfies any fixed five-bit center-cone mask, with all
originals independently framed. For any sufficiently small neighborhood
of its centers, there is another packing *inside that neighborhood*,
with exactly the same mask and original frames, for which:

1. every pair of physical squares has a strictly separating owned axis;
2. every bit-0 marked horizontal projection link is strict;
3. every one of the five marked center-cone inequalities is strict;
4. every bit-1 marked horizontal projection link remains strictly weak;
5. all original corner norms remain strictly below Q.

The common horizontal order of the two extras, when imposed, is retained.
Any originally strict inequality such as \`y_D-y_C>2/3\` is retained.
Every canonical frame-sign root is retained because no frame changes.

*Proof.* There are finitely many original corners and original pairs.
Since their corner norms are strictly below Q, continuity permits a
common factor \`lambda>1\`, arbitrarily near one, multiplying *all
nine centers* while fixing all nine side frames, without leaving the
strict Q-disk.

For each original disjoint pair choose one genuine directed SAT
separating axis \`n\`. Before expansion its center projection is at
least \`H_i(n)+H_j(n)>0\`. After expansion it is multiplied by lambda,
while its physical support sum is unchanged. Hence the same axis now
separates **strictly**. All 36 pair requirements are simultaneously
strict because the pair set is finite. A marked actual horizontal link
also becomes strict because its positive original center gap is
multiplied by lambda. Each weak-link deficit
\`h_i+h_j-(x_j-x_i)\` was originally strictly positive; choosing lambda
sufficiently close to one preserves those deficits. All cone
inequalities and the sorting of extras survive the common expansion.

Next, keep every enlarged horizontal center coordinate fixed and
multiply **all enlarged vertical center coordinates** by \`1-epsilon\`,
where \`epsilon>0\` is arbitrarily small. Every marked directed cone
gap originally has \`Delta x>=|Delta y|\` and \`Delta x>0\`. It now
satisfies

\`\`\`
Delta x > (1-epsilon)*|Delta y|.
\`\`\`

The horizontal mask bits and extra sorting are unchanged. The already
strict physical separating inequalities, strict disk containment and
any other originally strict guards survive by continuity for
sufficiently small epsilon. Frame signs are unchanged. Both
perturbations can be made arbitrarily small. This proves the lemma. □

The lemma makes no assertion that the closed-Q equality domain can be
perturbed while retaining \`q<=Q\`. Its use here is exclusively at
strictly subcritical radius.

## 3. The C887 boundary cell is conditionally redundant

**Proposition (C boundary dominance).** Assume the two entire,
unchanged original domains

\`\`\`
negative-d4021ade840b985c
negative-b882d8ade0cf9ea0
\`\`\`

are excluded for strict \`q<Q\`. Together with the already accepted
complete exclusions of every other branch of the frozen
\`alternate_four_escape([B,H])\` union, this **automatically excludes**
the entire original domain

\`\`\`
negative-887236b78100baf3.
\`\`\`

In particular there are **six independent original-cell closure
obligations**, rather than seven. Until d402 and b882 actually close,
all three C original IDs remain OPEN in the frozen register.

*Proof.* The accepted alternate-four escape is a complete eight-case
union. If none of its eight scalar slacks is nonpositive, its alternate
original cone four-chain has both outer links actual while E,F,G remains
an actual short chain. The previously proved \`010/00\` terminal then
excludes the unchanged nine-original physical caller. Thus any
hypothetical strict counterexample enters at least one of the eight
first-satisfied escape branches.

The first two escape inequalities are the two signed diagonal
failures on the already-selected AB center-cone link. In the accepted
literal decoder their primary rows can be written

\`\`\`
0: (x_B-x_A)-(y_B-y_A) <= 0;
1: (x_B-x_A)+(y_B-y_A) <= 0.
\`\`\`

The existing AB cone gives both left sides >=0. Consequently either
of these two branches is an **AB diagonal equality face**. In
particular the full C887 original (branch 1) lies on such a face.
The literal two predecessor inequalities printed in the original
Cd402 attachment are their nonpositive negatives:

\`\`\`
x_A-y_A-x_B+y_B <= 0,
x_A+y_A-x_B-y_B <= 0.
\`\`\`

Apply the strict-interiorization lemma to a hypothetical packing in
C887, choosing the perturbation small enough also to retain the
already strict \`y_D-y_C>2/3\` and the same A/D tangent-sign roots.
All the selected original masks, the two extras and their physical
constraints persist. Both AB cone slacks are now strictly positive,
so neither escape branch 0 nor branch 1 can be entered by the
perturbed configuration.

The alternate-four union still applies. Therefore its first
satisfied branch is one of 2,3,4,5,6,7. The exact archived
[231-cell register](https://github.com/vltanh/lean4-squares-in-circles/blob/6a9a45e0ad997c8e143b0f22a0de88370d9d7adb/research/nine/gates/A2_00100_FIXED_FRONTIER.json)
has these exhaustive remaining original obligations under the common
negative-D/nonnegative-A prefix:

| Branch | Frozen original descendants | Existing accepted status |
|---|---:|---|
| 2 | 1 | Cd402: OPEN |
| 3 | 1 | Cb882: OPEN |
| 4 | 1 | CLOSED |
| 5 | 1 | CLOSED |
| 6 | 1 | CLOSED |
| 7 | 29 | All CLOSED |

The previously certified v13 excluded leaves complete the rest of
each branch. If the full Cd402 and Cb882 originals are also proved
empty, every branch 2–7 is impossible. That contradicts existence of
the perturbed packing, and therefore of the original C887 packing. □

The proof uses a *nearby strict-radius packing*, not a claim that a
counterexample in C887 itself satisfies a different branch. No
unproved equality-to-strict inference is made.

## 4. Consequence for the research queue

This does **not** advance the certified count 224/231. It eliminates
an independent C887 research task *conditional on closing Cd402 and
Cb882*. It also shows why pursuing C887's own 43-node/24-node
incomplete covers in parallel is avoidable: one may use the already
closed branches and the uniform interiorization transfer.

The remaining independent targets are A-c744; B7, B462 and B16a; and
Cd402 plus Cb882. They remain continuously quantified nine-original
problems, not a promise that six hand tables will automatically
complete. Each requires a complete proof of its unchanged path
predicate before any register closure is credited. The **next useful
completion** is therefore a full Cd402 or Cb882 domain, because
finishing both also discharges C887 for free.

A universal exact alternative may supersede those individual tasks,
but cannot be credited merely from a numerical residual, an archived
partial tree, or a selected-seven relaxation.


## 5. A direct physical exclusion inside the remaining Cb882 original

This section proves a **complete continuous subdomain** of the unchanged
Cb882 original, not the whole Cb882 cell. The parent cell and the
224/231 ledger remain OPEN.

**Lemma (downward-cone obstruction).** Let B,H be two original physical
unit squares, disjoint in interior and contained in the Q-disk. Suppose

\[
 |x_B|<31/60,\quad y_B\le-4/5,\qquad
 y_H-y_B\le-|x_H-x_B|.
 \tag{22}
\]

These hypotheses are impossible. Only the two original contained
radius-half disks and their original corner containment are needed.

*Proof.* Put \(a=|x_B|\), \(b=-y_B\), and
\(w=c_H-c_B=(u,-t)\). Thus \(a<31/60\), \(b\ge4/5\),
\(t\ge|u|\), and the original contained radius-half disks give
\(s:=|w|=\sqrt{u^2+t^2}\ge1\). In particular
\(t\ge s/\sqrt2\), while \(b-a\ge17/60>0\).
Therefore

\[
 c_B\cdot w=x_Bu+bt
 \ge-a|u|+bt
 \ge(b-a)t
 \ge(b-a)s/\sqrt2.
\]

It follows that

\[
\begin{aligned}
 |c_H|^2
 &=|c_B|^2+s^2+2c_B\cdot w\\
 &\ge a^2+b^2+s^2+\sqrt2(b-a)s\\
 &\ge1+a^2+b^2+\frac75(b-a).
\end{aligned}
\tag{23}
\]

The last step uses \(\sqrt2>7/5\), \(s\ge1\), and \(b-a>0\).
The final right side decreases with \(a\) on \([0,31/60]\)
because \(2a-7/5<0\), and increases with \(b\ge4/5\).
Consequently

\[
 |c_H|^2
 >1+(31/60)^2+(4/5)^2+(7/5)(4/5-31/60)
 =\frac{8293}{3600}.
\]

But the original disk gives \(|c_H|<91/60\), so
\[
 |c_H|^2<\frac{8281}{3600},
 \qquad
 \frac{8293-8281}{3600}=\frac1{300}>0.
\]
This contradiction proves the lemma. \(\square\)

**Corollary (an exact Cb882 cut).** Every hypothetical packing in the
unchanged original cell \`negative-b882d8ade0cf9ea0\` must satisfy

\[
 \boxed{y_B>-4/5.}                                      \tag{24}
\]

Indeed, the *original* selected actual links AB and BC, together with
the center bound, imply
\(-31/60<x_B<31/60\). In the eight-entry escape union for the
original A,B,H,D tuple, entry 3 is the closed primary inequality
\[
 (x_H-x_B)+(y_H-y_B)\le0.
\]
Its immediately preceding entry 2 was not selected; the archived
first-satisfied path therefore retains the predecessor complement
\[
 (x_H-x_B)-(y_H-y_B)\ge0.
\]
Combining these two **literal original-path** inequalities yields
\(y_H-y_B\le-|x_H-x_B|\), precisely the third hypothesis of the lemma.
The margin \(1/300\) handles all contacts and equality faces.
Thus the whole closed subdomain \(y_B\le-4/5\) is excluded, and the
complete complement \(y_B>-4/5\) remains to be proved empty.

This result is a new necessary constraint on the **same original nine
physical squares**. It does not assume any independently chosen H
orientation, remove I, change the escape path, or substitute an
unproved optimizer bound. It can be installed as one hand terminal in
a future complete Cb882 table, but it earns no complete-original
closure credit now.
