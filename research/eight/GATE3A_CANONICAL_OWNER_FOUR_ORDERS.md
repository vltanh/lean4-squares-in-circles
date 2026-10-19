# Gate 3A: canonical SAT owners and four rational projection orders

2026-10-13. A full-domain structural reduction for arbitrary square frames,
not another exclusion of one sampled angle/owner box.

Depends on the true-square support identity in
`GATE1_ORDERED_RATIONAL_GLOBAL_MODEL.md`. The sparse force alternatives
in `GATE2_COMPLETE_SPARSE_FIBER_ALTERNATIVE.md` can be used on the resulting
necessary projected systems.

**The entire Gate 3 remains OPEN.** This proves its first owner-complete
reduction; it does not supply the final manageable survivor list.

## 1. Coverage theorem: replace arbitrary owners by maximum-projection owners

For two actual unit squares with centers p_i,p_j put d=p_j-p_i and let
N_ij be the list of eight signed true side-normal owners. The projected
support sum has the same value w_ij for every n in N_ij:

    H_i(n)+H_j(n) = w_ij >= 1.

This is Gate 1 identity (W); without choosing an angular chart it is
(1+|cos(delta)|+|sin(delta)|)/2, where delta is the relative frame angle.

Choose any n maximizing n dot d among N_ij. Call it a **canonical owner**.
The maximum exists because the list is finite, and all maximizing ties
are retained.

### Theorem 1 — exact preservation of the entire packing union

The two open square interiors are disjoint if and only if

    max_{n in N_ij} n dot d >= w_ij.

Consequently every valid SAT owner selection of every actual packing can
be replaced, pair by pair, by canonical owners, with the same square
centers, frames, containing disk, and radius. All 28 pairs remain valid.
No contact assumption, center perturbation, or strict tie-breaking is used.

Proof: the original SAT disjunction asks whether at least one n dot d is
at least its support sum. All eight support sums are equal. Its truth is
therefore equivalent to the displayed maximum inequality. QED.

This is an owner-complete transformation, not a claim that every arbitrary
valid owner is canonical. The quantifiers are:

    for every actual packing and every valid initial owner word,
    there exists a valid canonical replacement on the same packing.

At fixed frames, canonical ownership can also be recorded exactly by

    (n-m) dot (p_j-p_i) >= 0       for every m in N_ij.       (C)

These are homogeneous linear comparisons in the centers. Together with
true disk/SAT constraints, their union over canonical choices is exactly
the original full packing domain. They retain all maximizer ties.

## 2. The canonical owner is within 45 degrees of the center displacement

Let a=n dot d and b=(Jn) dot d. Because both signs of the perpendicular
axis Jn occur in the same actual square's owner list, maximality gives

    a >= |b|.

For a disjoint pair, a>=w_ij>=1. Thus d=a n+b Jn lies in the closed
45-degree cone about n. This fact is independent of the disk radius.
It need not hold for a merely valid but nonmaximizing owner.

## 3. A uniform rational projection inequality

Partition signed normal directions into the eight CLOSED coordinate
octants. On their common boundaries either adjacent octant is allowed.
Associate these integer vectors in cyclic order:

    u_0=(12,5),    u_1=(5,12),
    u_2=(-5,12),   u_3=(-12,5),
    u_4=(-12,-5),  u_5=(-5,-12),
    u_6=(5,-12),   u_7=(12,-5).

Each has norm exactly 13 and u_{k+4}=-u_k.

### Theorem 2 — whole-pair bound on every octant

If n is a canonical signed owner in octant k, then

    u_k dot (p_j-p_i) >= 7(n dot (p_j-p_i))
                         >= 7 w_ij >= 7.                  (P)

This holds for every square orientation and every center pair, provided
its canonical owner is a true nonoverlap witness. In particular it holds
at all octant, frame-tie, and SAT-tangency boundaries.

### Proof

By coordinate reflections and quarter-turns it suffices to take
n=(c,s), with c>=s>=0 and c^2+s^2=1, and u=(12,5).
Writing d=a n+b Jn with |b|<=a gives

    u dot d >= a[(u dot n)-|u dot Jn|].

The two quantities whose minimum is the bracket are

    (u dot n)-(u dot Jn) = 7c+17s,
    (u dot n)+(u dot Jn) = 17c-7s.

Since c+s>=1, the first is at least 7. Since c>=s and c>=1/sqrt(2),
the second is at least 10c>=5sqrt(2)>7 (use 50>49).
Hence u dot d>=7a. The canonical SAT inequality gives a>=w_ij>=1.
Reflections and quarter-turns prove all eight octants. QED.

The Pythagorean vectors (12,5) and their symmetries avoid irrational
projection coefficients. The bound is proved by these two elementary
inequalities, not by optimizing or sampling a cone.

## 4. Four global projected-center orders, not eight vacuous label DAGs

Opposite signed octants must be COMBINED. For k=0,1,2,3 define a directed
graph G_k on the eight square labels as follows. If a selected canonical
normal for i<j lies in octant k, insert i -> j in G_k. If it lies in
octant k+4, insert j -> i in G_k. On octant boundaries choose either
permitted class.

Then every graph edge a -> b satisfies

    u_k dot (p_b-p_a) >= 7.                             (O)

Each pair contributes one directed edge to one of four graphs; altogether
these graphs orient and partition the edges of K_8. They are simultaneously
realized by the same eight planar center vectors.

Every G_k is acyclic, because summing (O) around a directed cycle would
give 0>=7 times its positive length. More strongly, its vertices are
ordered by the ACTUAL common scalar projection u_k dot p_i, with a gap
of at least 7 across each edge.

**Important indexing point:** keeping opposite octants as separate graphs
while always writing i<j would give trivially acyclic label graphs and
miss the useful order restriction. Opposite octants are merged and their
arrows reversed as above.

### Disk-specific path restriction for the complete n=8 radius window

For any square contained in a radius-R disk and any u of norm 13,

    |u dot p_i| <= 13R-H_i(u) <= 13(R-1/2).

The second inequality follows from
|u dot e_i|+|u dot f_i|>=|u|=13. In the present window
R^2<=9789/2500<4, so R<2 and

    |u_k dot p_i| < 39/2.                              (B)

A six-edge directed path in a G_k would force projection difference
at least 42, while (B) bounds any difference strictly below 39.
Therefore each of the four graphs has longest directed path at most
**five edges** (at most six vertices).

This excludes complete directed-order families, simultaneously for all
square frames, rather than choosing a narrow angular box.

## 5. Cross-order force certificates reject whole coarse families

Fix the class and arrow of all 28 edges; call this the coarse order word.
Its necessary system consists of the 28 integer-row inequalities (O).
If nonnegative weights alpha_e, not all zero, balance these integer
vectors at every label, summing (O) gives

    0 >= 7 sum_e alpha_e > 0,

which is impossible. By Gate 2's finite convex-hull argument, the pure
projected separator system is infeasible exactly when such a balance
exists, and a witness needs at most 15 edges. Because the rows are integer,
a support-minimal normalized balance may be chosen rational: select an
affinely independent supporting set and solve its rational linear system.

This joint balance can couple different projection orders; separately
checking their DAGs is not sufficient. The integer coefficient system is
independent of the exact frame angles inside the chosen normal octants.
One such contradiction therefore excludes **every** actual owner choice
and every continuous angle configuration inducing that coarse order word.

For a stronger disk-aware necessary test, append the rational bounds

    -39/2 <= u_k dot p_i <= 39/2     (all i, k=0,1,2,3).

Any exact nonnegative weighted contradiction among these rows and (O)
also excludes that entire coarse family. Feasibility of this relaxed
system is NOT evidence of a real square packing; actual vertex, SAT,
canonical comparison, and sector conditions still have to hold.

## 6. The coverage statement obtained, and what has NOT been obtained

Every packing in the n=8 radius window maps to:

1. a Gate 1 ordered seven-angle representative;
2. a canonical actual SAT owner for every pair;
3. four simultaneous rational projection orders covering all 28 pairs,
   each acyclic with no six-edge directed path;
4. a feasible joint integer projection system and its bounded relaxation.

All implications hold for every actual packing, including any hypothetical
strict improvement and the genuine sharp equality construction. No central
square or S1--S4 / D0--D2 status has been silently selected.

This proves the first owner-complete reduction requested by Gate 3A.
It does NOT give an explicit manageable list of all surviving coarse words,
or prove that all their true-square refinements have q>=q_*.
Those are Gates 3B/3C and 4, respectively.

### Gate 2 compatibility warning

Gate 2's strict-dilation proof applies to the original positive-width SAT
rows. Adding homogeneous canonical comparisons (C) can force equality in
some of those comparisons, so full strict Slater must NOT simply be
assumed for the augmented system. Original-fiber dual bounds remain sound
on its canonical subset. The projected positive-width system has its own
proved force alternative above. A complete duality claim for additional
homogeneous comparisons would need a relative-affine-hull argument.

### Why the canonical condition cannot be dropped

Take two axis-parallel squares with center difference d=(1,-11/5), and
place their centers at +-d/2. They fit in squared radius 89/25, below the
n=8 ceiling, and the east-pointing owner n=(1,0) is a valid SAT witness
with n dot d=1. But u_0 dot d=12-11=1<7, violating (P).
There is no contradiction: that east-pointing owner is NOT maximizing.
The canonical downward owner does satisfy (P). This negative control
prevents the new theorem from being incorrectly applied to arbitrary old
owner words or to the earlier radius-dependent cone statements.

## 7. Exact arithmetic audits and equality guard

`verify_gated_fiber_and_canonical_owner.py` was executed locally. It checks:

* Gate 2's exact regularization reserve and the unbalanced-zero-anchor guard;
* 11,696 exact rational canonical-cone instances, including maximizing ties;
* the explicit noncanonical negative control;
* all 32 vertices and 28 canonical SAT pairs of the existing rational
  eight-square reference construction;
* all 32 vertices and 28 pairs of its strictly separated perturbation
  with eight distinct frames, together with the four actual order graphs.

Both genuine packing regressions are retained by the new conditions.
The global preservation of the exact sharp candidate follows from the
universal hand proof, not from substituting a nearby rational packing.
Finite tests are implementation audits, not the continuous proof.

**Current gate:** 3B — classify the surviving joint four-order families
with their actual owner/angle refinements. No unrestricted sharp radius
or global equality theorem is claimed.
