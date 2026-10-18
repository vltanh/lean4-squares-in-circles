# There is only one nontrivial contact component

## Statements and scope

Consider an attained minimum-radius packing of eight unit squares. Translate
the disk center to zero and write its radius as R. The analytical results
already on this branch give

    sqrt(2)+1/2 < R <= R_dagger < 2,

and a unique square C containing zero in its open interior. All the other
closed squares omit zero. The definition of R_dagger is in
SMALL_STEP_ROADMAP.md, section 1.

A physical stress means the nonnegative actual-contact multipliers and
nonnegative active-circle-vertex multipliers constructed in
HUMAN_CONTACT_EQUILIBRIUM.md. Its positive-stress graph has an edge precisely
when the total contact multiplier of a square pair is positive. A graph
component is called nontrivial if it contains an edge.

We prove two conclusions:

1. Every normalized physical stress on the eight-square minimizer has
   exactly one nontrivial positive-stress component.
2. Among radius minimizers, choose one with the fewest actual contacting
   pairs. Its actual-contact graph has exactly one nontrivial component.

Both conclusions allow isolated vertices. Neither says that all eight
squares carry positive stress, that every actual contact carries stress, or
that the central square lies in the nontrivial component. These distinctions
are necessary for using the reduction correctly.

## 1. Equilibrium facts needed below

For square i write p_i for its center, x_i,alpha for its vertices on the
containing circle, and mu_i,alpha>=0 for their multipliers. A positive
contact force acts at an actual common point of the touching squares.
Let F_i be the sum of contact forces on square i. Physical equilibrium says

    F_i = 2 sum_alpha mu_i,alpha x_i,alpha,
    sum_contacts z cross f_i,z = 0,
    sum_(i,alpha) mu_i,alpha = 1.                         (1)

The contact forces in a pair are equal and opposite. Put
`m_i=sum_alpha mu_i,alpha`. If p_i' is another feasible center of the
same square in its fixed frame, expanding each active vertex inequality
and summing gives

    F_i dot (p_i'-p_i) <= -m_i |p_i'-p_i|^2.              (2)

As R>1/sqrt(2), the fixed-frame admissible center set has nonempty interior.
It follows from (2) and (1) that `F_i=0` if and only if `m_i=0`.
In particular a normalized physical stress has at least one positive edge:
otherwise every F_i, and hence every m_i, would be zero.

Every point of C has norm at most its diameter sqrt(2), because zero is a
point of C. In fact the strict inequality holds for all its vertices since
zero is in the open interior. As R>sqrt(2), C has no circle contact and

    m_C=0,          F_C=0.                               (3)

The proof of the nonradial-component theorem in
HUMAN_CONTACT_EQUILIBRIUM.md, section 8, uses (1)--(2), actual contact
geometry and the displayed radius range. Thus it applies to each
nontrivial component of any physical stress satisfying these conditions:
each such component has nonzero contact-moment circulation. Orient each
nonzero edge moment in its positive direction. Moment balance gives a
finite nonnegative circulation; following positive edges until a vertex
repeats extracts a directed cycle, which may then be reduced to a simple
directed cycle.

## 2. A component avoiding C needs at least five vertices

Let J be a nontrivial positive-stress component with C not in J. By the
preceding facts, J contains a directed positive-moment cycle. Every square
of that cycle is exterior. HUMAN_GLOBAL_CYCLE_CLOSURE.md shows that it winds
positively around the open central square. A cycle with three vertices is
excluded by its area argument; a four-vertex cycle is forced to be a
parallel five-square cross including C. HUMAN_CROSS_OCCUPANCY.md proves
that a cross in R<2 has room for at most seven squares in total.

Since the present packing contains eight squares, the cycle has at least
five vertices. In particular,

    C not in J   implies   |J| >= 5.                     (4)

This argument uses the eight-square occupancy hypothesis when excluding the
four-cycle. It must not be asserted for an arbitrary small packing without
that hypothesis.

## 3. A component containing C needs at least four vertices

Suppose J contains C. Equation (3) rules out positive stress degree one
at C, since one nonzero contact force cannot sum to zero. If |J|=2, this
already gives a contradiction.

If |J|=3, write its other two squares as A and B. Connectedness and (3)
force both C-A and C-B to have positive weight. Write n_A and n_B for
the unit normals directed from C to those neighbors, with positive
weights lambda_A and lambda_B. The contact forces on C are their negative
weighted normals. Thus

    lambda_A n_A + lambda_B n_B = 0.

Taking norms gives equal weights and `n_B=-n_A`. Put n=n_A. For a square S,
write h_S for the support function of its centered square. Separation from
C yields

    n dot (p_A-p_C) >= h_A(n)+h_C(n),
    n dot (p_C-p_B) >= h_C(n)+h_B(n).

The projection gap between the two closed neighbor squares therefore obeys

    min_(a in A) n dot a - max_(b in B) n dot b
       >= 2h_C(n) >= 1.                                 (5)

A and B cannot touch, so J has only the two edges C-A and C-B. It is a
tree, contrary to the nonzero-circulation conclusion of section 1. Hence

    C in J   implies   |J| >= 4.                         (6)

This is not a prohibition of a central square with degree two in a larger
component. Its two opposite neighbors may then be connected by a path
through other squares, as in the candidate.

## 4. Uniqueness of the nontrivial positive-stress component

At least one such component exists by normalization and (2). Suppose two
distinct nontrivial components existed. At most one contains C.

If neither contains C, (4) requires at least ten distinct squares.
If one contains C, (4) and (6) require at least nine distinct squares.
Both alternatives contradict the total of eight. This proves the first
statement of the note.

The argument does not depend on which valid contact axes or normalized
physical stress were selected. It applies to every such stress.

## 5. A minimum-contact component is locally radius-minimizing

Now select, among all radius minimizers, a packing with the fewest actual
contacting pairs. Such a choice exists because there is at least one radius
minimizer and the number of actual contacting pairs takes values in the
finite set `{0,...,28}`. Actual contact means that the two closed squares
meet.

Let I be a nontrivial component of its actual-contact graph. We claim that,
with all other squares omitted, its displayed configuration is a local
minimum of the containing radius about the fixed origin, with value R.

Suppose not. There is then a sequence of interior-disjoint configurations
of the squares in I converging to their original centers and frames,
each lying strictly inside D_R. This includes the possibility that the
original component already lies strictly inside D_R.

Different original actual-contact components are compact disjoint unions
of squares. Their distances are positive. Thus, for a sufficiently close
member of the sequence, the modified squares remain at positive distance
from every square outside I. They also all have positive disk slack.

Leave the modified frames fixed and multiply all their centers by
`1+epsilon`, about the disk origin, for a sufficiently small epsilon>0.
Disk containment and the positive distances from outside I survive by
continuity. This expansion strictly separates every pair within I:
for any separating unit normal n of the modified pair i,j, directed
from i to j, interior disjointness gives

    n dot (p_j-p_i) >= h_i(n)+h_j(n) > 0.

After the expansion the projection gap between their closed squares is
at least

    epsilon [h_i(n)+h_j(n)] > 0.                         (7)

For each pair one may retain its own separating normal. No common axis
or common orientation is needed. There are finitely many pairs, so all
pairs within I become noncontacting simultaneously.

All squares outside I stayed fixed, and no new contact with them was
created. The resulting eight-square packing fits D_R and has fewer actual
contacting pairs. It either has radius smaller than R, contradicting
minimal radius, or still attains R, contradicting the chosen contact
count. This contradiction proves the claim.

Notice the strict disk slack preceding the expansion. Expanding centers
at the original radius-bound configuration without that slack would not
be a valid proof.

## 6. Put a normalized stress on each actual component

The strict-direction lemma and multiplier argument of
HUMAN_CONTACT_EQUILIBRIUM.md require only local minimality of the squared
radius. A direction strictly improving that radius and all active
constraints produces a packing for sufficiently small positive time,
contradicting local minimality. The expansion direction used to eliminate
abnormal multipliers is also unchanged.

Consequently section 5 gives a normalized physical stress on each
nontrivial actual-contact component, supported on contacts internal to
that component and on its active vertices of D_R. Extend each such stress
by zero to all other squares. This extension preserves force and moment
balance and complementary support, including at actual contacts on which
zero weight is assigned.

If there were k>=2 nontrivial actual components, average their k extended
normalized stresses. The average is a normalized physical stress on the
whole eight-square packing. Each original component has at least one
positive edge by (1)--(2), and positive edges cannot join different actual
components. The average therefore has at least k nontrivial positive-stress
components, contradicting section 4.

There is at least one nontrivial actual component because a normalized
physical stress on the original minimizer has a positive edge. We have
therefore proved that exactly one actual component contains all actual
contacting pairs. Every other vertex, if present, is isolated.

## 7. Precise continuation

This completes steps G1--G6 in SMALL_STEP_ROADMAP.md. It removes the need
to compare two disconnected contacting clusters or two separately stressed
clusters in a minimum-contact representative.

It does not remove isolated squares. Such a square contributes to the
eight-square occupancy constraints even though all its chosen stress
multipliers are zero. The unique nontrivial component need not yet be known
to contain C. Nor does its connectedness imply degree two, a seven-cycle,
the twin motif, or any common frame. The remaining proof must retain these
possibilities and use the space occupied by all eight squares.
