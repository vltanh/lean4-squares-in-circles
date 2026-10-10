# Analytical tools for the seven-cycle route

**Status.** Sections 2, 4, and 5 below are pen-and-paper lemmas with complete
proofs. They replace a discrete enumeration, reduce one support calculation
to genuine geometric cases, and quantify the cost of changing a shared
orientation. They do not establish the missing continuous pair inequalities
or the unrestricted sharp eight-square lower bound.

No interval cover, numerical minimization, generated classification table, or
Lean proof is used in these lemmas.

## 1. Keep the marker and stress cycles distinct

The label whose exterior-marker gaps are proved greater than `7/8` in
SHARP_MARKER_RING.md is

    ell_ring(a,u) = min(11u/10, 5/9+3u/5-17a/50, 157/200).

The older label

    min(11u/10, 3/5+4u/7-3a/8, 3/4)

does **not** have that property: the same note gives an exact counterexample.
The earlier ambiguous names in SEVEN_CYCLE_POTENTIAL.md have been replaced
by the explicit name `ell_ring`; only that label supplies the imported domain
`7/8<g<29/28`. The combinatorial lemma below does not depend on any particular
marker or on those gap bounds.

There are also two different useful cycles in the candidate. The exterior
marker cycle is

    E, H, G, A, B, T, D.

A possible separator-stress cycle is

    A, B, C, D, E, H, G.

The latter uses the central square C and omits T. In the displayed candidate,
C transmits a horizontal force and G transmits a force in the tilted e
direction. Their two incident weighted normals can cancel, so they need not
touch the circle. Contracting these two straight force chains leaves the five
support-bearing squares A, B, D, E, H. One may instead use T in place of C for
the horizontal chain. These are observations about the specified candidate;
neither cycle is thereby forced in an arbitrary packing.

## 2. Exact seven-step minimization on four types

Let `b_ij=b_ji` be any real symmetric weight table on four types
`{0,1,2,3}`. Diagonal entries are allowed. No positivity assumption is needed.
The weight of a closed seven-step type word is

    W(k_0,...,k_6) = sum_{r=0}^6 b_{k_r,k_(r+1)},    k_7=k_0.

Define

    m   = min_{i != j} b_ij,
    tau = min_{i,j,k distinct} (b_ij+b_jk+b_ki),
    L   = min_{i,j,k,l} [b_ii+2(b_ij+b_jk+b_kl)].

The indices in the definition of L may repeat.

**Theorem.** The exact minimum of W is

    min W = min(tau+4m, L).                              (2.1)

### Proof for words without loops

View the word as a closed walk on the complete undirected graph on four
vertices. A closed walk decomposes into simple cycles: whenever a vertex
repeats, cut off the intervening closed subwalk and continue until every
piece is simple. An edge followed immediately by its reverse gives a
two-cycle and is allowed in this decomposition.

If the original word has no loop, the simple-cycle lengths are 2, 3, or 4.
Their sum is seven, so at least one is odd and hence is a triangle. Its weight
is at least tau. The four remaining edge occurrences are all off-diagonal and
each has weight at least m. Thus

    W >= tau+4m.                                         (2.2)

Conversely, select a triangle attaining tau and an edge attaining m. An edge
on four vertices necessarily meets a triangle on three vertices. Starting at
a common vertex, traverse the triangle once and make two excursions along
the selected edge and back. This is a loopless closed walk of length
`3+2+2=7`, with weight exactly `tau+4m`. Therefore (2.2) is the exact minimum
among loopless words.

### Proof for words with a loop

Choose one occurrence of a loop at type i and remove that edge. The remaining
walk is closed at i and has six edges. Split it into its first and last three
edges, with respective weights A and B. Both halves are three-edge paths
starting at i after reversing the last half. Symmetry of the table preserves
the weight of the reversed path.

Keeping the cheaper half and retracing it gives a closed six-step walk of
weight `2 min(A,B) <= A+B`. Reinsert the loop at i. We have produced a word
of the form

    i, i, j, k, l, k, j, i,

whose weight is `b_ii+2(b_ij+b_jk+b_kl)` and is no greater than the original
weight. Conversely every such word is a legitimate closed seven-step word
with a loop. The minimum among loop-containing words is therefore exactly L.
Combining the two alternatives proves (2.1). `QED`

This proof replaces the `812` edge-count vectors mentioned in
SEVEN_CYCLE_POTENTIAL.md. It keeps the loop alternative; simply replacing
every odd closed walk by a triangle would be incorrect because adjacent
squares can have the same type.

For evaluation without listing words, L can also be obtained from three
nested row minima:

    d_1(i) = min_j b_ij,
    d_2(i) = min_j [b_ij+d_1(j)],
    d_3(i) = min_j [b_ij+d_2(j)],
    L      = min_i [b_ii+2 d_3(i)].

These identities are symbolic consequences of the path definition, not
numerical classification premises.

### Equality and the candidate type word

Suppose the following strict choices have been proved for a proposed table:

* the unique cheapest off-diagonal edge is `03`;
* the unique cheapest triangle is `012`;
* `L > tau+4m`.

Then every minimizing seven-step word is loopless. In the proof of (2.2),
the triangle must be `012` and every other edge occurrence must be `03`.
The triangle is traversed once, and the four `03` occurrences are two
out-and-back excursions attached at type 0. Consequently, up to cyclic
rotation and reversal, the minimizing word is

    0, 3, 0, 1, 2, 0, 3.                                (2.3)

This is the candidate word in SEVEN_CYCLE_POTENTIAL.md. Thus the odd-cycle
mechanism can explain that word without an exhaustive enumeration. The
strict choices above are hypotheses to prove, not assertions about the
unrecorded numerical fitted table.

## 3. What the exact type theorem would need from geometry

Let `x_0,...,x_6` be genuine square states in a fixed cyclic marker order,
with consecutive real gaps g_r summing to `2*pi`. Suppose a state potential
psi and a four-type map kappa satisfy, for every relevant disjoint ordered
pair,

    g + psi(target)-psi(source) >= b_(kappa(source),kappa(target)).

For the state model currently proposed in SEVEN_CYCLE_POTENTIAL.md, symmetry
of the table has a geometric justification. Its types depend only on `(a,u)`,
and its potential has the odd form `psi(a,sigma*u)=sigma P(a,u)`. Reflect a
pair in a line through the disk center and reverse the pair's order. The
marker gap stays g, each transverse sign reverses, and the new adjusted gap
is

    g-psi(source)+psi(target),

the same as before. Containment, disjointness, and the circular central-core
condition are reflection invariant. Thus the best ordered lower bounds for
types `(i,j)` and `(j,i)` agree. Even an initially asymmetric valid table may
be symmetrized by replacing both entries with their maximum. This argument
requires a reflection-invariant pair domain and an odd potential; it cannot
silently be applied after fixing additional asymmetric central data.

Summing cancels all potentials. Applying (2.1) gives the precise conclusion

    2*pi >= min(tau+4m, L).                              (3.1)

Therefore a subcandidate exclusion can be organized around only two
discrete targets:

    tau+4m > 2*pi,       L > 2*pi.

At the sharp endpoint one can instead prove both quantities at least
`2*pi`, followed by equality analysis. If the strict choices leading to
(2.3) also hold, they recover the candidate type word. Equality in the
original sum then forces equality in every one of the seven continuous pair
inequalities. Those pair equality conditions, rather than the type word
alone, would have to recover the geometry or force a vertex at radius R*.

The actual remaining tasks are substantial:

1. Define type boundaries from geometric support transitions, or justify the
   entire domains of any chosen types analytically.
2. Prove the pair inequalities for every admissible state, including interior
   states and each sign choice. The outward-radialization obstruction still
   applies.
3. Retain enough information about the central square. The proved
   radius-`1/12` core is one possible necessary restriction, but its present
   proof is certificate-based, and excluding the previously known exterior
   counterexample does not solve the new continuous domain.
4. Check every sharp equality family, including the sliders. If a table
   closes sharply at the candidate, its continuous pair inequalities must
   be equalities throughout the corresponding allowed slider intervals.

No fitted table, polynomial potential, or continuum inequality satisfying
these requirements has been proved here. In particular, (3.1) is not itself
an eight-square lower bound.

## 4. A force triangle reduces an orientation bound to three cases

BALANCED_SEPARATOR_REDUCTION.md gives an exact support criterion with the
centers eliminated. The following additional identity is useful when a
stress is supported on a cycle.

For a centered unit square with orthonormal axes `(e,f)`, write

    h(v) = (|v dot e|+|v dot f|)/2.

Let p and q be two weighted directed separator normals at a cycle vertex.
Then its contribution to the elementary disk-support bound is

    T(p,q) = h(p)+h(q)+h(p-q).                           (4.1)

### Triangle identity

For any real a,b,

    (|a|+|b|+|a-b|)/2
       = max(0,a,b)-min(0,a,b).

To prove the identity, order the three points `0,a,b` on the line. The sum of
their three pair distances is twice the distance between the two extremes.
Apply it once to the e projections of p,q and once to their f projections.
It follows that

    T(p,q) = width_e Delta + width_f Delta,
    Delta  = convex hull of {0,p,q}.                     (4.2)

Thus (4.1) is half the perimeter of the bounding rectangle of a force
triangle in the square's frame.

### Minimum over the square's orientation

Assume first that Delta is a nondegenerate triangle. Partition the angle of
the square frame at directions for which two triangle vertices have equal
projection onto one of its axes. On each open interval the identities of the
maximum and minimum projected vertices are fixed. The width sum therefore
has the form

    A cos(theta)+B sin(theta).

It is strictly positive, and its second derivative is its negative. It is
therefore strictly concave on that interval, so its minimum on the closed
interval is at an endpoint. Each endpoint has a square axis parallel to a
triangle edge. This proves that the global minimum is achieved with an axis
parallel to one of `p`, `q`, or `p-q`.

There is an explicit three-case formula. For a nonzero vector
`v in {p,q,p-q}`, put

    M_v = [max(0,p dot v,q dot v)-min(0,p dot v,q dot v)
           + |p cross q|] / |v|.

Then, minimizing over all square orientations,

    min T(p,q) = min_{v in {p,q,p-q}, v != 0} M_v.        (4.3)

Indeed, the first term in M_v is the triangle's width along v; its width
perpendicular to that edge is the altitude `|p cross q|/|v|`.

If the triangle degenerates to a segment, its width sum is its length times
`|cos(theta)|+|sin(theta)|`, minimized by an axis along the segment. Formula
(4.3) still holds. When `p=q=0`, both sides are defined to be zero. This also
covers straight force transmission `p=q != 0`: its minimum is `|p|`, even
though the net force vanishes.

### The resulting cycle inequality

For a cycle of square centers c_i, choose directed separating unit normals
n_i from square i to square `i+1`, and give them nonnegative weights lambda_i.
Put

    p_i = lambda_(i-1) n_(i-1),
    q_i = lambda_i n_i,
    F_i = p_i-q_i.

The weighted separation inequalities give

    sum_i [h_i(p_i)+h_i(q_i)] <= sum_i F_i dot c_i.

If the squares lie in the disk of radius R, select a vertex of square i
supporting F_i. Its disk support gives

    F_i dot c_i+h_i(F_i) <= R |F_i|.

Consequently the following inequality is valid for arbitrary square frames:

    sum_i T_i(p_i,q_i) <= R sum_i |p_i-q_i|.              (4.4)

Replacing each term on the left by its exact minimum (4.3) gives an
orientation-independent necessary inequality for the selected weighted
normals. All orientation cases here arise from the three edges of a force
triangle, rather than from an angle mesh.

The exact center support in BALANCED_SEPARATOR_REDUCTION.md can be stronger
than this elementary disk-support bound; (4.4) is a convenient relaxation,
not a replacement for it. Nor does minimizing (4.1) while holding p,q fixed
prove that an actual packing can independently rotate its squares. The
normals themselves may depend on square orientations, and other separators
must remain satisfied. An alignment conclusion is legitimate only from a
sharp complete inequality and its equality conditions.

## 5. Exact cost of breaking a parallel contact

The following pair identity gives a local tool for proving orientation
locking without assuming it. Choose oriented square frames whose relative
angle is `2h`, with `0<=h<=pi/4`. In their bisector frame, let the displacement
between centers have coordinates `(x,y)`, and put

    a = max(|x|,|y|),       b = min(|x|,|y|).

**Pair identity.** The open square interiors are disjoint if and only if

    a+b tan(h) >= cos(h)+sin(h).                          (5.1)

### Proof

The two unoriented axis pairs in the bisector frame can be represented by

    (cos h, sin h),       (-sin h, cos h),
    (cos h,-sin h),       ( sin h, cos h).

The pair half-width sum is the same on all four axes:

    W = (1+cos(2h)+sin(2h))/2
      = cos(h)[cos(h)+sin(h)].

The maximum absolute projection of the center displacement onto these axes
is

    max(|x| cos h+|y| sin h, |y| cos h+|x| sin h)
       = a cos h+b sin h,

since `cos h>=sin h>=0`. The separating-axis theorem says that the squares
have disjoint open interiors exactly when this maximum is at least W.
Divide by the positive number `cos h` to obtain (5.1). `QED`

### A quantitative rotation penalty

Suppose the tangential displacement obeys

    |x| <= 1-epsilon,       0<epsilon<=1,
    0<=h<=epsilon/2.

For disjoint interiors, (5.1) implies

    |y| >= 1+epsilon*h/2
         = 1+epsilon*|relative angle|/4.                 (5.2)

To check this, first observe that `cos h > 1-epsilon`: use
`cos h>=1-h^2/2` and `h^2/2<=epsilon^2/8<epsilon`. If also
`|y|<=|x|`, the maximum axis projection would be at most
`(1-epsilon)(cos h+sin h)<W`, a contradiction. Hence `|y|>|x|` and
(5.1) gives

    |y| >= cos h+sin h-(1-epsilon)tan h.

Put `d=1-cos h`, so `0<=d<=h^2/2`. The right side is

    1-d+(epsilon-d)tan h.

Here `epsilon-d>0`; the elementary inequality `tan h>=h` therefore gives

    |y| >= 1+epsilon*h-(1+h)h^2/2
         >= 1+epsilon*h/2.

The last step uses `h+h^2<=epsilon`, which follows from
`h<=epsilon/2` and `epsilon<=1`. At `h=0` the inequality reduces to the usual
unit separation. Thus a contact whose projected side intervals overlap by
at least epsilon acquires a definite linear separation cost when the square
orientations differ slightly.

In the candidate, the parallel contact chains have positive tangential
overlaps. Inequality (5.2) is therefore a possible input to an analytic local
orientation argument, coupled to balanced forces. It does not by itself
prove local optimality: the other center coordinates and the common tilt
may also change, and their contributions must be controlled in the same
inequality. In particular the failed frozen candidate stress must not be
reused as a uniform tilt bound.

## 6. Concrete continuation

The odd-cycle route now has an exact and small combinatorial target: prove
the continuous state inequalities, then the two expressions in (2.1), with
the desired equality conditions. A sharp type word would be a meaningful
intermediate conclusion, but it would still need geometric pair equalities.

The stress route can retain the central square explicitly, use the exact
center support of BALANCED_SEPARATOR_REDUCTION.md, and reduce selected
orientation support terms using the three force-triangle cases. The rotation
penalty (5.2) offers a way to justify shared orientations near a candidate
contact chain. Neither route currently forces the five-corner chain from
every minimizing packing. That unrestricted structural implication remains
the main open step.
