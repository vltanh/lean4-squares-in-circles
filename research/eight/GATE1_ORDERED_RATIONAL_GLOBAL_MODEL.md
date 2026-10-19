# Gate 1: an exhaustive ordered rational seven-angle model

2026-10-13. Companion to `GATED_ROADMAP_2026_10_13.md`.
This is a full-domain coordinate theorem, **not** the sharp radius bound.
It strengthens the eight-angle representation in
`GLOBAL_SAT_ANGLE_FIBER_DUALITY.md` by removing the common rotation gauge,
retaining a closed symmetry domain, and explicitly clearing all denominators.

## Theorem 1 — exact global representation

Every packing of eight pairwise interior-disjoint unit squares in a disk
has, after translating the disk center to zero, rotating the whole plane,
and relabeling the squares, a representation with centers p_i in R^2 and

    z_1 = 0 <= z_2 <= ... <= z_8 <= 1.

Conversely, the vertex inequalities and 28 SAT disjunctions below define
actual unit-square packings. No central square, contact, common frame,
seven-outer hypothesis, or candidate topology is assumed.

The physical continuous frame domain is thus the **seven-dimensional
closed simplex**, not an eight-dimensional orientation product.
Its redundant boundary representatives are intentionally retained.

### Proof of the normalization

Translate the given disk center to zero. Choose any one square and rotate
a side-normal frame of that square to the standard basis. A unit square's
orientation is unchanged by a quarter-turn. Represent each remaining
relative frame angle by theta_i in [0,pi/2), then sort these seven angles
and relabel their centers and all pair labels consistently. The chosen
square is label 1 with theta_1=0; ties cause no problem.

Put z_i=tan(theta_i/2). This is increasing on [0,pi/2] and maps that interval
to [0,1]. Passing to the closed domain adds theta=pi/2 as a duplicate
representation of theta=0, not a new geometric object. It neither loses
an equality configuration nor requires a discontinuous strict tie rule.

Conversely every z in the displayed simplex gives genuine orthonormal
frames by the rational formulas below. This proves the normalization in
both directions. No assertion of a unique representative is needed. QED.

## 2. Genuine vertices, with integer-coefficient polynomial disk inequalities

For each i define

    d_i = 1 + z_i^2,
    E_i = (1-z_i^2, 2z_i),
    F_i = (-2z_i, 1-z_i^2),
    e_i = E_i/d_i,   f_i = F_i/d_i.

Direct expansion gives |E_i|^2=|F_i|^2=d_i^2 and E_i dot F_i=0.
Hence e_i,f_i are an orthonormal frame and the actual four vertices are

    v_i(s,t) = p_i + (s E_i + t F_i)/(2 d_i),  s,t in {-1,1}.

A square is contained in the closed radius-sqrt(q) disk exactly when its
four vertices are. One direction is immediate; the other follows because
the square is their convex hull and the disk is convex.

Since 1 <= d_i <= 2, the vertex inequality is exactly equivalent to

    |2 d_i p_i + s E_i + t F_i|^2 <= 4 d_i^2 q.       (V)

These are 32 polynomial inequalities with integer coefficients. No sign
of an inequality is changed and no extra root is introduced.

## 3. A common rational support width for all eight owners of a pair

Fix i<j, set a=z_i, b=z_j, Delta=b-a, and define

    P_ij = (1+ab)(1+ab+b-a).

For a unit direction n, the projected half-width of square i is

    H_i(n) = (|n dot e_i| + |n dot f_i|)/2.

For **each** of the eight signed true owner axes

    n in {+e_i,-e_i,+f_i,-f_i,+e_j,-e_j,+f_j,-f_j},

the sum of the two genuine half-widths is the SAME rational expression:

    w_ij = H_i(n)+H_j(n) = P_ij/(d_i d_j).           (W)

### Proof

The ordered relative angle delta=theta_j-theta_i belongs to [0,pi/2].
One square has half-width 1/2 on its own side-normal, and the other has
half-width (cos(delta)+sin(delta))/2 on that axis or its perpendicular.
Signs of n do not change half-width. Thus

    w_ij = (1+cos(delta)+sin(delta))/2.

The rational frame identities give

    cos(delta) = ((1+ab)^2-(b-a)^2)/(d_i d_j),
    sin(delta) = 2(b-a)(1+ab)/(d_i d_j),
    d_i d_j = (1+ab)^2+(b-a)^2.

Adding the three numerators proves (W). All signs are valid on the CLOSED
simplex. In particular

    1+ab-(b-a) = (1-b)+a(1+b) >= 0,
    P_ij-d_i d_j = (b-a)(1+ab-(b-a)) >= 0,

so w_ij>=1, including coincident and quarter-turn-equivalent frames. QED.

## 4. All 28 exact eight-way SAT disjunctions

For every i<j choose an owner k in {i,j}, one numerator U_k in {E_k,F_k},
and a sign sigma in {-1,1}. Write ell for the other index in {i,j}.
The associated actual directed separating inequality is

    (sigma U_k/d_k) dot (p_j-p_i) >= w_ij.

Clearing the strictly positive d_i d_j yields exactly

    sigma d_ell U_k dot (p_j-p_i) >= P_ij.           (S)

There are eight such options per unordered pair, and at least one must
hold. All 28 pair conditions are imposed. Choosing one holding option
for every pair gives a full owner word; taking the union over all words
recovers precisely the disjunction, even when several choices hold.

### Why these disjunctions are necessary and sufficient

For two centrally symmetric squares with centered shapes K_i,K_j, their
open interiors overlap exactly when p_j-p_i belongs to the interior of
the Minkowski sum K_i+K_j. This sum is the convex polygon generated by the
four side directions of the two squares. Its facet normals are among
+-e_i,+-f_i,+-e_j,+-f_j. Thus p_j-p_i is outside its open interior exactly
when at least one facet-support inequality holds weakly, which is (S).

Equivalently this is the separating-axis theorem for the two actual
squares. Coincident facet normals merely duplicate an option. Weak
inequalities intentionally admit edge or corner tangency; they do not
admit overlapping open interiors.

Therefore (V), all 28 disjunctions (S), and the ordered simplex are
necessary and sufficient for a true packing. This finishes Theorem 1.

## 5. Compactness and attainment below a fixed ceiling

Let Q be any fixed finite ceiling for which the domain is nonempty; in
this project one may use Q=9789/2500, which is above the actual construction.
Average the four vertex squared norms of square i:

    (1/4) sum_{s,t} |v_i(s,t)|^2 = |p_i|^2 + 1/2.

Containment implies |p_i|^2 <= q-1/2 <= Q-1/2 and q>=1/2.
Hence the centers are uniformly bounded. The simplex and [1/2,Q] are
compact. For a fixed owner word, (V) and (S) are closed polynomial
inequalities; the finite union over all words is closed as well.
The complete feasible domain below Q is therefore compact.

The continuous objective q attains its minimum on that nonempty domain.
Since the candidate gives a packing below Q, this attained minimum is
also the unrestricted global infimum: configurations with q>Q cannot
improve it. This argument does not presume the candidate is optimal.

## 6. Symmetries and boundaries that must not be lost later

* z_i=z_j represents parallel frames and is allowed.
* z_1=0 and z_8=1 may represent quarter-turn-equivalent frames.
* Several owner choices may simultaneously be valid.
* A separator may be a tangency, so equality in (S) is allowed.
* A circle constraint may be slack or an equality.
* Centers are not forced to be contacts, radial, or in a selected chart.
* Relabeling by orientation is unrelated to cyclic center order or the
  central-square labels used by older conditional lemmas.

A later branch proof must either work directly with these conventions or
supply an explicit relabeling and coverage implication. In particular,
strict orientation ordering may not be imposed to simplify a search.

## 7. Arithmetic regression, not the theorem

`verify_ordered_rational_gate.py` uses only Fraction arithmetic. Its local
execution checked 3,672 signed SAT polynomial/residual identities,
vertex denominator identities, edge/corner tangencies, the z=0/1 duplicate,
and exact common-rotation normalization of eight rational frames.
The script checks the implementation of the formulas. The full continuous
coverage theorem is the hand proof above, not those finite tests.

## Gate exit and limit of the result

**Gate 1 passes:** the domain, actual geometry, owner disjunctions,
boundaries, positive denominators, and compactness are explicit and proved.

**Not proved:** any sharp lower bound for the union, any reduction of the
raw 8^28 words to a manageable structural list, or any global equality
classification. Gate 2 must next make the per-fiber proof alternatives
complete, including zero-anchor and strict-certificate issues.
