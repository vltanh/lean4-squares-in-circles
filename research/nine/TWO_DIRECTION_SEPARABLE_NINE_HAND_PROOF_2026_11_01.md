# Sharp nine-square theorem for every two-direction separation cover

November 1, 2026. **Hand theorem, with explicit dependencies and equality
domain.** No mathematical enumeration, external mathematical script, Lean,
or CI was used in this derivation.

## 1. The theorem and its scope

Write `Q=1105/256`. Suppose nine unit squares with pairwise disjoint open
interiors lie in a disk of squared radius `q`. Assume there are two fixed
unit directions `e,f` such that **every pair of squares has disjoint open
projections along at least one of `e,f`**. The two directions need not be
perpendicular, and the nine squares may initially have unrelated frames.

**Theorem.** Such a packing satisfies `q>=Q`. At `q=Q`, the covering
directions are necessarily perpendicular, and seven squares belong to the
aligned family in Section 7, with the two endpoint signs equal. Section 8 gives a necessary-and-sufficient
finite parameter domain for all equality packings admitting a two-direction
cover.

In particular, this proves the sharp bound for every packing of nine
parallel unit squares, without requiring rows, stratification, a chosen
contact graph, or a convenient complement to a particular four-chain.

This theorem is conditional on the existence of the two-direction cover.
It does not supply a cover for unrestricted packings. The exact example in
`NO_GLOBAL_ORTHOGONAL_FRAME.md` has no orthogonal cover; by this theorem's
equality conclusion, it has no two-direction cover of any angle either.
No original positional root is removed merely because some of its
assignments satisfy this theorem's premise.

### Named dependencies

The lower-bound proof invokes precisely two existing nontrivial theorems:

1. Greene's finite-poset chain/antichain partition theorem, stated exactly
   in Section 3, with its original publication cited there.
2. The physical four-plus-three projection-chain terminal, Theorem 2 of
   `PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`.
   Its hypothesis is two disjoint projection chains of lengths four and
   three along one direction, **only physical nonoverlap**, and disk
   containment. Its conclusion is `q>=Q`, with the equality endpoints
   printed in Section 7 below. It does not assume a perpendicular
   separating direction.

All other needed geometric and combinatorial reductions are proved below.
In particular, no implication from a Greene partition to a geometric grid
is used.

For the additional equality simplification excluding crossed endpoint
signs, Section 7 uses the separate hand derivation
`CROSSED_SIGN_EQUALITY_EXCLUSION_2026_11_01.md`. That addendum uses only
the displayed anchor form, the common-coordinate separation just proved
here, and elementary containment/support inequalities.

## 2. Projection orders, widths, and the chain bound

Translate the disk center to zero. For a square `S` with center `c_S` and
orthonormal side axes `u_S,v_S`, write

    H_S(w)=(|w.u_S|+|w.v_S|)/2,
    h_S(e)=H_S(e), h_S(f)=H_S(f).

For every unit direction, the square's projection width is at least one,
so `h_S(e),h_S(f)>=1/2`. Define strict partial orders

    S <_e T  iff  e.(c_T-c_S) >= h_S(e)+h_T(e),
    S <_f T  iff  f.(c_T-c_S) >= h_S(f)+h_T(f).

Both are transitive and irreflexive. The cover assumption means that each
distinct pair is comparable in at least one order. Therefore every
e-antichain is an f-chain, and every f-antichain is an e-chain.

We may assume `q<=Q`; otherwise the conclusion is immediate. Every center
satisfies `|c_S|<rho=61/40`, because its farthest squared corner norm is

    |c_S|^2+1/2+|c_S.u_S|+|c_S.v_S|
       >= |c_S|^2+|c_S|+1/2,

while `rho^2+rho+1/2=6961/1600>Q`. Five squares in one projection chain
would have extreme center projections differing by at least four. This
contradicts the bound `2rho=61/20<4`. Thus each order has height at most
four, and each has width at most four by the antichain-to-chain observation.

If `e,f` are parallel or antiparallel, their unoriented projection
separations coincide and every pair is comparable in a single order.
That would give a nine-chain. Hence this case is impossible at `q<=Q`.
For the rest, reverse `f` if needed so their angle satisfies
`0<theta<=pi/2`.

## 3. A nine-element chain/antichain extraction lemma

For a finite poset `P`, let `c_k` be the maximum cardinality of a union of
`k` chains, and `a_k` the maximum cardinality of a union of `k` antichains;
set `c_0=a_0=0`. Greene's theorem states that

    lambda=(c_1,c_2-c_1,c_3-c_2,...)

is a decreasing partition of `|P|`, and that its conjugate is

    lambda'=(a_1,a_2-a_1,a_3-a_2,...).

Source: Curtis Greene, *Some partitions associated with a partially ordered
set*, Journal of Combinatorial Theory, Series A **20** (1976), 69–79,
[DOI 10.1016/0097-3165(76)90078-9](https://doi.org/10.1016/0097-3165(76)90078-9);
[author's publication record](https://scholarship.haverford.edu/mathematics_facpubs/150/).
This is an explicit imported classical theorem, not a computation.

**Lemma.** A nine-element poset of height four and width at most four
has either two disjoint chains of sizes four and three or two disjoint
antichains of those sizes.

*Proof.* If `c_2>=7`, choose two chains with union at least seven and remove
their intersection from one of them. Each has size at most four; discard
elements if necessary to obtain sizes four and three. Otherwise `c_2<=6`,
so Greene's partition has first part four, every later part at most two,
and at most four parts, since its number of parts is `a_1<=4`. Its sum is
nine. The only possibility is

    lambda=(4,2,2,1), lambda'=(4,3,1,1).

Indeed three parts could sum to at most eight, and with four parts the
last three must be `2,2,1`. Hence `a_2=7`. Two antichains realizing that
union can be made disjoint; their individual sizes are at most four, so
they have sizes four and three. QED.

The argument does **not** assume that one chain partition realizes all
the values `c_k`, or that the parts of `lambda` are lengths of
simultaneously selected chains. It only uses the two separately defined
extremal union sizes.

If either projection order has height four, apply the lemma to it.
The chain alternative gives projection chains of sizes four and three
in that direction. The antichain alternative gives such chains in the
other direction. The named physical chain theorem then yields `q>=Q`.

It remains to exclude the case in which both heights are at most three.

## 4. A literal rank grid, with the full geometric inequalities

For each square let `(r_e,r_f)` be its longest-chain ranks in the two
projection orders. Comparability strictly increases the corresponding
rank. Thus equal rank pairs cannot occur at different squares, because
each distinct pair is comparable in at least one order.

If both heights are at most three, nine rank pairs inject into
`{1,2,3}^2`, so all nine occur. At a fixed f-rank the three squares
cannot be f-comparable; therefore they form an e-chain in increasing
e-rank order. The extreme span of that chain is at least one plus the
two endpoint halfwidths. The corresponding assertion holds for fixed
e-rank and f-chains.

Label the four rank corners `TL=(1,3)`, `TR=(3,3)`, `BL=(1,1)`,
`BR=(3,1)`. They satisfy the actual inequalities

    e.(c_TR-c_TL) >= 1+h_TR(e)+h_TL(e),
    e.(c_BR-c_BL) >= 1+h_BR(e)+h_BL(e),
    f.(c_TL-c_BL) >= 1+h_TL(f)+h_BL(f),
    f.(c_TR-c_BR) >= 1+h_TR(f)+h_BR(f).

This conclusion comes from equality of actual projection ranks. It is
unrelated to a proposed geometric realization of a Greene diagram.

## 5. Two small triangle support minima

Put

    c=cos(theta/2), s=sin(theta/2),
    t=c+s, d=c-s.

Then `1<t<=sqrt(2)`, `d>=0`, `t^2+d^2=2`,
`sin(theta)=t^2-1`, and `cos(theta)=t*d`.

For any square frame, the expression

    H_S(e)+H_S(f)+H_S(e+f)

is the sum of the side lengths of the bounding rectangle, in that frame,
of the triangle with vertices `0,e,-f`. To see this, in either scalar
frame coordinate the sum of the absolute projections of the three
triangle edges equals twice its projection range. The factor `1/2` in
`H_S` cancels that factor two. Likewise

    H_S(e)+H_S(f)+H_S(e-f)

is the bounding-rectangle side sum of the triangle `0,e,f`.

For any nondegenerate triangle, the minimum such side sum over rectangle
frames occurs when a rectangle axis is parallel to a triangle edge.
Indeed between consecutive changes of which vertices are extremal in
either frame coordinate, the side sum is a positive function
`A cos(phi)+B sin(phi)`. Its second derivative is its negative, so it
has no interior minimum. At a change, two vertex projections tie and
one rectangle axis is parallel to their joining edge. The finitely many
edge-aligned frames therefore suffice.

Both triangles above are isosceles. Aligning with either equal edge or
with the base gives the exact minima

    m_+ = min(1+cos(theta)+sin(theta), 2c+s),
    m_- = min(1+sin(theta), c+2s).

For the first triangle, an equal-edge frame has ranges
`1+cos(theta)` and `sin(theta)`, and the base frame has ranges `2c,s`.
For the second, those ranges are `1,sin(theta)` and `2s,c`.
This derives every entry; no sampled angle or unchecked support
minimization is hidden in the formulas.

## 6. A sharp skew-grid radius bound

Disk containment gives the linear support inequality

    w.c_S+H_S(w) <= R|w|,   R=sqrt(q).

Apply it to `TR,BL` with vectors `e+f,-e-f`, and to `BR,TL` with
`e-f,-e+f`. The four center terms sum to the left sides of the four
span inequalities in Section 4. Consequently

    4R(c+s)
      >= 4+sum_S [H_S(e)+H_S(f)+H_S(e+/-f)]
      >= 4+2m_++2m_-.

Here the plus sign belongs to `TR,BL` and the minus sign to `BR,TL`.
Therefore

    R >= (2+m_++m_-)/(2t).

We prove `2+m_++m_- >= 3sqrt(2)t` for the entire angle interval by
checking the four possible sums in the two displayed minima. In terms
of `t,d`, those sums are exactly

| chosen rectangle frames | value of the candidate sum |
| --- | --- |
| equal edge / equal edge | `2t^2+t*d` |
| equal edge / base | `t^2+3t/2+(t-1/2)d` |
| base / equal edge | `t^2+3t/2+d/2` |
| base / base | `3t` |

All four cases are elementary:

- Since `d^2=2-t^2` and `1<=t<=sqrt(2)`, we have
  `d>=sqrt(2)-t`. For the first row,

      2+2t^2+t*d-3sqrt(2)t >= (t-sqrt(2))^2 >= 0.

- In either middle row the coefficient of `d` is nonnegative.
  Using `2+t^2>=2sqrt(2)t` gives a strict lower bound for the difference,

      2+t^2+3t/2-3sqrt(2)t >= (3/2-sqrt(2))*t > 0.

- For the final row, `t<=sqrt(2)` gives

      2+3t-3sqrt(2)t >= 3sqrt(2)-4 > 0.

These cases prove `R>=3/sqrt(2)`, hence

    q>=9/2>1105/256.

Thus the branch with both projection heights at most three is impossible
under `q<=Q`. Sections 2–6 now exhaust the two-direction cover and prove
the claimed sharp lower bound.

## 7. Equality forces perpendicular directions and seven aligned squares

At `q=Q` the skew-grid branch is impossible, so Section 3 produces two
disjoint chains of lengths four and three in one of the covering
directions. Call that direction horizontal. Equality in the physical
four-plus-three theorem gives independent signs `sigma_L,sigma_R` and
the four endpoint centers

    M_L=(-3/2, sigma_L/16), M_R=(3/2, sigma_R/16),
    B_L=(-1,-15sigma_L/16), B_R=(1,-15sigma_R/16).

All four endpoint squares are aligned with the horizontal direction.
Both chain spans are sharp, so the intermediate widths equal one and
all intervening projection gaps vanish. Therefore the other three chain
squares are aligned too, with centers

    M_2=(-1/2,alpha), M_3=(1/2,beta), B_2=(0,gamma).

The matched left endpoints have center difference `(1/2,-sigma_L)`.
For two aligned unit squares with this difference, a unit projection
direction `(a,b)` can separate them only if

    |a/2-sigma_L*b| >= |a|+|b|.

The left side is at most `|a|/2+|b|`; hence `a=0`. Thus their **only**
unoriented projection-separating direction is vertical. The chain
direction is horizontal, so the other direction in the original cover
must be vertical. This proves that the covering directions are
perpendicular at equality.

Define

    U_M=sqrt(849)/16-1/2, U_B=sqrt(1041)/16-1/2.

The seven aligned squares fit the disk and are pairwise interior-disjoint
exactly when

    |alpha|<=U_M, |beta|<=U_M, |gamma|<=U_B,
    |alpha+15sigma_L/16|>=1,
    |beta+15sigma_R/16|>=1,
    |alpha-gamma|>=1, |beta-gamma|>=1.

The first three are exact corner-containment bounds. Within each chain
all pairs are horizontally separated. Among cross-chain pairs, the two
matched outer pairs have vertical gap one; exactly the four remaining
pairs represented above have horizontal center gap less than one. Thus
these inequalities check all 21 pairs among the seven anchors.

The hand argument in `CROSSED_SIGN_EQUALITY_EXCLUSION_2026_11_01.md`
proves that crossed signs admit at most one further square under this
coordinate-separation hypothesis. They therefore cannot occur in a
nine-square equality packing. Hence `sigma_L=sigma_R`, and after one
vertical reflection both signs can be fixed to `+1`. In this normalization
the seven-square inequalities simplify to

    1/16<=alpha<=U_M, 1/16<=beta<=U_M, |gamma|<=U_B,
    |alpha-gamma|>=1, |beta-gamma|>=1.

The excluded alternatives for alpha or beta would be at most `-31/16`,
outside their containment ranges. No row stratification is inferred.

## 8. Exact equality parameter domain for this whole cover class

Fix both signs to `+1` and choose the three sliders satisfying the final
five inequalities of Section 7. Let two additional
unit squares have centers `f_i=(X_i,Y_i)` and orthonormal axes `u_i,v_i`,
`i=1,2`. Put

    h_i=(|u_ix|+|v_ix|)/2=(|u_iy|+|v_iy|)/2.

The additional exact conditions are:

1. Disk containment for each additional square:

       |f_i|^2+1/2+|f_i.u_i|+|f_i.v_i| <= Q.

2. For each additional square and each of the seven anchor centers `(x,y)`:

       |X_i-x|>=h_i+1/2  OR  |Y_i-y|>=h_i+1/2.

3. For the two additional squares:

       |X_1-X_2|>=h_1+h_2  OR  |Y_1-Y_2|>=h_1+h_2.

Every equality packing with a two-direction cover has this form up to
common isometry and relabeling, by Sections 3–7. Conversely every
parameter choice satisfying Sections 7–8 is a two-direction-separable
physical packing at `q=Q`: the seven scalar conditions handle all 21
anchor pairs and the fifteen simple coordinate disjunctions handle every
remaining pair. The four fixed outer anchor corners attain `Q`.

This is a necessary-and-sufficient finite parameterization of the entire
stated class, not an assertion that every slider choice admits a
completion. The two additional squares may rotate. The parameterization
does not cover unrestricted equality packings requiring more than two
projection directions, and it does not claim to solve their classification.

### An exact witness retaining the upper gamma branch

It is not valid to delete the branch `gamma>=max(alpha,beta)+1` for a
fixed selection of the two chains. Take every square axis-aligned and set

    alpha=beta=1/2, gamma=3/2,
    f_1=(0,-1/2), f_2=(0,-3/2).

The resulting nine centers and maximal squared corner radii are

| centers | maximal squared corner radius |
| --- | --- |
| `(-3/2,1/16)`, `(3/2,1/16)` | `1105/256` |
| `(-1,-15/16)`, `(1,-15/16)` | `1105/256` |
| `(-1/2,1/2)`, `(1/2,1/2)` | `2` |
| `(0,3/2)`, `(0,-3/2)` | `17/4` |
| `(0,-1/2)` | `5/4` |

All pairs separate along a coordinate: the two inner M squares are
one unit apart horizontally; their height differs from `3/2,-1/2,-3/2`
by at least one; the three squares on `X=0` have consecutive height
gaps two and one. The short outer anchors have horizontal gap one from
all `X=0` squares and vertical gap `23/16` from the adjacent inner M
square. The long outer anchors have horizontal gap at least one from
each inner M or `X=0` square and vertical gap one from the matched short
anchor. Every other anchor pair is horizontally separated by at least
one. Thus the table is a direct exact equality witness, with all weak
contacts retained. Relabeling a lower central square as `B_2` is possible,
but it does not put both of the remaining squares above the long chain.

### Complete one-dimensional completion in the upper-gamma branch

There is a stronger exact description of this branch. Put
`U=U_B=(sqrt(1041)-8)/16`. If `gamma>=max(alpha,beta)+1`, then the two
additional squares must be **aligned and centered on `X=0`**. Label their
heights `z_1<z_2`. The entire branch is exactly the domain

    -U<=z_1, z_1+1<=z_2,
    z_2+1<=alpha<=gamma-1,
    z_2+1<=beta<=gamma-1,
    gamma<=U.

These inequalities imply `2-U<=alpha,beta<=U-1`, `3-U<=gamma<=U`,
all five anchor-slider bounds above, and containment of the two
additional aligned squares.

For necessity, an additional square of halfwidth `h` which is not
aligned at `X=0` must have `Y>=h-7/16`, by comparison with the two short
outer anchors. At least one horizontal separation fails, and the
downward alternatives lie outside the center disk. If it were
horizontally separated from `(0,gamma)`, it would have `|X|>=h+1/2`;
comparison with the corresponding long outer anchor then forces
`Y>=h+9/16`. The individual corner obstruction in the crossed-sign
addendum would give `q>=1201/256`, impossible. Thus it must be below
`gamma` in vertical projection, and

    1/16<=Y<=gamma-h-1/2<21/40.

Here `alpha,beta<=gamma-1<21/40` as well. Comparison with the long
outer anchors forces `h-1<=X<=1-h`; otherwise the upward alternative
would require `Y>=17/16`. In this horizontal interval the square
cannot be horizontally separated from both inner M squares:
separation from the left one would require `X>=h`, and from the right
one `X<=-h`. At least one inner M square therefore needs vertical
separation. Both center heights lie in `[1/16,21/40)`, so their
difference is less than one, impossible. Every additional square is
consequently aligned at `X=0`.

Each such central square lies below `gamma`. It must also be at least
one below both `alpha,beta`: an upper alternative conflicts with
`Y<=gamma-1<21/40`, and an intervening alternative is impossible since
`|alpha-beta|<2`. The displayed inequalities now follow from vertical
separation and exact aligned containment `|z_i|<=U`. Conversely those
inequalities check all inner-M/central and central/central pairs; every
central square is horizontally separated from each fixed outer anchor.
Thus they suffice, proving the exact completion domain.

## 9. Consequence for the global A.2 obligation

Every physical packing with `q<Q`, if one existed, would now necessarily
have **no** two-direction separation cover. The previous conditional
two-direction draft can be replaced by this theorem and its exact
dependencies. The remaining global caller must exclude or route those
genuinely many-direction packings; this manuscript makes no claim that
the caller is complete and makes no change to the canonical root counts.
