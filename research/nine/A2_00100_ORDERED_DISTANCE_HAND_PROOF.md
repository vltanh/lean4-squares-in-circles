# Complete D-parent closure by ordered octagon and original-selector rows

November 3, 2026. This document proves the additional row and coverage rules
used by the frozen `disk_octagon_structural_v3` certificate. It retains the
unchanged original-nine strict `001/00` caller and closes exactly one original
cell of the accepted 231-cell cover. It asserts no whole-mask closure.

## 1. Original caller and the exact parent

Let nine physical unit squares with pairwise disjoint interiors be contained
in a disk of squared radius `q<Q=1105/256`. Keep the original witness
A,B,C,D;E,F,G and every original frame, corner, physical pair, and marked bit.
The horizontal center-cone comparisons hold on the three main links and two
short links; AB, BC, EF, FG are actual, while CD is strictly weak. Use the
accepted common vertical normalization and its proved consequences. In
particular `y_D-y_C>2/3`, `y_G>y_D`, `29/60<x_C<4/5`, and no other original
with nonnegative horizontal coordinate lies at or below C.

This closure concerns the immutable original parent
`positive-3622c4448973035b`, whose complete original path is

```json
[["angle",3,1],["angle_cut",[0,"0"],1],
 ["alternate_four_escape",[1,7],[5]]]
```

Its ID is the original sign plus the first sixteen hexadecimal characters of
the SHA256 of the compact original-path JSON. The independent checker verifies
the path and ID against the unchanged fixed register. New descendants never
replace this parent in the register.

The original square frame variables have their frozen meanings
`AL(i)=alpha_i`, `BE(i)=beta_i`, `AB(i)=|beta_i|`, and
`GI(i)=g_i=1/[2(alpha_i+|beta_i|)]`. Write
`h_i=(alpha_i+|beta_i|)/2`; thus `g_i=1/(4h_i)`. The physical square contains
the concentric axis-aligned inset of halfwidth `g_i`, and

    1/2 <= h_i <= 1/sqrt(2),
    g_i >= 1/(2sqrt(2)).

The unchanged version14 physical verifier supplies all earlier rows. Its
SHA256 is
`ec1b7de7b15bcc9d89d12087bff974c68e6d056bdaae26b482d514027ec97993`.
The accepted finite tables remain established inputs, with their original
scopes; this package does not describe their unchanged proofs as fresh work.

## 2. Physical center distance and the rational octagon union

Each physical unit square contains the concentric open disk of radius `1/2`.
If the distance between two square centers were less than `1`, these two open
disks would overlap, and so would the interiors of the original squares.
Consequently every pair of original centers satisfies

    |c_j-c_i| >= 1.                                    (1)

This includes contact at equality. It does not constrain their independent
orientations.

Let `d` be any vector of norm at least `1`. Let `R` be an orthogonal rotation
and write `w=R^T d`. Consider the following eight alternatives, in this order:

    w_x >= 12/13,       -w_x >= 12/13,
    w_y >= 12/13,       -w_y >= 12/13,
    w_x+w_y >= 17/13,    w_x-w_y >= 17/13,
   -w_x+w_y >= 17/13,   -w_x-w_y >= 17/13.              (2)

Their closed complements define the convex polygon

    |w_x| <= 12/13, |w_y| <= 12/13,
    |w_x|+|w_y| <= 17/13.

Its eight vertices are `(±12/13,±5/13)` and `(±5/13,±12/13)`, with
independent signs. Every vertex has squared norm `(144+25)/169=1`.
The independent arithmetic checker obtains exactly these vertices by
intersecting every pair of boundary lines and testing all eight halfplanes.

Every point in the closed polygon is a convex combination of these vertices.
The squared Euclidean norm is strictly convex, so a nonvertex point of the
polygon has norm strictly less than `1`: a convex representation of any
nonvertex uses at least two distinct vertices with positive weights. If all
eight alternatives in (2) failed, every defining inequality of the polygon
would be strict. Such a point is not a vertex and has norm less than `1`,
contradicting `|w|=|d|>=1`. Therefore (2) is an exhaustive union on the original
physical pair. No positive margin above distance `1` is assumed.

The rotation in a certificate is encoded by an exact rational half-angle
`t=p/q`, with `q>0`:

    c=(1-t²)/(1+t²), s=2t/(1+t²),
    R=[[c,-s],[s,c]].

The identity `c²+s²=1` is exact rational arithmetic. For a base normal
`(a,b)` from `(1,0),(-1,0),(0,1),(0,-1),(1,1),(1,-1),(-1,1),(-1,-1)`,
the world normal is `(n_x,n_y)=(a*c-b*s,a*s+b*c)`.
On `d=c_j-c_i`, the corresponding escape is exactly the linear row

    n_x*x_i+n_y*y_i-n_x*x_j-n_y*y_j <= -threshold,      (3)

where the threshold is `12/13` for the first four normals and `17/13`
for the last four. The step marker is
`["disk8_ordered",[i,j,p,q],[k]]`, with distinct originals `0<=i<j<9`
and `0<=k<8`. These rows concern the same original centers, without products
or substitute frames.

## 3. Ordered closed predecessor complements

Suppose a caller satisfies the exhaustive union of exact linear inequalities
`f_0(z)<=0,...,f_(m-1)(z)<=0`. For each `k`, define child `k` by

    f_k(z)<=0, and -f_r(z)<=0 for every r<k.            (4)

For any point of the caller, choose the smallest index with `f_k(z)<=0`.
Every earlier `f_r(z)` is strictly positive, hence satisfies its closed
complement `-f_r(z)<=0`. The point therefore lies in child `k`. All `m`
children cover the caller. Replacing strict predecessor complements by
closed complements retains boundary points and may add overlap; it cannot
remove a caller point.

In a `disk8_ordered` step, append the chosen primary row (3), then negatives
of primary rows `0,...,k-1`, in that order. This gives eight complete children
and a definite exact row order. The previous `disk8` kind, if encountered,
adds only its primary row and retains its original unordered semantics.

This reasoning uses exact linear predicates. It does not authorize negating
necessary linear relaxations of a nonlinear SAT condition. The frozen
eight-way SAT children retain their original semantics.

## 4. Unique penultimate original and the strong selector union

The full hand proof and dependency scopes are frozen in
[`WEAK_OUTER_UNIQUE_PENULTIMATE_ORIGINAL_HAND_PROOF.md`](WEAK_OUTER_UNIQUE_PENULTIMATE_ORIGINAL_HAND_PROOF.md).
The statement used here is: if four distinct original centers A',B',X,D,
disjoint from the same E,F,G, form a center-cone chain and its first two links
are actual, then `X=C`.

Here is the complete argument from the accepted inputs. If XD is actual,
the new four-chain and unchanged actual short chain form a `000/00` witness,
excluded by the established strict-radius cap theorem. Hence XD is strictly
weak, and the new witness is `001/00`. The accepted all-sign low-gap theorem
gives `|y_D-y_X|>2/3`. The original G-order theorem gives `y_G>y_D`. If X is
above D, reflect the entire original packing in the horizontal axis and
apply that same G-order theorem to the new witness: it gives `y_G<y_D`, a
contradiction. Therefore X is below D. The accepted C-localization and bottom
exclusion theorem, applied to this new witness, gives `x_X>29/60` and excludes
every other original of nonnegative horizontal coordinate at or below X.
The old exclusion at C gives `y_X>y_C`; the new one at X gives `y_C>y_X`
whenever `X!=C`. Thus X must equal C.

The argument is only asserted for `q<Q`, because the actual-XD branch uses
the strict `000/00` terminal. Permuting original labels and reflecting the
whole packing preserve every physical square, pair, cone, and marked bit.

There are exactly 48 eligible chains in the new selector: choose
`X` from `{A,B,H,I}` and then choose ordered distinct `A',B'` from the
remaining four members of `{A,B,C,H,I}`. All end at D, all avoid E,F,G,
and none has `X=C`. For one such chain, make eight primary linear forms:
six cone forms, two for each successive pair, followed by the two actual
forms for the first two links. Their order is

    x_j-x_i-(y_j-y_i), x_j-x_i+(y_j-y_i)  (each edge),
    x_B'-x_A'-(AL(A')+AB(A')+AL(B')+AB(B'))/2,
    x_X-x_B'-(AL(B')+AB(B')+AL(X)+AB(X))/2.

If all eight forms were nonnegative, all hypotheses of the uniqueness
theorem would hold with `X!=C`, a contradiction. At least one form is
negative, and therefore the eight closed escapes `f_k<=0` cover the caller.
The `first_two_escape` kind uses exactly the ordered children (4).

The original ordered pairs AB, BC, and AC are globally cone and actual
pairs. AC follows by adding the two original cone inequalities and actual
AB and BC gaps; the latter sum is at least `h_A+h_C`. Thus, for any such pair
among the first two links, its two cone forms and one actual form can be
omitted. If all retained forms were nonnegative, the omitted globally true
ones would complete the forbidden configuration, so the retained escapes
still cover. There can be at most one omitted first-prefix pair: two would
force the original ordered chain A,B,C and the forbidden choice `X=C`.

Exactly 11 of the 48 chains omit one known pair and have five children;
the remaining 37 have eight children. The `first_two_reduced_escape` child
index refers to the retained ordered list, and its row expansion is its
primary form followed by the negative earlier retained forms. The checker
independently enforces the original labels, endpoint D, distinctness,
`X!=C`, omitted-pair criterion, retained count, and every child index.

## 5. The four guarded ABXD rows

For `X=H` or `I`, suppose the path establishes all three cones of A,B,X,D.
AB is actual in the original caller. The theorem above forces BX to be
strictly weak. Cones plus physical inset disjointness force the first two
inset inequalities below. The four necessary closed rows are

    x_B-x_X+g_B+g_X <= 0,
    x_X-x_D+g_X+g_D <= 0,
    x_X-x_B-(AL(B)+AB(B)+AL(X)+AB(X))/2 <= 0,
    y_C-y_X+g_C+g_X <= 0.                              (5)

For the final row, actual BC and weak BX give
`x_X-x_C<h_X-h_C<=1/sqrt(2)-1/2<g_C+g_X`.
The universal center bound `|c_i|<rho=91/60`, actual AB, and the BX inset
gap imply `x_X>-31/60+g_B+g_X>0`. The opposite horizontal gap satisfies
`x_C-x_X<79/60-g_B-g_X<g_C+g_X`, using
`g_B+g_C+2g_X>=sqrt(2)>79/60`.
Thus the C and X insets overlap strictly horizontally and must separate
vertically. The accepted bottom exclusion at C fixes the sign to
`y_X>y_C`, proving the last row of (5). The only radical comparisons needed
here have exact positive reserves

    1/2-(31/60)²=839/3600,
    2-(79/60)²=959/3600.

The v3 checker allows these four rows only at the following syntactically
proved guards, each of which retains all six ABXD cone inequalities:

| Path kind | Marker | Child |
|---|---|---|
| Frozen `alternate_four_escape` | `[1,X]` | 6 or 7 |
| New `first_two_escape` | `[0,1,X,3]` | 6 or 7 |
| New `first_two_reduced_escape` | `[0,1,X,3]` | 4 |

In the last case the two original AB cone rows and actual AB form were
omitted as globally true; predecessor complements retain the other four
cone forms. Outside these guards v3 adds none of the four rows. The checker
adds them once per eligible X, sorted by `X=7,8`, in the displayed order.

## 6. Exact bound induction, row sums, and complete parent coverage

The coordinate prefix proves 33 rational bounds on the same original
parent, by finite induction. A round collects the unchanged physical rows
at the already established intervals. For objective `s*z_k`, `s=±1`, and
nonnegative rational row weights, let

    r=sum_j(lambda_j*a_j)-s*e_k,
    U=sum_j(lambda_j*b_j)+sum_l(M_l*|r_l|).

Here `a_j*z<=b_j` and `|z_l|<=M_l` are valid at the beginning of that
round. Their weighted sum proves `s*z_k<=U`; the checker compares this
exact value to the recorded bound. Every proposal in the same round uses
the same old intervals. Only the next round may use the tightened bounds.
The final proved intervals can be intersected with every descendant's
decoded intervals because they hold on the entire immutable parent.

For a v3 leaf, regenerate the frozen original rows and exact variable
bounds under these proved intervals. Insert all new path rows, in path
order; then insert the four guarded rows for each eligible X in sorted
order; leave adaptive original-circle rows last. The supplied nonnegative
rational weights prove a contradiction precisely when

    -sum_j(lambda_j*b_j)
      -sum_l(M_l*|sum_j(lambda_j*a_jl)|) > 0.           (6)

All 458 D leaves satisfy (6), with minimum exact reserve
`108729700542755497/59855924914754578022400`.
The printed tables include every used row, exact weight, residual
coefficient, absolute variable bound, and positive reserve.

The complete D tree has 67 internal nodes: 63 ordered eight-child octagon
splits and four five-child reduced ABI-D selectors. Hence it has
`1+63*(8-1)+4*(5-1)=458` leaves. Its deepest relative path has length six.
There are zero retained frontier nodes. The independent trie reconstruction
requires a single query at each internal node, exactly its complete child
set, no duplicate leaves, no leaf that is another leaf's ancestor, and
the unchanged parent prefix on every path. All 458 leaves pass. A missing
leaf is a failed coverage proof, regardless of how many other leaves pass.

The checker also retains the original four-child proxy and eight-child SAT
decoders for earlier physical proofs. No proxy, SAT, or new angle split is
needed inside this particular completed D tree.

The numerical solver discovered weights and rotations only. One final
default HiGHS call returned status 4 without a point; a dual-simplex retry
with presolve disabled supplied a point from which nine further nodes
completed the tree. This numerical fallback changes no row or certificate
semantics. The exact proof is the complete union and rational arithmetic
above, independently replayable without a numerical optimizer, Lean, Lake,
or CI.
