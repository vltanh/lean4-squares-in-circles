# Sharp stress for fixed candidate frames and fourteen separators

Fix the exact three frames at the isolated root `(q_c,t_c)` in
`CANDIDATE_CONTACT_SYSTEM.md`. There is a positive stress proving the sharp
bound `q≥q_c` for arbitrary centers satisfying the fourteen listed separator
inequalities and the ten listed corner bounds. There is no small-neighborhood
assumption on the centers in this result. Among actual packings in this
conditional class, equality holds exactly for the horizontal sliding family.

The fixed frames and fourteen separators are hypotheses. A reduction deriving
them from an arbitrary eleven-square packing remains necessary for a global
sharp theorem.

## The active functions and the exact dual

Use the ten signed corners and fourteen signed pair directions in
`CANDIDATE_CONTACT_SYSTEM.md`. For a selected corner of square `i`, write its
fixed frame offset as `v_k`, and set

\[
g_k(p,q)=q-|p_i+v_k|^2.
\]

For a selected pair `e=(i,j)` with direction `n_e` and support sum `b_e`, set

\[
h_e(p)=n_e\cdot(p_j-p_i)-b_e.
\]

All twenty-four functions vanish at the reference centers `p_i^*` and `q_c`.
The same equalities hold for every slider value `h`; none depends on square
1's horizontal coordinate when these frames are fixed.

To specify a unique dual, temporarily allow the two tilted group half-angle
parameters to vary independently, while keeping squares 0 through 6 parallel
to the coordinate axes. Let `J` be the Jacobian of these twenty-four functions
with respect to the following twenty-four coordinates:

1. all center coordinates in label order, except the horizontal coordinate of
   square 1: twenty-one coordinates;
2. the two independent tilted-group half-angle parameters;
3. `q`.

The support sums for cross-group contacts are the smooth expressions `k`,
`k'`, or `K`, in the strictly ordered-angle branch specified in the contact
note. Same-group support sums are identically one. Define the exact weights
`w=(λ_1,…,λ_10,μ_1,…,μ_14)` by

\[
\boxed{J^T w=e_q}.
\]

`check_fixed_orientation_stress.py` encloses every entry of this matrix on the
root rectangle and solves the interval linear system with rational outward
arithmetic. Every pivot interval excludes zero. Consequently the actual
matrix at the root is invertible and these weights are well defined. Every
weight satisfies the certified strict bound

\[
\lambda_k>1/100,\qquad\mu_e>1/100.
\]

The omitted center derivative is identically zero for all twenty-four active
functions, so the dual provides balance in all twenty-two center coordinates.
The `q` coordinate gives `Σλ_k=1`. The other two dual rows provide group-angle
balance for the local analysis in `LOCAL_OPTIMALITY.md`; those rows are not
needed for the fixed-frame square-completion argument below. The matrix and
weights are independent of the slider coordinate.

The checker differentiates the frame parameterization exactly:

\[
\frac{dc}{dt}=\frac{-4t}{(1+t^2)^2},\qquad
\frac{ds}{dt}=\frac{2(1-t^2)}{(1+t^2)^2}.
\]

For the interval linear solve, each arithmetic operation is rounded outward to
multiples of `10⁻³⁰`, using integer floor and ceiling. The selected Gaussian
pivots depend only on exact rational bounds. Normalized diagonal entries and
eliminated entries are set to their algebraically exact values one and zero.
Induction through elimination and back substitution therefore encloses the
unique real solution. The successful output includes outward rational
intervals for all twenty-four weights.

## Global square-completion identity

Let `Δp_i=p_i−p_i^*`, and define

\[
L_i=\sum_{k\text{ belonging to }i}\lambda_k.
\]

Exact expansion of each corner norm, together with the center-balance and
`Σλ_k=1` identities, gives

\[
\boxed{\sum_k\lambda_k g_k(p,q)+\sum_e\mu_e h_e(p)
=q-q_c-\sum_i L_i|\Delta p_i|^2.}
\]

This identity holds for every choice of centers and `q`, with the frames
fixed. In particular, if all ten corner bounds and all fourteen separator
inequalities hold, the left side is nonnegative. Hence

\[
q\ge q_c+\sum_i L_i|\Delta p_i|^2\ge q_c.
\]

It suffices to assume the selected corner bounds and separators for the lower
bound. Full disk containment and pairwise nonoverlap imply the corner bounds,
but do not automatically imply this chosen set of fourteen separators.

## Complete equality reconstruction in this conditional class

At `q=q_c`, every selected corner and separator is tight because every weight
is positive. The square-completion term also vanishes. Thus the centers of
squares `0,2,3,5,6,7,9,10`, each having a positive corner weight, equal their
reference centers.

The remaining centers are recovered as follows:

- Separator `(3,4)` fixes `p_4.x=p_3.x−1`; separator `(4,5)` fixes
  `p_4.y=p_5.y+1`. Thus square 4 is fixed.
- Separator `(4,8)` fixes `p_8.x=p_4.x−k`. Separator `(7,8)` gives
  `u·(p_8−p_7)=1`. Since `s>0`, this fixes `p_8.y` as well.
- Separator `(0,1)` gives `p_1.y=b−1`. Its horizontal coordinate `h` remains.

For an actual packing, the full physical pair constraints then force exactly
`H≤h≤a`; this necessity does not assume that pair `(1,8)` uses a prescribed
owner.

First, `q_c<81/16` implies `R_c<9/4`. Disk containment of the axis-parallel
square 1 gives `|h|≤R_c−1/2<7/4`. The vertical projections of squares 1 and 2
overlap, because `|d−(b−1)|<1`. Therefore their nonoverlap requires
`|h−(a+1)|≥1`. The possibility `h≥a+2` is excluded by `a>0` and `h<7/4`, so
`h≤a`.

Next let `Δ=p_1−p_8=(X,Y)` and use the range `−7/4≤h≤a`. The exact checker
verifies uniformly on the root rectangle

\[
|X|<k,\quad |Y|<k,\quad |j\cdot\Delta|<k,
\qquad u\cdot\Delta>-k.
\]

For squares 1 and 8, the support sum in each of their four unoriented axes
`ex,ey,u,j` is `k`. The separating-axis theorem leaves only
`u·Δ≥k`. Substituting the known center of square 8 gives

\[
ch+s(b-1)-(1-r)\ge k,
\]

which is precisely `h≥H`. Conversely, the earlier feasibility certificate
proves every `h∈[H,a]` packs the disk and satisfies all fourteen separators.
This proves necessity and sufficiency for equality in the conditional class.

## Verification and remaining scope

Run:

```sh
python check_fixed_orientation_stress.py
```

The script checks the root prerequisite, matrix invertibility, positivity of
all twenty-four weights, and the physical slider necessity bounds. It writes
no Lean and makes no kernel-verification claim.

This settles a sharp terminal theorem with fixed frames and specified
separators, including its full equality family. The unrestricted local theorem
in `LOCAL_OPTIMALITY.md` allows all eleven orientations to move and retains
owner ties. Neither result provides the still-open global reduction of every
packing to a controlled terminal class.
