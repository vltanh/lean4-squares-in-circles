# Local optimality and complete local equality of the eleven square family

The exact candidate family is a local minimum in the unrestricted physical
packing problem: every square may translate and rotate independently, and
separating-axis owners may switch. More precisely, after normalizing the disk
center and allowing a common rotation, there is a neighborhood of the whole
closed sliding family in which every packing satisfies `q≥q_c`. A packing in
this neighborhood has `q=q_c` if and only if it belongs to the same sliding
family. The reflected family has the corresponding statement by reflection.

The proof combines the positive stress from `FIXED_ORIENTATION_STRESS.md`,
strict margins for the angular owner ties, and a first-order compactness
argument. The neighborhood is existential; this result does not assign a
numerical capture radius. It gives neither a global lower bound nor an
exhaustive classification of distant packing configurations.

## Local physical separator choices

Use continuous angle representatives near the reference orientations, and fix
the common rotation by setting the angle of square 0 to zero. The nine
parallel contacts are

\[
E=\{01,02,14,23,34,45,56,78,9\,10\}.
\]

At each of these contacts the signed reference normal `n_e` has
`n_e·(p_j^*−p_i^*)=1`. Write

\[
\tau_e=(Jn_e)\cdot(p_j^*-p_i^*),
\]

where `J(x,y)=(-y,x)` is the quarter turn. The exact checker proves
`|τ_e|<1` uniformly over the slider interval, enlarged on both sides by
`10⁻⁴`. Thus every parallel pair shares a positive edge segment. In a
sufficiently small neighborhood, the only possible physical separator axes
for this pair are the two nearby owner normals belonging to that shared edge.
The opposite signs and the two perpendicular axes fail strictly at the
reference configuration and continue to fail nearby.

The five nonparallel contacts are `0,10`, `4,8`, `6,7`, `7,9`, and `8,9`.
Their selected signed normals are the ones in the contact-system note. At each
of these pairs, every other unoriented owner axis fails its separation
inequality with slack less than `−1/100`. All fifteen alternative axes are
checked. The opposite sign of the selected axis also fails strictly since the
selected projection is a positive support sum. Hence each selected signed
owner remains mandatory for that pair in some neighborhood.

This establishes the local case cover from actual nonoverlap. No owner is
chosen by assuming that a numerically convenient constraint stays active.

## The derivative at a parallel owner tie

Let a direction of perturbation consist of center velocities `v_i`, angle
velocities `ω_i`, and squared-radius velocity `ρ`. For one parallel pair, its
two candidate signed normals rotate with their respective owners. Their
common support sum, for relative angle difference `δ`, is

\[
\tfrac12(1+\cos\delta+|\sin\delta|).
\]

The derivatives of the two separator slacks are

\[
n_e\cdot(v_j-v_i)+\tau_e\omega_i-\tfrac12|\omega_j-\omega_i|,
\]

and the same expression with `τ_e ω_j` in place of `τ_e ω_i`. Physical
separation requires the maximum of these two slacks to be nonnegative.
Consequently its directional derivative is

\[
D_e=n_e\cdot(v_j-v_i)
+\frac{\tau_e}{2}(\omega_i+\omega_j)
-\frac{1-|\tau_e|}{2}|\omega_j-\omega_i|.
\]

The equality
`max(τx,τy)=τ(x+y)/2+|τ||x−y|/2` proves the formula for either sign of `τ`.
The expression retains both owners, including all ties. Smooth Taylor
expansions of sine, cosine, and center projections, together with the
Lipschitz property of absolute value and maximum, give an error
`O(||perturbation||²)` uniformly for the compact enlarged slider interval.

The ten selected disk constraints and the five nonparallel separator
constraints have their ordinary smooth directional derivatives. All of these
necessary local constraints vanish at the reference family.

## Angular balance as a finite flow problem

Let `λ_k,μ_e>1/100` be the exact stress from the fixed-orientation certificate.
For a parallel edge, define its angular penalty capacity

\[
\gamma_e=\frac{\mu_e(1-|\tau_e|)}2.
\]

First take the smooth part of each parallel derivative, omitting the absolute
value penalty. The weighted sum of all twenty-four smooth derivatives is

\[
\rho+\sum_{i=0}^{10} r_i\omega_i.
\]

Center terms cancel by the dual equations, and the coefficient of `ρ` is one.
The vector `r` is specified exactly as follows. A selected disk corner with
offset `z_k` contributes
`−2λ_k(p_i^*+z_k)·Jz_k` to `r_i`. A parallel edge contributes
`μ_e τ_e/2` to each of `r_i,r_j`. At a nonparallel contact with
`δ=θ_j^*−θ_i^*∈(0,π/2)`, put
`k_δ'=(cos δ−sin δ)/2`. The support derivative contributes
`+μ_e k_δ'` to `r_i` and `−μ_e k_δ'` to `r_j`; the selected normal's rotation
contributes an additional `μ_e τ_e` to its owner.

The exact group balances are

\[
\sum_{i=0}^6r_i=0,\qquad r_7+r_8=0,\qquad r_9+r_{10}=0.
\]

The last two are the two group-angle dual equations; using half-angle
coordinates merely multiplies each by the nonzero factor `2/(1+t²)`. The
first follows from those two and global rotation invariance: rotating all
centers and frames preserves every disk and support constraint, and the
already-balanced center derivatives contribute zero. The omitted slider
center derivative is identically zero. The checker confirms interval
consistency with these equalities, but their proof is these algebraic dual
identities, not the fact that an interval contains zero.

Orient all nine edges from smaller label to larger label. Choose the following
exact flow, using the freedom on the five-edge cycle to set `f_02=0`:

| Edge | Flow |
| --- | --- |
| `01` | `−r₀` |
| `02` | `0` |
| `14` | `−r₀−r₁` |
| `23` | `−r₂` |
| `34` | `−r₂−r₃` |
| `45` | `r₅+r₆` |
| `56` | `r₆` |
| `78` | `r₈` |
| `9,10` | `r₁₀` |

The group balances give
`r_i = incoming flow − outgoing flow` at every vertex. Therefore

\[
\sum_i r_i\omega_i=\sum_{e=(i,j)\in E}f_e(\omega_j-\omega_i).
\]

`check_local_angular_stress.py` verifies, with exact rational intervals,

\[
\boxed{\gamma_e-|f_e|>1/100\quad\text{for every }e\in E.}
\]

The bounds hold over the entire enlarged slider range. They are strict enough
that equality cannot hide in an owner-switch direction.

## The feasible first-order cone has only the slider at zero cost

For any direction satisfying the necessary first-order disk and separation
inequalities, their positively weighted sum is nonnegative. Restoring the
parallel penalties gives

\[
0\le\rho+\sum_i r_i\omega_i
-\sum_{e=(i,j)\in E}\gamma_e|\omega_j-\omega_i|.
\]

Hence

\[
\boxed{\rho\ge\frac1{100}
\sum_{e=(i,j)\in E}|\omega_j-\omega_i|\ge0.}
\]

If `ρ=0`, every angle difference along `E` vanishes. The parallel-contact
graph has precisely the three connected components
`{0,…,6}`, `{7,8}`, and `{9,10}`. Thus all angles in each group move together.
The rotation gauge `ω₀=0` fixes the first group's velocity to zero.

The weighted sum of the twenty-four constraint derivatives now equals zero.
Each individual derivative is nonnegative and every stress weight is
positive, so all twenty-four derivatives vanish. With group alignment, these
are exactly the homogeneous system given by the invertible twenty-four by
twenty-four Jacobian in the fixed-orientation certificate. After also setting
the slider velocity `v_1.x=0`, its only solution is the zero direction.

Thus a feasible direction of nonpositive radius cost is a slider direction,
plus a common rotation if the rotation gauge is not fixed. This is stronger
than stationarity of the two-variable contact root.

## From first order to an actual neighborhood theorem

Here is a sequential proof that no unstated second-order assumption is needed.
Suppose there were packings arbitrarily close to the closed candidate family
with `q≤q_c` that did not belong to the family. Choose a sequence of them
converging to that family, normalize their disk centers and the angle of square
0, and let `h_n` be the horizontal coordinate of square 1.

Compare the nth packing to the exact contact configuration with the same
`h_n` and squared radius `q_c`. This reference configuration is defined even
if `h_n` lies slightly beyond a slider endpoint. All twenty-four selected
constraints remain equalities there; the uniform angular certificates cover
this extended range. Write the displacement as `d_n V_n`, where `d_n>0` and
`||V_n||=1`. The case `d_n=0` already gives the exact contact configuration;
physical nonoverlap then forces `H≤h_n≤a` by the slider necessity argument,
contradicting the choice of the packing.

Pass to a subsequence with `h_n→h_*∈[H,a]` and `V_n→V`. The limiting direction
has unit norm, zero slider velocity, and zero square-0 angle velocity. Since
`q_n≤q_c`, its radius velocity is nonpositive. The uniform expansions above
and actual feasibility imply every necessary first-order constraint is
nonnegative at `h_*`. The preceding cone argument forces `V=0`, contradicting
its unit norm.

Therefore some neighborhood contains no packing with `q≤q_c` other than the
exact family. This proves both local optimality and complete local equality,
including the slider endpoints. Applying rigid motions, reflections, and
relabelings transports the same result to the corresponding families.

## Verification and the global frontier

Run:

```sh
python check_fixed_orientation_stress.py
python check_local_angular_stress.py
```

The new certificates use exact integer/rational arithmetic and the earlier
isolated-root certificate. No Lean source or kernel verification is involved.
Numerical free-angle experiments were useful diagnostics but are not premises:
their lower-radius outputs had overlapping squares and were rejected.

This closes the local sharpness and local equality gate for the actual
physical problem. It does not show that an arbitrary packing with `q≤q_c`
lies in this neighborhood, nor exclude other isolated or distant packing
families. Those are precisely the unresolved global classification and
orientation-uniform terminal-bound obligations.
