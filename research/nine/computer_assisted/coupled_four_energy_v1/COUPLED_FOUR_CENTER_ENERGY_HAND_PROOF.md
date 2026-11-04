# Coupled four-center energy: exact affine and compact lifted rows

November 4, 2026. This is a conversion of the already accepted universal
four-original center-energy inequality. It is valid in every mask and needs
no additional geometric hypothesis or case split. It grants no original-cell
or mask closure by itself. No Lean, Lake or CI.

## 1. Physical premise and retained originals

Choose four distinct retained original unit squares, with centers
`c_a,c_b,c_c,c_d` in that order of labels. Their open incircles have radius
one half, so all six center distances are at least one. Use the accepted
planar four-center inequality

\[
 E_4=\sum_{i<j}|c_j-c_i|^2\ge8.
\]

The unchanged accepted source is `four_center_rows.py` in the original
caller packet. This document does not supply or claim a new proof of that
physical inequality. It proves a stronger interval-to-affine conversion
than six independent scalar secants. Every original frame, corner,
physical pair and marked mask comparison remains part of the caller.

Let `e=(p,q)` be any nonzero rational direction, let `f=(-q,p)`, and put
`n=p^2+q^2>0`. Define

\[
 u=(e\cdot(c_b-c_a),e\cdot(c_c-c_a),e\cdot(c_d-c_a)).
\]

Its six scalar differences have coefficient vectors

| Original pair | Coefficient on `u` |
|---|---|
| `ab` | `(1,0,0)` |
| `ac` | `(0,1,0)` |
| `ad` | `(0,0,1)` |
| `bc` | `(-1,1,0)` |
| `bd` | `(-1,0,1)` |
| `cd` | `(0,-1,1)` |

Let the caller have independently proved rational bounds `[L_r,U_r]`
for these six projections. A projection of a Cartesian difference rectangle
uses its four exact endpoint values. If the caller also has proved bounds
on `dx+dy` or `dx-dy`, the corresponding projected interval may be
intersected with those bounds, with the sign reversed when required.
These are intersections of necessary bounds, not assumptions or branches.

The actual vector lies in the closed bounded polytope

\[
 P=\{u\in\mathbb R^3:L_r\le N_r\cdot u\le U_r\ (r=1,\ldots,6)\}.
\]

The first three interval bounds make `P` bounded. Lower-dimensional
polytopes, including points and segments, are retained without widening.

## 2. Complete exact vertex enumeration

There are twelve boundary planes, with coincident lower and upper faces
retained when an interval has zero width. Examine every choice of three
planes: at most `binomial(12,3)=220` choices. Solve each nonsingular system
exactly and retain its solution precisely when all twelve inequalities
hold. Duplicate vertices are removed as exact rational tuples.

This finds every vertex. At an extreme point the active normals span
three-dimensional space: otherwise there is a nonzero direction orthogonal
to every active normal and a sufficiently small displacement in either
sign stays in all inactive inequalities, contradicting extremality.
Three independent active planes therefore identify that vertex. The same
argument covers lower-dimensional polytopes, since their defining
equalities are active on both faces of an equality.

A nonempty bounded polytope is the convex hull of its vertices. Hence an
empty enumerated vertex set proves `P` empty. That produces the necessary
contradiction row `0<=-1`; it does not silently discard a case.

The discovery generator precomputes integer inverses of the independent
normal matrices. The independent checker instead reconstructs all 220
candidates with generic rational Gaussian elimination. Neither uses
floating arithmetic to decide membership or completeness.

## 3. A finite exact majorant certificate

The projected energy is the convex quadratic

\[
 F(u)=\sum_{r=1}^6(N_r\cdot u)^2
      =4(u_1^2+u_2^2+u_3^2)-(u_1+u_2+u_3)^2.
\]

For rational `A=(A_1,A_2,A_3)` and `K`, an affine plane
`L(u)=A dot u+K` is accepted only after checking

\[
 L(v)-F(v)\ge0\quad\text{at every enumerated vertex }v.
\]

This implies `F(u)<=L(u)` on the entire closed polytope: write
`u=sum lambda_v v` with nonnegative weights summing to one, apply convexity
of `F`, and use affinity of `L`. Shared faces and every contact point are
included. No interior sampling is needed or used.

A numerical convex hull of lifted points may nominate interpolation
vertices. Its coordinates, normal vectors, tolerances and facet labels
are not proof inputs. Each nominated plane is reconstructed from exact
rational vertex energies and checked against the complete exact vertex
set. If discovery misses a facet, it loses strength only. The generator
also supplies the independently valid sum of six secants and the constant
`max_v F(v)` as fallback majorants, checked by the same rule.

For example, when all six difference intervals are `[-1,1]`, independent
secants give `F<=6`, while the exact polytope certificate gives `F<=4`.
The latter is attained at `u=(1,1,0)`. This illustrates the gain from
retaining the identities between all six pair differences.

## 4. Affine necessary rows

Construct a second polytope and its majorants for direction `f` and
relative vector `v`. Orthogonality gives the exact identity

\[
 F(u)+F(v)=nE_4\ge8n.
\]

Therefore every accepted pair of majorants
`A dot u+K` and `B dot v+J` gives

\[
 -A\cdot u-B\cdot v\le K+J-8n.
\]

For the `e` part, the four coefficients on scalar center projections
are `(A_1+A_2+A_3,-A_1,-A_2,-A_3)`. Multiply these by `(p,q)` to obtain
the corresponding coefficients on the eight original Cartesian center
coordinates. The `f` part uses the same construction with `B` and
`(-q,p)`. Thus every row uses only original center variables.

For `e=(1,1)`, `n=2`, so the right-hand energy threshold is `16`.
This is exactly equivalent to the usual one-half diagonal-energy identity;
there is no unproved normalization or rounded square root.

## 5. Equivalent compact extension with one auxiliary per quartet

A Cartesian product of two plane lists can be large. The compact version
introduces one auxiliary with the exact physical definition

\[
 z=F(u),\qquad 0\le z\le M:=\max_{w\in\operatorname{Vert}(P)}F(w).
\]

For each first-axis majorant add

\[
 z-A\cdot u\le K,
\]

and for each second-axis majorant add

\[
 -z-B\cdot v\le J-8n.
\]

These are necessary for the same physical caller because
`8n<=z+F(v)<=z+B dot v+J`. Adding a first-axis row to a second-axis row
recovers the Cartesian-product row. The bounds on `z` are exact and are
also included as rows. Its residual-correction bound in any rational dual
certificate is `|z|<=M`, derived from the same vertex certificate.

This extension introduces no geometric case choice and no new frame.
Its variable is an exact function of the original centers. A numerical
relaxation may choose another feasible value, which can only weaken the
relaxation; proof soundness uses the physically defined value.

## 6. Files and replay

- `coupled_four_center_energy.py`: exact vertices, candidate majorants,
  direct `rows` conversion and compact `lifted_rows` conversion.
- `check_coupled_four_center_energy.py`: independent rational vertex
  enumeration and complete majorant verification, with no NumPy/SciPy.
- `check_four_fixtures.py`: point, segment, planar, full-dimensional,
  empty and rational varied fixtures; checks conversion identities.
- `FOUR_COUPLED_FIXTURE_REPLAY.json`: exact replay counts and source hashes.

`rows(differences, directions=..., diagonal=...)` returns `(rows, guards)`.
`lifted_rows(differences, first_aux=len(old_bounds), directions=...,
diagonal=...)` returns `(rows, auxiliary_absolute_bounds, guards)`.
Append the returned absolute bounds after the original bounds in order;
all older physical variable indices remain unchanged.

The first current-D6 pilot used the whole published I22/H01/I-angle-0
parent. All 126 Cartesian-axis quartet guards independently passed:
4,896 vertices, 7,851 affine planes and 153,401 exact majorant comparisons.
Its 122,273 direct rows did not close that domain, and every new row was
satisfied by the old phase-I point with margin at least approximately
0.5899. This is an explicit negative discovery result, not closure credit.
The exact guards and the limited pilot result are retained separately.
