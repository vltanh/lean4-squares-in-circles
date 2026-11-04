# Coupled differences in the three-square energy bound

## Physical premise and scope

Retain any three distinct, interior-disjoint physical unit squares with
centers `c_i,c_j,c_k`, where `i<j<k`. The accepted
`THREE_SQUARE_CENTER_ENERGY_HAND_PROOF.md` gives

\[
\|c_j-c_i\|^2+\|c_k-c_j\|^2+\|c_k-c_i\|^2\ge 7/2.
\]

The construction below converts this same theorem to stronger necessary
affine rows using already proved difference intervals. It requires no
order of the centers, no common square orientation, no extra separation
margin, and no new geometric case split. Every closed endpoint and physical
contact is retained. The construction alone earns zero original-cell or
whole-mask credit; a caller still needs a complete contradiction.

## 1. The exact two-dimensional difference polygon

Fix a rational projection direction `e=(p,q)`. Put

\[
u=e\cdot(c_j-c_i),\qquad v=e\cdot(c_k-c_j).
\]

Then the third projection is **the same** sum
`u+v=e·(c_k-c_i)`. Suppose independently proved intervals for the three
physical differences give

\[
u\in[a,b],\quad v\in[c,d],\quad u+v\in[e_0,f_0].
\]

Their simultaneous domain is the closed polygon

\[
P=\{(u,v):a\le u\le b,\ c\le v\le d,
                    \ e_0\le u+v\le f_0\}.
\]

If the three intervals are ordered, this domain is empty exactly when

\[
\max(a+c,e_0)>\min(b+d,f_0).
\]

Indeed, a feasible sum belongs to both displayed sum intervals. Conversely,
for a sum `s` in their intersection, the interval
`[max(a,s−d), min(b,s−c)]` is nonempty. Any `u` in it, with `v=s−u`,
is feasible. Thus the empty-polygon terminal is an exact contradiction
and keeps equality faces.

Every vertex of a nonempty `P` is a feasible intersection of two
nonparallel lines among

\[
u=a,b;\qquad v=c,d;\qquad u+v=e_0,f_0.
\]

To see completeness directly, begin with the closed rectangle and clip it
by the two sum halfplanes. Clipping keeps old corners on the retained side
and adds precisely the intersections of its boundary with the existing
edges. Every retained point is a convex combination of the resulting
vertices. This argument applies when an interval has zero length: a
segment retains its two endpoints, and a point retains itself. It also
shows that the boundary-line enumeration and the independent clipping
enumeration describe the same complete polygon.

## 2. Rational affine upper planes

Write

\[
F(u,v)=u^2+v^2+(u+v)^2.
\]

This is convex. For `0≤t≤1`, its convexity difference is explicitly

\[
tF(u,v)+(1-t)F(u',v')-F(tu+(1-t)u',tv+(1-t)v')
=t(1-t)\bigl((u-u')^2+(v-v')^2+(u+v-u'-v')^2\bigr)\ge0.
\]

Consequently, a rational affine expression `L(u,v)=Au+Bv+C` dominates
`F` on all of `P` whenever it dominates `F` at every polygon vertex.
For a convex combination of vertices, use convexity of `F` and affinity
of `L`. This proves the entire domain at once.

The producer enumerates planes through triples of noncollinear vertices
and keeps those passing every vertex inequality. A two-dimensional
polygon has such an upper-hull plane. If there are no noncollinear vertex
triples, the polygon is a point or segment: use a constant at a point,
or the secant through the two extreme endpoints of the segment.
Both implementations explicitly assert this degeneracy before using the
fallback, and still check every vertex.

For independent validation, a plane need not have trusted facet indices.
For proposed slopes `A,B`, recompute

\[
C_* =\max_{(u,v)\text{ a vertex of }P}\bigl(F(u,v)-Au-Bv\bigr).
\]

Then `Au+Bv+C_*` is a valid upper plane. This is the check used on the
literal printed row. It does not depend on how the producer discovered
or numbered its plane.

## 3. A complete affine consequence for the physical triple

Let `f=(-q,p)` and `n=p²+q²>0`. Apply the preceding construction in the
two directions `e,f`, obtaining

\[
F(u_e,v_e)\le A_eu_e+B_ev_e+C_e,
\qquad
F(u_f,v_f)\le A_fu_f+B_fv_f+C_f.
\]

Orthogonality and equal squared norm give

\[
F(u_e,v_e)+F(u_f,v_f)
=n\sum_{a<b\text{ in }\{i,j,k\}}\|c_b-c_a\|^2\ge 7n/2.
\]

Therefore the necessary affine row is

\[
-A_eu_e-B_ev_e-A_fu_f-B_fv_f\le C_e+C_f-7n/2.
\]

For one direction, the coefficient on the three center vectors is
`A e` at `i`, `(B−A)e` at `j`, and `−B e` at `k`. Add the two
directions. Their sum is zero, so the row is translation invariant.
No variable from a replacement square or an independently chosen frame
appears.

The default directions are `(1,0)` and `(1,1)`, each with its own
perpendicular. The latter uses `n=2`; the threshold is then `7`,
without an irrational normalization. Optional certified intervals for
`dx+dy` and `dx−dy` further restrict each projection through

\[
p\,dx+q\,dy=\tfrac{p+q}{2}(dx+dy)+\tfrac{p-q}{2}(dx-dy).
\]

The intersection of this interval with its Cartesian enclosure is valid
for the same physical difference. An empty intersection is itself a
strict exact contradiction.

## 4. Why this can strengthen the existing rows

For `u,v∈[0,1]` and `u+v∈[0,2]`, independent square secants give
`F(u,v)≤3u+3v`. The complete coupled polygon gives both valid planes

\[
F(u,v)\le2u+4v,\qquad F(u,v)\le4u+2v.
\]

At `(u,v)=(1/5,4/5)`, the old upper bound is `3`, while the better
coupled upper plane is `12/5`. The gain of `3/5` comes from retaining
the exact identity between the three differences. All three physical
pair intervals and the accepted `7/2` theorem remain unchanged.

## 5. Exact implementation and acceptance boundary

`coupled_three_square_energy.py` uses rational boundary-line intersections
and explicit determinant formulas. `independent_coupled_three_square_energy.py`
uses rational polygon clipping and Gaussian elimination; its
`verify_literal` additionally recovers the plane slopes from the printed
center coefficients and recomputes the required intercept maxima without
trusting facet numbers. Empty-domain checks use the explicit sum-interval
criterion above.

The row can enter a positive rational affine combination or an exact
bound-induction step in an existing physical proof. All coefficient
residuals still require their usual exact absolute-bound payment. A
numerical phase margin or an improved bound alone is not an original-cell
closure. No Lean, Lake, CI, human verification, or proof-kernel verification
is claimed by these companions.
