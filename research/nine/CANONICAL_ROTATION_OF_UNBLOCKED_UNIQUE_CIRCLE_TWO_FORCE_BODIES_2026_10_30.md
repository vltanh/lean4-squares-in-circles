# Canonical rotation reduces an unblocked unique-circle two-force body to radial diagonal form

Date: October 30, 2026. Author: joint-pockets continuation.
Comparison tree: `4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed conditional hand theorem, awaiting independent
review.** This is a uniform local reduction at an original radius/Phi
minimizer. It applies independently of the size of the selected component
and of the neighboring positive degrees. Its hypothesis checks every
actual physical contact of the moving body, including contacts carrying
zero stress. Under that full hypothesis a loaded true-degree-two body
with one physical circle corner must have radial diagonal geometry, must
contact at its two opposite lateral vertices, and must have equal positive
contact magnitudes. The precise surviving configuration is retained.

This theorem does not prove that the hypothesis holds at some vertex of
every short seven-cycle, or that its surviving radial configuration is
impossible. It closes no original packing cell. The only canonical
functionals used are the existing ordered pair `(R,Phi)`, where
`Phi=sum_i |c_i|^2`; no discontinuous circle-contact-count selector is added.

## 1. Actual packing, rotation center, and complete contact condition

Work with a finite packing of independently oriented unit squares in the
closed origin-centered disk `D_R`. Their open interiors are pairwise
disjoint. Put

\[
  \sigma=\frac1{\sqrt2},\qquad J(x,y)=(-y,x),\qquad
  \det(x,y)=x_1y_2-x_2y_1.
\]

Let S be one of these actual squares, with center c. Assume `R>sigma`
and that exactly one of its physical vertices z is on the containing
circle. Its other three vertices have norm strictly less than R. Fix
a point

\[
                    q=\tau z\in S,\qquad 0<\tau\le1.       \tag{1.1}
\]

For each other actual square T with `S intersection T` nonempty, impose
the following explicit condition. There are a unit normal `n_T`, an
actual common point `p_T`, and a number `alpha_T>=0` such that

\[
\begin{split}
 &n_T\cdot x\le n_T\cdot p_T &&(x\in S),\\
 &n_T\cdot y\ge n_T\cdot p_T &&(y\in T),\\
 &p_T\text{ is the unique vertex maximizing }n_T\cdot x
       \text{ on }S,\\
 &p_T-q=\alpha_T n_T.                                     \tag{1.2}
\end{split}
\]

The unique-vertex condition means that the other three vertices have
strictly smaller scalar product. The normal is held fixed while S
rotates; all of T is held fixed. A side owned by T is allowed, as is
a strict vertex/vertex separator. A supporting side of S, including
a shared segment, does not satisfy this unique-vertex condition.

Condition (1.2) must be checked for **every actual touching square**, not
only the two neighbors in a chosen positive stress support. The normals
at any additional zero-weight contacts are only separators for the
motion proof. They are not inserted into, or substituted for, the
already selected positive certificate.

## 2. An exact feasible curve of the entire original packing

Let `R_theta` denote rotation through theta about the origin. Rotate only
S about q:

\[
       S_\theta=q+R_\theta(S-q),\qquad
       c_\theta=q+R_\theta(c-q).                            \tag{2.1}
\]

All other original squares, and the containing circle, remain fixed.
The result is again a unit square with its independently rotated frame.

**Lemma 2.1 (complete feasible rotation).** Under (1.1)--(1.2), there is
an epsilon>0 such that replacing S by `S_theta` gives an original
packing of all the same units in `D_R` for every `|theta|<epsilon`.

*Proof: actual contacts.* Fix a touching T. At theta=0 the vertex
`p_T` has a strictly positive support gap over the other three vertices
in direction `n_T`. By continuity of the four rotated vertices, its
same vertex label remains the unique maximizer for all sufficiently
small positive and negative theta. The exact displacement of its
support value is

\[
\begin{split}
 n_T\cdot\bigl(q+R_\theta(p_T-q)-p_T\bigr)
 &=\alpha_T n_T\cdot(R_\theta n_T-n_T)\\
 &=\alpha_T(\cos\theta-1)\le0.                            \tag{2.2}
\end{split}
\]

Thus every point of `S_theta` stays on the old S side of the fixed
line `n_T dot x=n_T dot p_T`, while every point of T stays on the
other side. Their open interiors are disjoint. This includes
`alpha_T=0`: the contact vertex is then q and remains fixed. The
same argument applies to each of the finitely many actual touching
squares, including every zero-weight physical contact.

*Noncontacts.* Every other original square T is compact and disjoint
from the compact set S. Their Euclidean distance is strictly positive.
For sufficiently small `|theta|`, the maximum pointwise displacement
in (2.1) is smaller than half this distance. Hence they remain
disjoint. Taking a minimum of finitely many positive neighborhoods
handles all such pairs. All pairs not involving S are unchanged.

*The containing circle.* From (1.1), the unique active circle vertex
satisfies

\[
\begin{split}
 z_\theta&=\tau z+(1-\tau)R_\theta z,\\
 |z_\theta|^2
 &=R^2-2\tau(1-\tau)R^2(1-\cos\theta)\le R^2.             \tag{2.3}
\end{split}
\]

This is strict for `0<tau<1` and nonzero sufficiently small theta.
For `tau=1` the vertex remains fixed, which is still feasible. Each
of the other three vertices begins strictly inside the disk and stays
inside in a neighborhood of zero. The entire rotated square is the
convex hull of these vertices, and the disk is convex. Thus all of
`S_theta` remains contained. Intersecting the finitely many neighborhoods
proves the lemma for both signs of theta. QED.

This is an actual feasible curve, not only an infinitesimal constraint
calculation. In particular, it accounts for active constraints with
zero multipliers. It also does not purport to lower the maximum radius
merely because one circle vertex moves inward: other actual squares
may still touch the same circle.

## 3. The existing Phi minimum forces radial center alignment

Assume now that the entire original packing first minimizes R and then

\[
                         \Phi=\sum_i |c_i|^2               \tag{3.1}
\]

among all original radius minimizers. Such a packing exists by
`ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md`,
Theorems 1--2. It is chosen before contact normals and the positive
support. The feasible curve of Lemma 2.1 keeps the original radius and
all original labels. Therefore Phi cannot decrease along that curve;
the positive stress support need not persist in the competing packing.

Write

\[
                    A=q\cdot(c-q),\qquad B=\det(q,c).
\]

Only the center of S changes. Directly expanding (2.1), with
`q dot Jc=-det(q,c)`, gives

\[
       \Phi(\theta)-\Phi(0)
           =2A(\cos\theta-1)-2B\sin\theta.                 \tag{3.2}
\]

If `B!=0`, the derivative at zero is `-2B`, so one of the two
allowed signs of a sufficiently small theta strictly decreases Phi.
If `B=0` and `A>0`, every sufficiently small nonzero theta strictly
decreases Phi. Consequently

\[
                          B=0,\qquad A\le0.                \tag{3.3}
\]

Since q is a positive multiple of z, the first equality says that
`c=kappa z` for some real kappa. The vertex offset has length sigma:
`|z-c|=sigma`. If `kappa<=0`, this length is at least `R>sigma`,
a contradiction. If `kappa=1`, the offset is zero. If `kappa>1`,
the opposite actual vertex `2c-z` has norm `(2kappa-1)R>R`, also
a contradiction. Thus `0<kappa<1` and

\[
 e=\frac zR,\qquad t=Je,\qquad
 c=r e,\qquad r=R-\sigma>0.                               \tag{3.4}
\]

The square has the four actual vertices

\[
      (r+\sigma)e=z,\quad (r-\sigma)e,\quad
      r e+\sigma t,\quad r e-\sigma t.                     \tag{3.5}
\]

This is radial diagonal geometry: the outward diagonal from c points
exactly toward the unique circle corner. Writing `q=s e`, condition
`A<=0` becomes `s(r-s)<=0`. Since `s>0`, it follows that

\[
                    r\le s\le r+\sigma,
                    \qquad \delta=s-r\in[0,\sigma].       \tag{3.6}
\]

The upper bound follows either from `tau<=1` or from `q in S`.
So the concurrence has to be at or outward of the center, on the
radial segment leading to z.

**Theorem 3.1 (uniform canonical alignment).** In an original
radius/Phi-minimizing packing, a unique-circle square satisfying the
complete actual-contact condition (1.2) at a point (1.1) necessarily
has (3.4)--(3.6). This conclusion needs no stress equations or graph
classification beyond the stated geometric hypotheses.

## 4. A true two-force body has only one surviving contact pattern

Now retain an actual physical force-and-torque certificate. Suppose S
is loaded, has exactly two positive body-pair forces, and has exactly
one physical circle corner z. Let its positive circle coefficient be
`lambda>0`. Write its two positive pair forces as `mu_i n_i`, with
`mu_i>0`, outward unit normals, and their genuine actual applications
`p_i`, for `i=1,2`. Require that the lines are nonparallel and have
the proper concurrence from (1.1):

\[
                         p_i-q=\alpha_i n_i,
                         \qquad \alpha_i\ge0.              \tag{4.1}
\]

In the complete contact condition (1.2), use these original normals
and applications at the two positive neighbors. Thus they must be
unique exposed vertices of S in their original selected normals.
At every other actual touching square retain the additional geometric
condition (1.2). No positive contact, extra chord, physical circle
corner, shared-segment mean, or zero-weight contact is deleted to
make these assumptions true.

### 4.1 A containing-circle point cannot be shared

For completeness, no two contained squares can have a common point
z with `|z|=R`. The circle's strict supporting line at z implies that
z must be a vertex of either contained square that contains it. If
`w_1,w_2` are its orthogonal unit edge directions pointing into such
a square, containment of `z+w_j` gives

\[
                           z\cdot w_j\le-\frac12.
\]

The vector `-z` has strictly positive components in both inward edge
directions. Therefore `z-epsilon z` belongs to the open interior of
that square for every sufficiently small positive epsilon. If two
squares shared z, the same point would lie in both open interiors.

Thus neither `p_i` can be the outer circle vertex in (3.5).

### 4.2 The two ports must be the opposite lateral vertices

By Theorem 3.1 we already have (3.4)--(3.6). The remaining possible
contact vertices are the inner radial vertex and the two lateral ones.
The point q on the segment `[c,z]` equals none of these three vertices.
Consequently `alpha_1,alpha_2` in (4.1) are strictly positive.

The contact vertices are distinct: if they coincided, (4.1) would
make the two normals parallel. If one were the inner radial vertex,
its normal would be `-e`. The other, necessarily lateral, would
have a nonzero t component, by (4.1). The positive force sum could
then not cancel the purely radial circle force `2lambda R e`.
The exact force-balance equation is

\[
                  \mu_1n_1+\mu_2n_2+2\lambda R e=0.        \tag{4.2}
\]

Thus the only possible pair is

\[
              p_+=r e+\sigma t,\qquad
              p_-=r e-\sigma t.                           \tag{4.3}
\]

With `L=sqrt(delta^2+sigma^2)`, their original normals are exactly

\[
              n_+=\frac{-\delta e+\sigma t}{L},\qquad
              n_-=\frac{-\delta e-\sigma t}{L}.            \tag{4.4}
\]

For the upper lateral vertex to be the unique support point of S,
its scalar product must exceed that of the inner radial vertex.
After subtracting the center, these two values are respectively
`sigma^2/L` and `sigma delta/L`. Therefore `delta<sigma`.
The lower lateral contact gives the same strict inequality. At
`delta=sigma` the normal would expose an entire side, which is
expressly excluded by (1.2).

The t component of (4.2), using (4.4), yields

\[
                         \mu_+=\mu_-=\mu>0.                \tag{4.5}
\]

Its e component then yields

\[
                \lambda R=\frac{\mu\delta}{L}.             \tag{4.6}
\]

Since lambda and R are positive, `delta>0`. Combining these facts
gives the complete surviving configuration:

\[
\boxed{\begin{gathered}
 c=(R-\sigma)e,\qquad z=Re,\qquad
 q=(R-\sigma+\delta)e,\quad 0<\delta<\sigma,\\
 p_\pm=c\pm\sigma Je,\qquad
 n_\pm=\frac{-\delta e\pm\sigma Je}{\sqrt{\delta^2+\sigma^2}},\\
 \mu_+=\mu_-=\mu>0,\qquad
 \lambda R=\frac{\mu\delta}{\sqrt{\delta^2+\sigma^2}}.
\end{gathered}}                                                        \tag{4.7}
\]

The two application points are opposite actual vertices and have
distance `2sigma=sqrt(2)`. Both original nonnegative coefficients in
(4.1) equal `L>0`. The concurrence is strictly outward of the center
and strictly inward of the unique circle corner. In particular
`0<tau<1` in the resulting configuration.

**Theorem 4.1 (complete-contact two-force reduction).** Under the actual
packing, canonical, physical-degree, one-circle and complete-contact
hypotheses above, (4.7) is necessary. The theorem is independent of
the number of vertices in the full positive component and of any
additional positive forces at neighboring bodies.

It is a reduction to (4.7), not an exclusion of (4.7). Indeed in this
case `A=-s delta<0` and `B=0`, so the curve of Section 2 increases
Phi to second order. That curve supplies no canonical contradiction
at the surviving configuration.

## 5. Literal applications and limits

### 5.1 The existing proper-concurrence theorem supplies the local point

In the project's radius window

\[
           \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},     \tag{5.1}
\]

Lemma 1.1 of `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` applies to a loaded
body with exactly two positive pair forces and nonparallel original
force lines. Despite that manuscript's title, the local lemma does
not require a five-cycle or a boundary neighbor. In the one-physical-
circle-corner case it proves that the concurrence belongs to the
actual square, is a positive multiple of the circle resultant, and
satisfies (4.1) for both original applications.

For one physical circle corner and lambda>0, that resultant is
`lambda z`. Consequently `q=tau z` with `tau>0`. Since q lies
inside the contained square, `|q|<=R`, whence `tau<=1`. Thus (1.1)
and (4.1) are literal consequences of that existing theorem. The
extra requirement for this rotation argument is exactly the unique
vertex exposure at both positive contacts and the condition (1.2)
at every additional physical contact.

In particular, if S has exactly two actual physical neighbors and
they are its two positive neighbors, the complete-contact condition
requires no additional zero-weight checks. If each of its two
original selected normals uniquely exposes a vertex of S, Theorem
4.1 applies. Here “exactly two actual physical neighbors” is stronger
than true positive degree two and must not be inferred from it.

The proper-concurrence input also has a two-physical-circle-corner
branch. That branch is outside this theorem: its concurrence need
not belong to the square, and two active circle vertices need not
remain contained under the same rotation. A zero multiplier at the
second physical circle corner does not remove this obstruction.

### 5.2 Propagation in a fully screened cycle

As a direct conditional consequence, suppose a positive simple cycle
has the following properties: every loaded vertex has one physical
circle corner and satisfies the complete hypotheses of Theorem 4.1;
every other vertex is an unloaded true-degree-two transmitter. Each
loaded vertex preserves the two adjacent force magnitudes by (4.5).
Each unloaded degree-two vertex does so by force balance. Following
the connected cycle therefore gives one common positive magnitude
on all its original edges. Each loaded body also has the literal
opposite-lateral-vertex geometry (4.7). No orientation constraint on
a neighbor was inserted to obtain this consequence.

This statement is conditional on the full physical checks at every
loaded body. A side-owned contact, a shared segment, a two-circle
mask, or an additional physical contact that fails (1.2) remains a
separate case. Failure of this sufficient test alone is not proof
that every possible feasible motion is blocked.

### 5.3 What remains before a seven-cycle closure

For a general short-run seven-cycle, true positive degree two does
not forbid zero-weight contacts with the two additional original
squares. Those contacts may fail (1.2). Its loaded bodies may also
have side-owned contacts or two physical circle corners. Finally,
even after every hypothesis has been checked, (4.7) survives the
present canonical argument. A whole-family exclusion requires a
new argument treating these alternatives or using their combined
geometry. None is asserted here.

A negative second variation of only a chosen positive-stress
Lagrangian would not replace Section 2: additional active zero-weight
constraints could obstruct an otherwise suggested motion. Conversely,
the direct feasible-curve proof above needs no general second-order
multiplier theorem and never changes a post-extraction normal or mean.

## 6. Direct inputs, review scope, and unchanged gates

The two direct mathematical sources below were read in full. The
canonical source supplies the original global minimum and exact
scope of a Phi-decreasing competitor. The local proper-concurrence
source supplies only its explicit Lemma 1.1 for the caller in Section
5.1. Sections 1--4 prove the conditional rotation result directly
from their stated geometric and force equations.

| Direct source | SHA-256 |
| --- | --- |
| `ORIGINAL_PACKING_COMPACT_CANONICAL_MINIMUM_AND_RADIUS_TRANSFER.md` | `be6636a018df64f52a48f382dc21b453a208d0a929fdeaa7cb5bef9c30822c06` |
| `FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md` | `7d0c4092ba133a832cf963f329b1c3a6442a3260576f16319293835b39e6d282` |

The actual one-corner rectangle calculation in Sections 4--5 of
`C7_FORCE_POLYGON.md` and the local extension in Lemma 2.1 of
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md` were also read for the
proper-concurrence scope. Their boundary-neighbor premise is not
silently used to infer nonparallelism here; nonparallelism itself is
expressly assumed in the caller. The imported one-corner concurrence conclusion
retains actual applications and needs no boundary-neighbor assumption.

The original nine-body predicate, full physical contacts, original
positive degrees, true load masks, and every additional actual square
are retained. No original fine or coarse packing flag changes. This
is a proposed hand theorem for separate review, not a checked adoption.
No Lean/Lake invocation, numerical pose search, mesh, computational
packing certificate, CI dispatch or remote mutation was used.
