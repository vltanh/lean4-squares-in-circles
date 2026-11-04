# CA1: executable exact full physical system for the unloaded direct triangle

November 1, 2026 — n=9 / PR #11.

**Deliverable.** [`emit_full_triangle_system.py`](emit_full_triangle_system.py)
constructs the complete nine-square physical force-and-torque system and emits
exact nonlinear real-arithmetic SMT-LIB. The five roots retain every possible
identity pattern of the three outside terminals. All nine actual bodies, all
36 pairwise nonoverlaps, all original pair forces, all circle multipliers, and
all original shared-side means remain present.

**Status.** The emitter and exact rational predicate evaluator run, and the
committed oblique nine-square witness at \(Q=1105/256\) satisfies the full base
physical system. No SMT solver has been run. No root has been proved
infeasible. No original coarse/fine/exterior case closes from this encoding.

The physical conventions come from
[`../PHYSICAL_CONTACT_STRESS.md`](../PHYSICAL_CONTACT_STRESS.md) and
[`../AUDIT_EXISTING_COMMON_PHYSICAL_PLANAR_CERTIFICATE_AND_EXACT_SELECTION_BOUNDARY_2026_10_30.md`](../AUDIT_EXISTING_COMMON_PHYSICAL_PLANAR_CERTIFICATE_AND_EXACT_SELECTION_BOUNDARY_2026_10_30.md).
The source head used for those inputs was
`ad00eaa16a27e5e1000d1a9dc7be0c4421c54b91`.

## 1. Exact variables and the radius boundary

The circle center is the origin. For each actual body \(i=0,\ldots,8\), use

\[
 c_i=(c_{ix},c_{iy}),\quad u_i=(u_{ix},u_{iy}),
 \quad v_i=Ju_i=(-u_{iy},u_{ix}),\quad |u_i|^2=1.
\]

Its four original corners are

\[
 p_{i,\sigma,\tau}=c_i+\frac12(\sigma u_i+\tau v_i),
 \qquad (\sigma,\tau)\in\{-1,+1\}^2.
\]

The model imposes \(0\le q\le1105/256\) and
\(|p_{i,\sigma,\tau}|^2\le q\) for every original corner. A convex disk
contains a square exactly when it contains all its corners. No positive
radius margin is introduced, and no \(Q-\varepsilon\) limit argument is used.

By default \(u_0=(1,0)\). This is a legitimate common-rotation gauge: rotate
the complete physical packing, its normals, and its application points about
the disk center. It does not fix any relative angle, center, or contact.
`--ungauged` retains the redundant global orientation variable.

For each of the 36 unordered body pairs \(i<j\), declare

\[
 \mu_{ij}\ge0,\quad n_{ij}=(n_x,n_y),\quad
 p_{ij}=(p_x,p_y),\quad \eta_{ij}.
\]

The normal points from \(i\) toward \(j\). When \(\mu_{ij}>0\), the physical
contact constraints below apply. When \(\mu_{ij}=0\), its normal and application
variables have no effect on force or torque, but the actual two squares still
obey their full pairwise nonoverlap constraint. This permits zero-weight
contacts and arbitrary physical circle-touching masks.

No angle mesh or rational-angle restriction is used. Polynomial unit-circle
equations represent every real frame and every permitted real common normal.

## 2. All 36 nonoverlap disjunctions

For a unit direction \(d\), define the actual projection halfwidth

\[
 h_i(d)=\frac{|d\cdot u_i|+|d\cdot v_i|}{2}.
\]

For every pair \(i<j\), impose

\[
 \bigvee_{d\in\{u_i,v_i,u_j,v_j\}}
 |d\cdot(c_j-c_i)|\ge h_i(d)+h_j(d). \tag{SAT}
\]

These are precisely the four unoriented separating-axis alternatives for two
squares, equivalently all eight directed alternatives. Equality is allowed,
so all touching and tie cases remain. The model includes (SAT) even for pairs
with zero force and bodies with no positive forces or circle multipliers.

Absolute values are expanded as exact `ite` expressions. Each alternative is
piecewise polynomial over the reals; no numerical sign tolerance enters.

## 3. Positive pairs use one actual common support point

For \(\mu_{ij}>0\), impose \(|n|^2=1\), membership

\[
 |u_i\cdot(p-c_i)|,\ |v_i\cdot(p-c_i)|\le\frac12,
 \qquad
 |u_j\cdot(p-c_j)|,\ |v_j\cdot(p-c_j)|\le\frac12,
\]

and the two actual support equations

\[
 n\cdot(p-c_i)=h_i(n),\qquad
 n\cdot(p-c_j)=-h_j(n). \tag{P}
\]

There is one shared variable \(p\), not separate lever points for the two
bodies. Thus \(p\) is in their actual intersection, and the same line separates
their complete squares. Subtracting (P) recovers the full tight support gap
\(n\cdot(c_j-c_i)=h_i(n)+h_j(n)\).

The original strict normal convention is retained through the following four
logical contact branches. Define

\[
 \operatorname{strict}_i(n):
 (n\cdot u_i\ne0)\ \wedge\ (n\cdot v_i\ne0),
\]

\[
 \operatorname{side}_i(n):
 (n\cdot u_i=0)\ \vee\ (n\cdot v_i=0),
 \qquad t=Jn.
\]

Because the frame and normal are unit, `side` means an actual outward side
normal up to sign. Under (P), `strict` means the exposed point is a unique
corner, with the normal strictly inside that corner's normal cone.

| Contact branch | Additional conditions |
| --- | --- |
| Vertex/vertex singleton | `strict_i` and `strict_j` |
| Side interior on \(i\), vertex on \(j\) | `side_i`, `strict_j`, and \(|t\cdot(p-c_i)|<1/2\) |
| Vertex on \(i\), side interior on \(j\) | `strict_i`, `side_j`, and \(|t\cdot(p-c_j)|<1/2\) |
| Positive shared side | `side_i`, `side_j`, positive overlap, and the exact weighted mean below |

Each nonzero condition is the disjunction of the two strict sign inequalities.
A singleton vertex/vertex contact is therefore never accepted merely with a
boundary side normal. A limiting zero-length side overlap is also never
silently assigned to the positive-side branch; it must use a legitimate
singleton branch. This matches the local physical certificate construction.

### Exact original shared-side means

When both normal directions are side normals, the common support line has
the shared normal coordinate

\[
 s=n\cdot c_i+\frac12=n\cdot c_j-\frac12.
\]

The actual common segment has tangent interval

\[
 L=\max(t\cdot c_i,t\cdot c_j)-\frac12,
 \qquad H=\min(t\cdot c_i,t\cdot c_j)+\frac12.
\]

The side branch imposes

\[
 L<H,\qquad 0\le\eta\le1,\qquad
 t\cdot p=(1-\eta)L+\eta H. \tag{M}
\]

The support equations already fix \(n\cdot p=s\), so (M) places the exact
original application point at the weighted mean of the two true endpoints
\(sn+Lt\) and \(sn+Ht\). The original endpoint weights can be recovered as
\(\mu(1-\eta)\) and \(\mu\eta\); aggregation preserves every force and moment.
Both endpoints, partial overlaps, full overlaps, and all interior means are
included. No mean is moved to a convenient common junction.

`min` and `max` are exact finite `ite` expressions, retaining their ties.
The emitter does not assume that all shared-side segments have length one.

## 4. All original circle multipliers and complete body balances

Every original corner has \(\lambda_{i,k}\ge0\), with

\[
 \sum_{i,k}\lambda_{i,k}=1,
 \qquad \lambda_{i,k}(|p_{i,k}|^2-q)=0.
\]

For \(i<j\), the contribution of pair \(ij\) is \(+\mu_{ij}n_{ij}\) at body
\(i\) and \(-\mu_{ij}n_{ij}\) at body \(j\), as in the source's constraint
gradient convention. Write this sign as \(s_{i,e}\). All nine bodies satisfy

\[
 2\sum_k\lambda_{i,k}p_{i,k}
 +\sum_{e\ni i}s_{i,e}\mu_e n_e=0, \tag{F}
\]

\[
 2\sum_k\lambda_{i,k}p_{i,k}\cdot J(p_{i,k}-c_i)
 +\sum_{e\ni i}s_{i,e}\mu_e n_e\cdot J(p_e-c_i)=0. \tag{T}
\]

All exterior-to-exterior forces and all original outside circle weights remain
unknowns in these complete equations. In particular, an outside neighbor's
force and moment balance is not replaced by a fictitious reaction, truncated
degree, center-only force, or freely movable application point.

## 5. Five exhaustive exit-identity roots

The three completely unloaded hubs are bodies \(0,1,2\). Impose

\[
 \mu_{01},\mu_{12},\mu_{02}>0,
 \qquad \lambda_{i,k}=0\quad(i\in\{0,1,2\}).
\]

Each hub has exactly one positive pair to the exterior bodies \(3,\ldots,8\).
All its other five exterior pair magnitudes are zero. The possibilities for
the identities of those three outside terminals are the five set partitions:

| Root | Outside neighbors of hubs \((0,1,2)\) |
| --- | --- |
| AAA | \((3,3,3)\) |
| AAB | \((3,3,4)\) |
| ABA | \((3,4,3)\) |
| ABB | \((3,4,4)\) |
| ABC | \((3,4,5)\) |

Relabeling only the six actual outside squares puts any triple into exactly
one of these identity patterns. The hub labels need not be permuted. Unused
labels are still actual arbitrary squares with every containment, nonoverlap,
circle, force, and torque constraint. In particular the three-distinct case
still has all nine bodies, not only its six positively incident bodies.

The optional `--weak-screen` switch adds the analytic result from
[`FORCE_TRIANGLE_ANALYTIC_COMPRESSION_AND_AUDIT_2026_11_01.md`](FORCE_TRIANGLE_ANALYTIC_COMPRESSION_AND_AUDIT_2026_11_01.md).
Introduce a positive real \(s\) with \(s^2=3\), let
\(W=\mu_{01}+\mu_{12}+\mu_{02}\), and impose

\[
 \bigvee_{e\in\{01,12,02\}}93\mu_e<(4+2s)W. \tag{W}
\]

This uses the exact algebraic threshold. No weak edge is deleted. The strict
inequality is a proved consequence of the full physical model at \(q\le Q\).

## 6. Soundness and coverage boundary

**Forward coverage.** Given a selected original physical certificate with the
specified unloaded triangle, assign the actual nine poses, radius, circle
weights, pair magnitudes, common normals, and application points. A side mean
determines \(\eta\) by its true tangent coordinate. Every positive pair has one
of the four source contact types. Relabel the outside bodies and apply a common
rotation if the gauge is enabled. The result satisfies one of the five roots;
the optional weak-edge screen follows from its analytic proof.

**Physical interpretation of a satisfying assignment.** The unit frames and
all corner bounds produce nine actual contained squares; (SAT) makes their
open interiors disjoint. Every positive pair has one actual contact point,
one actual common unit support normal, and its unchanged mean where relevant.
Equations (F)–(T) are complete original equilibria. The triangle root has
precisely the asserted positive incident degrees and unloaded masks.

This is a necessary physical system, not a sufficient characterization of a
global minimizer or of every downstream generic-selection property. It does
**not** impose atom sparsity, abstract graph planarity, matched free normals at
four-body junctions, or the later common generic-avoidance polynomials. Omitting
those additional restrictions enlarges the feasible set and preserves every
selected physical certificate. An exact infeasibility certificate for this
larger system would therefore suffice for the physical triangle exclusion;
a satisfying assignment would not by itself verify the selected-certificate
conditions of an original caller. These interfaces remain explicit rather
than being silently inferred from a numerical model.

The five exit roots are finite, but their internal contact alternatives and
continuous variables remain substantial. An SMT emission is not an exhaustive
certificate or a promise of solver termination. Any later numerical solution
is discovery data; any later exclusion still needs an exact independently
checkable proof covering all branches and limiting cases.

## 7. Executed validation

Run from this directory:

```bash
python emit_full_triangle_system.py --self-check
```

The exact `Fraction` evaluator checks the same expression tree that the
SMT-LIB emitter serializes. The executed validation covers:

1. **Known upper-bound witness.** The committed rational oblique nine-square
   record from `../check_physical_contact_stress.py` satisfies every base
   constraint at exactly \(Q=1105/256\), including all 36 pairwise SATs,
   its seven original positive shared-side means, all circle complementarity,
   and all nine force/torque equations. Its two oblique unstressed squares
   are retained. This witness is used only for the base model with no triangle
   requirement, and is correctly rejected by each triangle root.
2. **Original mean matters.** Moving the \(01\) mean by \(1/1000\) along its
   true common side, and updating its mean parameter consistently, preserves
   contact and all translations but fails exactly the two affected torque
   equations. The model therefore retains the moments lost by arbitrary
   mean relocation.
3. **Unstressed obstacles matter.** Moving one oblique unstressed square onto
   the other violates their pairwise SAT. Zero multipliers do not delete a body.
4. **Strict singleton normal matters.** A corner/corner singleton at
   \((1/2,1/2)\) between axis-parallel squares at \((0,0)\), \((1,1)\)
   accepts the strict rational normal \((3/5,4/5)\), and rejects the boundary
   normal \((1,0)\). The latter cannot escape into a zero-length side branch.

Recorded output:

```text
Exact self-check passed: known Q witness, all 36 SATs, original shared-mean torque,
unstressed-square obstacle, strict singleton normal, and five distinct exit roots.
Base model: 289 real variables, 108 definitions,
257 assertions. No solver or exclusion claim.
```

Each triangle root has 289 real variables and 290 assertions. Enabling the
analytic screen gives 290 real variables and 293 assertions. The definitions
are exact corner-coordinate and circle-margin abbreviations.

## 8. Reproducible emission and next step

```bash
# One physical root, with the proved weak-edge restriction.
python emit_full_triangle_system.py --case AAA --weak-screen --output /tmp/triangle_AAA.smt2

# Every exit-identity root; each includes all nine bodies and all 36 pairs.
python emit_full_triangle_system.py --all-cases /tmp/nine_triangle_roots --weak-screen

# The full physical system without imposing an unloaded triangle.
python emit_full_triangle_system.py --case none --output /tmp/nine_physical.smt2
```

All five screened roots were emitted successfully. The script uses Python's
standard library only and performs no network access. A solver is neither
installed nor invoked by it. Generated SMT-LIB files are reproducible working
outputs; the emitter and this mathematical contract are the maintained source.

The next step is to exploit physical contact and moment structure to select
tractable subbranches, use numerical solutions only to guide the split, and
produce an exact exclusion certificate or a verified surviving physical
configuration for each chosen branch. Before crediting CA1 as independently
verified, review the emitter against the coverage argument above. No Lean,
Lake, or CI is involved.
