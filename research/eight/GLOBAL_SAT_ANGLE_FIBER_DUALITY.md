# Exact center elimination for the unrestricted eight-square problem: angle fibers and true SAT owners

**2026-10-13. Complete structural convexity/duality theorem; the global
sharp lower bound remains OPEN.**

This is a directly relevant route from full eight-square geometry
to lower-dimensional global certification. Unlike the previous
"capture every counterexample near the candidate" slogan, this is an
**explicit mathematical equivalence** whose remaining continuous
nonconvex variables are **only square frame angles**. It uses all
eight genuine squares and all 28 true pairwise separating-axis
disjunctions; no candidate contact pattern is assumed.

It does **not** provide the enormous final exhaustive
eight-angle/SAT-owner certificate. It identifies a valid certificate
format and an exact rational dual inequality for each convex fiber.

## 1. True unit-square parameterization

Normalize the containing disk to have center zero. For each
square i=1,...,8, choose a center \(p_i\in\mathbb R^2\)
and a frame angle \(\theta_i\in[-\pi/4,\pi/4]\);
quarter-turn symmetry of a square makes this angular chart sufficient,
with understood equivalent endpoints. Put
\[
e_i=(\cos\theta_i,\sin\theta_i),\quad
f_i=(-\sin\theta_i,\cos\theta_i),
\]
\[
o_{i,\epsilon,\eta}
=\tfrac12(\epsilon e_i+\eta f_i),
\quad \epsilon,\eta\in\{\pm1\}.
\]
The four true vertices are \(p_i+o_{i,\epsilon,\eta}\);
the exact squared disk constraints are
\[
q\ge|p_i+o_{i,\epsilon,\eta}|^2
\qquad (8\times4=32\ \text{constraints}).      \tag{1}
\]

For a unit direction n define the genuine square
projected half-width
\[
H_i(n)=\tfrac12(|n\cdot e_i|+|n\cdot f_i|).
\]
By the exact separating-axis theorem, the interiors
of squares i and j are disjoint **if and only if**
for **at least one** of the eight signed normals
\[
n\in\{\pm e_i,\pm f_i,\pm e_j,\pm f_j\}
\]
one has the *directed true-square inequality*
\[
n\cdot(p_j-p_i)\ge H_i(n)+H_j(n).                \tag{2}
\]
Here n is oriented from i toward j, not an arbitrary
chosen common frame direction.

Thus all 28 pair-disjointness conditions are
28 explicit finite disjunctions of eight
genuine support directions. There is **no
center-only or circular-disk surrogate**.

## 2. Exact convexity of each fixed-frame, fixed-owner fiber

Fix all eight \(\theta_i\), and for each unordered
pair i<j fix ONE signed true owner normal \(n_{ij}\)
from (2). These are a total of 28
directed affine separator inequalities. Consider
the following optimization in only the eight
square centers and the squared radius q:
\[
\begin{array}{ll}
\text{minimize}&q\\
\text{over}&p_1,\dots,p_8\in\mathbb R^2,\quad q\in\mathbb R\\
\text{subject to}
 &|p_i+o_{i,\epsilon,\eta}|^2\le q,
  \quad i=1,\ldots,8,\ \epsilon,\eta=\pm1,\\
 &n_{ij}\cdot(p_j-p_i)\ge
       H_i(n_{ij})+H_j(n_{ij}),\quad i<j .
\end{array}                                                     \tag{3}
\]

**Theorem A (convex center fiber).** For fixed angles and chosen
actual SAT-owner normal directions, (3) is a **convex program**.
Every disk constraint is the epigraph of a convex quadratic
and every directed separator is affine in the center coordinates.
Equivalently, minimizing \(R=\sqrt q\) gives a standard
**second-order-cone program** (SOCP)
with constraints
\[
\|p_i+o_{i,\epsilon,\eta}\|_2\le R .
\]
No nonconvexity from center positions remains inside a
specified angle/owner fiber.

If the directed separator system is feasible at any centers,
it is **strictly** feasible after center dilation:
replace \(p_i\) by \(\lambda p_i\), \(\lambda>1\).
Since every directed contact has positive support sum,
\[
\begin{aligned}
&n_{ij}\cdot(\lambda p_j-\lambda p_i)
 -(H_i+H_j)\\
&\quad\ge(\lambda-1)(H_i+H_j)
\ge\lambda-1>0.
\end{aligned}
\]
Then take q sufficiently large to make all vertex disk
inequalities strict. Therefore **Slater's condition** holds
for every nonempty fixed-owner fiber, and convex duality
is exact.

## 3. Explicit exact dual that ELIMINATES ALL center variables

The same formula works for any finite collection of
prescribed directed true-square separator edges E,
including the seven candidate edges or all 28
owner-fixed edges.

Give each true disk-vertex constraint a
nonnegative multiplier \(\mu_{i,\epsilon,\eta}\)
and each directed separator e=(i,j,n_e) a
nonnegative multiplier \(\lambda_e\), with
\[
\sum_{i,\epsilon,\eta}\mu_{i,\epsilon,\eta}=1.
\]
Define
\[
m_i=\sum_{\epsilon,\eta}\mu_{i,\epsilon,\eta},
\quad
a_i=\sum_{\epsilon,\eta}
       \mu_{i,\epsilon,\eta}o_{i,\epsilon,\eta},
\]
and the oriented contact-force incidence
\[
c_i=\sum_{e=(i,j,n_e)}\lambda_e n_e
       -\sum_{e=(j,i,n_e)}\lambda_e n_e.
\]
Also put \(w_e=H_i(n_e)+H_j(n_e)\).
For each square with \(m_i>0\), write
\[
\Psi_i=\frac{|2a_i+c_i|^2}{4m_i}.
\]
If \(m_i=0\), we require \(c_i=0\)
(otherwise the unconstrained-center infimum
of the dual Lagrangian is \(-\infty\))
and set \(\Psi_i=0\).

**Theorem B (explicit global-in-centers dual).**
For EVERY feasible set of true square centers at these
fixed angles and valid directed separator inequalities,
\[
\boxed{
q\ge
D(\boldsymbol\theta,\boldsymbol n,\boldsymbol\mu,
  \boldsymbol\lambda)
:=\frac12+\sum_{e\in E}\lambda_e w_e
          -\sum_{i:m_i>0}\Psi_i .
}                                                             \tag{4}
\]
This inequality is fully rigorous whenever
\(\mu,\lambda\ge0,\ \sum\mu=1\) and the zero-anchor
force condition is met. It applies to **all**
centers simultaneously; their positions have been
eliminated analytically.

**Proof.** Define true directed gaps
\(g_e=n_e\cdot(p_j-p_i)-w_e\ge0\).
By disk containment and normalized μ,
\[
q\ge\sum_{i,\epsilon,\eta}
  \mu_{i,\epsilon,\eta}|p_i+o_{i,\epsilon,\eta}|^2
 -\sum_{e}\lambda_e g_e.
\]
Expand and group terms by center:
\[
\begin{aligned}
&\sum_i\left(m_i|p_i|^2+
  (2a_i+c_i)\cdot p_i\right)\\
&\qquad+\sum_{i,\epsilon,\eta}
  \mu_{i,\epsilon,\eta}|o_{i,\epsilon,\eta}|^2
 +\sum_e\lambda_e w_e .
\end{aligned}
\]
Every genuine square vertex offset has
\(|o|^2=1/2\), and the total μ is one,
so the middle sum is exactly \(1/2\).
Completing each center's square gives
\[
m_i|p_i|^2+(2a_i+c_i)\cdot p_i
\ge-\frac{|2a_i+c_i|^2}{4m_i},
\]
proving (4). The zero-anchor convention is
necessary for a finite center-independent bound.

**Theorem C (exact fiber duality).**
For any fixed-angle/fixed-owner fiber (3) with at
least one feasible center arrangement,
\[
\boxed{q_{\min}(\boldsymbol\theta,\boldsymbol n)
  =\sup_{\substack{\lambda,\mu\ge0,\ \sum\mu=1\\
              c_i=0\text{ whenever }m_i=0}}
      D(\boldsymbol\theta,\boldsymbol n,\mu,\lambda).} \tag{5}
\]
This follows from Slater's condition and standard
convex Lagrangian strong duality. The right-hand
side is a family of explicit, purely angular
inequalities with **no center variables**.

## 4. Exact global variational reduction (NOT a completed certificate)

Let \(\Omega=[-\pi/4,\pi/4]^8\) denote all possible
eight true frame angles modulo square quarter-turns.
Let \(\mathcal N\) be the finite set of choices of one
of eight signed actual SAT-owner axes for **each of
the 28 square pairs**. There are at most \(8^{28}\)
symbolic owner words, many redundant or impossible.

The true unrestricted eight-square optimum satisfies
the exact logical identity
\[
\boxed{
R_8^2=
\inf_{\boldsymbol\theta\in\Omega}
\ \min_{\boldsymbol n\in\mathcal N}
q_{\min}(\boldsymbol\theta,\boldsymbol n),
}                                                            \tag{6}
\]
where infeasible fibers are assigned value \(+\infty\).

**This is a valid all-eight-square, no-contact-ansatz,
no-common-frame reduction.** It has eliminated
the 16 center-coordinate nonconvex variables,
leaving eight frame angles and finite discrete
genuine SAT owner choices, with every center
fiber having an **exact positive dual**.

Equation (6) is **NOT** a proof that
\(R_8=\widehat R\): it is a smaller-dimensional
but still formidable exact global optimization.
No exhaustive interval/angle-owner certificate
has been completed. An unverified numerical fiber
scan cannot replace it.

A future rigorous global checker may cover the
eight-angle domain and compatible owner words with
rational interval boxes, and for each box either

* exhibit a sound geometric/Farkas rejection of
  every center arrangement, or
* certify a common choice of interval-valid positive
  dual multipliers for which (4) is
  \(\ge\widehat R^2\), or
* reduce the box to an explicitly certified local
  true-SAT sharp neighborhood.

The global angular/marker reduction already in
SHARP_MARKER_RING.md should be used to prune
impossible owner words BEFORE applying this
center-fiber dual. Without such pruning,
\(8^{28}\) possible owner combinations cannot
be handled by hand, and no global proof claim
is justified.

## 5. One completely rational exact fiber certificate

At zero oblique tilt \(t=0\) with all seven named
candidate exterior frames axis-parallel, the
seven directed supports have a **complete exact
sum-of-squares optimality identity** proving
\[
\boxed{q\ge q_0:=2257/576>q_*}
\]
for arbitrary centers. The identity and a
genuine seven-square attaining packing are
proved in
[HUMAN_SEVEN_PARALLEL_EXACT_DUAL.md](HUMAN_SEVEN_PARALLEL_EXACT_DUAL.md),
and checked algebraically (not numerically) by
[verify_seven_parallel_exact_dual.py](verify_seven_parallel_exact_dual.py).

This verifies that the angle-fiber dual method
can yield a finite **exact human-readable**
certificate on a whole center fiber, and provides
a regression test for future global checkers.
It is not a new unconditional radius lower bound;
the earlier five-corner conditional theorem
already covers the aligned special case.

## 6. The deliberately noncertifying angle-fiber experiment

A numerical SLSQP implementation of (3) for the
seven candidate directed supports optimized 14
center coordinates and one squared-radius variable
for each **fixed** seven frames and free separator
tilt t. It uses all 28 true vertices and the
seven genuine directed support inequalities, with
analytic constraint Jacobians.

At t near its exact attaining tilt and with
all frames aligned within their two candidate clusters,
it recovers \(q\approx3.9155344\), agreeing with
the nearby rational construction. At t=0 it recovers
\(2257/576\); at t≈0.2 it gives q≈3.91664.
A separate 3456-evaluation eight-angular-variable
differential-evolution scan found no certified
below-candidate **fixed-support-fiber** value, but
this does **not** exclude one, establish convergence,
or prove anything about the full 28-pair SAT union.

The numerical experiment suggests (and does not prove)
that the oriented seven-directed-separator class might
be sharp even without aligned end frames. The
stronger genuine GLOBAL statement still requires
either an exact angular dual proof for all relevant
angles and separator owners or an independently sound
disk marker-based capture theorem. Both are OPEN.

## Exact proof status

**Completed here:** rigorous fixed-owner convexity,
Slater, explicit global-in-center dual (4), exact
global variational identity (6), one rational
attaining SOS fiber certificate.

**Unproved:** any finite certificate covering
all eight angle/SAT-owner fibers, the unrestricted
sharp radius \(R_8\ge\widehat R\), equality
classification, and Lean 4 formalization.

Do not call (6), a numerical SLSQP run, or a
failed exhaustive search a global optimality proof.
