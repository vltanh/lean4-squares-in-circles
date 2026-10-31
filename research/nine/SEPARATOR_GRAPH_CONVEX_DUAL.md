# n=9: separating-axis graph duality — exact elimination of center positions

**Status (2026-10-22): a complete general weak-duality theorem**, valid
for any number of independently rotating unit squares, with any fixed
choice of true pairwise separating axes. It eliminates all **center
variables** from a candidate proof certificate. The square-frame
angles and the discrete choice of separating-axis edges still remain;
this theorem is therefore **not** an unrestricted n=9 proof.

This is a potential replacement for a large center/angle grid:
a finite geometric separator-graph classification, followed by
small explicit dual stresses. The paired-four-anchor stress is an
example of the sparse positive multipliers envisaged here.

## 1. Exact primal inequalities

Fix the disk center at the origin. Let S_i be a freely rotated
unit square with center c_i and orthonormal edge directions
u_i,v_i. Its exact maximal squared vertex norm is

\[
 f_i(c_i)=\|c_i\|^2+\frac12+
              |c_i\cdot u_i|+|c_i\cdot v_i|.
 \tag{1}
\]

For a direction e define the square's projection halfwidth

\[
 h_i(e)=\frac{|e\cdot u_i|+|e\cdot v_i|}{2}.
\tag{2}
\]

Every valid packing satisfies \(f_i(c_i)\le q\) for each square.
By the separating-axis theorem, for every pair of
interior-disjoint squares there is an oriented direction e
equal to one of their own edge normals, with a choice of sign
such that

\[
        e\cdot(c_j-c_i)\ge h_i(e)+h_j(e)=:w_{ij,e}.
\tag{3}
\]

Fix a set E of such **valid directed separation edges**.
No assumption that all chosen e are parallel or perpendicular
in a common global frame is made.

For fixed orientations (u_i,v_i) and directed axes E,
(1) is a convex constraint in the center coordinates,
while (3) is linear. Hence the optimization of
the squared containing radius subject to these
chosen separator constraints is a finite-dimensional
convex optimization problem, even when the original
unrestricted problem is globally nonconvex because
the orientations and separator owners are not fixed.

## 2. Explicit all-frames weak-dual theorem

**Theorem 2.1 (finite separator graph certificate).**
Let \(q\ge0\) and centers \(c_1,\ldots,c_n\) satisfy
(1)--(3). Choose arbitrary multipliers

\[
 \lambda_i>0,\quad \sum_{i=1}^n\lambda_i=1,
 \qquad \mu_e\ge0\quad(e\in E).
\tag{4}
\]

For each directed edge \(e=(i\to j,d_e)\), define its
oriented unit direction \(d_e\), separation length
\(w_e=h_i(d_e)+h_j(d_e)\), and its contribution to
each node's force. Set

\[
 F_i=
   \sum_{e:i\to j}\mu_e d_e
  -\sum_{e:j\to i}\mu_e d_e.
\tag{5}
\]
Let \(t_+=\max(t,0)\). Then every packing satisfying
the selected separations obeys the **exact explicit**
lower bound

\[
\boxed{
q\ge
 \sum_{e\in E}\mu_e w_e
 +\sum_{i=1}^n
 \left[
 \frac{\lambda_i}{2}
 -\frac{
 (|F_i\cdot u_i|-\lambda_i)_+^2+
 (|F_i\cdot v_i|-\lambda_i)_+^2
 }{4\lambda_i}
 \right].
}
\tag{6}
\]

No unbounded search over center coordinates, numerical optimizer,
certificate execution, or external axiom is needed to verify
this inequality for any supplied \((\lambda,\mu)\).

*Proof.* Since \(f_i(c_i)\le q\) and
\(\sum\lambda_i=1\), we have
\(q\ge\sum_i\lambda_i f_i(c_i)\).
For every selected edge (3),
\(\mu_e(w_e-d_e\cdot(c_j-c_i))\le0\).
Adding these nonpositive quantities preserves the lower bound:

\[
\begin{aligned}
q&\ge\sum_i\lambda_i f_i(c_i)
 +\sum_e\mu_e\bigl(w_e-d_e\cdot(c_j-c_i)\bigr)\\
 &=\sum_e\mu_e w_e+
   \sum_i\bigl(\lambda_i f_i(c_i)+F_i\cdot c_i\bigr).
\end{aligned}
\tag{7}
\]

In the own square frame write \(s_i=c_i\cdot u_i\),
\(t_i=c_i\cdot v_i\), \(a_i=F_i\cdot u_i\),
\(b_i=F_i\cdot v_i\). Because u_i,v_i are
orthonormal, the node contribution is

\[
 \frac{\lambda_i}{2}
 +\bigl(\lambda_i s_i^2+\lambda_i|s_i|+a_i s_i\bigr)
 +\bigl(\lambda_i t_i^2+\lambda_i|t_i|+b_i t_i\bigr).
\tag{8}
\]

For any real a and any \(\lambda>0\), direct
completion of squares separately on x≥0 and x≤0
proves the exact one-variable inequality

\[
 \lambda x^2+\lambda|x|+a x
 \ \ge\
 -\frac{(|a|-\lambda)_+^2}{4\lambda}.
\tag{9}
\]
If \(|a|\le\lambda\), the right side is zero
and x=0 minimizes the left. Otherwise the
minimizer is
\(-\operatorname{sgn}(a)(|a|-\lambda)/(2\lambda)\)
and its value is the displayed negative square.

Apply (9) twice to each node in (8), then sum
in (7) to obtain (6). \(\square\)

## 3. Boundary-only stresses

Theorem 2.1 also permits some \(\lambda_i=0\), with
the convention that the corresponding node term
is zero **only when \(F_i=0\)**. If \(F_i\ne0\)
and \(\lambda_i=0\), the infimum over that
node's center is \(-\infty\), so there is no finite
certificate from this weak dual.

This provides a clean way to use only a few
boundary-active squares as circle witnesses:
set \(\lambda_i>0\) on those squares, set
\(\lambda_i=0\) on the interior squares, and
balance the separator forces at every interior
node. A chain of intermediate squares can transfer
stress without requiring any of their own circle
contacts. The earlier cap-row and four-anchor
proofs exploit exactly this idea in elementary
support-function form.

## 4. What the theorem changes and what it does not

For a **fixed** separator-owner graph and orientations, arbitrary
center coordinates have been eliminated from the verification
of a lower bound. A candidate stress (λ,μ) produces an explicit
finite function of the square orientations alone. If that
function is ≥q* uniformly over all orientations allowed in
the selected graph branch, then *every* packing in that
branch obeys \(q\ge q_*\).

This is not the assertion that a generic choice of λ,μ
will be sharp, nor that one universal graph owner
assignment exists. The crucial global tasks remain:

1. Compress the SAT alternatives to a short **exhaustive
   set of geometric separator graphs**, without enumerating
   all \(8^{36}\) raw sign/axis assignments.
2. For each graph, find a short exact stress with a
   human-checkable uniform orientation inequality,
   or prove the graph itself impossible at \(q\le q_*\).
3. Record the exact equality cases, including zero
   multipliers at genuinely movable squares.

The sparse n=9 four-anchor tangent certificates
(FOUR_ANCHOR_STRESS.md and PAIRED_FOUR_ANCHOR_STRESS.md)
show that large sets of free squares can have zero
dual contact weights. Consequently the graph approach
may separate a rigid boundary skeleton from obliquely
separated interior/free squares without forcing all nine
squares into a shared coordinate frame.

**Status:** the analytic duality identity is proved in this
document; the separator-graph coverage theorem and
uniform n=9 sharp stresses are **OPEN**.
