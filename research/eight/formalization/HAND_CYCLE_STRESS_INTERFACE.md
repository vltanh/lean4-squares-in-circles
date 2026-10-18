# The coupled seven-cycle stress: exact hand interface

**Status: the structural identities and stress implication below are proved. The global coarse mismatch inequality is not proved.** This is the main-lane interface for G4, not a claim to have removed the coarse affine table. The separate owner lane is recorded in `HAND_QUARTER_OWNER_CLOSURE.md` and `HAND_MIXED_OWNER_CLOSURE.md`.

The point of this formulation is to retain the shared vertex coordinates and exact cyclic compatibility. Independently moving seven phases to their individually optimal SAT contacts generally destroys that compatibility. The earlier pairwise contact-frontier lemma remains valid for pair inequalities; it is not a theorem that every phase in a constrained whole-cycle extremum can independently be moved to a contact.

## 1. The actual variables and geometric domain

Indices i are cyclic modulo seven, with roles H,G,A,B,T,D,E. Let

\[
 k=(0,1,0,1,0,1,1),\qquad
 \phi_i=k_i\pi/2+d_i,\qquad d_i=\theta_{i+1}-\theta_i.
\]

Normalize theta_A=0. Keep the actual spread |theta_i-theta_j|<7/10. At each vertex the own-frame center is (a_i,-sigma_i b_i), where a_i>=b_i>=0 and sigma_i is either sign. A zero b coordinate retains either sign label with the same signed product. Every original corner satisfies

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q.
\tag{1}
\]

The outer/core-side/core-corner charts, when needed, retain their original equations and junctions. The physical gaps are

\[
 g_i=\phi_i+\sigma_i\arctan(b_i/a_i)
              -\sigma_{i+1}\arctan(b_{i+1}/a_{i+1}),
 \qquad 19/25<g_i<3\pi/4,\quad\sum_i g_i=2\pi.
\tag{2}
\]

At least one of the four original forward SAT projections P_ij on each edge obeys

\[
 P_{ij}\ge W_i,\qquad
 W_i=(1+|\sin\phi_i|+|\cos\phi_i|)/2.
\tag{3}
\]

Their exact formulas are the original `Candidate.Model`/`MISMATCH_GEOMETRY.md` formulas, not already-restricted terminal owners. Before the sign or owner gate is proved, it must not be inserted here. The coarse stage can use the E/G/T tangent cuts only once those particular cuts have been supplied.

The global core lemma says at most one neighboring edge has two core endpoints. Its proof only uses separation on neighboring edges, so it also applies to the boundary neighbor relaxation; no nonneighbor disjointness after deformation is needed.

## 2. One polynomial expresses exact angular closure

Put z_i=tan(d_i/2), so d_i=2 arctan(z_i) and |z_i|<3/8. For the elementary symmetric polynomials e_j in the seven z coordinates, define

\[
 \mathcal C(z)=e_1-e_3+e_5-e_7.
\]

Then, on the closed enlarged chart |z_i|<=3/8,

\[
 \boxed{\mathcal C(z)=0\quad\Longleftrightarrow\quad
                    \sum_i\arctan(z_i)=0.}
\tag{4}
\]

Proof: write

\[
 \prod_i(1+\mathrm i z_i)=
   (1-e_2+e_4-e_6)+\mathrm i\mathcal C(z).
\]

Each factor has positive modulus and argument arctan(z_i); the sum A of these arguments satisfies

\[
 |A|\le\sum_i|z_i|\le21/8<\pi.
\]

Thus the imaginary part vanishes exactly when sin(A)=0, which in (-pi,pi) is equivalent to A=0. In that case the real part is positive automatically. This proves both directions and controls the branch: a closure with an extra full turn has not been silently admitted.

Since sum k_i=4, (4) is exactly sum phi_i=2pi. Conversely, from z satisfying (4), define theta_i by cumulative sums of 2 arctan(z_j), then subtract theta_A. This reconstructs the cyclic frame differences. The additional spread inequalities must still be checked; they do not follow from (4) alone.

The intrinsic sign split z_i>=0 or z_i<=0 makes every SAT margin rational, with positive denominator 1+z_i^2 and quadratic numerator in z_i. The same denominator gives

\[
 h(|d_i|)=\frac{|z_i|-z_i^2}{1+z_i^2}.
\tag{5}
\]

The angle variables therefore have one exact global algebraic compatibility constraint, in addition to their original geometric inequalities. They are not seven independent contact parameters.

## 3. Exact collection of a whole-cycle force

Fix any original feasible axis j_i on each edge and nonnegative weights lambda_i. Every P_ij is linear in the two adjacent centers. Collect coefficients **before bounding any vertex**:

\[
 \sum_i\lambda_iP_{i,j_i}
       =\sum_i(A_i a_i+B_i b_i).
\tag{6}
\]

Each A_i,B_i is the sum of the contributions of the two edges incident to vertex i. In particular, any cancellation uses exactly the same a_i,b_i on both edges. From (3),

\[
 \sum_i\lambda_i W_i\le\sum_i(A_i a_i+B_i b_i).
\tag{7}
\]

One can additionally use only those linear cone inequalities already proved in the current stage. Write them as u_ir a_i+v_ir b_i>=w_ir and give them arbitrary nonnegative weights tau_ir. Define

\[
 \widehat A_i=A_i+\sum_r\tau_{ir}u_{ir},\quad
 \widehat B_i=B_i+\sum_r\tau_{ir}v_{ir},\quad
 D=\sum_i\lambda_iW_i+\sum_{i,r}\tau_{ir}w_{ir}.
\]

Then

\[
 D\le\sum_i(\widehat A_i a_i+\widehat B_i b_i).
\tag{8}
\]

The signs are important: adding a known nonnegative cone slack changes both the force and its constant demand. It does not permit an unproved inequality, a negative multiplier, or a later-stage tangent cut.

## 4. The global circle-support theorem

For arbitrary positive masses mu_i, (1) gives the exact completed-square identity

\[
\begin{aligned}
&\mu_i q+\frac{\widehat A_i^2+\widehat B_i^2}{4\mu_i}
       -\frac{\widehat A_i+\widehat B_i}{2}
       -\widehat A_i a_i-\widehat B_i b_i\\
&=\mu_i\bigl(q-(a_i+1/2)^2-(b_i+1/2)^2\bigr)
 +\mu_i\left(a_i+1/2-\frac{\widehat A_i}{2\mu_i}\right)^2
 +\mu_i\left(b_i+1/2-\frac{\widehat B_i}{2\mu_i}\right)^2\ge0.
\end{aligned}
\]

Therefore every actual feasible cycle obeys

\[
 \boxed{
 D+\frac12\sum_i(\widehat A_i+\widehat B_i)
 -\sum_i\frac{\widehat A_i^2+\widehat B_i^2}{4\mu_i}
 \le q\sum_i\mu_i.}
\tag{9}
\]

All force signs are allowed. No equality in containment or closeness to a reference center has been assumed. A zero-force vertex may instead be omitted entirely; a nonzero force must not be assigned zero mass without a separate valid support bound.

Alternatively, Cauchy applied to each shifted corner gives

\[
 D+\frac12\sum_i(\widehat A_i+\widehat B_i)
 \le\sqrt q\sum_i\sqrt{\widehat A_i^2+\widehat B_i^2}.
\tag{10}
\]

Equations (9) and (10) are sufficient stress tests for exclusion when their inequalities are violated by a proposed stage domain. They are not asserted to be equivalent to feasibility of the original nonconvex radial-chart problem. Removing core geometry to get a convex relaxation is legitimate only in the direction of a necessary condition.

The already completed quarter and mixed-owner proofs are explicit instances of (8)–(9), with masses on four corners, cancellations at sliders, and a single shared mismatch loss.

## 5. The missing coarse theorem, now without an angular ambiguity

The coarse bad domain has q=Q1, the candidate frame, the E/G/T cuts, all original sign/radial possibilities not already excluded, the exact closure (4), and

\[
 S=2\sum_{i\in\{H,A,B,T,D\}}|\arctan z_i|\ge13/50.
\]

A direct stress proof must exhibit weights satisfying the nonnegativity requirements and prove, on **every** such bad cycle and every original feasible axis choice,

\[
 D+\frac12\sum_i(\widehat A_i+\widehat B_i)
 -\sum_i\frac{\widehat A_i^2+\widehat B_i^2}{4\mu_i}
 >Q_1\sum_i\mu_i.
\tag{11}
\]

That would contradict (9) and bypass the coarse table directly. A similar statement at S>=2/5 can be used as an earlier stage. The weights may be analytic functions of the phase/state data, but their signs, complete domain coverage and (11) have to be proved; an existence definition or numerical fit is not enough.

A useful algebraic necessary relaxation of the bad-S condition follows from arctan(x)<=x for x>=0:

\[
 S\ge s_0\quad\Longrightarrow\quad
                     \sum_{i\in I}|z_i|\ge s_0/2.
\]

For a previously established upper bound S<=s_1, the opposite Taylor inequality arctan(x)>=x-x^3/3 gives the necessary condition

\[
 \sum_{i\in I}(|z_i|-|z_i|^3/3)\le s_1/2.
\]

The directions of these implications must not be reversed. Proving an exclusion on the resulting larger algebraic domain would be sufficient, but may be too strong.

## 6. Current blocker and separation of lanes

The exact closure equation, force collection and support theorem above are proved. What is missing is a whole-domain choice of stress and a proof of (11) for the coarse domain. None of the new owner theorems supplies that estimate: they need the earlier small-mismatch hypotheses. Likewise, the fixed-state pair contact-frontier lemma cannot be used to set all seven phases to independent minima while retaining (4).

The positive tilt-tail work also remains open in this execution. Frozen stresses useful near one tilt need not remain positive on the entire tail; the next valid replacement must control an actual varying support or the primal five-corner envelope, including the shared frame errors. No endpoint experiment is recorded here as a proved tail exclusion.

This note adds no Lean source, numerical table, external proof premise or claim of closure for G4/G8. It is a hand proof of the exact interface and a statement of the remaining coupled inequality, not a replacement for that inequality.
