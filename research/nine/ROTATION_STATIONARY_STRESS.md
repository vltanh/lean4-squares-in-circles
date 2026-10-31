# n=9: angular stationarity without differentiating absolute-value cusps

**Status: completed hand necessary-condition theorem for unrestricted
minimizers.** It complements SPARSE_MINIMIZER_STRESS.md and
PLANAR_STRESS_CORE.md, not the missing sharp global inequality.

Every global minimizing packing of nine independently rotating unit
squares admits a normalized nonnegative active-constraint certificate
with **at most 27 positive scalar atoms** and exact stationarity in
all center coordinates **and all nine independent orientation angles**.
The terms are actual circle-contact vertices and selected separator-
owner support-vertex constraints on physically touching square pairs.
There is no differentiability assumption on `abs(sin theta)` at
parallel square frames: we replace support maxima by finitely many
smooth vertex inequalities before taking derivatives.

**Separate certificates:** this angular certificate need not equal
the at-most-19-term planar translational certificate. The planar
uncrossing proof preserves forces, not the full torque equations.
No simultaneous planar-and-angular sparsity result is claimed.

## 1. Smooth coordinates and exact owner constraints

Translate the containing circle center to zero. Work in local real
angle coordinates near the minimizing configuration:

\[
 u_i=(\cos\theta_i,\sin\theta_i),\quad v_i=Ju_i,
 \qquad a_{i,k}=\tfrac12(\epsilon_k u_i+\eta_k v_i),
 \quad k\in\{(-1,-1),(-1,1),(1,-1),(1,1)\}.
\]

The four circle inequalities for square `i` are smooth:

\[
 C_{i,k}:=\|c_i+a_{i,k}\|^2-q\le0. \tag{1}
\]

For each unordered pair, choose one actual oriented own-axis
separator at the minimizing packing as in SPARSE_MINIMIZER_STRESS.md.
Call the square supplying the axis its **owner**, and relabel the
pair for this edge as `e=(i -> j)` with owner `i`. Let
`d_e(theta_i)` be that signed axis of square `i`, oriented toward
square `j`. The sign and which of the owner's two axes is used
are kept fixed in this local branch. Then

\[
 h_i(d_e)=\tfrac12,\qquad
 d'_e(\theta_i)=Jd_e(\theta_i).
\]

Instead of differentiating `h_j(d_e)`, use all four smooth
inequalities

\[
 B_{e,k}:=\tfrac12+d_e\cdot a_{j,k}
                     -d_e\cdot(c_j-c_i)\le0
                      \qquad(k=1,\ldots,4). \tag{2}
\]

Their conjunction is exactly
`d_e dot(c_j-c_i) >= 1/2 + h_j(d_e)`. It suffices for physical
nonoverlap and correctly treats ties of the two support vertices
at a parallel edge contact. The full selected-owner branch, with
(1) and (2) for all pairs, is a subset of the original feasible
packing set and contains the minimizing configuration. That
configuration is therefore a local minimum of `q` on this branch,
even though the branch is not convex in its angles.

For every physically noncontacting pair choose a strict separator.
All four associated inequalities (2) are then strictly inactive.

## 2. Constraint qualification holds in the full pose variables

Use variables `(c_1,...,c_n,theta_1,...,theta_n,q)` of dimension
`3n+1`. Consider the velocity

\[
 \dot c_i=c_i,\qquad \dot\theta_i=0,\qquad \dot q=K,
 \quad K>\max_{i,k}2(c_i+a_{i,k})\cdot c_i.
\]

For circle constraints, `dot C_{i,k}<0`.
For an active separator-vertex constraint, its support vertex
maximizes `d_e dot a_{j,k}`, since all four inequalities hold.
Consequently

\[
 \dot B_{e,k}=-d_e\cdot(c_j-c_i)
             =-(\tfrac12+h_j(d_e))\le-1<0. \tag{3}
\]

Thus every active constraint has a strictly negative derivative
in one common direction. Apply the elementary active-gradient
alternative proved in SPARSE_MINIMIZER_STRESS.md, Lemma 3.1.
There exist nonnegative circle multipliers `lambda_{i,k}` and
separator-vertex multipliers `nu_{e,k}`, supported on active
constraints, such that the objective gradient plus their weighted
gradients vanishes. No abnormal objective multiplier and no
absolute-value derivative selection are being assumed.

## 3. Exact normalization, center balance and angular balance

The radius component gives

\[
                   \sum_{i,k}\lambda_{i,k}=1. \tag{4}
\]

Set `mu_e=sum_k nu_{e,k}` and define

\[
 F_i=\sum_{e:i\to j}\mu_e d_e-\sum_{e:j\to i}\mu_e d_e.
\]

The center equations are

\[
          2\sum_k\lambda_{i,k}(c_i+a_{i,k})+F_i=0.
                                                        \tag{5}
\]

The angular derivatives are exactly

\[
 \begin{aligned}
 \partial_{\theta_i}C_{i,k}
     &=2(c_i+a_{i,k})\cdot Ja_{i,k},\\
 \partial_{\theta_i}B_{e,k}
     &=Jd_e\cdot(a_{j,k}-(c_j-c_i))
                        &&(i\text{ owns }e),\\
 \partial_{\theta_j}B_{e,k}
     &=d_e\cdot Ja_{j,k}
                        &&(j\text{ is the nonowner of }e).
 \end{aligned}                                             \tag{6}
\]

Therefore each square obeys

\[
\begin{split}
0={}&2\sum_k\lambda_{i,k}(c_i+a_{i,k})\cdot Ja_{i,k}\\
 &+\sum_{e:i\to j}\sum_k\nu_{e,k}
                Jd_e\cdot(a_{j,k}-(c_j-c_i))\\
 &+\sum_{e:j\to i}\sum_k\nu_{e,k}
                d_e\cdot Ja_{i,k}.                         \tag{7}
\end{split}
\]

Here the directed edge convention records the owner, not a global
left/right order. Formula (7) includes the derivative of the
**owner's separating normal**. Freezing that normal while rotating
its owner would omit its second line and give an incorrect torque
condition.

Complementarity is

\[
 \lambda_{i,k}>0\Rightarrow\|c_i+a_{i,k}\|^2=q_0,
 \qquad \nu_{e,k}>0\Rightarrow B_{e,k}=0.                    \tag{8}
\]

A positive `mu_e` joins actual touching squares, by the strict
noncontact separator choice. The individual selected support
vertices in (2), however, need not each belong to the two squares'
intersection segment. Thus (7) is an exact **selected-owner
constraint** stationarity equation; interpreting every atom as
an independent physical point-contact force requires an extra
argument not asserted here. Convex combinations can give genuine
contact application points in concrete certificates, as in Section 6.

Aggregating `lambda_i=sum_k lambda_{i,k}`, the center equations and
complementarity imply that the center-eliminating dual of
SEPARATOR_GRAPH_CONVEX_DUAL.md is attained **exactly** at `q0`, by
the same convex-in-centers argument as in the translational proof.
This does not make the original orientation problem convex.

## 4. Remove the global rotational redundancy: at most 3n atoms

All inequalities (1) and (2) are invariant under a simultaneous
rotation of every center and every square frame. At the minimizing
configuration the infinitesimal global-rotation vector is

\[
 T=(Jc_1,\ldots,Jc_n,1,\ldots,1,0).
\]

This vector is nonzero. Every active constraint gradient is
orthogonal to `T`, and so is the objective vector `e_q`.
Their cone therefore lies in a subspace of dimension at most
`3n`, not `3n+1`.

Apply conic sparsification in that subspace. The normalized
stationarity relation can be represented with

\[
 \#\{(i,k):\lambda_{i,k}>0\}
    +\#\{(e,k):\nu_{e,k}>0\}\le3n.                       \tag{9}
\]

For nine squares this is **at most 27 scalar atoms**. This bound
counts different support-vertex atoms of the same edge separately.
It is not a bound of 27 graph types, nor does it replace any
necessary geometric classification.

A connected positive-stress component can again be selected and
renormalized: circle/edge complementarity and all center/angular
balances are componentwise. It retains at least two different
circle-loaded squares for `q0>1/2`.

## 5. Precise conclusion for a hypothetical counterexample

**Theorem.** If an unrestricted nine-square packing fits in any
squared radius `q<Q`, a globally minimizing packing at `q0<Q`
exists, and for a true owner-axis selection with every noncontact
pair strict it has a nonnegative normalized certificate satisfying
(4)–(9). It also has, possibly separately, the planar 19-term
translational certificate of PLANAR_STRESS_CORE.md.

*Proof.* Compactness gives the minimizer. Select actual owner axes,
write the smooth finite vertex constraints, use the strict dilation
velocity to apply the active-gradient alternative, and remove the
one-dimensional global rotation symmetry in the sparsification.
All the steps have been proved above. QED.

These conditions apply to **every unrestricted minimizer**, not
merely nearly aligned, generic, or numerically sampled poses.
They are necessary conditions; no conclusion `q0>=Q` has yet
been derived from them.

## 6. An exact angular-stationary stress on the oblique record witness

Take the seven aligned anchors from SPARSE_MINIMIZER_STRESS.md and
the two obliquely separated upper squares. Keep its circle weights
`23/64` on each outer M corner and `9/64` on each outer B corner.
Keep edge magnitudes `23/16` along each of the three M-row edges,
`27/64` along each of the two B-row edges, and `207/512` on each
corresponding upward B-to-M edge.

Choose effective contact points as follows:

- Along the M row, all horizontal forces act at common height
  `45/128`, i.e. `37/128` above its center height `1/16`.
- Along the B row, all horizontal forces act at common height
  `-115/96`, i.e. `-25/96` relative to center height `-15/16`.
- The two vertical contact forces act at
  `(-5/4,-7/16)` and `(5/4,-7/16)`.

All these points lie in actual common side segments. Represent
each by convex weights on the two active support vertices of the
nonowner square. This gives two positive `nu` atoms per edge:
**14 separator-vertex atoms + 4 circle atoms = 18 atoms**.

For example, an M-row edge has nonowner averaged support offset
`(1/2,-37/128)`, so the positive-corner and negative-corner
probabilities along its second coordinate are `27/128` and
`101/128`. A B-row edge has averaged support offset
`(1/2,25/96)`, giving probabilities `73/96` and `23/96`.
The left and right upward edges use horizontal probabilities
`(1/4,3/4)` and `(3/4,1/4)` respectively.

Substitution in (7) gives exactly zero at every one of the nine
square nodes. The upper obliquely separated pair is unstressed:
all its circle and contact weights vanish, with zero angular
balance. Thus this necessary-condition theorem handles that
counterexample to common-frame normalization without rejecting it.

The rational regression script `check_sparse_stress.py` checks
all these angular derivatives and zero residuals, as well as
all 36 original physical pair separations and all 36 corners.
The test does not certify any other packing or prove the missing
unrestricted lower bound.

## 7. Gate boundary

The full-pose regularity and sparse angular-stationarity subgates
of G2.O3.0.2 are CLOSED by this argument. The remaining oblique
closure needs a complete structural classification and sharp
orientation-uniform inequalities, retaining the influence of the
unstressed squares on the number of squares that physically fit.

No claim of simultaneous planar-and-torque stress, sufficiency of
KKT for the nonconvex orientation problem, independent full audit,
Lean build, CI run, or global n=9 theorem is made.
