# Fixed-star selection in the entire nonparallel middle-house domain

**Status: complete hand necessary-feature implication; root and separate independent
full hand audits passed.** Use the one-owner middle-triple domain of
HOUSE_MIDDLE_TRIPLE_OWNED_HUB_DOMAIN.md and the complete parallel-star
exclusion HOUSE_MIDDLE_TRIPLE_PARALLEL_STAR_EXCLUSION.md. The remaining
hub A has nonparallel positive forces. All three loaded physical circle
masks, actual shared means and four completion squares remain.

The exact positive graph is AD,AT,DT,AB,BC,CD. Use

\[
 A=[-1,0]\times[-t,H],\quad t,H>0,\quad t+H=1,
 \quad p_{AD}=0,\quad n_{AD}=e_x,
\]

\[
 D=[0,1]u+[0,1]v,\quad u=(a,b),\quad v=(b,-a),
                    \quad a,b>0,\quad a^2+b^2=1.
\tag{1}
\]

Let alpha be the A-to-T normal, eta the A-to-B normal, beta the D-to-T
normal, and zeta the D-to-C normal. The complete domain already gives

\[
 \alpha_x\ge0,\quad\alpha_y>0,\qquad
 p_{AB}=r=(-1,-t),\quad\eta_x<0,\quad\eta_y<0,
\]

\[
 p_{AT,y}=H,\qquad p_{DT}=u,\quad\beta_y>0,
                     \qquad p_{DC,y}<0,\quad\zeta_y<0.
\tag{2}
\]

**Theorem.** The same finite necessary-certificate selection can enforce
all of the following whole-domain implications:

1. AT is not genuinely free. It is owned by A or by T.
2. If AB is genuinely free, AT is a positive-length shared side.
3. If DT is genuinely free, DC is a positive-length shared side.

The preceding all-domain free-external theorem also excludes free DC.
Thus every actual variable mean mentioned in items2--3 is explicitly
retained, rather than treated as a fixed application.

## 1. A genuinely free AT direction has a nonzero local determinant

If AT is genuinely free, its singleton A application is the upper-right
vertex q=(0,H). The other two A applications are the fixed physical
singletons0 and r. Let mu,kappa>0 be the AT,AB magnitudes. Their
y-force and torque equations at the actual unloaded A are

\[
              \mu\alpha_y+\kappa\eta_y=0,
       \qquad\mu\det(q,\alpha)+\kappa\det(r,\eta)=0.
\]

They require

\[
 L_{AT}(\alpha)=\eta_y\det(q,\alpha)
                         -\det(r,\eta)\alpha_y=0,
\]

\[
 L_{AT}(\alpha)=-H\eta_y\alpha_x
                         -\det(r,\eta)\alpha_y.
\tag{3}
\]

The coefficient -H*eta_y is strictly positive. With the independent
other normal fixed, at most two unit AT directions satisfy (3).
No loaded-body force or circle-weight relation is used.

## 2. A free AB direction requires a genuine shared AT side

Suppose AB is genuinely free and AT is a singleton. Write q for its
fixed physical AT point, keeping any actual A-owned vertical normal.
The same full A equations give

\[
 L_{AB}(\eta)=\alpha_y\det(r,\eta)
                            -\det(q,\alpha)\eta_y=0,
\]

\[
 L_{AB}(\eta)=t\alpha_y\eta_x
                         +(-\alpha_y-\det(q,\alpha))\eta_y.
\tag{4}
\]

Its first coefficient is strictly positive by (1)--(2). Hence this
free AB direction is also confined to at most two unit directions
when the other normal is fixed. The conclusion applies to every
singleton AT owner, including a physical tilted T vertex on A's
upper side; no boundary mask is restricted.

If AT is a positive-length shared side, its force application q is
an actual variable mean. Equation (4) is not invoked with q fixed.
This entire shared-side alternative remains in item2 of the theorem.

## 3. A free DT direction requires a genuine shared DC side

Suppose DT is genuinely free and DC is a singleton. Write w for the
fixed physical DC application. The complete domain has w_y<0, while
the roof point u has u_y=b>0. The actual D y-force and torque equations
give

\[
 L_{DT}(\beta)=\zeta_y\det(u,\beta)
                               -\det(w,\zeta)\beta_y=0,
\]

\[
 L_{DT}(\beta)=-b\zeta_y\beta_x
                         +(a\zeta_y-\det(w,\zeta))\beta_y.
\tag{5}
\]

The first coefficient is strictly positive. This covers both a C-owned
singleton and a D-owned singleton with its actual point fixed by the
physical intersection. No roof corner weight is used. A genuinely
shared DC side keeps its variable mean and is not removed by (5).

## 4. One compatible simultaneous selection and the full remaining scope

In every displayed determinant, the free direction is at a physical
point distinct from the other two hub applications. For A these points
have respective heights0,H,-t. For D they have heights0,b,w_y<0.
Matched four-junction choices only couple opposite pairs at one point,
so the free parameter is independent of the other directions used in
its determinant. Any matched pair with additional physical squares
does not couple those distinct local points.

Prelist every ordered physical middle-house tuple and every fixed
singleton feature in items1--3 before extracting multipliers. The
strictly positive coefficients in (3)--(5) make each real-analytic
condition nontrivial on its permitted open product domain. Avoid the
finitely many zero sets together with all previously required strict,
nonradial, fixed-tip, fixed-star and matched-junction conditions.
Physical uncrossing retains every surviving free direction; added
forces occur only on actual shared sides, and thinning removes atoms.
Every final forbidden free feature would satisfy its prelisted
determinant, which is impossible.

The normal of AT is therefore either A-owned vertical e_y or T-owned
with both components positive. In the second case AT is necessarily
singleton, so AB is B-owned: its strict southwest A vertex cone has
no A side-axis owner. DT cannot be D-owned by the complete domain
theorem. Thus DT is T-owned whenever DC is singleton; it can remain
free only opposite an actual shared DC side. Free DC was already
excluded by HOUSE_MIDDLE_TRIPLE_FREE_EXTERNAL_SELECTION.md.

These implications do not close the nonparallel-A star. They retain
every genuinely shared roof/external side and the complete parallel-roof
radial-S alternative. There is no circle-mask assumption, frozen mean,
post-certificate normal change, numerical parameter subdivision,
Lean compilation or CI.
