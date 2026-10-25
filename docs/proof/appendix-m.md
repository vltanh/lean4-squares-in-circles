# Appendix M. Eight squares: the dual at the original centres

[Contents](README.md) · [← Appendix L](appendix-l.md)

This appendix proves the lower bound $q \ge q_*$ for every packing of eight
unit squares in a disk of squared radius $q$, and it finds every packing at
$q = q_*$, once [Chapter 11](11-eight.md) has shown that the seven squares
around the central one carry the frames of the optimal packing and are
separated along its axes. Both results come from one identity. Weight the five
corner constraints of the stationary chain by the circle weights $\mu_P$ and
the seven contacts by the contact weights $\lambda_e$ of
[Lemma J.6](appendix-j.md#lemma-j6-the-weights-of-the-chain); then for *any*
seven points in the place of the centres, the weighted sum equals $q_*$ plus a
positive combination of the squared distances of five of the points from their
places in the optimal packing (Theorem M.4). No estimate of how far the
centres are from the optimal ones is needed: the identity is exact at
arbitrary centres. It is the stress argument of
[§9.4](09-six.md#94-stresses) in the form of an identity.

Throughout, $d$ is a chain of [§J.1](appendix-j.md#j1-the-chain) with zero
defect, $F_y = 0$ and the signs of Lemma J.6, and $q$, $y$, $c$, $s$,
$x_1, \dots, x_4$, $y_3$, $y_4$, $h_1$, $h_2$ are its coordinates; in the end
$d = d_*$, the stationary solution of
[Proposition J.5](appendix-j.md#proposition-j5-the-stationary-solution), with
$q = q_*$. We write $e = (c, s)$, $f = (-s, c)$, $e_0 = (1, 0)$, $f_0 = (0, 1)$
and $w = \frac{1 + c + s}2$, and use the weights $\mu_P$
($P = A, B, D, E, H$), $\lambda_e$ ($e = AB, TB, DT, ED, GA, HG, HE$) and
$\omega = \lambda_{GA} = \lambda_{HG}$ of Lemma J.6.

## M.1 The dual at arbitrary centres

The *model centres* of the chain are those of the squares of the optimal
packing:

```math
\begin{gathered}
p^0_A = \left(x_1 - \tfrac12,\ y + \tfrac12\right), \quad p^0_B = \left(x_2 - \tfrac12,\ y + \tfrac32\right), \quad p^0_D = \left(x_3 + \tfrac12,\ y_3 - \tfrac12\right), \quad p^0_E = \left(x_4 + \tfrac12,\ y_4 + \tfrac12\right), \\
p^0_H = \left(h_1 + \tfrac12\right)e + \left(h_2 + \tfrac12\right)f, \qquad p^0_T(Z) = \left(x_2 - \tfrac32,\ Z\right), \qquad p^0_G(\eta) = \left(h_1 + \tfrac32\right)e + \left(h_2 + \tfrac12 + \eta\right)f ,
\end{gathered}
```

the last two for every height $Z$ of $T$ and offset $\eta$ of $G$. With the
offsets $o_A = (\frac12, -\frac12)$, $o_B = (\frac12, \frac12)$,
$o_D = (-\frac12, \frac12)$, $o_E = (-\frac12, -\frac12)$ and
$o_H = -\frac12 e - \frac12 f$, the points $p^0_P + o_P$ are the corners $P_P$
of the chain: the lower right corner of $A$, the upper right corner of $B$, and
so on.

### Definition M.1 (the gaps and the dual)

For seven points $p = (p_A, p_B, p_D, p_E, p_H, p_T, p_G)$ of the plane, the
*gaps* are

```math
\begin{gathered}
g_{AB} = \langle f_0, p_B - p_A\rangle - 1, \quad g_{TB} = \langle e_0, p_B - p_T\rangle - 1, \quad g_{DT} = \langle e_0, p_T - p_D\rangle - 1, \quad g_{ED} = \langle f_0, p_D - p_E\rangle - 1, \\
g_{GA} = \langle e, p_A - p_G\rangle - w, \qquad g_{HG} = \langle e, p_G - p_H\rangle - 1, \qquad g_{HE} = \langle f, p_E - p_H\rangle - w ,
\end{gathered}
```

and the *dual* is

```math
\mathcal V(p) = \sum_{P = A, B, D, E, H} \mu_P\,|p_P + o_P|^2 - \sum_e \lambda_e\,g_e(p) . \tag{M.1}
```

When the points are the centres of seven unit squares with the frames of the
optimal packing, each gap is the margin of a separating axis of one contact:
the projection of the difference of the two centres on the normal of the
contact, minus the sum of the half-widths of the two squares along it, which is
$1$ for two aligned squares and $w = \frac12 + \frac12(c + s)$ for an
axis-parallel square against a square turned by $t$.

*Lean:
[`Eight.Stationary.Coordinates.pA`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L164),
[`Eight.Stationary.Coordinates.pT`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L169),
[`Eight.Stationary.Coordinates.pG`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L170),
[`Eight.Stationary.Coordinates.anchorCenters`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L197),
[`Eight.Stationary.Coordinates.anchorOffsets`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L200),
[`Eight.Stationary.Coordinates.anchor_vertex`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L204),
[`Eight.OriginalDual.Positions`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L50),
[`Eight.OriginalDual.gap`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L58),
[`Eight.OriginalDual.value`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L67).*

### Lemma M.2 (the model centres)

For every $Z$ and $\eta$, all seven gaps of
$p^0 = (p^0_A, p^0_B, p^0_D, p^0_E, p^0_H, p^0_T(Z), p^0_G(\eta))$ vanish, and
$\mathcal V(p^0) = q$.

*Proof.* The aligned gaps are $g_{AB} = (y + \frac32) - (y + \frac12) - 1$,
$g_{TB} = (x_2 - \frac12) - (x_2 - \frac32) - 1$,
$g_{DT} = x_2 - x_3 - 3$ and $g_{ED} = y_3 - y_4 - 2$, all zero, as
$x_3 = x_2 - 3$ and $y_4 = y_3 - 2$. Next
$\langle e, p^0_G - p^0_H\rangle = 1$, and with $h_1 = c\,x_1 + s\,y - 2 - c$,

```math
\langle e, p^0_A - p^0_G\rangle = c\left(x_1 - \tfrac12\right) + s\left(y + \tfrac12\right) - \left(h_1 + \tfrac32\right) = \tfrac12 + \tfrac c2 + \tfrac s2 = w ,
```

and likewise $\langle f, p^0_E - p^0_H\rangle = w$ from
$h_2 = -s\,x_4 + c\,y_4 - 1 - s$. So the gaps vanish, and
$\mathcal V(p^0) = \sum_P\mu_P|P_P|^2 = q\sum_P\mu_P = q$, the five corners
lying on the circle of squared radius $q$ when $F = 0$. $\square$

*Lean:
[`Eight.Stationary.Coordinates.standard_contacts`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L246),
[`Eight.Stationary.Coordinates.GA_contact`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L225),
[`Eight.Stationary.Coordinates.HG_contact`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L220),
[`Eight.Stationary.Coordinates.HE_contact`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L240),
[`Eight.Stationary.Coordinates.anchor_circle`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L211),
[`Eight.OriginalDual.reference`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L55),
[`Eight.OriginalDual.reference_gap`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L71),
[`Eight.OriginalDual.reference_value`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L91).*

### Lemma M.3 (the forces)

The gaps are affine in the points: for all $p$ and $r$,

```math
\sum_e \lambda_e\,g_e(r) - \sum_e \lambda_e\,g_e(p) = \sum_{P = A, B, D, E, H, T, G}\langle F_P, p_P - r_P\rangle ,
```

with

```math
\begin{gathered}
F_A = \lambda_{AB}f_0 - \omega e, \quad F_B = -\lambda_{TB}e_0 - \lambda_{AB}f_0, \quad F_D = \lambda_{DT}e_0 - \lambda_{ED}f_0, \quad F_E = \lambda_{ED}f_0 - \lambda_{HE}f, \quad F_H = \omega e + \lambda_{HE}f, \\
F_T = (\lambda_{TB} - \lambda_{DT})\,e_0 = 0, \qquad F_G = (\lambda_{GA} - \lambda_{HG})\,e = 0 .
\end{gathered}
```

As $F_y = 0$, the force balance (J.2) of Lemma J.6 reads $F_P = -2\mu_P P_P$
for $P = A, B, D, E, H$.

*Proof.* Collect the coefficient of each point in $-\sum_e\lambda_e g_e$: for
instance $p_A$ appears in $g_{AB}$ with $-f_0$ and in $g_{GA}$ with $e$, so
$F_A = \lambda_{AB}f_0 - \lambda_{GA}e$. The two contacts of $T$ have equal
weights and opposite normals, and so have the two contacts of $G$. The last
claim compares with (J.2). $\square$

*Lean:
[`Eight.Stationary.Coordinates.forces`](../../SquaresInCircles/Eight/Stationary/Weights.lean#L189),
[`Eight.OriginalDual.weighted_gap_difference`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L83),
[`Eight.Stationary.Coordinates.force_balance`](../../SquaresInCircles/Eight/Stationary/Weights.lean#L192),
[`Eight.Stationary.Coordinates.slider_forces_zero`](../../SquaresInCircles/Eight/Stationary/Weights.lean#L203).*

### Theorem M.4 (the completed identity)

For all seven points $p$ of the plane,

```math
\mathcal V(p) = q + \sum_{P = A, B, D, E, H} \mu_P\,\left|p_P - p^0_P\right|^2 . \tag{M.2}
```

*Proof.* For each $P = A, B, D, E, H$, expanding the square with
$p^0_P + o_P = P_P$ and $-2\mu_P P_P = F_P$ (Lemma M.3),

```math
\mu_P|p_P + o_P|^2 = \mu_P|P_P|^2 - \langle F_P, p_P - p^0_P\rangle + \mu_P|p_P - p^0_P|^2 .
```

By Lemma M.3 with $r = p^0$ and Lemma M.2, and as $F_T = F_G = 0$,
$-\sum_e\lambda_e g_e(p) = \sum_{P = A, B, D, E, H}\langle F_P, p_P - p^0_P\rangle$.
Adding, and using $\sum_P\mu_P|P_P|^2 = q$ (Lemma M.2), gives (M.2). $\square$

*Lean:
[`Eight.center_square_difference`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L29),
[`Eight.OriginalDual.exact_identity`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L100).*

The identity uses $F = 0$ and $F_y = 0$ but not $F_t = 0$: it holds for every
chain with zero defect and a stationary position, whatever its tilt. The tilt
equation enters through $q$: by the envelope of
[§J.4](appendix-j.md#j4-the-stationary-solution), of all these chains $d_*$ has
the least squared radius.

![The optimal packing of eight squares in the circle of radius root q*, the central square grey and the seven others in colour, with the forces of the dual drawn as arrows: at each of the five corners on the circle, the lower right corner of A, the upper right corner of B, the upper left corner of D, the lower left corner of E and the corner of H, a dark arrow pointing to the centre o, labelled with its weight mu; and at each of the seven points of contact a pair of opposite arrows, each in the colour of the square it pushes, labelled with the weight lambda of the contact. The arrow at the corner of E is very short, its weight mu_E being about 0.025](figures/appendix-m/forces.svg)

*Figure M.1.* The weights of the dual on the optimal packing, drawn as forces:
at the five corners on the circle, the forces $-2\mu_P P_P$ (pointing to $o$,
labelled $\mu_P$); at the seven contacts, pairs of opposite forces
$\pm\lambda_e n_e$ along the normals (labelled $\lambda_e$). At every square
they add up to zero, Lemma M.3; at $T$ and at $G$ the two contacts balance each
other, so these two squares feel no force and can slide.

## M.2 The radius and the rigid centres

### Corollary M.5 (the radius and the rigid centres)

Let $p$ be seven points with $|p_P + o_P|^2 \le q'$ for $P = A, B, D, E, H$
and $g_e(p) \ge 0$ for the seven contacts. Then

1. $q + \sum_{P = A, B, D, E, H}\mu_P|p_P - p^0_P|^2 \le q'$; in particular
   $q \le q'$;
2. if $q' \le q$, then $q' = q$, $p_P = p^0_P$ for $P = A, B, D, E, H$, every
   gap vanishes, and $p_T = p^0_T(Z)$, $p_G = p^0_G(\eta)$ for some $Z$ and
   $\eta$.

*Proof.* (1) The weights $\mu_P$ are positive with sum 1 and the $\lambda_e$ are
positive (Lemma J.6), so $\mathcal V(p) \le q'$; then (M.2). (2) By (1),
$q' = q$ and $\sum_P\mu_P|p_P - p^0_P|^2 = 0$, so $p_P = p^0_P$; then
$\sum_P\mu_P|p_P + o_P|^2 = q$ and $\mathcal V(p) = q$, so
$\sum_e\lambda_e g_e(p) = 0$, and each gap vanishes. With $p_B = p^0_B$,
$g_{TB} = 0$ gives $\langle e_0, p_T\rangle = x_2 - \frac32$, so
$p_T = p^0_T(Z)$ for $Z = \langle f_0, p_T\rangle$; with $p_H = p^0_H$,
$g_{HG} = 0$ gives $\langle e, p_G\rangle = h_1 + \frac32$, so
$p_G = p^0_G(\eta)$ for $\eta = \langle f, p_G\rangle - h_2 - \frac12$.
$\square$

*Lean:
[`Eight.OriginalDual.value_le`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L133),
[`Eight.GeometricModel.original_dual_quantitative`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L28),
[`Eight.GeometricModel.original_dual_radius_lower`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L40),
[`Eight.OriginalDual.original_centers_rigid`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L147),
[`Eight.OriginalDual.slider_coordinates`](../../SquaresInCircles/Eight/Stationary/CenterCompletion.lean#L193),
[`Eight.GeometricModel.original_radius_and_centers`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L56),
[`Eight.GeometricModel.sharp_original_radius_and_centers`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L75).*

## M.3 The five-corner problem

The statement of [Theorem 11.1](11-eight.md#theorem-111-eight-squares)
defines the optimal radius by five corners $P_A, P_B, P_D, P_E, P_H$ and an
angle $\theta \in [0, \frac\pi4]$, with $e_\theta = (\cos\theta, \sin\theta)$,
$f_\theta = (-\sin\theta, \cos\theta)$ and the *spans*

```math
(P_B - P_A)_y \ge 2, \qquad (P_B - P_D)_x \ge 3, \qquad (P_D - P_E)_y \ge 2, \qquad \langle f_\theta, P_E - P_H\rangle \ge 1 + \sin\theta, \qquad \langle e_\theta, P_A - P_H\rangle \ge 2 + \cos\theta ,
```

as the least radius of a closed disk about $o$ that holds the five corners.

### Proposition M.6 (the five-corner minimizer)

If five corners with these spans and the angle $\theta = t_*$ of $d_*$ lie in
the closed disk of radius $\sqrt{q_*}$, they are the corners of $d_*$.

*Proof.* Put $p_P = P_P - o_P$ for $P = A, B, D, E, H$,
$p_T = ((P_B)_x - \frac32, 0)$ and $p_G = p_H + e$: formal positions, not
squares. Then $p_P + o_P = P_P$, and the gaps of Definition M.1 are

```math
g_{AB} = (P_B - P_A)_y - 2, \quad g_{TB} = 0, \quad g_{DT} = (P_B - P_D)_x - 3, \quad g_{ED} = (P_D - P_E)_y - 2, \quad g_{GA} = \langle e, P_A - P_H\rangle - 2 - c, \quad g_{HG} = 0, \quad g_{HE} = \langle f, P_E - P_H\rangle - 1 - s ,
```

all nonnegative by the spans. Corollary M.5 (2) with $q' = q = q_*$ gives
$p_P = p^0_P$, that is $P_P = p^0_P + o_P$, the corners of $d_*$. $\square$

*Lean: [`Eight.FiveCorner.spans`](../../SquaresInCircles/Geometry.lean#L303),
[`Eight.FiveCorner.sourcePositions`](../../SquaresInCircles/Eight/Corners/Selection.lean#L138),
[`Eight.FiveCorner.sourcePositions_gap`](../../SquaresInCircles/Eight/Corners/Selection.lean#L152),
[`Eight.FiveCorner.sourcePositions_gap_nonneg`](../../SquaresInCircles/Eight/Corners/Selection.lean#L173),
[`Eight.FiveCorner.stationary_points_of_fits`](../../SquaresInCircles/Eight/Corners/Selection.lean#L194).*

Chapter 11 shows that the least radius is $\sqrt{q_*}$ and that every
minimizer has the angle $t_*$, by the envelope of §J.4; with
Proposition M.6 the minimizer is unique, and it is $d_*$. This is the
configuration that the statement selects.

*Lean:
[`Eight.FiveCorner.stationary_angle_of_fits`](../../SquaresInCircles/Eight/Corners/Selection.lean#L111),
[`Eight.FiveCorner.minimizer_eq_canonical`](../../SquaresInCircles/Eight/Corners/Selection.lean#L219),
[`Eight.FiveCorner.existsUnique_minimizer`](../../SquaresInCircles/Eight/Corners/Selection.lean#L227),
[`Eight.FiveCorner.selected_eq_stationary`](../../SquaresInCircles/Eight/Corners/Selection.lean#L236).*

## M.4 Witnesses on the squares

Let $K_H, K_G, K_A, K_B, K_T, K_D, K_E$ be unit squares, in the cyclic order of
the boundary cycle of Chapter 11, with centres $c_H, \dots, c_E$. They have the
*stationary frames* if their frames, each written in the quarter turn that the
cycle uses, are $(1, 0)$ for $K_A$ and $K_B$, $(0, 1)$ for $K_T$ and $K_D$,
$(-1, 0)$ for $K_E$, and $(s, -c)$, which is $e$ turned back by a quarter turn,
for $K_H$ and $K_G$: these are the frames of the squares of the optimal packing.
The *stationary normals* of the seven edges
$H \to G \to A \to B \to T \to D \to E \to H$ are

```math
e, \quad e, \quad f_0, \quad -e_0, \quad -e_0, \quad -f_0, \quad -f .
```

### Lemma M.7 (witnesses)

Let the squares have the stationary frames, lie in the closed disk of squared
radius $q'$, and for each edge $i \to j$ let the signed axis with the stationary
normal $n$ separate $K_i$ from $K_j$: $\langle n, c_j - c_i\rangle$ is at least
the sum of the half-widths of the two squares along $n$. Then the points
$p = (c_A, c_B, c_D, c_E, c_H, c_T, c_G)$ satisfy the hypotheses of Corollary
M.5.

*Proof.* With these frames the sum of the half-widths is $1$ on the five
edges between aligned squares and on $H \to G$, and $w$ on $G \to A$ and on
$E \to H$. So each separation says that a gap of Definition M.1 is
nonnegative: for instance on $E \to H$, $\langle -f, c_H - c_E\rangle \ge w$ is
$g_{HE} \ge 0$. With these frames the points $c_P + o_P$ are vertices of the
squares $K_P$ ($P = A, B, D, E, H$), so they lie in the disk. $\square$

*Lean:
[`Eight.canonicalCos`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L30),
[`Eight.canonicalSin`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L33),
[`Eight.StationaryFrames`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L36),
[`Eight.stationaryNormal`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L40),
[`Eight.threshold_of_stationary_frames`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L49),
[`Eight.dual_gap_as_projection`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L78),
[`Eight.gaps_of_retained_normals`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L89),
[`Eight.anchor_offsets_closed`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L109),
[`Eight.vertices_at_original_radius`](../../SquaresInCircles/Eight/Boundary/OriginalWitnesses.lean#L123),
[`Eight.GeometricModel.sharp_rigidity_of_original_witnesses`](../../SquaresInCircles/Eight/Equality/SharpOriginal.lean#L90).*

Nothing is assumed about the positions of the squares beyond containment and
the seven separations: the squares need not be close to those of the optimal
packing, and the sliders $T$ and $G$ may be anywhere.

## M.5 The lower bound

### Theorem M.8 (the lower bound)

Every packing of eight unit squares in a closed disk of radius $R$ has
$R \ge \sqrt{q_*}$.

*Proof.* Translating the packing, we may take the disk centre at $o$; let
$q = R^2$ and suppose $q \le q_*$. Chapter 11 normalizes the packing at the
level $q_*$: a relabelling, a rotation and possibly a reflection give a packing
of the same disk whose square $0$ holds the core disk and whose seven other
squares, in the order of their centre directions, form the boundary cycle
$H, G, A, B, T, D, E$, with separating axes chosen on the packing itself. The
exclusion of Chapter 11 shows that these seven squares have the stationary
frames of $d_*$ and that the chosen axes have the stationary normals. By
Lemma M.7 and Corollary M.5 (2), with $d = d_*$ and $q' = q \le q_*$, $q = q_*$.
So $q \ge q_*$ in all cases. $\square$

*Lean:
[`Eight.GeometricModel.stationary_normalization_exists`](../../SquaresInCircles/Eight/Equality/SharpBoundary.lean#L73),
[`Eight.GeometricModel.normalized_at_original_radius`](../../SquaresInCircles/Eight/Equality/SharpBoundary.lean#L61),
[`Eight.GeometricModel.source_contained_at_original_radius`](../../SquaresInCircles/Eight/Equality/SharpBoundary.lean#L115),
[`Eight.SharpSourceEntry`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L24),
[`Eight.sharp_source_entry`](../../SquaresInCircles/Eight/Owners/GA/High/SourceComplete.lean#L22),
[`Eight.sharp_source_entry_original_rigidity`](../../SquaresInCircles/Eight/Boundary/SharpEntry.lean#L33),
[`Eight.GeometricModel.origin_sharp_rigidity`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L25),
[`Eight.GeometricModel.origin_sharp_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L42),
[`Eight.GeometricModel.sharp_squared_radius_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L49),
[`Eight.GeometricModel.sharp_radius_lower_bound`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L60),
[`Eight.lower_bound`](../../SquaresInCircles/Eight/Uniqueness.lean#L55).*

## M.6 The packings at the optimal radius

At $q = q_*$ the proof of Theorem M.8 gives more: the five squares
$A, B, D, E, H$ are at their places in the optimal packing, every contact gap
vanishes, and $T$ and $G$ lie on their *slider lines*, $c_T = p^0_T(Z)$ and
$c_G = p^0_G(\eta)$. Let $z_{\max} = \sqrt{q_* - (x_2 - 1)^2} - \frac12$,
$\eta_{\min} = -h_2 - \sqrt{q_* - (h_1 + 2)^2}$ and
$\eta_{\max} = -h_2 - \frac{13}{12}$.

### Theorem M.9 (the packings at the optimal radius)

A packing of eight unit squares in a closed disk of radius $\sqrt{q_*}$ is
congruent to the model, or to the mirror image of the model, of parameters
$(x, y, w, Z, \eta)$ with:

1. the central square centred at $(x, y)$ with the frame
   $(\frac{1 - w^2}{1 + w^2}, \frac{2w}{1 + w^2})$,
   $1 - \sqrt2 \le w < \sqrt2 - 1$, and the core disk in its interior;
2. $\frac7{12} \le Z \le z_{\max}$ and $\eta_{\min} \le \eta \le \eta_{\max}$;
3. the central square separated from each of the seven others.

Conversely, the model of such parameters is a packing in the closed disk of
radius $\sqrt{q_*}$, and the five corners of the chain lie on its circle.

*Proof.* Take the normalized packing of the proof of Theorem M.8. With the
stationary frames, a square is determined by its centre, so the seven squares
are those of the model with the sliders $Z$ and $\eta$. In the order of the
centre directions $T$ lies between $B$ and $D$, and $G$ between $H$ and $A$,
which fixes the sides of the two sliders; as $T$ and $G$ avoid the core disk of
the one-twelfth core ([§K.5](appendix-k.md#k5-the-one-twelfth-core)),
$Z \ge \frac7{12}$ and $\eta \le \eta_{\max}$. The central square has a frame
parameter $w$ in $[1 - \sqrt2, \sqrt2 - 1)$, recovered as
$w = \sin\varphi/(1 + \cos\varphi)$ from the angle
$\varphi \in [-\frac\pi4, \frac\pi4)$ of one of its four frames. The remaining
conditions hold because the model is a packing: containment of $T$ and $G$ gives
$Z \le z_{\max}$ and $\eta \ge \eta_{\min}$, and disjointness gives the
separations of (3), which are exactly the separating-axis conditions of the
central square against the seven others. Undoing the normalization gives the
congruence.

Conversely, for admissible parameters the seven outer squares lie in the disk
and are pairwise separated, on the whole closed ranges of the two sliders,
contacts included, along explicit normals; the central square lies in the disk
and is separated from them by (3). $\square$

*Lean:
[`Eight.GeometricModel.source_centers_of_original_anchors`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L69),
[`Eight.sameSquare_of_physical_center`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L84),
[`Eight.GeometricModel.source_squares_of_original_centers`](../../SquaresInCircles/Eight/Equality/SharpAssembly.lean#L93),
[`Eight.GlobalNormalization.original_slider_sectors`](../../SquaresInCircles/Eight/Boundary/Normalization.lean#L560),
[`Eight.Stationary.central_parameters_exist`](../../SquaresInCircles/Eight/Stationary/CentralParameters.lean#L119),
[`Eight.Stationary.EqualityParameters.Admissible`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L297),
[`Eight.admissible_of_original_geometry`](../../SquaresInCircles/Eight/Stationary/Family.lean#L165),
[`Eight.GeometricModel.origin_sharp_uniqueness`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L23),
[`Eight.GeometricModel.sharp_uniqueness`](../../SquaresInCircles/Eight/Equality/SharpEquality.lean#L86),
[`Eight.Stationary.exterior_separator`](../../SquaresInCircles/Eight/Stationary/EqualityGeometry.lean#L359),
[`Eight.Stationary.model_sqPacking`](../../SquaresInCircles/Eight/Stationary/EqualityGeometry.lean#L558),
[`Eight.Stationary.Coordinates.anchor_circle`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L211),
[`Eight.model_reaches`](../../SquaresInCircles/Eight/Stationary/Family.lean#L255).*

![The circle of radius root q* with the five fixed squares A, B, D, E, H drawn solid and their five corners on the circle marked in red; the square T drawn twice, dashed at its lowest position Z = 7/12, where it touches the red core disk about o, and dotted at its highest position z_max, where its upper right corner reaches the circle, with the vertical segment of its centres between them; and the turned square G drawn twice, dashed at the offset eta_min, where it reaches the circle, and dotted at eta_max, where it touches the core disk, with the segment of its centres along the side of H](figures/appendix-m/sliders.svg)

*Figure M.2.* Theorem M.9: the five squares with a corner on the circle are
fixed; the centres of $T$ and $G$ run over their slider segments, bounded by
the core disk ($Z = \frac7{12}$, $\eta = \eta_{\max} \approx 0.347$) and by the
circle ($Z = z_{\max} \approx 1.366$, $\eta = \eta_{\min} \approx -0.445$). The
central square, not drawn, moves and turns in the room left by the seven
others, around the core disk.

Every point of the box
$[0.139, 0.141] \times [-0.001, 0.001] \times [0.099, 0.101] \times [1.349, 1.351] \times [-0.321, -0.319]$
of parameters satisfies the conditions of Theorem M.9: eighteen quantities of
the model, among them the seven separation margins of the central square and the
room left in the containment of $T$ and $G$, are bounded on the box by interval
evaluation ([§L.6](appendix-l.md#l6-interval-evaluation)).

*Lean:
[`Eight.Stationary.EqualityParameters.InBox`](../../SquaresInCircles/Eight/Stationary/Coordinates.lean#L316),
[`Eight.Stationary.box_data_bounds`](../../SquaresInCircles/Eight/Stationary/EqualityBox.lean#L232),
[`Eight.box_admissible`](../../SquaresInCircles/Eight/Stationary/Family.lean#L28),
[`Eight.sample_admissible`](../../SquaresInCircles/Eight/Stationary/Family.lean#L129).*

## M.7 The models of the statement

The statement of Theorem 11.1 describes the optimal packings by the centre and
the angle of the central square, the height of $T$ and the offset of $G$, with
the corners of the five-corner minimizer, which are those of $d_*$ by §M.3.
Its *admissible parameters* have the angle $\varphi$ of the central square in
$[-\frac\pi4, \frac\pi4)$, the disk centre inside the central square, $T$ above
and $G$ below the horizontal axis, $T$ and $G$ in the disk, and the central
square separated from the seven others. The angle and the parameter $w$ of
Theorem M.9 correspond by $w = \frac{\sin\varphi}{1 + \cos\varphi}$,
$\varphi = 2\arctan w$. Under this change of variables the two sets of
conditions agree: the one-twelfth core, applied to the model of admissible
parameters as a packing, puts the core disk inside its central square, and
avoiding it gives $Z \ge \frac7{12}$ and $\eta \le \eta_{\max}$; the converse
directions are direct computations. So the models of the admissible parameters
and their mirror images are exactly those of Theorem M.9. They are packings of
the disk of radius $\sqrt{q_*}$ that reach its circle, and by Theorems M.8 and
M.9 every optimal packing is congruent to one of them, which is the uniqueness
part of Theorem 11.1.

*Lean:
[`Eight.Parameters.toStationary`](../../SquaresInCircles/Eight/Equality/Angles.lean#L149),
[`Eight.Parameters.ofStationary`](../../SquaresInCircles/Eight/Equality/Angles.lean#L152),
[`Eight.Parameters.ofStationary_admissible`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L29),
[`Eight.Parameters.central_core_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L80),
[`Eight.Parameters.top_core_rail_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L99),
[`Eight.Parameters.tilted_core_rail_recovered`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L123),
[`Eight.Parameters.toStationary_admissible`](../../SquaresInCircles/Eight/Equality/Equivalence.lean#L159),
[`Eight.GeometricModel.models_eq_stationary`](../../SquaresInCircles/Eight/Construction.lean#L39),
[`Eight.radius_eq_stationary`](../../SquaresInCircles/Eight/Uniqueness.lean#L33),
[`Eight.uniqueness`](../../SquaresInCircles/Eight/Uniqueness.lean#L62),
[`Eight.models_reach`](../../SquaresInCircles/Eight/Uniqueness.lean#L70),
[`Eight.optimum`](../../SquaresInCircles/Eight/Uniqueness.lean#L82).*
