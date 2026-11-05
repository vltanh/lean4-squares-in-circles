# Two symmetries of the entire nine-square fixed-mask caller

**Prepared for review. No normalized root, row or proof tree is installed.**
This is a separate layer from the unnormalized strict-011 root. It uses no
registered 001 original, large-gap consequence or old ordering convention.

## Full target and conclusion

The caller has nine physical unit squares in a centered disk, all 36
physical pair conditions, and the five directed links AB, BC, CD, EF, FG
in a common orthonormal witness basis. A link has `dx>=|dy|`; each of its
five exact bits chooses either `dx>=h_i+h_j` or `dx<h_i+h_j`. The two extra
labels H and I occur in no marked link. Corners are either all strictly
inside Q or all in the closed disk, according to the original caller.
That strictness is not changed by this argument.

For every one of the 32 exact masks, existence of such a full caller is
equivalent to existence with both additional closed conditions

\[
 \beta_D\geq0,\qquad x_H\leq x_I.
\]

Since canonical alpha_D is positive, the first condition is equivalently
`t_D>=0`. Thus an exclusion of the entire normalized caller would exclude
the entire original caller. The reverse implication is immediate because
the normalized caller is a subset. The forward implication follows from
the two explicit transformations below. It does not assert that either
condition holds in every untransformed physical assignment.

## 1. Vertical reflection

Reflect the **whole configuration** in the witness x axis:

\[
 c_i'=(x_i,-y_i),\quad
 \alpha_i'=\alpha_i,\quad \beta_i'=-\beta_i,
 \quad z_i'=z_i,\quad g_i'=g_i.
\]

The new canonical axes are `u_i'=(alpha_i,-beta_i)` and
`v_i'=(beta_i,alpha_i)`. If R is the reflection matrix, then
`R u_i=u_i'` and `R v_i=-v_i'`. Consequently the old corner with signs
`(epsilon,tau)` becomes the new corner `(epsilon,-tau)`. This is a
bijection of each original's four corners and preserves every corner
norm exactly. Both strict and closed containment are preserved.

Unit frame norm, canonical folding, z, h and g are preserved. Reflection
is an isometry, so all 36 physical nonintersection conditions are
preserved. More explicitly, a signed owned u-axis separator keeps its
sign, and a signed owned v-axis separator changes sign. The dot product
of its reflected normal and reflected difference is unchanged. The
relative cosine `C=alpha_i*alpha_j+beta_i*beta_j` is unchanged; the relative
sine `S=alpha_i*beta_j-beta_i*alpha_j` changes sign. Hence all four signed
support inequalities of each of the eight alternatives are carried
bijectively to the corresponding original inequalities. No chosen owner
or separator is dropped.

For each marked link, dx is unchanged, dy changes sign and both physical
halfwidths are unchanged. Thus the absolute-value cone and the exact
actual/weak comparison are unchanged, including every equality face.
In particular all five bits remain the same: this is not a monotonicity
argument or a transfer to another mask.

Reflection negates t_D. If t_D is negative, apply it; otherwise use the
identity. The resulting t_D is nonnegative. The zero face remains in the
normalized caller. The two diagonal canonical endpoints are exchanged;
they remain valid parameterizations of the same reflected squares.

## 2. Swapping only the two unmarked extras

Let the label permutation exchange H and I and fix A through G. Transport
the **entire physical square** at each label: its center, frame, four
corners and all attached pair predicates. This is a bijection of all nine
frames, all 36 corners and all 36 unordered pairs. Containment is unchanged
and all marked endpoints are fixed, so the five cones and exact bits are
unchanged.

The code stores a pair in increasing-label order. If swapping H and I
reverses that order, the new directed difference is the negative of the
old one. The signed owned normal must therefore also negate. This happens
for the pair H,I itself; it must not be omitted when transporting an owned
separator. The owner label is always transported. Relative cosine stays
the same; relative sine negates when the pair order reverses. The
polynomial controls check the corresponding support-sign permutation.

If x_H exceeds x_I, apply the swap; otherwise use the identity. The result
has x_H<=x_I. Equal x coordinates remain included, with no discarded tie
case or auxiliary ordering on y or orientation.

## 3. Combining the maps without narrowing the caller

Reflection acts identically on each original's coordinates, while the
swap permutes only the two extra labels. Therefore the operations commute.
Each is an involution, and their four compositions form a finite group of
whole-caller bijections. Reflection does not change x_H or x_I. Swapping
H and I does not change D. The two choices above can therefore be made
independently, producing both closed conditions at once.

For a proof by contradiction, suppose a full original caller exists. Apply
the indicated whole-configuration map to obtain a member of the normalized
caller with the same strict radius condition and the same five exact
bits. An independently established exclusion of that normalized caller
would contradict its existence. There is no gap at `t_D=0` or `x_H=x_I`,
because both target inequalities are non-strict and normalization can
choose the identity on those faces.

This argument authorizes a **new, explicitly normalized root only after
review and attachment**. It does not authorize inserting its two rows into
the unnormalized root as unconditional necessary inequalities. Likewise,
the code maps physical assignments and literal owned cases; it does not
transport weighted proof certificates, child intervals or branch trees.
Such certificate transport would require an additional exact checker.
The same restriction applies to a registered original cell: its complete
path would have to be transported, so these symmetries are not installed
inside any current A, B, C or D original-cell proof.

## 4. Independent exact controls

`full_mask_symmetry_maps.py` implements the variable permutation/sign map,
corner map, sorted-pair and owned-axis maps, inset-proxy map, and the
four-choice normalization of a physical assignment. It imports only
`Fraction`. `check_full_mask_symmetries.py` independently reconstructs
polynomials over all 54 original columns. It checks every corner norm,
unit/fold/inset identity, every signed support literal for all 288 owned
alternatives, all 144 proxy alternatives, and all five cones and bit
margins under each of the four maps.

The comparison is an exact equality of rational coefficient dictionaries,
so it includes irrational unit frames such as the canonical diagonal
endpoints; sampling rational angles is not a premise. Separate rational
assignment controls verify selection, involution, commutation and the
shared zero faces. They need not satisfy a full packing to check these
algebraic map identities, and are not presented as packing witnesses.
Damaged maps omit a beta sign, desynchronize centers and frames, change a
marked frame, omit a physical block, or lose a sorted-pair/owned-v sign.
Every such control must fail.

No solver is called and no proof credit follows from this packet alone.
The fixed-mask caller, 9/36/36/5 inventory and strictness remain exactly
the original ones throughout.
