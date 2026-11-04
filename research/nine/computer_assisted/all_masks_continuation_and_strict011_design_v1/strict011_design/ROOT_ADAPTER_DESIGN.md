# Fresh full strict 011/00 root: source and implementation design

**Prepared design only.** No geometry adapter is installed, no search is
started and no state or row is accepted by this packet. This is the next
source map after the current 001/00 original-cell work. Independent exact
controls and physical review are required before an implementation can
enter a proof. SOURCE_MAP.json pins the inspected sources and classifies
their permitted reuse.

## 1. The root caller

The target is the entire original D_011/00^lt predicate of the fixed A.2
contract, at Q = 1105/256. It has nine physical squares A through I, all
36 original corners strictly inside Q, all 36 physical pair conditions,
and the five directed center-cone links AB, BC, CD, EF and FG. AB, EF and
FG have actual horizontal projection separation. BC and CD have the
strict reverse comparison. There is no old original-cell path, no
large-gap normalization, no endpoint angle sign, no vertical DG sign,
no DG corridor, no actual BC and no ordering of H and I.

A common rotation places the supplied witness basis on the coordinate
axes without translating the disk center. Independent square symmetries
then choose u_i = (alpha_i,beta_i), v_i = (-beta_i,alpha_i), with
alpha_i >= abs(beta_i), alpha_i^2 + beta_i^2 = 1. This changes each
square's parameterization, not its physical set or its neighbors. Define
z_i = abs(beta_i), h_i = (alpha_i+z_i)/2 and
g_i = 1/(2(alpha_i+z_i)). The first 54 scalar variables match the reusable
exact core's layout:

| Columns | Meaning |
|---|---|
| 2i, 2i+1, for 0 <= i < 9 | x_i, y_i |
| 18+i | alpha_i |
| 27+i | beta_i |
| 36+i | z_i = abs(beta_i) |
| 45+i | g_i, the physical contained-square halfwidth |

Each center-cone edge i,j supplies two inequalities
x_i-x_j + y_j-y_i <= 0 and x_i-x_j + y_i-y_j <= 0.
For the three actual links use
x_i-x_j+(alpha_i+z_i+alpha_j+z_j)/2 <= 0.
For BC and CD retain the strict inequality
x_j-x_i-(alpha_i+z_i+alpha_j+z_j)/2 < 0 in the caller. Its weak version
may be used as a necessary affine relaxation, but the strict source
predicate must remain available to a valid terminal.

The exact nonlinear caller is already available from the accepted generic
emit_fixed_mask.py with mask 011/00, radius strict and n=9. It emits all
original physical separating alternatives; no actual separator is chosen
at the root. The new affine adapter must implement its own root and
propagation rather than route this caller through the old V/K stack.

## 2. A conservative rational initial box

The prepared specification uses nine slope intervals [-1,1], 18 center
intervals [-2,2], and the scalar intervals below. They are deliberately
derived from the unrestricted physical caller.

| Quantity | Closed initial interval | Physical derivation |
|---|---|---|
| alpha | [7/10,1] | Canonical alpha >= abs(beta) and unit norm give alpha^2 >= 1/2 > 49/100. |
| beta | [-3/4,3/4] | beta^2 <= 1/2 < 9/16. |
| z | [0,3/4] | z = abs(beta). |
| g | [1/3,1/2] | 1 <= alpha+z <= sqrt(2) < 3/2. |

The average of the four squared physical corner norms is
abs(c_i)^2+1/2. Thus abs(c_i)^2 < Q-1/2 = 977/256 < 4,
which proves each center interval [-2,2]. These are outer bounds; they
add no restriction to the full strict caller. The initial path and
selected-pair list are empty, and inherited difference/diagonal maps
are empty. Initial coordinate differences can be reconstructed as
[-4,4] before any exact mask or pair propagation.

prepare_root_spec.py prints this proposed root plus 159 elementary
necessary affine rows: 108 interval bounds, 36 canonical-frame linear
consequences and 15 cone/mask rows. It does not prove or install those
rows. The nonlinear frame, inset, corner and pair relations remain
explicit caller requirements. The file deliberately states
accepted_geometry_adapter=false and proof_credit=0.

## 3. Reuse boundary found in the existing source

Calling the old initializer with an empty path is insufficient. Direct
inspection found the following 001-specific behavior:

| Existing entry point | Reason to replace it for this caller |
|---|---|
| V.effective_boxes | Clips A/B slopes using the actual A-B-C span and contains CD separator restrictions. |
| V.center_bounds | Unconditionally narrows C/D/F/G positions and orders H <= I; versioned branches add more old geometric consequences. |
| V.difference_bounds | Unconditionally adds a CD vertical gap and DG sign/corridor restrictions. |
| K.rebuild and collect_rows | Invoke those routines and the old fixed-mask geometry; their output is not a universal root model. |
| Existing B/C/D Context subclasses | Load the old ancestry stack transitively, even when their final wrapper changes only an original ID. |

The new root must not import that transitive stack. A row cannot become
universal merely because its printed label sounds generic. The following
parts have a narrower, usable boundary:

- The generic independent physical replay core performs rational weighted
  sums, residual payments and complete-cover checking through an external
  geometry adapter. Keep that arithmetic unchanged, with a new caller ID.
- Corner support and four-product corner helpers use one original's
  physical frame, its containment and current proved intervals. Rebuild
  their literals with the new root's propagated intervals.
- Pair-frame and projection Gram helpers use the selected original pair,
  the current owned-separator slot and proved difference intervals. They
  introduce no mask premise, but they cannot be evaluated before their
  required pair choice exists. Recompute all auxiliary absolute bounds.
- The owner-free support helper is a candidate reusable family, subject
  to its independent reconstruction and every local interval guard. Do
  not import the Context which currently installs it.
- Pure rational square-root and frame-interval formulas can be extracted
  into a separate reviewed module. Importing K merely for analytic() would
  also load its old proof stack; avoid that dependency.

The discovery engine may later be adapted for the new geometry interface,
but the exact replay must import no numerical producer or optimizer.
All import and premise bindings should be explicit.

## 4. Required adapter interface and coverage

Implement independent rebuild(state, printed_rows), analytic(angles),
infer_angles(angles, scalar), choices(path), and verify_early_terminal
against this exact caller. At every rebuild check its strict 011/00 scope,
nine labels, 54-variable layout, mask rows and inherited path restrictions.
Return only the independently reconstructed printed rows and proved
nonnegative absolute bounds for every original and auxiliary variable.

Start path handling with closed angle/coordinate bisections, complete
four-way physical inset alternatives and complete eight-way physical SAT
alternatives. The latter enumerate both owners, both owned axes and both
signs for the chosen pair. A split must preserve all alternatives before
searching any child. A containing square may contact another on a side;
zero reserves in separation inequalities and interval boundary faces must
remain covered. Old
row-escape kinds have no meaning here until their theorem, guards and
whole complement have been separately attached to this caller.

For the accepted strict actual-AB terminal, derive every quantitative
guard from the new state, replay the accepted scalar certificate and use
the published strict 011 adapter. A failure to prove a guard leaves that
domain OPEN. There is no inherited five-domain reduction and no 001
closed-Q equality blocker in this root.

## 5. Exact controls before any installation

The first acceptance should reconstruct the root independently, compare
every literal elementary row and reject altered masks, labels, variable
indices, missing physical pairs, inherited original paths, extra endpoint
signs, DG corridor assumptions and H/I order. Rational physical frame
and corner examples must check the proposed box derivations and row
identities. Exact endpoint tests must include zero slope and both
canonical diagonal endpoints, using symbolic unit-frame identities for
the irrational diagonal components.

For physical splits, check every owned axis/sign formula and all closed
4/8/2 union faces independently. McCormick and Gram tests must use the new
root's own product intervals and residual bounds, including broad center
differences. Preserve the exact selected-seven 011 control: it should
still satisfy the seven-square restriction, while duplicating a square
as H or I must fail the full nine-square pair predicate. Retain the five
known full-nine closed-Q witnesses as controls for any broader proposed
relaxation; they do not assert feasibility of this strict 011 root.

Only after those controls and physical review pass should a numerical
pilot create a certificate. Its first weighted use then needs the same
independent exact row and ancestry replay as any eventual complete tree.
This design starts no new numerical lane and claims no domain closure.
