# n=9: all remaining positive-tree candidates reduce to TWO explicit completion families

**Status:** exhaustive hand reduction of the remaining tree branch. Subsequent complete capacity proofs are P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md; together they now close TREE.ALL in the declared radius window. The reduction below retains its original geometric scope. Full prerequisite-chain audit and Lean verification remain separate.

**Purpose:** replace an indefinite list of branching-tree graphs or angular subcases by two explicit geometric skeletons with complete continuous parameter ranges. The full cyclic branch remains separate and open.

## 1. Inputs and scope

Use the physical minimizing certificate from PHYSICAL_CONTACT_STRESS.md, with the strict common normal at every point-only vertex/vertex contact and the prior nonradial normal selection at off-origin such contacts. The declared lower-radius window is 79/40<=R<=sqrt(1105)/16.

TREE_BODY_LOCALIZATION.md and TREE_RADIUS_QUANTIZATION.md prove that any selected positive tree component in this window has

    R^2=17/4,

with all unloaded bodies containing the origin on their boundaries, and every loaded body a radial side-normal square S(e), center (3/2)e and inward contact point e.

The six origin-incidence profiles (s,v) are exhaustive. TREE.12 and TREE.04 are already excluded by TREE_FINITE_COMPLETIONS.md. THREE_VERTEX_ORIGIN_CAPACITY.md now excludes all TREE.03 completions. TREE02_POINT_CONTACT_COMPLETION.md excludes the whole point-only contact type TREE.02.P and identifies the shared-edge type TREE.02.E as an exact endpoint path.

The only remaining work inside the tree branch can therefore come from TREE.20, TREE.11 or TREE.02.E.

## 2. Family P: arbitrary staggered four-square path, five further squares

For parameters

    -1/2 <= tau_1,tau_2 <= 1/2,

take the four axis-aligned unit squares with centers

    (-3/2,0), (-1/2,tau_1), (1/2,tau_2), (3/2,0).

They fit the disk of squared radius 17/4 and have disjoint open interiors. This is the complete two-loaded path family, with its boundary values retained.

**P completion gate, CLOSED hand:** P_ALL_COMPLETION.md proves that no FIVE other independently oriented unit squares can be added inside the same disk with pairwise disjoint open interiors. No common-coordinate separation is allowed as an extra premise.

- TREE.20 lies in the strict interior parameter range |tau_i|<1/2.
- TREE.02.E is tau_1=tau_2=1/2 or its reflection.
- Certain aligned TREE.11 boundary cases give exactly one |tau_i|=1/2.
- The flat case tau_1=tau_2=0 was already excluded by SOLID_FOUR_ROW_UNRESTRICTED_NINE.md.
- The parameter range is deliberately allowed to include physically feasible cores whose arbitrary equilibrium certificate is not the strict-normal selected one; a complete physical capacity proof for the larger family suffices.

**Rejected shortcut:** a side of this path can hold THREE extra squares. The exact seven-square counterexample is in TREE_FINITE_VALIDATION.md, Section 5. A proof must couple both sides or use a whole-configuration invariant; it cannot independently assume two per side.

## 3. Family Y: nonaligned side-plus-vertex tree, four further squares

Let

    0<alpha<1,   0<theta<pi/2,
    u=(cos(theta),-sin(theta)),
    v=(-sin(theta),-cos(theta)),  e=(0,1).

The five-square skeleton consists of:

1. the axis-aligned side-origin square

       H=[-alpha,1-alpha] x [0,1],

   with center (1/2-alpha,1/2);
2. the vertex-origin square

       K={ a u+b v : 0<=a,b<=1 },

   with center (u+v)/2 and side axes u,v;
3. the radial terminal S(e), centered at (0,3/2);
4. the radial terminal S(u), centered at (3/2)u;
5. the radial terminal S(v), centered at (3/2)v.

**Y completion gate, CLOSED hand:** Y_ALL_COMPLETION.md proves that no FOUR other independently oriented physical unit squares fit the same disk of squared radius 17/4, disjoint from these five and one another, for the ENTIRE displayed alpha/theta range.

The exact nonaligned witness alpha=1/2, theta=pi/4 is in TREE_FINITE_VALIDATION.md. Its physical force-and-torque stress was executed in exact arithmetic there. Thus the skeleton itself must not be excluded; the subsequent complete theorem excludes its completion to nine squares.

## 4. TREE.11 has no other positive-tree geometry

**Theorem Y-normal form.** Every TREE.11 positive component, up to an orthonormal frame and relabeling, is either a member of family Y above or an endpoint member of family P.

*Proof.* There is one side-origin unloaded square H and one vertex-origin unloaded square K. Rotate/reflect so H is the displayed rectangle above y=0. Since zero lies in the relative interior of its lower side, its tangent cone is the entire upper half-plane. K's right-angle cone must lie in the lower half-plane. Hence its two side rays can be uniquely written as u,v above for some 0<=theta<=pi/2.

At q0=17/4 every loaded contact radius is one. For H, its only nonzero outward radial support point of norm one is (0,1): its two lower vertices have norms alpha and 1-alpha, both <1, and its upper vertices have norms >1. Thus H can have only the loaded neighbor S(e).

For K, the only outward radial support points of norm one are u and v, so its only possible loaded neighbors are S(u),S(v). None of these can be shared with H: u,v lie in the closed lower half-plane, whereas e is upward.

Connectivity therefore requires a positive H--K edge at zero. Its normal on H is vertically downward, because zero is in the relative interior of H's lower side. H's force balance also requires S(e) with some positive contact force magnitude mu. K consequently receives the upward force mu*e at zero. Write its outward radial loaded force magnitudes as a,b>=0 on u,v. Its force balance is

    a u + b v + mu e = 0.

The two scalar equations give exactly

    a=mu sin(theta),  b=mu cos(theta).

If 0<theta<pi/2, both are positive, so all three loaded terminals are present and the positive component is precisely the five-body family Y. There are no other unloaded bodies in TREE.11, and no other radius-one support directions for its loaded attachments.

If theta=0, a=0 and only S(v)=S((0,-1)) occurs below H. K=[0,1]x[-1,0], and the four-body component has centers

    (0,3/2), (1/2-alpha,1/2), (1/2,-1/2), (0,-3/2).

After exchanging x and y and relabeling, this is family P with one endpoint slider equal to 1/2. The case theta=pi/2 is its reflection. These two boundary cases are physical shared-side contacts, not discarded limits. QED.

This proof is a necessary structural implication for the selected tree certificate. It does not assume extra squares follow the same frame, does not discard zero-weight physical contacts, and does not assert every formal positive load automatically gives a full nine-square packing.

## 5. Exhaustive remaining-tree theorem

**Theorem.** Every hypothetical nine-square minimizing configuration in the declared window whose selected positive graph contains a tree component must contain either a family-P four-square skeleton with FIVE additional physical squares, or a family-Y five-square skeleton with FOUR additional physical squares.

*Proof.* The six-case tree theorem is exhaustive. TREE.12 and TREE.04 cannot complete to nine by their earlier capacity theorems. TREE.03 cannot by THREE_VERTEX_ORIGIN_CAPACITY.md. The point-only part of TREE.02 cannot by the new pocket completion theorem; its shared-edge boundary is family P. TREE.20 is family P. The only remaining profile TREE.11 is P or Y by Section 4. Every additional physical square remains in the respective completion premise. QED.

This is a finite two-family classification with all continuous parameters retained. P_ALL_COMPLETION.md and Y_ALL_COMPLETION.md now supply both whole-family capacities. Their combination closes the entire positive-tree branch in the explicit radius window; LOWER_WINDOW_FROM_EIGHT.md now supplies the explicit n=8 lower-window import, with its existing proof dependencies retained.

## 6. Exact remaining global obligations

- [x] **P.ALL:** no five-square completion of any staggered path in Section 2; P_ALL_COMPLETION.md.
- [x] **Y.ALL:** no four-square completion of any nonaligned fan in Section 3; Y_ALL_COMPLETION.md.
- [x] **TREE.ALL:** both capacities plus the exhaustive reduction exclude every positive tree component in the declared window.
- [ ] **CYCLIC:** a sharp exhaustive classification or universal inequality when every selected positive component contains a cycle.
- [x] The declared lower-radius window is explicitly imported from n=8 in LOWER_WINDOW_FROM_EIGHT.md.
- [ ] Global assembly, complete equality necessity/converse, independent mathematical audit and Lean/kernel integration; an independent coarse bound if standalone table-freedom is required.

The completed tree exclusions do not make nonbridge forces radial. No conclusion about CYCLIC is inferred from this tree classification. No global n=9 proof, independent full audit, Lean compilation or CI is claimed.
