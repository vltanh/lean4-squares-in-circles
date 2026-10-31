# Every four-body diamond block with a radial leaf is excluded

**Status: complete whole-graph assembly; root and two separate independent assembly
audits passed.** Work throughout
\[
                       79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

**Theorem.** No selected positive five-body component can consist of a
four-body diamond block and one bridge to a leaf. Both attachment orbits,
both radial leaf types, every physical circle-corner mask, every actual
shared-side mean and all four arbitrary completion squares are retained.
The assertion is a core exclusion and requires no secondary minimizing
choice or motion of any square.

The diamond is K4 with one edge removed. Its two attachment orbits are
a hub and a tip. The completed sources below cover all of them. This
closes the entire diamond part of C1.4.b1. The other graph type, C4 with
a leaf and all three non-articulation cycle bodies loaded, remains a
separate gate; no closure of that entire coarse cell is claimed here.

## 1. Previously completed attachment and physical-mask reductions

NO_UNLOADED_DIAMOND_HUB.md, Section 5, already proves:

* a leaf at a diamond tip is impossible, for both S and D leaf types;
* an S leaf at a diamond hub is impossible;
* for a D leaf at a hub, the second hub U must carry positive circle load.

These statements include zero-weight physical boundary states. Briefly,
the tip-attachment proof forces both hubs and the unattached tip to be
loaded, creating three mutually touching boundary squares. For an S leaf
at a hub, the connected boundary-neighbor theorem excludes a boundary U,
and the unloaded-hub theorem excludes the remaining zero-load U.

In the remaining D hub case write the positive pair edges as
\[
                           AL,\ AU,\ AB,\ AC,\ UB,\ UC.
\tag{2}
\]
The tips B,C have exact positive degree two and are loaded because each
has physically touching neighbors. The articulation A is physically
clear. The D leaf forces, after rotation,
\[
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[H-1,H],\qquad0<H<1.
\tag{3}
\]
Its force is horizontal and applied at (1-s,0), so its origin moment
is zero. The local D articulation argument is recorded in
D_DIAMOND_RADIAL_HUB_EXCLUSION.md, Section 1, with its exact prerequisites.

The entire physical two-circle-corner mask of U is excluded by
D_DIAMOND_RADIAL_HUB_EXCLUSION.md. Thus U has exactly one physical
circle corner z_U and positive weight at it. Section 1 of
D_DIAMOND_PARALLEL_HUB_EXCLUSION.md, before any frame assumption, gives
an exhaustive normal localization. After horizontal reflection,
\[
                (z_U)_x<0<(z_U)_y,\qquad
                (n_0)_x<0,\quad(n_0)_y\ge0,
\tag{4}
\]
where n_0 is the actual outward AU normal from A.

The proof of (4) retains the other tips' physical masks. It uses acute
boundary-corner products, the global force sum, the strict unit support
span and A's balance. No degree-two equation is used at U.

## 2. A strict vertex contact localizes every other triangle application

We give the geometric fact needed to pass from an oblique n_0 to the
complete lower-triangle domain. It is the strict-vertex form of the
contact fact in BOWTIE_SHARED_SIDE_FREE_INTERFACE.md, Section 1.1;
its proof needs no free-normal assumption on the other body.

**Lemma.** Let three unit squares A,U,C have all three physical pair
contacts. Suppose the AU normal strictly exposes a vertex Q of A.
Then every actual AC application P, including an arbitrary shared-side
mean, satisfies
\[
                                  |P-Q|\le1.
\tag{5}
\]

*Proof.* If AC has an A-owned side-axis normal n, the triangle
side-normal theorem gives n dot n_0>=0. Because n_0 is strict at
an A vertex, both its A-side components are nonzero; hence the scalar
product with the signed side axis n is positive. Therefore Q lies on
the AC support side, and P,Q lie on the same unit segment.

Otherwise the AC normal is not an A side axis. It strictly exposes an
A vertex P. If P=Q or P is adjacent to Q, (5) follows. If they were
opposite vertices, their strict outward normal cones have negative
scalar product. In direction n_0 the support separation across A is
its width, which is strictly larger than one. At the minimum AC
normal support point P of C, the strict support-span lemma of
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, Section 1, gives
\[
                    \max_{x\in C}n_0\cdot(x-P)<1.
\]
Every point of U has n_0 projection at least n_0 dot Q, whereas
n_0 dot(Q-P)>1. Thus C and U would be closed-disjoint, contrary
to their physical contact. This excludes the opposite vertex and
proves the lemma. The owned-side case retained the full actual mean.
\(\square\)

## 3. Every oblique central normal has the exact lower-tip star

Suppose (n_0)_y>0 in (4). Its A application is the upper-left vertex
\[
                              Q=(-s,H).
\tag{6}
\]
Positive vertical force balance on A requires at least one tip normal
to have negative vertical component, because the leaf is horizontal.
Call that tip C. Its A support point P lies on the bottom side
of A, at height H-1. Applying (5) to the physical triangle AUC
shows that P's horizontal coordinate equals Q's: the vertical
difference already has length one. Thus
\[
                              P=(-s,H-1).
\tag{7}
\]

The C normal cannot have positive horizontal component, since its A
support would then be the lower-right vertex instead of (7). It also
cannot be the pure downward A axis: its scalar product with n_0 is
negative, contradicting the triangle side-normal theorem. Therefore
that normal is strictly southwest.

The two loaded physical boundary squares U,C, their actual contacts at
Q,P, and C's exact positive degree-two star now satisfy every hypothesis
of D_DIAMOND_OBLIQUE_HUB_EXCLUSION.md. That theorem derives C's physical
unique-corner mask from these contact locations, makes the compatible
fixed-tip selection only for singleton applications, and treats the
entire shared UC mean separately. It excludes every actual UC owner
and every actual AU endpoint, without using an equation at U.

Thus the entire oblique alternative in (4) is impossible. The upper
tip B was used only through force balance to supply the downward tip;
its physical mask, application and mean were not restricted.

## 4. Horizontal central normals and the complete final cover

It remains that n_0=-e_x. If the frames of A,U are parallel,
D_DIAMOND_PARALLEL_HUB_EXCLUSION.md excludes the complete configuration.
That source also separately covers every oblique normal in the
parallel-frame case, so no parallel endpoint is missing.

If the frames are not parallel,
D_DIAMOND_HORIZONTAL_HUB_EXCLUSION.md excludes this entire horizontal
alternative. Its proof retains the upper tip B's full mask. Three
horizontal reactions are impossible by an exact unit-section argument.
Otherwise it localizes only the downward tip C, proves that tip has a
unique physical circle corner, and exhausts the C-owned, U-owned and
positive-length shared UC alternatives. The U-owned and shared cases
contradict the exact bound
\[
                              Y-VX<-31/3200,
\]
while C's true force and torque require the same expression to be
nonnegative. The C-owned case uses the independently audited uniform
radius estimate in D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md.

These alternatives exhaust every central normal, every relative frame
and every physical U mask. Combined with Section 1, they exclude both
attachment orbits and both radial leaf types of the diamond block.

## 5. Certificate compatibility and exact scope

Only the established strict, nonradial, matched-junction certificate is
used. The fixed-application unique-tip exclusions are finite generic
conditions imposed before extracting multipliers, simultaneously with
the earlier selections. Every application to a final singleton star
has a physical fixed point. Positive-length shared contacts keep their
actual aggregate means, including endpoint means, throughout their
separate proofs. No side mean is replaced by a chosen point in order
to apply a determinant argument.

The proof preserves the exact positive degree three at U in the D hub
case. Its loaded tips alone have degree-two force and torque equations.
The component's four other packing squares are arbitrary and remain
present; no completion, squeezing or secondary-minimizer argument is
needed in this whole diamond exclusion.

The remaining all-three-loaded C4-with-leaf branch and larger mixed
positive components require their own full arguments. No Lean
compilation, CI, numerical extremum or changed contact-normal convention
is a premise of this completed diamond theorem.
