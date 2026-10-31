# Every off-origin unloaded bridge body is a short side transmitter

Date: October 26, 2026.
**Status: accepted uniform hand theorem after full-source root review in
REVIEW_ONE_ROOT_FORESTS_AND_OFF_ORIGIN_BRIDGES_ROOT_2026_10_26.md and
separate independent review in
REVIEW_OFF_ORIGIN_BRIDGE_TRANSMITTERS_ROOTED_BLOCKS_2026_10_26.md.**
No shared ledger or original gate has been changed by this source.

Work in 79/40<=R<=sqrt(1105)/16 with the common compatible physical
certificate. Put d=sqrt(R^2-1/4)-1 and delta=max(R-2,0). Keep every
original application, normal, mean, circle mask and physical square.
The component need not be a tree. A body is all-bridge when every
one of its incident positive pair edges is a graph bridge.

**Uniform theorem.** Let U have positive pair degree, be truly unloaded
and all-bridge, and be disjoint from the origin. Its positive forces
are all collinear, and it has
exactly one outward neighbor. In suitable own axes its actual square
and applications have the form

    U=[rho,rho+1] times [b-1/2,b+1/2],
    0<rho<=d-1<1/60,          |b|<=1/2,
    p_in=rho e_x,            p_out=(rho+1)e_x.             (1)

Every incoming neighbor contains the origin. Every actual incoming
force acts at p_in and every outgoing force at p_out. Under the
proved minimal-support selection of
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, U has precisely one
incoming neighbor as well, and hence its actual positive degree is
two. It is an original side-normal transmitter of width one.

In particular R^2>17/4 is necessary. The outward neighbor may belong
to an arbitrary cyclic block; it is not declared loaded, radial, or
a leaf by this statement.

## 1. Local center and radial-support bounds

First U meets D_delta. Otherwise the radial bridge central-endpoint
theorem would make it the outer body at every incident edge. All
applications would be its unique nearest point to zero and all its
positive pair directions would agree, impossible at a truly unloaded
body. This is the local proof of TREE_BODY_LOCALIZATION.md, Theorem
F1.1, and it needs no tree premise elsewhere in the component.

Every contained unit has center norm below M=91/60. The sharper
local consequence for U is

    |c_U|<=delta+1/sqrt(2)<19/24.                           (2)

At a nonzero radial bridge application, call its direction outward
from U when U is on the inner side of the radial support. Such an
application has the form p=t e, t>0, with U in e.x<=t. The actual
neighbor lies in e.x>=t. The sharp contained-unit supporting-half-plane
bound from END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1, gives

    t<=d<61/60.                                          (3)

If a square avoids zero, every outward radial support point has norm
strictly greater than one. To verify this directly, some own center
coordinate has absolute value greater than 1/2; reverse that axis to
make it positive. Every square point then has positive coordinate on
that axis, so support in the radial direction of p uses the far face,
whose coordinate exceeds one. Hence

    1<t<=d.                                              (4)

This is the geometric Lemma F1.3 of TREE_BODY_LOCALIZATION.md and
does not require a zero load. In particular an outward bridge from U
is impossible if d<=1.

## 2. Both incoming and outgoing edges occur

Let p_* be U's unique nearest point to zero, with positive norm, and
let f=p_*/|p_*|. Every incoming bridge uses p_* and has outward force
direction -f on U. They cannot balance by themselves.

Conversely every outgoing application p=t e belongs to U, and the
nearest-point supporting inequality gives f.p>=|p_*|>0. Thus
f.e>0 for every outgoing force. Outgoing forces alone cannot balance
either. Because U has zero circle load, at least one incoming and
at least one outgoing edge exist.

## 3. Full own-frame force classification

Choose an own axis for which the U center coordinate a is greater
than 1/2. If the other coordinate also had magnitude greater than
1/2, every outward radial support would use both far faces. Its
norm would exceed sqrt(2), contrary to (3). Therefore the center is
(a,b), where a>1/2 and |b|<=1/2. Its actual nearest point is

    p_*=(a-1/2,0).

Every incoming pair force is consequently horizontal. Put x_0=a+1/2.
Every outgoing radial support has first coordinate x_0>1. Its second
coordinate is either zero, or a top/bottom vertex height b+1/2 or
b-1/2, with the same sign as that height.

By (3), each nonzero outgoing height y satisfies

    |y|^2<=d^2-x_0^2<d^2-1<(61/60)^2-1=(11/60)^2.        (5)

The strict final inequality follows from d<61/60. If both positive
and negative outgoing heights occurred, they would be the top and
bottom side endpoints, differing by exactly one. Equation (5) would
instead bound their difference by less than 22/60, impossible.

There can therefore be at most one nonzero sign among the outgoing
heights. Any such height gives its radial force the same strict
vertical sign. All incoming forces and all zero-height outgoing
forces are horizontal, so the vertical equilibrium of U excludes
that sign too. Thus every outgoing application is exactly

    p_out=(x_0,0),

with direction e_x. All original forces are collinear, and the
two actual applications differ by precisely one. Equations (3)--(4)
give rho=x_0-1 in (0,d-1], proving the complete geometry (1).

No individual endpoint mean is replaced. In particular b=+/-1/2,
where an actual application is a side endpoint, remains in (1).

## 4. There is only one physical outward neighbor

Every outward neighbor lies in x>=x_0>1. Its center c has
c_x>=x_0+1/2>3/2 and |c|<M=91/60. Two such centers would satisfy

    |c_1-c_2|^2
      <(M-3/2)^2+4(M^2-9/4)
       =1/3600+724/3600=29/144<1.                        (6)

This uses the full rectangular cap containing all such centers and
requires no orientation or circle-load premise on the neighbors.
But distinct interior-disjoint unit squares have center distance
at least one, by their disjoint open radius-1/2 incircles. Thus U
has only one outward neighbor.

For every incoming neighbor V, the point rho e_x is an outward
radial support in direction e_x. Since 0<rho<1, the full unit
inward segment of V contains zero. Hence every incoming neighbor
is an actual origin-containing square, whether or not it belongs
to a cyclic block.

## 5. Minimal support leaves exactly one incoming neighbor

Suppose now the normalized stress has minimal positive scalar support
among those with the same selected physical normals and pose, as in
GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md, Section 5.

Deleting U separates its incident edges into distinct branches because
they are all bridges. Each branch has positive circle mass a_j and
contributes a resultant f_j at U. By Section 3 every f_j is horizontal.
The vectors (f_j,a_j) therefore lie in a two-dimensional linear
subspace. If at least three branches existed, the exact nonnegative
branch reweighting of the articulation source would preserve force,
torque and normalization while removing a positive branch. This
contradicts minimal support.

There are at least two incident branches, by Section 2, so there
are exactly two. Section 4 already identifies one outward neighbor;
the other is the unique incoming neighbor. No new normal or mean
is selected, and the original square U has exact positive degree
two only after this full-support argument.

## 6. Direct consequences and limits

At R^2<=17/4, every truly unloaded all-bridge body of positive pair
degree contains zero,
even without the minimal-support selection. This follows directly
from Sections 1--2 and the contradiction 1<t<=d<=1.

Under minimal support, every such body avoiding zero is one single
side transmitter from an origin-containing body to its sole outward
neighbor. Two off-origin unloaded all-bridge bodies cannot be adjacent:
one would have to be an incoming neighbor of the other, whereas every
incoming neighbor contains zero.

If the outward neighbor happens to be a genuine radial leaf, its
application radius greater than one forces it to be S, and x_0=d.
Then rho=d-1, recovering the older tree-side law. Without that actual
leaf premise, x_0 is retained over the entire interval (1,d]; no
terminal geometry is assigned to the outward cyclic neighbor.

All operations keep the nine physical squares, the original radius
and every physical contact. The lemma makes no claim about a body
with a nonbridge incident edge or a nonzero circle load. It closes
no larger coarse cell by itself and is not a proof of sharpness.

No Lean compilation, CI, numerical pose search or coefficient packet
is used.
