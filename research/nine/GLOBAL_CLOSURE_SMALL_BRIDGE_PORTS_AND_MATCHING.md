# Small bridge applications have degree one; unloaded bridge bodies form a matching

Date: October 26, 2026.
**Status: accepted complete theorem after full-source root review in REVIEW_BRIDGE_MATCHING_TRIANGLE_FORESTS_ROOT_2026_10_26.md and separate review in REVIEW_SMALL_BRIDGE_PORTS_MATCHING_ROOTED_BLOCKS_2026_10_26.md.**
No shared ledger or original gate has been changed by this source.

Use the compatible physical stress at the unchanged common pose in
79/40<=R<=sqrt(1105)/16. Choose minimal positive original scalar support
as in GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md. Every surviving
normal, application and aggregate mean is retained. Put

    d=sqrt(R^2-1/4)-1<61/60,
    epsilon=max(d-1,0)<1/60.

**Small-port theorem.** A truly unloaded body incident only to bridges
has at most one incident bridge whose actual application p satisfies
|p|<=1/4. This includes every zero application and every original mean
endpoint.

**Matching corollary.** The positive graph induced by all truly unloaded
all-bridge bodies is a matching together with isolated vertices. Thus
each connected collection of these bodies has at most two members,
even when arbitrary cyclic blocks occur elsewhere in the component.

Neither statement deletes an additional positive force at a cyclic
body. Their premises refer to the true complete degree and zero circle
load of each body to which they are applied.

## 1. Exact degree and radial preliminaries

An unstressed body of degree zero has no incident application, so the
small-port theorem is immediate for it and it is isolated in the
matching corollary. All nontrivial degree statements below concern
bodies of a positive component, with positive pair degree.

An unloaded all-bridge body H cannot have degree one. Its incident
bridges are distinct branches of G minus H. The minimal-support
articulation theorem bounds their number by three. Thus H has degree
two or three.

At degree three its three branch resultants cannot be collinear.
Indeed each branch has positive circle mass a_j, and the three
vectors (f_j,a_j) would lie in a two-dimensional linear subspace.
The exact branch scaling in the articulation source would then remove
a positive branch while preserving force, moment and normalization.
This contradicts minimal support. Consequently every pair of its
three positive force directions is nonparallel: if one pair were
parallel, the full three-force equilibrium would make the third
parallel as well.

The accepted off-origin theorem
GLOBAL_CLOSURE_OFF_ORIGIN_BRIDGE_TRANSMITTERS.md makes every truly
unloaded all-bridge body avoiding zero have degree two in this same
selection. Therefore a degree-three H contains zero.

All actual bridge force lines pass through zero. At a body containing
zero, an application p with outward unit normal n consequently has

    p=rho n,      rho=n.p=h_H(n)>=0.                      (1)

The actual neighboring unit lies beyond that support, so the sharp
contained-neighbor half-plane theorem gives

    rho<=d.                                               (2)

This is the unchanged support bound of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1.

## 2. The complete degree-two alternative

The two actual force directions of an unloaded degree-two H are
opposite. Their applications lie on opposite supporting faces.
The projected width of a unit square is at least one, so their
Euclidean distance is at least one. Two applications of norm at
most 1/4 would instead have distance at most 1/2. This is impossible.

This argument does not require either application to be a midpoint,
nor a specific transmitter width or orientation.

## 3. Two small radial applications force a near-corner frame

It remains to consider degree three. Suppose two actual applications
p_1,p_2 have norms at most 1/4. Their force directions n_1,n_2 are
nonparallel by Section 1.

If p_1=p_2, equation (1) and nonparallelism force p_1=p_2=0.
Zero cannot be in a side interior of H, whose normal cone is a
single ray. Thus it is a vertex. Choose H's own axes so that

    H=[-1,0] times [-1,0].                                (3)

Both normals belong to its closed northeast normal cone at zero.

Now suppose p_1!=p_2. They cannot both be vertices, because distinct
unit-square vertices have distance at least one whereas
|p_1-p_2|<=1/2. Relabel so p_1 is in a relative side interior.
Choose that outward direction as e_x. Equation (1) gives

    p_1=(x,0),       0<=x<=1/4,
    H=[x-1,x] times [b,b+1],       b<=0<=b+1.              (4)

No point of the opposite left face can be p_2: its first-coordinate
magnitude is at least 3/4. A right-face interior would have normal
n_2=e_x, contrary to nonparallelism. Therefore p_2 lies on a
horizontal face or at one of its right endpoints, and that face
has distance at most 1/4 from zero. Reflect the vertical axis if
needed to put it above zero. In these actual own axes,

    H=[x-1,x] times [y-1,y],       0<=x,y<=1/4.             (5)

The first normal is e_x. The second has nonnegative first component
and strictly positive second component: it is the top normal or a
normal at the upper-right vertex that is not parallel to e_x.

The coincident case (3) is also (5), with x=y=0. There both normals
lie in the closed northeast quadrant and are nonparallel. In either
case their actual positive weighted sum has both components strictly
positive.

## 4. The third actual bridge is too far from the origin

Write the unchanged equilibrium at H as

    mu_1 n_1+mu_2 n_2+mu_3 n_3=0,       mu_i>0.

Section 3 makes both components of n_3 strictly negative. Its unique
support point on H is therefore the southwest vertex

    p_3=(x-1,y-1).

Because this third edge is a bridge, its line is radial too.
Equation (1) forces n_3=p_3/|p_3| and hence its support height is

    |p_3|>=3sqrt(2)/4>61/60>d.                            (6)

The exact squared reserve in the middle comparison is

    9/8-(61/60)^2=329/3600>0.

But its actual neighbor is a unit contained in the same disk,
contradicting (2). This exhausts the degree-three alternative and
proves the small-port theorem.

No norm, force magnitude, port, side mean or physical frame has been
reset during this proof. The three-force equation is the genuine
equation of the chosen degree-three body.

## 5. Every edge between unloaded all-bridge bodies is small

Let U,V both be truly unloaded and all-bridge, with a positive edge.
If both contain zero, their separating line passes through zero.
Its radial application must consequently be exactly zero.

If one, say U, avoids zero, the off-origin transmitter theorem gives
its unique incoming application rho e, with

    0<rho<=d-1<=epsilon,

and an origin-containing incoming neighbor. Its outgoing application
is (rho+1)e. The outward neighbor cannot be V: it would lie wholly
in e.x>=rho+1>1, whereas every unloaded all-bridge body meets the
central disk D_delta with delta<1/12. Thus V is precisely the
incoming neighbor, and the actual UV application has norm at most
epsilon.

The two cases exhaust the edge: in particular two such off-origin
bodies cannot be adjacent. Hence every positive edge induced by
unloaded all-bridge bodies has

    |p|<=epsilon<1/60<1/4.                               (7)

The small-port theorem bounds every vertex degree in this induced
graph by one. A simple graph of maximum degree one is a matching
plus isolated vertices, proving the corollary.

## 6. Additional direct consequences and exact scope

Every unloaded all-bridge body has at most one bridge to any body
that contains zero, when it itself contains zero: every such contact
is an actual zero application. At degree three it also cannot have
two off-origin transmitter neighbors whose inner applications lie
at radii at most epsilon. These are immediate uses of the same
small-port bound; no branch force is omitted.

In a forest attached to cyclic blocks, every outside nonleaf is truly
unloaded at the accepted common selected-canonical-minimizer scope,
by the exact loaded-articulation split and the complete small-core
assembly. Thus its internal unloaded bridge bodies occur only singly
or in adjacent pairs. A later graph classification must still keep
the genuine leaves and every interface at a cyclic body.

The theorem is about the proved minimal-support choice on the same
physical pose. It does not assert these bounds for every earlier
nonminimal stress representation, and it excludes no biconnected
component on its own. It is not a sharp-radius or equality theorem.

No Lean compilation, CI, numerical search or coefficient certificate
is used.
