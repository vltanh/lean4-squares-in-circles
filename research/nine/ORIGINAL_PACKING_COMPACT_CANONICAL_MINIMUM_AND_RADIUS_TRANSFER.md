# Original finite packings admit compact canonical minima

Date: October 28, 2026 UTC. Author: root.
Comparison head: bbc1e87f65168bba704d2b21a91faf0e313945c2.

**Status: complete hand proof proposed for separate independent review.**
This supplies the exact original-predicate compactness and canonical-entry
interface. It is uniform in every finite number of independently rotated
unit squares. It proves no missing sharp geometric exclusion, selects no
contact normal, and does not classify all equality packings.

The basic attainment argument is already present in Section 1 of
SPARSE_MINIMIZER_STRESS.md. The present source makes its link to the actual
`SquaresInCircles.Packing` definition explicit, gives a proof of closed
nonoverlap without choosing any separating axes, includes the secondary
minimum needed by later canonical-motion arguments, and separates lower-bound
transfer from original-equality classification. No stress sparsity bound is
needed for these statements.

## 1. Exact original objects and unchanged predicate

The current `SquaresInCircles/Geometry.lean` defines `Point` as a pair of real
coordinates. Its `UnitSquare` has center c=(c_x,c_y), real frame coordinates
C,S, and the equation C^2+S^2=1. Put

    u=(C,S), v=(-S,C), J(x,y)=(-y,x).

These are an orthonormal frame: u.u=v.v=1, u.v=0 and v=Ju. The actual
functions `localX` and `localY` are (p-c).u and (p-c).v. Therefore the
original definitions have exactly the sets

    closedSquare = {c+x*u+y*v : -1/2<=x,y<=1/2},
    openSquare   = {c+x*u+y*v : -1/2<x,y<1/2}.

This equivalence follows by expanding the two scalar products and the
identity

    ((p-c).u)*u+((p-c).v)*v=p-c.

There is no shared-frame assumption. The equation C^2+S^2=1 is imposed
independently for every original label i in Fin n. All represented frames
are permitted; the harmless multiple representations of the same geometric
square are retained.

The current `Packing S o R` is exactly the conjunction

1. R>=0;
2. every point of every actual closed square is in the closed disk with
   center o and radius R;
3. for i!=j, no point belongs to both actual open squares.

In particular disjointness concerns open interiors. Shared sides, single
contact points, multiple junctions and arbitrary boundary tangencies are
allowed. The squared `inDisk` formula is used together with the separate
nonnegative-radius conjunct. No inference from R^2 to R is made without
that conjunct.

### 1.1 Translation removes the unbounded disk-center variable exactly

Given any original Packing S o R, replace each center c_i by c_i-o and
leave its frame coordinates unchanged. Call the resulting square S'_i.
For every actual point p,

    localX(S'_i,p-o)=localX(S_i,p),
    localY(S'_i,p-o)=localY(S_i,p),
    normSq((p-o)-0)=normSq(p-o).

Thus closed membership, open membership and disk containment are equivalent
under the same translation. All labels and all n actual bodies remain, and
Packing S' 0 R holds. Translation back gives the converse. A global radius
minimum over arbitrary disk centers is therefore equivalent to a minimum in
the origin-centered coordinate family. This translation neither rotates an
individual frame nor changes any physical relation between units.

## 2. The finite origin-centered sublevel is compact

Fix n>=0 and one actual feasible origin-centered packing at finite radius
R_0>=0. Use the finite real coordinate space with one radius R and, for each
label, its two center coordinates and two frame coordinates. Consider

    K_0=[0,R_0] x product_i (closed disk D_(R_0) x S^1).

Here S^1={(C,S):C^2+S^2=1}; no angular coordinate with a missing wrap endpoint
is introduced. Every factor is closed and bounded in a finite-dimensional
Euclidean space, so K_0 is compact. For n=0 the product over squares is the
one-point empty product.

Any feasible packing at radius R<=R_0 lies in K_0. Indeed each actual center
is in its own closed square, so containment implies |c_i|<=R<=R_0. Its
frame lies on S^1 by the original structure equation.

We now prove that the feasible subset K of K_0 is closed. All coordinates
and all statements here are about the original fixed labels and square
sets.

### 2.1 Closed containment is exactly four continuous inequalities per unit

The four actual vertices are

    p_(i,epsilon,eta)=c_i+(epsilon*u_i+eta*v_i)/2,
    epsilon,eta in {-1,1}.

They depend continuously on the finite coordinates. Every point with own
coordinates x,y in [-1/2,1/2] is their convex combination with weights

    w_(epsilon,eta)=(1+2*epsilon*x)*(1+2*eta*y)/4.

The weights are nonnegative, sum to one, and have weighted own coordinates
x,y. The closed Euclidean disk is convex. Consequently the whole original
closed square is contained if and only if

    |p_(i,epsilon,eta)|^2<=R^2

for all four actual vertices. These finitely many inequalities are closed
conditions. Conversely, no pointwise containment property was lost in
replacing the universal square-point quantifier by these exact vertices.

### 2.2 Original open-interior nonoverlap is closed under coordinate limits

Take any sequence of origin-centered feasible coordinate tuples in K_0
converging to a tuple in K_0. Suppose, for a contradiction, that the limit
has a point p in both open squares at two distinct original labels i,j.
Then all four real quantities

    |localX(S_i,p)|, |localY(S_i,p)|,
    |localX(S_j,p)|, |localY(S_j,p)|

are strictly less than 1/2. There is a positive common margin between their
maximum and 1/2. Each quantity is a continuous function of the center and
frame coordinates at the fixed point p. For every sufficiently late tuple
all four inequalities are therefore still strict at that same point p.
That contradicts nonoverlap in the original sequence.

The limit has no common open-interior point for any distinct pair. There are
finitely many labels, and the argument applies to each pair; no contact
classification, supporting direction or active-set selection is required.
Since this is a finite-dimensional metric space, sequential closedness is
closedness. Together with Section 2.1 and R in [0,R_0], this proves K closed
in compact K_0. Thus K is compact and nonempty.

In particular limits may gain contacts, common side segments or physical
circle corners without leaving K. They may not gain an intersection of
open square interiors. Distinct labels cannot become the same geometric
square, since that would give a common nonempty open square. All n bodies
survive the compactness argument.

## 3. Global radius attainment and finite canonical refinement

**Theorem 1 (original radius attainment).** Given any original finite
packing, there is an origin-centered packing of the same n units at a radius
R_* such that R_*<=R for every original packing of n units at any disk
center. In particular R_*<=R_0 for the supplied witness.

The continuous radius coordinate attains a minimum on K. Reconstruct the
original `UnitSquare` objects from those center/frame coordinates, retaining
each equation C_i^2+S_i^2=1. Sections 1--2 give the original Packing
predicate at that minimum, without an added orientation or contact premise.

To see that the minimum is global, let any original packing have radius R.
If R>R_0, then R>=R_* already. If R<=R_0, translate its disk center to zero
by Section 1.1. Its coordinates belong to K, so minimality gives R>=R_*.
This exhausts all nonnegative original packing radii, not just a
neighborhood of the supplied witness.

Because all radii are nonnegative, minimizing R is equivalent to minimizing
q=R^2. Thus the attained q_*=R_*^2 is also the global least squared radius.
The nonempty fiber

    K_*={z in K:R(z)=R_*}

is compact, as the preimage of a closed singleton under a continuous map.

**Theorem 2 (finite continuous canonical refinement).** On the actual
minimum-radius family, any prescribed finite ordered list of continuous
real functionals admits a lexicographically minimizing packing. All original
minimum-radius packings, including every contact and frame limit, are in the
family before this refinement is imposed.

Proof: minimize the first functional on compact nonempty K_*. Its minimizer
set is again nonempty and compact. Minimize the second on that set and
continue through the prescribed finite list. Each stage is a closed fiber
of a continuous function inside the preceding compact set. The finite last
set is nonempty. The resulting tuple has the stated lexicographic property.
No claim about an infinite list, discontinuous selector or uniqueness is
made.

For the canonical functional used by the present physical reductions take

    Phi=sum_i |c_i|^2,

where c_i are measured from the unchanged containing-circle origin. Phi is
continuous, so some original packing first minimizes R and then Phi among
all radius minimizers. Since every original radius minimizer can be
translated into K_*, this second minimum is global on that family, not
restricted to an assumed contact graph or prescribed frame pattern.

Choose this actual packing before any contact normals, stress support,
uncrossing or thinning choices. Compactness supplies the packing and its
minimum property only. It does not assert that future normal choices exist
simultaneously or survive later operations; those are separate mathematical
obligations.

### 3.1 Exact scope of a subsequent canonical-motion contradiction

At the fixed radius/Phi minimizer, a proposed change to any subset of its
actual units is contradictory if it preserves the original Packing
predicate for all n units at radius R_* and strictly decreases the total
Phi. All unchanged units are still included in that feasibility test.
No assumption about maintaining the chosen stress support is needed for
this particular minimization contradiction: the competing point is any
original feasible packing. Conversely, an argument checking only a selected
stressed subcomponent does not establish such a competing original packing.

## 4. Radius bounds and closed endpoint cases

The statements above include n=0, where R_*=0. For n>=1, averaging the
squared norms of the four vertices of one contained square gives

    R^2 >= |c_i|^2+1/2 >=1/2.

Thus R>=1/sqrt(2)>0. This follows in the original coordinates after
translation and is valid at every contact or frame endpoint. For n>=2 the
inequality is strict for every feasible packing: if R^2=1/2, the average
identity forces all centers to be zero. Every square then contains the open
disk of radius 1/2 centered at zero, contradicting the original disjoint-open-
interior condition for two labels.

No one-body or lower-n bound is being applied to a smaller artificial core.
For the nine-body problem any stronger lower window, such as the existing
same-nine R>2 theorem, must be invoked on the same actual nine units.

## 5. Conditional sharp-radius transfer from a canonical minimum

The following elementary implications isolate exactly what remains for the
geometric proof. Let Q>=0 be a proposed squared threshold, in particular
Q=1105/256 in the present project.

**Corollary 3 (contradiction entry).** If an original packing of n units has
R^2<Q, then there is an original origin-centered radius/Phi minimizer of
those n units with R_*^2<Q.

Apply Theorems 1--2 using the given packing as the feasible bound. They give
0<=R_*<=R and therefore R_*^2<=R^2<Q. All original units remain and every
contact/frame endpoint is allowed. An independently known sharp upper-bound
construction is unnecessary for this contradiction entry.

**Corollary 4 (lower-bound transfer).** If no original radius/Phi-minimizing
packing of n units can have squared radius below Q, then every original
packing of n units satisfies R^2>=Q.

A counterexample would give exactly the contradictory canonical minimizer
in Corollary 3. Equivalently, once a global minimum is known to satisfy
R_*^2>=Q, Theorem 1 and nonnegativity give R^2>=R_*^2>=Q for every original
packing, at any original disk center and with independent original frames.

**Corollary 5 (matching an exact upper witness).** If the universal lower
bound has been proved and an actual original packing at radius sqrt(Q)
exists, then the least nonnegative radius is sqrt(Q). More generally an
upper witness with radius squared at most Q combines with the lower bound
to give exactly Q. These are conditional implications, not a proof of the
missing universal lower bound or an unverified construction.

## 6. Original equality packings are not replaced by Phi minimizers

Once the universal lower bound R^2>=Q is established, every particular
original packing with R^2=Q is itself a global radius minimizer. Indeed its
own existence gives R_*^2<=Q, and the universal lower bound gives the reverse
inequality. Thus a radius-minimum necessary condition can then be applied to
that original equality packing without moving any physical unit.

Such an equality packing need not minimize Phi among the radius minimizers.
Replacing it by a Phi minimizer is sufficient for a subcritical
contradiction, but it cannot classify the original equality packing. A
reduction using a strict Phi-decreasing motion proves an exclusion at the
chosen canonical minimizer; exporting that exclusion to every equality
packing requires a separate argument. No such export is asserted here.

Similarly, equality of radii does not choose unique frames, labels, stress
weights, contact owners or a unique model. Continuous freedom of unstressed
units and additional physical zero-weight contacts remain possible. These
statements preserve the existing open/closed definition of congruence;
they do not substitute a narrower equality convention.

## 7. Source identities, gate scope and verification boundary

The exact current original definition was read directly:

| Source | Bytes | SHA256 | Git blob | Consumed scope |
| --- | ---: | --- | --- | --- |
| `SquaresInCircles/Geometry.lean` | 20319 | `64bb2e778f86274f9c256aa875d6cf0737006dcf7d70694e7fe5cf1124c72a94` | `14e10cb5be282f490ad46ac2cac63185de4ff566` | Actual Point, normSq, UnitSquare, localX/localY, closedSquare/openSquare, inDisk and Packing definitions; no theorem implementation is changed |
| `research/nine/SPARSE_MINIMIZER_STRESS.md` | 16597 | `b182276dace03bf64d9903145e8861022712b05f7ff7317ad62f30f97850e9ac` | `5ee6d10f5e7a2770ae1916f0f65cf7ca73b4e868` | Full source read; Section 1 is provenance only, with the complete attainment proof supplied above; no later stress conclusion imported |

The complete SPARSE_MINIMIZER_STRESS.md was also read. Its Section 1 is
provenance for the already available attainment argument, not an external
mathematical premise of the full proof above. Its later 2n+1 translational
stress sparsity bound is not imported into a torque-stationary physical
certificate. PHYSICAL_CONTACT_STRESS.md and the simultaneous normal/planarity
sources retain their separate full hypotheses and audit obligations.

At its exact original scope this source supplies G4.2.a: original nine-square
Packing gives compact attainment without extra orientation or contact
hypotheses. It additionally supplies the optional Phi refinement before
selection and the conditional G4.2.f transfer. It does not close G4.2.c,
G4.2.d, G4.2.e, all of G4.2, the equality gates, or the full G6.1 audit. No
authoritative gate is edited before separate full review and root adoption.

Every argument is over the full finite-dimensional continuous domain. No
computational pose certificate, finite case exclusion, numerical optimizer,
normal reselection, mean replacement or deleted physical body is used. The
proof uses only elementary finite-dimensional compactness, continuity,
convexity and the extreme-value theorem. No Lean compilation, CI/workflow
dispatch, remote mutation or merge is performed.
