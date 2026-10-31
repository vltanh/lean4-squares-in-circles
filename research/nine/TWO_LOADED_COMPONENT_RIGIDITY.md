# n=9 CY.TWO: every two-loaded positive component is an aligned four-layer network

**Status:** new symbolic hand argument for a whole class of physical stress
components; independent mathematical audit and Lean verification pending.
It does not prove the unrestricted nine-square lower bound or the P/Y
completion capacities. The proof does not assume a tree, a simple cycle,
planarity, a common square frame, or common coordinate separators.

**Read base:** PR #11 `a89802cd834aef3a96d9622bd4829a2c49df17fd`.
The physical shared-point force/torque equations are the input from
PHYSICAL_CONTACT_STRESS.md. The explicit radius window is

    79/40 <= R <= sqrt(1105)/16.

Its lower endpoint is a declared prior-theorem dependency, not proved here.
The result strengthens the two-loaded *simple-cycle* theorem in
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md to arbitrary connected positive
body-pair graphs with exactly two loaded bodies.

## 1. Physical stress and virtual power

Select a nontrivial connected positive physical stress component. A body i
has center c_i and square side axes u_i,v_i. Its nonnegative circle weights
lambda_ik occur at actual corners z_ik on |z|=R. Put

    m_i = sum_k lambda_ik z_ik.

A loaded body has positive total circle weight. All other bodies are
unloaded. Every positive edge i -> j has weight mu>0, unit normal n pointing
from i to j, and the SAME genuine common application point p in both
squares. The two squares are supported there on opposite sides:

    n.(x-p) <= 0 on S_i,    n.(x-p) >= 0 on S_j.

For any assigned center velocities a_i and angular velocities omega_i, the
physical center and angular balances give the exact identity

    2 sum_{i,k} lambda_ik z_ik . [a_i + omega_i J(z_ik-c_i)]
      + sum_{i->j} mu_ij n_ij .
          [a_i + omega_i J(p_ij-c_i)
           -a_j - omega_j J(p_ij-c_j)] = 0.                 (1)

This is algebraic virtual power. No finite motion preserving containment
is asserted or needed. It follows by multiplying each body's force and
torque equations by a_i and omega_i and summing, using the actual shared
application point on each edge.

Assume now exactly two bodies are loaded. Summing force balances gives
m_A+m_B=0. Both vectors are nonzero: a circle-loaded square in this window
lies in a strict cone about its circle corners, as established in
ACUTE_LOADED_CONTACT_GRAPH.md, Theorem A.1. Choose coordinates so

    m_A = k e_x,   m_B = -k e_x,   k>0.                    (2)

## 2. An all-angle virtual opening inequality for one square

Let P(x,y)=(0,y), the projection onto the vertical axis. For each square,
choose an oriented side basis

    u=(a,b),  v=(-b,a),  a^2+b^2=1,

and set

    omega = -a b (a^2-b^2),
    V(p) = P c + omega J(p-c),
    B = P - omega J.                                     (3)

The value of omega is unchanged by replacing the square's basis with a
quarter-turn-equivalent one. Thus (3) depends only on the square frame.

**Lemma V.1.** At every outward support point r=p-c of the centered square,
with any nonzero outward normal n,

    n.B r >= 0.                                         (4)

If the square is neither axis-aligned nor at 45 degrees to the selected
frame, the inequality is STRICT for every nonzero support normal.

*Proof.* In the side basis u,v, the matrix B is exactly

    [ b^2       2 a b^3 ]
    [ 2 a^3 b   a^2    ].                               (5)

On a side with outward normal +u, r_u=1/2 and |r_v|<=1/2. Hence

    u.B r >= (b^2 - |2ab^3|)/2
           = b^2 (1-2|ab|)/2 >= 0.

The same estimate holds on the opposite side with outward normal -u.
The two v-side estimates are

    a^2 (1-2|ab|)/2 >= 0.

Every vertex support normal is a nonnegative combination of the two
outward side normals at that vertex, so these side estimates imply (4)
for every support direction. If ab!=0 and 2|ab|<1, both bounds are strict;
those are precisely the orientations other than multiples of pi/4. QED.

For a positive contact i->j with point p, put r_i=p-c_i and r_j=p-c_j.
Using c_i-c_j=r_j-r_i, its virtual relative velocity satisfies

    n.[V_i(p)-V_j(p)] = -n.B_i r_i + n.B_j r_j <= 0.     (6)

Indeed n is an outward normal of i, whereas -n is an outward normal of j.
If either incident square has a nonexceptional angle, (6) is strict.
The signs in (6) agree with the positive-contact terms of (1).

## 3. Circle virtual power is nonpositive when its load vector is horizontal

**Lemma V.2.** If a loaded square has a nonzero horizontal circle-load
vector m, then for the field (3),

    2 sum_k lambda_k z_k.V(z_k) = 2 omega m_x c_y <= 0.  (7)

For a non-axis/non-diagonal orientation the inequality is strict.

*Proof.* The left side is

    2 m.Pc - 2 omega m.Jc,

because z.Jz=0. Since m_y=0, this is the displayed 2 omega m_x c_y.

A global half-turn reverses m_x and c_y and leaves omega unchanged.
Reflection in the x axis reverses c_y and omega together. Square
quarter-turn equivalence leaves omega unchanged. These symmetries let us
assume m_x>0 and 1>=a>=b>=0 without changing the sign of (7).
At b=0 or a=b, omega=0 and (7) is zero. It remains to prove c_y>0 when
0<b<a, since then omega<0.

Write the center in its side frame as c=C u+D v. The load vector's side
coordinates are (m_x a,-m_x b), with first coordinate positive and second
negative. If C<0, every farthest circle corner has first side coordinate
C-1/2<0, contradicting the first load coordinate. Likewise D>0 is
impossible. Thus C>=0 and D<=0.

If C=0 and D<0, put T=sqrt(R^2-1/4)>1/2. Every circle corner has second
side coordinate -T, whereas the weighted first side coordinate has
absolute value at most 1/2 times total circle weight. Consequently the
ratio of first to absolute second load coordinates is <=1/(2T)<1,
contradicting a/b>1. C=D=0 would require R^2=1/2 and is outside the window.
Therefore C>0.

If D<0, the farthest corner is unique, and its direction is the horizontal
load direction. It is z=(R,0), so

    C=R a-1/2,  D=-R b+1/2,
    c_y=b C+a D=(a-b)/2>0.

If D=0, then C=T-1/2>0 and c_y=b(T-1/2)>0. These cases include a
zero-weight adjacent circle corner; no genericity assumption is made.
This proves (7), including strictness. QED.

## 4. Every body has an axial or diagonal frame

Apply (1) with a_i=P c_i and the angular velocities in (3). Every contact
term is nonpositive by V.1, and the only two circle-loaded bodies have
nonpositive circle terms by V.2. Their total is exactly zero. Thus every
positive contact term and each circle term is zero.

Every body of the nontrivial connected positive component has an incident
positive edge. If any square had an angle other than a multiple of pi/4,
that edge's contribution would be strict negative. Hence:

> Every square in a positive two-loaded component is either axis-aligned
> or diagonal at 45 degrees in the frame of its circle-load vectors.

This is derived from physical force and torque, not assumed from the
packing diagram. The virtual field was used only in the exact power
identity, not as an unproved finite deformation.

## 5. Every positive force is horizontal

At an axis-aligned square omega=0 and B=P. At a support point r, if n_y!=0,
then r_y=sign(n_y)/2, so n.B r=|n_y|/2>0. Equality in V.1 therefore forces
**every positive edge incident to an axial body to have n_y=0**.

For a diagonal square omega=0 also. In the centered diamond
|r_x|+|r_y|<=1/sqrt(2), equality n_y r_y=0 at a support point forces that
point to be one of the two horizontal vertices

    r=(+/-1/sqrt(2),0).

If n_y=0 these are the only support points. If n_y!=0, all other support
points have n_y r_y>0; the same conclusion follows.

Consider the subgraph induced by diagonal bodies and positive edges
between them. A shared contact must join a right vertex to a left vertex;
joining two identical-side vertices would give identical centers and
physical overlap. Adjacent diagonal centers thus have equal y coordinate
and horizontal gap sqrt(2). There is at most one diagonal neighbor on
each side, because two such neighbors would be identical squares.
Therefore this finite induced subgraph is a disjoint union of horizontal
paths and isolated vertices; it has no cycle.

At an endpoint of any such path, all other incident forces are horizontal,
since they join axial bodies, and its circle load is horizontal or zero.
Vertical force balance therefore forces its sole diagonal-path edge to
be horizontal. Continue along the path: vertical balance propagates this
conclusion to every edge. Isolated diagonal bodies have only axial
neighbors, already treated. Thus **all positive body-pair forces in the
whole component are horizontal**.

This step does not assume that a diagonal body's total degree is two.
It may meet several axial neighbors at a vertex; their forces are already
horizontal, so the same endpoint propagation is valid.

## 6. Positive horizontal flow and exact radius quantization

Loaded bodies receive only horizontal contact forces. Their circle loads
are respectively positive and negative horizontal. From their zero-power
frames and actual circle geometry they are radial S or D squares:

    S: center (+/-(T-1/2),0), inward support plane x=+/-(T-1),
       T=sqrt(R^2-1/4);
    D: center (+/-(R-1/sqrt(2)),0), inward vertex x=+/-(R-sqrt(2)).

For axial bodies this follows because a horizontal circle average requires
center height zero and equal weights on its two outer circle corners.
For diagonal bodies both side-center coordinates are nonzero; the only
positive circle corner is (+/-R,0), giving the D form. After the next outward-neighbor exclusion, Lemma N.4 of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md also gives the same formulas;
parallel forces alone must not be confused with parallel same-sign forces.

The positive loaded body has no neighbor farther to the right. Such a
neighbor would start at the loaded body's far x support, T or R, and
extend by at least one, contradicting T+1>R. The negative loaded body
similarly has no neighbor farther left.

Orient every positive edge from smaller to larger center x. Along an
edge the center x increases by the sum of positive coordinate halfwidths,
so this graph is acyclic as a directed graph (its undirected graph can
have cycles). At each unloaded node horizontal force balance requires
both an incoming and an outgoing edge. Consequently every body lies on
a directed path from the negative loaded body to the positive loaded body:
follow predecessors and successors in the finite directed acyclic graph.

Set

    A=T-1,  B=R-sqrt(2).

The horizontal distance between the loaded bodies' inward support planes
is one of 2A, A+B, 2B. Along ANY directed path it equals the sum of the
intermediate squares' full horizontal widths. Each width is exactly 1
for an axial body or sqrt(2) for a diagonal body.

In the declared radius window the exact comparisons are

    9/10<A<51/50,  11/20<B<7/10,
    1<2B<sqrt(2),
    sqrt(2)<A+B<2,
    sqrt(2)<2A<51/25<1+sqrt(2).

A positive sum of widths 1 and sqrt(2) below 51/25 can be only 1,
sqrt(2), or 2. (A path with no interior body would require zero gap,
contrary to A,B>0.) Comparing the three endpoint gaps with these sums
leaves only

    2A=2,  A=1,  R^2=17/4.                               (8)

Both loaded bodies are S, and every directed path has exactly TWO axial
interior bodies. Every component body lies on a path, so no diagonal
body remains anywhere in the positive component.

## 7. The complete two-loaded structural theorem

**Theorem CY.TWO.** Under the physical stress equations and the explicit
radius window, EVERY connected positive component with exactly two
circle-loaded square bodies has R^2=17/4. In one common frame:

- its two loaded bodies are the aligned squares centered at
  (-3/2,0) and (3/2,0);
- every other component square is aligned, with center x=-1/2 or x=1/2;
- every positive edge joins consecutive layers in

      left loaded -> left column -> right column -> right loaded;

- every component body lies on a three-edge directed path between
  the loaded ends;
- the undirected positive graph is bipartite and contains NO odd cycle;
- each intermediate column has at most three bodies, hence the component
  uses at most eight bodies.

*Remaining claims in the conclusion.* A path with two width-one interior
squares gives their centers exactly -1/2 and 1/2. No same-layer edge is
possible, since all normals are horizontal and widths positive. A skip
edge would supply a directed loaded-to-loaded path with too few internal
squares, contradicting (8). Every intermediate body directly contacts its
adjacent loaded endpoint, whose side segment has y range [-1/2,1/2].
Thus its center has |y|<=1. Within one column, distinct aligned unit
squares must have vertical center gaps >=1, giving at most three. The
four-layer graph is bipartite by alternating layer parity. QED.

**Important limitation:** the component's coordinate separability does not
imply a common separating frame for all nine physical squares. The other
squares and zero-weight contacts remain in every completion problem.
An eight-body component or a smaller component can be completed by fewer
than nine squares, and no blanket physical impossibility is claimed here.
In particular, the open family P is retained. Two-column networks may
include cycles and still require a genuine completion-capacity argument.

## 7A. A finite four-topology cover for the selected strict-contact certificate

The physical certificate used in the repository chooses a strictly exposing
common normal at every point-only vertex/vertex contact. Under that
additional, already available selection rule, CY.TWO sharpens further:

> Each intermediate column contains at most TWO bodies; the whole
> two-loaded component has four, five or six bodies and exactly one
> of the four graph types listed below.

*Proof.* All frames and positive normals are axial by CY.TWO. A point-only
contact between aligned squares is a vertex/vertex contact, whose strictly
exposing normals are not axial. Such a contact therefore cannot carry a
positive edge in this certificate. Every positive body-pair edge has a
positive-length shared side segment.

Every intermediate body directly touches its neighboring loaded endpoint,
so its center height satisfies **strictly** -1<y<1. Three aligned unit
squares in one column would need center-height span at least two, which
cannot fit the open interval (-1,1). Thus column sizes p,q belong to {1,2}.

All p left bodies are joined to the left load, all q right bodies to the
right load, and every intermediate vertex has at least one across-column
edge. An across-column edge means positive-length overlap of their open
vertical projection intervals. For two bodies in each column, label them
bottom-to-top L1,L2 and R1,R2. It is impossible to have both cross edges
L1--R2 and L2--R1: their strict overlaps and the within-column disjointness
would give

    sup(L1)>inf(R2)>=sup(R1)>inf(L2)>=sup(L1),

an impossible strict inequality loop. Four across-column edges are thus
impossible. With two edges the only feasible matching is L1--R1, L2--R2;
with three edges either one of the two noncrossing three-edge patterns
occurs. These alternatives are equivalent after vertical reflection. QED.

The resulting **exhaustive** graph inventory, up to left/right or vertical
reflection, is:

| Intermediate columns | Across-column edges | Positive component | Exact geometric status |
|---|---:|---|---|
| (1,1) | 1 | Four-body path P4 | q=17/4, contains the existing P path family |
| (1,2) or (2,1) | 2 | Four-cycle with one pendant bridge, five bodies | q=17/4, five-body completion capacity OPEN |
| (2,2) | 2 | Simple six-cycle, six bodies | q=17/4, three-square completion capacity OPEN |
| (2,2) | 3 | Six-body, seven-edge graph with a four-cycle and six-cycle | q=17/4, three-square completion capacity OPEN |

This is a genuine finite topology cover of **all two-loaded positive
components of the selected certificate**, not a claim that every minimizer
has only two loaded bodies. Zero-weight contacts and every other physical
square remain in the completion premise. The last three capacity problems
are not declared solved merely because their core frames are aligned.

In the coarse block inventory, the three cyclic types belong only to
C1.4.b1 or C1.6.b0. Therefore every other cyclic cell's **two-loaded
subfamily** is excluded for this selected certificate. Cells with three
or more loaded bodies remain open unless covered by another theorem;
these subfamily exclusions do not tick the whole cells.

## 8. Immediate complete cyclic exclusion: the four-body diamond

The four-body diamond is K4 minus one edge. By the acute loaded-contact
and connected-loaded-noncontact theorem in ACUTE_LOADED_CONTACT_GRAPH.md,
every load pattern is excluded except **exactly the two nonadjacent tips
loaded**. (Any adjacent two loads touch; every loaded subset of at least
three has a body touching all the other loaded bodies.)

In that last pattern the new theorem CY.TWO applies, so the component's
positive graph must be bipartite. The diamond contains triangles and is
not bipartite. Contradiction.

> **C1.4.b0.DIAMOND CLOSED hand:** no positive four-body diamond component
> occurs in the radius window, for any physical square orientations,
> load weights, application points, or completion by the other squares.

The complete biconnected simple four-vertex graph list is C4, K4-e, K4:
minimum degree at least two gives C4 with four edges, K4-e with five,
or K4 with six. C4 and K4 were excluded in the two preceding branch
manuscripts. Therefore **the whole coarse cyclic cell C1.4.b0 closes**,
not merely one drawing or one small angular subclass.

The other 56 coarse cells remain open as parent cells unless another
whole-cell theorem applies. The new necessary two-loaded classification
restricts every one of them uniformly but does not dispose of their
three-or-more-loaded possibilities or their unstressed completions.

## 9. Validation, provenance and exact scope

The proof consists of (i) the support matrix inequalities (5), (ii) the
circle-load sign calculation, (iii) equality propagation on finite paths,
and (iv) exact positive-width arithmetic. It does not rely on numerical
infeasibility, orientation sampling, a claimed generic graph drawing,
or strong duality beyond the already established physical equilibrium.

An accompanying exact Fraction-based checker tests the displayed matrix
identities, support points with signed orientations, circle-work cases,
physical two-loaded path/cycle examples and the four-body graph/load
classification. Those finite checks are regression evidence only.

Independent full review, Lean compilation and CI have not been performed.
The unrestricted n=9 theorem, P.ALL, Y.ALL and the other full cyclic-cell
capacity inequalities remain OPEN. This continuation is prepared locally;
no GitHub write is claimed unless separately confirmed by a tool result.
