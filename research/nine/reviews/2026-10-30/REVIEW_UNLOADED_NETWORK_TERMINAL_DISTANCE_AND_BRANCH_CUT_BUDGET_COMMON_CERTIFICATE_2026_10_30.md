# Independent review of the complete unloaded-network distance and branch-cut theorem

Date: October 30, 2026. Reviewer: common_certificate continuation.

Target:
`UNLOADED_NETWORK_TERMINAL_DISTANCE_AND_FULL_BRANCH_CUT_BUDGET_2026_10_30.md`

Target SHA-256:
`28506dbf70ccc567765d98f9a4021c79dc46acb5c40fa682993886ab1fca4e46`.

**Verdict: ACCEPT at the full printed scope.** I read the entire target,
reconstructed its force identities and equality cases, and checked the
complete imported occupied-arc metric proof and the order interface used
in Section 6. This review gives no whole original-cell closure credit.

## 1. The quantitative theorem keeps the complete original network

The network `K` contains only zero-circle-load bodies; physical circle
contact with zero weight is correctly allowed. Every positive edge
leaving `K` is included in the cut, and every internal undirected edge
is included once. The target's quantities are

    C=sum_cut mu,
    H=sum_cut mu*h_internal(n),
    I=sum_internal mu*(h_i(n)+h_j(n)).

The main theorem assumes `C>0`. Since every unit square has centered
support halfwidth at least `1/2`, `H>=C/2` and `I>=sum_internal mu`.
No equality of the internal weights or common direction is assumed.

For an arbitrary auxiliary point `o`, summing the original force
equations dotted with `c_i-o` gives the exact internal contribution `-I`.
For a cut contact to terminal `t`, the original application `p`
minimizes its normal on `t` and maximizes it on the internal square.
Consequently, for any actual terminal point `z_t` with `|z_t-o|<=delta`,

    n.(c_i-o)=n.(p-o)-h_i(n)
               <=n.(z_t-o)-h_i(n)<=delta-h_i(n).

The signs are correct for the stated outward-from-network convention.
Multiplication by every original positive cut magnitude and summation
therefore give `delta*C>=I+H`. The proof uses no torque equation but is
a necessary consequence of the full torque-balanced certificate. All
internal branches, cycles, degrees and means are retained.

The terminal hitting-radius corollary follows by taking an infimum;
no minimizer for the general terminal set is required. The one-terminal
case, the `delta<1/2` loading conclusion, and the `delta=1/2` exclusion
when `I>0` have the right strictness. The explicit separate treatment of
a zero-cut set avoids applying a division by `C` there.

## 2. Whole-set distance and exact equality

For two compact terminal squares `A,B`, choose actual closest points
`a,b`. Their midpoint gives a hitting ball of radius `dist(A,B)/2`.
Conversely the triangle inequality gives

    dist(A,B)<=dist(o,A)+dist(o,B)
                <=2 max(dist(o,A),dist(o,B)).

Thus the optimized auxiliary radius is exactly half the **whole-set**
distance. Substitution yields

    dist(A,B)>=2(I+H)/C>=1+2I/C.

The application does not confuse a projection gap or section gap with
Euclidean set distance. Multiple cut contacts with the same terminal
are fully included. The earlier one-terminal contradiction ensures
that a nontrivial unloaded network attached only to `A,B` actually has
positive contact with both.

At terminal distance one, equality forces `I=0`. Connectedness then
forces `K` to be one actual body: any connected graph with more than
one vertex has a positive internal edge. Its two terminal pairs are
its full positive star, so the degree-two premise is derived rather
than imposed by suppression.

Because every positive summand of the work bound must be exact,
equality in Cauchy gives the two opposite normals along the closest
point direction, and equality in `h_U>=1/2` makes that direction one
of the actual square's side axes. Force balance fixes equal original
magnitudes. No common orientation of the terminal squares follows or
is claimed.

With full torque, the difference of the original two application means
is parallel to that same force direction. The two support projections
differ by one, so the full vector difference is precisely the unit
normal. This checks the printed equality conclusion including the
unchanged side means.

The path calibration counts both cut incidences when there is only
one internal body. For any `k`, the endpoint halfwidths plus the
internal edge halfwidths sum to twice each internal halfwidth. Hence
`2(I+H)/C` equals the original full path-width reserve. The explicit
refusal to replace this quantity by the body count of an arbitrary
branching network is necessary and correct.

## 3. The plane two-cut argument

The target correctly adds a compatible plane embedding with actual
circle-access spokes as a separate premise for its graph theorem.
This premise is supplied by the current physical uncrossing pipeline
when used there; translational force balance alone would not supply it.

Delete `A,B` from the full retained component. Every bilateral
component has full outside-neighbor set contained in `{A,B}`. If the
terminal distance is less than one, the quantitative theorem forces
each bilateral component to contain a positive circle load.

Three bilateral components supply three internally disjoint `A`--`B`
paths. In the resulting plane theta, exactly two of the three paths
bound the unbounded face, while an internal point of the third path
is separated from infinity by their Jordan cycle. A loaded body in
the third component can be joined inside that component to its theta
path, avoiding `A,B` and the other two paths. Its actual circle spoke
then gives an exterior access forbidden by that Jordan separation.
This verifies the asserted bound of at most two bilateral components.

Equivalently, a component containing the interior theta path cannot
escape the outer Jordan cycle: its only possible intersections with
that cycle would lie in the two other deleted-graph components or in
`A,B`, neither of which belongs to it. The conclusion therefore remains
valid if the chosen loaded body is off the initial theta path.

The quantitative remainder for three or more bilateral components is
also sound. The topological argument forces at least one to be entirely
unloaded, and its entire original component receives the distance
bound. At distance one every such connected unloaded component is the
genuine side transmitter already classified. The source correctly
requires deleting from the full retained component, rather than from
a displayed block that might have omitted loaded outside attachments.

## 4. Occupied arcs and the weighted branching-network caller

I read and reconstructed the imported metric proof in
`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`,
whose current SHA-256 is
`369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403`.

At radius `rho=5/4`, each actual physical boundary square has a
connected inner-circle intersection whose relative interior lies in
the open square and whose angular length is greater than `pi/4`.
The source's convex-in-`a+b` estimate for
`(a-1)^2+(b-1)^2+sqrt(2)(a-1)(b-1)` correctly checks both endpoint
configurations. Its parallel-strip comparison gives the same strict
width, and its radial-point argument places every actual outer corner
direction in that one inner arc. Thus the trimmed occupied arcs have
the actual boundary-corner cyclic order.

Their disjointness and total circular length imply

    sum_i dist(B_i,B_(i+1)) < (5*pi/16)(8-t).

For each chosen gap the network theorem gives an actual set-distance
lower bound by its full charge `W_i=2(I_i+H_i)/C_i`. Summing proves the
target's weighted inequality. Each charged gap contributes at least
one, and `5*pi/16<1` gives `t+k<=7` by the integer comparison. The
additional continuous work reserve `2 sum I_i/C_i` is retained with
the correct strict inequality.

If several private networks have the same terminal pair, only their
maximum individual lower bound can be charged to that one distance.
The target explicitly states this limitation. It does not add charges
for parallel networks without a separate theorem.

The actual corner order may be taken directly from physical geometry.
If instead a caller derives it from a graph cycle, the source correctly
requires the compatible embedding and actual boundary spokes. Its
reference to the occupied-arc source's annular-order argument matches
those premises and is not extended to arbitrary graph orderings.

## 5. Exact acceptance boundary

The theorem is a new full-degree quantitative tool for unloaded private
networks, an arbitrary-size two-cut exclusion at nearby terminals, and
a weighted extension of the occupied-arc budget. It applies to branching
graphs without assigning them a degree-two equation.

It does not prove that every private network is unloaded, does not count
an arbitrary small positive-weight branch as a full unit of path length,
does not cover every three-connected block by a two-cut argument, and
does not close any entire original `C1` or `C2` parent. These limits are
stated accurately in the target. The original inventory remains
unchanged.

The review used hand reconstruction of the complete identities,
inequalities, equality cases and topology. No numerical sampling,
pose search, Lean compilation or CI was used.
