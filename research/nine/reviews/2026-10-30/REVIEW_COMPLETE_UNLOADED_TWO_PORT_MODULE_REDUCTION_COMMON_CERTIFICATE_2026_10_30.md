# Independent review of the complete unloaded two-port module reduction

Date: October 30, 2026. Reviewer: common_certificate continuation.

Target:
`EVERY_UNLOADED_TWO_PORT_MODULE_IS_A_ONE_OR_TWO_SQUARE_CHANNEL_2026_10_30.md`

Target SHA-256:
`686e49bdd41e6c105cfc0af956a7b294227e62f4332e8b317b3177b0b003fa8a`.

**Verdict: ACCEPT at the full printed scope.** I read the entire target
and reconstructed its weighted graph-distance estimate, complete
topological reduction, unchanged-mean channel classification, arbitrary
network inequalities and stated block callers. I also read both complete
long-gap domination sources cited in Section 6. The previously reviewed
terminal-ball and occupied-arc sources retain their exact printed pins.
There is no remaining mathematical objection and no original fine or
coarse inventory flag is changed by this review.

The main result is a classification of the full original module. It
does not presume that an arbitrary branching network can be called a
transmitter path. The fact that it becomes such a path is proved.

## 1. The complete cut and the work inequality

The target explicitly uses a nonempty entirely unloaded set with its
complete positive body-pair cut. Zero selected circle coefficients do
not imply absence of physical circle contact. All internal positive
edges and all original supporting normals are retained.

At each pair the original tight support equality is

    n_ij.(c_j-c_i)=h_i(n_ij)+h_j(n_ij),
    h_i(n)=(|n.u_i|+|n.v_i|)/2>=1/2.

For any auxiliary disk meeting every terminal square, dotting all full
unloaded balances with `c_i-o` gives internal contribution `-I` and
cut contribution at most `delta*C-H`. The point chosen in a terminal
and the auxiliary disk need not equal its contact point: the original
separator minimizes its projection at every point of the actual
contact segment, so the inequality has the correct direction.
Consequently `delta*C>=I+H` holds with all original terms.

When the terminals have a common point, `delta=0` contradicts `H>0`.
This proves the one-terminal and touching-two-terminal exclusions even
when a private network branches or contains cycles. For two arbitrary
distinct terminals, the midpoint of actual nearest points belongs to a
disk of radius half their whole-set distance meeting both. Thus

    dist(A,B)>=2(I+H)/C>=1+2I/C.

The proof uses neither rotation equilibrium nor a choice of new contact
means. These statements agree with the previously independently
reviewed network source at SHA
`28506dbf70ccc567765d98f9a4021c79dc46acb5c40fa682993886ab1fca4e46`.

## 2. Exact weighted graph distance from the full force equations

For an exactly two-edge cut, summing all full vector balances gives two
equal magnitudes `mu>0` and opposite outward normals. Both edges cannot
lead to the same external body by the preceding common-terminal
exclusion. The attachment bodies `x,y` inside the module may coincide.

Every internal edge has the positive actual weight

    w_ij=h_i(n_ij)+h_j(n_ij)>=1.

In the connected internal graph, `phi_i=D_w(x,i)` is finite and obeys
`|phi_i-phi_j|<=w_ij` at every internal edge. Taking the common cut
direction `n`, projecting every original force balance on `n`, and
multiplying by `phi_i` gives cut sum `-mu*D_w(x,y)`. Hence

    mu*D_w(x,y)
      =sum_internal mu_ij*(phi_i-phi_j)*(n_ij.n)
      <=sum_internal mu_ij*w_ij=I.

The last step uses the bound on the absolute difference and the unit
normals. It does not require all projected currents to have one sign.
Cycles, backflow, branches, and edges outside a shortest path remain
in the sum. Since every path weight is at least its edge count,
`D_w(x,y)>=dist_K(x,y)`.

The two original cut halfwidths give

    C=2mu,
    H=mu*(h_x(n)+h_y(n)),

including the case `x=y`, where the same body's even halfwidth occurs
twice. Substitution in the complete work inequality proves exactly

    dist(A,B)>=D_w(x,y)+h_x(n)+h_y(n)
             >=1+dist_K(x,y).

This is the main quantitative step. It is valid without a containing
disk and without any assumed internal degree bound.

## 3. The diameter restriction removes every extra body

Every actual square contains its closed center disk of radius `1/2`.
Containment in `D_R` therefore implies `|c|<=R-1/2`. Distinct squares
with disjoint interiors have center distance at least one, and their
inscribed disks provide actual point pairs at distance
`|c_A-c_B|-1`. This proves

    dist(A,B)<=|c_A-c_B|-1<=2R-2.

For `R<5/2`, comparison with the preceding graph-distance inequality
gives `dist_K(x,y)<2`. The distance is an integer, so it is zero or one.

If `x=y`, each connected component of `K-{x}` has nonempty full cut
only to `x`: the two original external edges of `K` both ended at
`x`, and components of the deletion have no edges to each other.
Every such component would violate the one-terminal work inequality.
Thus `K` contains only `x`.

If `x,y` are distinct, their distance one supplies an original positive
edge and therefore a physical intersection point of their squares.
Each component of `K-{x,y}` has a nonempty full cut with terminal set
contained in `{x,y}`. The common physical point gives auxiliary radius
zero, again impossible. Thus `K` contains exactly `x,y`.

The full original degree claim follows, rather than being assumed:
the singleton has its two cut edges, and the two-body case has exactly
one external edge and the common internal edge at each member. No
positive edge is erased. In particular every connected unloaded set
of at least three bodies with nonempty full cut has at least three
cut edges in this radius range; a single edge already fails vector
balance.

## 4. The actual applications give precisely the three channel labels

For a now-proved genuine unloaded degree-two member, full force
balance makes its original forces opposite and equal. Full torque
balance makes the difference of their original application points
parallel to the common signed normal. A side-normal direction has
opposite applications on two opposite sides at equal transverse
coordinate, and their vector difference is exactly the unit normal.
Every other direction exposes opposite vertices; their diagonal
displacement is parallel to the direction only at a square diagonal,
giving difference `sqrt(2)` times the signed normal.

Thus the original actual widths are `1` or `sqrt(2)`. This includes
endpoint applications of shared segments and does not choose new means.
The shared application at each successive pair cancels in the full
vector telescope, so terminal applications satisfy

    p_B-p_A=L*d.

They lie in the actual terminal squares. The two original terminal
supporting lines have gap `L` in direction `d`, hence every terminal
point pair is at least `L` apart, while these actual applications attain
that distance. Therefore the whole-square terminal distance equals
`L`, not merely a projection bound.

At `R<=sqrt(1105)/16<17/8`, the earlier envelope gives
`dist(A,B)<9/4<1+sqrt(2)`. Both strict comparisons have the exact
justifications printed in the target. A two-body module cannot contain
a diagonal width. The three alternatives are consequently exactly one
side transmitter, one diagonal transmitter, or two side transmitters,
with whole-terminal distances `1,sqrt(2),2` respectively.

## 5. More cut edges: no body with two exits

The target's second theorem uses no two-edge-cut assumption. If each
member has at most one cut edge, its full vector balance bounds that
cut magnitude by the sum of its incident internal magnitudes. Sum over
every member, allowing zero on the left for members with no exit:

    C<=2 sum_internal mu<=2I.

Every internal pair is counted exactly twice. Together with `H>=C/2`
and the complete work bound, this proves auxiliary hitting radius at
least one and, for two external terminal squares, distance at least
two. Internal branching and arbitrarily many exits at different
members are allowed. For two terminal bodies, the premise is exactly
that no member has positive edges to both of them, since edges here
are aggregated body pairs.

## 6. The triangle and boundary callers preserve their hypotheses

I read the full geometric expanded-square cover at SHA
`78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6`
and its translational metric formulation at SHA
`5b3c31c3aae5afc91cb2bbba0cabfdd9fcb6ff9f7893b5bd8673f43852a471b0`.
Their exact conclusion is that whole-set terminal distance at least
two forces every third actual square to have distance strictly less
than one from at least one terminal. The complete support-gap/metric
equivalence follows from nearest-point separation of the two compact
convex squares; the incidence or load degree is unrestricted.

Three complete private unloaded networks with terminal pairs `AB,BC,CA`
each give their pair distance at least one. If one network has no
member with two exits, that pair distance is at least two. The full
geometric domination conclusion therefore excludes the configuration.
The printed disjointness and full external-neighbor conditions suffice;
no path is extracted and no contact at a terminal is discarded.

For the boundary budget, the occupied-arc source at SHA
`369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403`
was independently read and reviewed with the original network theorem.
Every selected gap's complete network charge `2(I+H)/C` is at most
the distance between its actual boundary terminals. The selected gaps
are distinct and their distances are nonnegative. Thus their summed
charges are bounded by the complete cyclic sum, giving

    a+2b<tau*(8-t),    tau=5*pi/16<1.

This entails `t+a+2b<=7`: a realizable instance first requires `t<8`,
and then the integer left side is strictly below eight. The four
listed excluded feature counts all have `t+a+2b=8`, and their minimum
body counts are eight because an exit-restricted network needs at
least two members. The source properly demands disjoint modules for
this count. Parallel networks on one terminal pair cannot have their
distance charges added; the source retains their maximum instead.

The actual boundary order is an explicit premise. An arbitrary graph
cycle order is not silently substituted for it, and physically
boundary bodies with zero selected load remain allowed.

## 7. Literal parent features and acceptance boundary

The displayed graph-family caller uses a two-connected unloaded `H`
of at least three bodies, an exterior cycle of at least three bodies,
and two joins with distinct endpoints in each constituent. Its union
is two-connected: deleting any one vertex leaves both surviving
constituents connected and leaves at least one join. When these are
the entire cut of `H`, the main theorem excludes the full physical
feature. A triangle, a four-cycle or diamond, and `K2,3` give precisely
the printed total sizes six through nine, including the branching
`K2,3` cases of sizes eight and nine. The argument does not require
a long simple cycle in `H`.

This is a uniform original-degree-preserving family exclusion across
multiple original bare-block domains. It is conditional on the full
unloaded and complete-cut feature, and it does not assert that an
abstract example has a physical realization or that every graph in an
original parent has that feature. All unused completion squares remain.

The main topology and arbitrary-network inequalities require only
the original force equations and actual support geometry. Torque
enters at the discrete channel labels. Generic normal selection,
physical planarization, canonical rotation and the downstream G4.2.c
audit are not prerequisites for the main topology result. The source
accurately leaves positive-load modules, three-or-more-edge cuts and
unrelated parent alternatives unresolved.

This review uses no numerical search, pose mesh, altered certificate,
Lean compilation or CI. It changes no original inventory flag.
