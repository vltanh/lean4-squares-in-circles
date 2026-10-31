# Every unloaded two-port module is an actual one- or two-square channel

Date: October 30, 2026. Input tree:
`4d2b3d62ce489b3251f0241d6c592e868fd7a410`.

**Status: complete proposed uniform hand theorem, awaiting separate
independent review.** No original fine or coarse flag changes here.

The main theorem classifies an entire connected unloaded module whose
**full positive cut consists of exactly two body-pair edges**. In the
target disk, it is necessarily one genuine transmitter or two adjacent
genuine side transmitters. Arbitrary internal branches, cycles and
chords are excluded by the original equations, not deleted to create
a path. This is a theorem about two cut edges, not merely two external
terminal bodies; a module can have many cut edges to the same two
terminals.

A second theorem allows arbitrarily many cut edges. If no member has
two of them, the terminal gap is at least two. This gives a uniform
three-module triangle exclusion and strengthens the common boundary
gap budget. Every original square, contact mean, selected normal,
positive force, and physical circle mask remains throughout.

## 1. Exact full-network work quantities

Retain one full physical force-and-torque certificate on actual unit
squares with disjoint open interiors. At a body with zero total circle
coefficient, all original positive pair forces sum to zero. Such a body
may still physically touch the circle with zero selected coefficients.

For an oriented positive pair `i->j`, let `n_ij` be its unit separator
normal and `mu_ij>0` its magnitude. For the actual square frame put

    h_i(n)=(|n.u_i|+|n.v_i|)/2 >= 1/2.

The tight original support equation is

    n_ij.(c_j-c_i)=h_i(n_ij)+h_j(n_ij).                 (1)

Let `K` be a nonempty entirely unloaded set with a nonempty positive
cut. All its external neighbors belong to a specified terminal set
`T`. Define, counting each internal pair once,

    C=sum_cut mu,
    H=sum_cut mu*h_i(n),
    I=sum_internal mu*(h_i(n)+h_j(n)).                 (2)

Thus `C>0`, `H>=C/2`, and `I>=sum_internal mu`.

The full terminal-ball work theorem gives

    delta*C >= I+H                                   (3)

whenever a disk of radius `delta` meets every actual terminal square.
For completeness, dot each full unloaded force equation with `c_i-o`
at the disk center `o`. Internal contacts sum to `-I`. For a cut
`i->t`, choose `z_t` in the terminal and auxiliary disk. Its original
application `p` maximizes `n` on `i` and minimizes it on `t`, hence

    n.(c_i-o)=n.(p-o)-h_i(n)
              <=n.(z_t-o)-h_i(n)<=delta-h_i(n).

Summing proves (3) without changing any application or force.

If all terminals have a common point, take `delta=0`; the nonempty
unloaded set is impossible. In particular this excludes any unloaded
private network attached only to one body, or only to two physically
touching bodies.

For two distinct terminals `A,B`, the midpoint of nearest points gives
`delta=dist(A,B)/2`. Therefore

    dist(A,B) >= 2(I+H)/C >= 1+2I/C.                  (4)

Both terminals must actually have a positive contact with `K`, since
otherwise the preceding one-terminal contradiction applies.

## 2. Exact two-port graph-distance bound

Suppose `K` is connected and its full cut has exactly two edges.
They cannot both lead to the same terminal body. Write them as
`x--A` and `y--B`, where `x,y` are members of `K`; they may coincide.
The external squares `A,B` are distinct. Sum the complete force
equations on `K`. Internal pairs cancel, so the two cut magnitudes
are equal, say `mu>0`, and their outward normals are `n,-n`.
Consequently

    C=2mu,
    H=mu*(h_x(n)+h_y(n)).                             (5)

For each internal edge `ij`, assign its actual positive length

    w_ij=h_i(n_ij)+h_j(n_ij) >= 1.

Let `D_w(x,y)` be shortest-path distance in this weighted internal
graph, and let `ell=dist_K(x,y)` be ordinary edge distance.

**Lemma 2.1 (full projected-flow bound).**

    I >= mu*D_w(x,y) >= mu*ell.                       (6)

*Proof.* Set `phi_i=D_w(x,i)`. Along every internal edge,
`|phi_i-phi_j|<=w_ij`, while `phi_x=0` and
`phi_y=D_w(x,y)`. Dot each body's complete force balance with `n`,
multiply by `phi_i`, and sum. The two cut terms total
`-mu*D_w(x,y)`. The internal sum is therefore

    mu*D_w(x,y)
      =sum_internal mu_ij*(phi_i-phi_j)*(n_ij.n)
      <=sum_internal mu_ij*w_ij=I.

Every original internal edge is included. The bound uses no assertion
that its direction equals the cut direction. Since all `w_ij>=1`,
every internal path has weighted length at least its edge count,
so `D_w(x,y)>=ell`. QED.

Combining (4)--(6) proves the quantitative statement

    dist(A,B) >= D_w(x,y)+h_x(n)+h_y(n)
              >= 1+dist_K(x,y).                      (7)

This holds at unrestricted radius and at arbitrary original internal
degrees. It charges the actual support widths before taking the
integer consequence.

## 3. Complete two-port topology at radius less than five halves

Every unit square contains its closed radius-`1/2` center disk.
If it is contained in `D_R`, then `|c|<=R-1/2` by considering the
farthest point of that inscribed disk. The two disjoint open
inscribed disks of distinct actual squares give
`|c_A-c_B|>=1`. Nearest points of these smaller disks show

    dist(A,B) <= |c_A-c_B|-1 <= 2R-2.                 (8)

**Theorem 3.1 (complete two-port module reduction).** If `R<5/2`,
every entirely unloaded connected module with exactly two positive
cut edges is either a single square, or the two distinct adjacent
attachment squares `x,y`. In the latter case each has true positive
degree two in the original graph.

*Proof.* Equations (7)--(8) imply

    1+dist_K(x,y) < 3,

so the integer distance is zero or one.

If `x=y`, suppose another body remains in `K-{x}` and take one
connected component `L` of that remainder. Connectivity of `K`
makes its cut nonempty. All external positive contacts of `L` end
at `x`: the only two edges leaving `K` were at `x`, and distinct
components of the remainder have no positive edges between them.
All members of `L` are unloaded. The one-terminal consequence of
(3) is a contradiction. Thus `K={x}`.

If `x!=y`, their internal graph distance is one, so they have an
actual positive contact. If a body remains in `K-{x,y}`, any
connected remainder component `L` has a nonempty full cut whose
terminal set is contained in `{x,y}`. Its terminals share their
actual contact point. Equation (3) with `delta=0` again gives a
contradiction. Thus `K={x,y}`.

In the two-body case, the original full edges at `x` are exactly
`xA,xy`, and those at `y` are exactly `xy,yB`. Both full degrees
are therefore two. This is a conclusion about the unchanged graph,
not an extraction discarding internal forces. QED.

As a convenient contraposition, **every connected unloaded set
with at least three actual bodies and a nonempty positive cut has
at least three cut edges** in this radius range. A one-edge cut
is already impossible by force balance; Theorem 3.1 handles two.
This applies across blocks and attachment forests when their entire
original cut, rather than a displayed subgraph cut, is used.

## 4. Exact physical channel labels in the target disk

Now assume `R<=sqrt(Q)`, `Q=1105/256`, so in particular `R<5/2`.
Retain the original torque equations and applications.

For a genuine unloaded degree-two square the equal opposite forces
and full torque give `p_+-p_-` parallel to their common signed normal
`d`. Its support width is positive. If `d` is an own-side normal,
the opposite applications have the same transverse coordinate and
`p_+-p_-=d`. Otherwise they are the unique opposite support vertices;
their diagonal displacement can be parallel to `d` only when `d`
is a diagonal direction, giving `p_+-p_-=sqrt(2)*d`.

Thus each genuine transmitter has its actual width `1` or `sqrt(2)`,
with its original shared-side means unchanged. Adding these original
application differences along the one- or two-body module gives

    p_B-p_A=L*d,

where `L` is the sum of its actual widths. The terminal support
halfplanes are separated in direction `d` by exactly `L`, and the
actual points `p_A,p_B` attain distance `L`. Consequently

    dist(A,B)=L.                                      (9)

The two-body case cannot contain a diagonal transmitter. Indeed
`R<=sqrt(1105)/16<17/8`, since `1105<1156`, and (8) gives

    dist(A,B)<9/4<1+sqrt(2).

The last inequality follows by squaring `5/4<sqrt(2)`. A diagonal
plus any second transmitter would contradict this bound.

**Corollary 4.1 (complete original module alternatives).** In the
target disk, an entirely unloaded connected two-edge-cut module
has exactly one of these three forms:

| Actual members of `K` | Actual transmission | Terminal distance |
| --- | --- | ---: |
| One | Side normal, original opposite-side means | `1` |
| One | Diagonal, original opposite vertices | `sqrt(2)` |
| Two | Both side normal, original consecutive means | `2` |

No branching or cyclic alternative remains. The table does not
classify a module with three or more cut edges, even if it has only
two external terminal bodies.

## 5. Arbitrary many ports with at most one exit per body

Return to any entirely unloaded set `K`, with the full quantities
(2), and assume that **each member has at most one positive cut
edge**. It may have arbitrarily many internal positive contacts.

At a member with a cut edge, full force balance and the triangle
inequality give

    mu_cut <= sum_(internal edges incident at that member) mu.

At a member without a cut edge the analogous inequality has left
side zero. Summing over all members counts every internal edge
twice. Hence

    C <= 2 sum_internal mu <= 2I.                     (10)

Together with (3) and `H>=C/2`, this proves

    delta >= 1                                       (11)

for every disk meeting all terminal squares. In particular, if
the only external neighbors are `A,B`,

    dist(A,B) >= 2.                                  (12)

For two terminals the exit hypothesis is exactly that no member
has positive contacts to both terminals. Every original internal
branch, cycle and chord remains. The hypothesis constrains the
cut, not the full degree of a member. Formula (4) remains available
with its possibly stronger exact value `2(I+H)/C`.

## 6. A complete forbidden triangle of arbitrary private networks

The force-free two-endpoint domination theorem states that for three
actual unit squares in `D_sqrt(Q)`,

    dist(A,B)>=2  =>  dist(A,C)<1 or dist(B,C)<1.       (13)

Its complete geometric source is the expanded-square cover cited
below; the metric formulation and the radius-`1/2` incircle passage
are proved in the translational domination source. Neither requires
any degree, circle mask or load condition at `A,B,C`.

Suppose three distinct actual terminals `A,B,C` have nonempty
pairwise disjoint unloaded private networks `K_AB,K_BC,K_CA`, all
disjoint from the terminals. Each network's full positive external
neighbor set is contained in its displayed terminal pair, and its
cut is nonempty. Suppose at least one network has at most one cut
edge per member. Equations (4) and (12) give pair distances at least
`(2,1,1)` in some order, contradicting (13).

**Corollary 6.1.** This entire three-network configuration is
impossible, with arbitrary internal branching, internal chords,
selected application means, and arbitrary terminal degrees and
loads. It is not necessary that the terminals touch the circle or
that a chosen graph cycle give their order. All other actual squares
remain. This extends the true-path `2/1/1` obstruction to complete
private networks without assigning them fictitious channel degrees.

## 7. The strengthened shared boundary budget

Assume the occupied-arc radius window

    79/40 <= R <= sqrt(Q),    tau=5*pi/16<1.

Choose `t>=2` distinct actual boundary squares in their actual
circle-corner order, `B_1,...,B_t`. Their selected circle weights
may individually be zero. The complete occupied-arc theorem gives

    sum_i dist(B_i,B_(i+1)) < tau*(8-t).               (14)

On each of any chosen distinct cyclic gaps, select one nonempty
entirely unloaded private network with full external neighbor set
contained in that terminal pair. For the body-count caller below,
the chosen networks are pairwise disjoint and avoid all selected
boundary marks. Let `a` chosen gaps have arbitrary
such networks, and `b` other chosen gaps have networks satisfying
the at-most-one-cut-edge-per-member hypothesis. Every gap is
counted once. Equations (4), (12), (14) give

    a+2b <= sum_chosen 2(I_i+H_i)/C_i
          < tau*(8-t),

and therefore the strengthened integer budget

    t+a+2b <= 7.                                     (15)

It is the full `I_i,H_i,C_i` that may improve the left side further;
no unit charge is assigned to an arbitrary weak internal branch.
Several parallel networks on the same terminal pair provide the
maximum of their charges, never their sum.

In particular the following whole structural features are impossible:

| Boundary count `t` | Other charged gaps `a` | Gaps with no double exit `b` |
| ---: | ---: | ---: |
| 3 | 1 | 2 |
| 4 | 2 | 1 |
| 5 | 1 | 1 |
| 6 | 0 | 1 |

Their minimum body count is eight: every ordinary charged gap has
at least one member, and every no-double-exit gap has at least two
by (10). Arbitrary additional internal branches are permitted, so
the same exclusions transfer to nine-body chorded configurations
whenever the complete-cut premises hold. For three boundary marks,
Corollary 6.1 is stronger: even three nonempty gaps with only one
no-double-exit network are excluded.

The terminal circle-corner order in (14) is a geometric hypothesis.
If a caller supplies only graph cyclic order, it must establish
agreement through a compatible embedding, actual boundary spokes
and internally disjoint chosen terminal paths. The ordinary Jordan
cycle argument then supplies this order; it is not automatically
assigned to an arbitrary chorded block.

## 8. Literal block families and remaining scope

For an explicit broad two-port caller, let `H` be a two-connected
graph of at least three actual unloaded bodies, let an exterior
cycle contain at least three actual bodies, and connect distinct
vertices of `H` to distinct cycle vertices by exactly two positive
joins. Require these joins to be the entire positive cut of `H`.
Their union is two-connected: deletion of any vertex leaves each
constituent connected and at least one of the two joins intact.
Theorem 3.1 excludes the complete physical feature, regardless of
the contact types or original means of those joins.

This treats, in one argument, a triangle `H` against exterior cycle
sizes `3--6`, a four-cycle or diamond `H` against sizes `3--5`, and
`K2,3` against sizes `3--4`. Thus the feature occurs within the
original bare-block parent domains `C1.6.b0` through `C1.9.b0`;
the branching `K2,3` caller includes `C1.8.b0` and `C1.9.b0` and
uses no long cycle inside `H`. No abstract graph is asserted to have
a physical realization. The statement is that any such original
graph/load/contact feature would contradict its full equations.
When fewer than nine bodies are displayed, all remaining actual
completion squares stay in place; no extra positive cut into `H`
may be silently omitted.

This does not close any whole original parent. Modules carrying a
positive circle load, modules with at least three cut edges, and
arbitrary cyclic arrangements lacking the complete private-network
cuts retain their obligations. The original open six-body outer
hexagon load rows do not automatically meet a new contradictory
cut hypothesis. No fine-cell identifier is invented or checked.

## 9. Direct sources and verification boundary

The work proof and two-port topology above are repeated in full.
The two geometric imports in Sections 6--7 were read in full; their
exact source identities are:

| Source | SHA-256 |
| --- | --- |
| `UNLOADED_NETWORK_TERMINAL_DISTANCE_AND_FULL_BRANCH_CUT_BUDGET_2026_10_30.md` | `28506dbf70ccc567765d98f9a4021c79dc46acb5c40fa682993886ab1fca4e46` |
| `PHYSICAL_CONTACT_STRESS.md` | `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5` |
| `TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md` | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` |
| `TRANSLATIONAL_LONG_CHANNEL_DOMINATING_PAIR_AND_THREE_LOAD_CYCLE_BOUND_2026_10_30.md` | `5b3c31c3aae5afc91cb2bbba0cabfdd9fcb6ff9f7893b5bd8673f43852a471b0` |
| `OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md` | `369dca0e938754dc7336af7734c7cc916d3ed34894b8fe35a19eb4482fce7403` |

The main topology theorem and (10)--(12) require only the original
translational equations and tight physical supports. Torque is
used solely for the discrete channel labels in Section 4. No new
generic-normal choice or compatible-planarity assertion is needed
for these conclusions. Section 7 imports only the stated actual
boundary order and occupied-arc theorem.

All nine original physical squares, zero-stress physical contacts,
full degrees, actual shared means and individual circle coefficients
remain. No numerical search, mesh, Lean compilation, CI, metadata
mutation or remote publication was used.
