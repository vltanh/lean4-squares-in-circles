# An unloaded network pays for its internal force: terminal-distance and branch-cut budgets

Date: October 30, 2026 UTC. Author: branch_budget continuation.

**Status: complete proposed hand theorem, awaiting independent review.**
No original fine or coarse flag is closed by this source. The result applies
to arbitrary connected unloaded networks, including branches, chords and
attached blocks. It does not replace such a network by a degree-two body.

The main quantitative conclusion is the following. If an entire unloaded
network K has positive contacts with only two external actual squares A,B,
let C be the sum of its cut-force magnitudes, I its full internal support
work, and H its internal-side cut support work. Then

    dist(A,B) >= 2(I+H)/C >= 1+2I/C.                    (1)

Every internal positive edge makes the last bound strictly greater than
one. At distance exactly one, a connected K is necessarily one genuine
width-one, true-degree-two transmitter. Thus a network with branches is
charged by its actual forces, rather than by an invented integer path
length. An actual k-body transmission path recovers the sharp charge k
when all its internal widths are one.

This is an extension of the translated-ball virial calculation in
`THREE_GENUINE_ROOTS_ARBITRARY_PRIVATE_NETWORK_LOAD_AND_UNIQUE_PAIR_CLASS_2026_10_29.md`,
Section 1. That source applies its calculation to three genuine near-origin
roots. Here the auxiliary ball is chosen freely, its exact support work is
retained, and minimization over the two terminal sets yields (1).

## 1. One complete physical stress, and the exact cut quantities

Let a finite family of actual closed unit squares have disjoint open
interiors. The containing radius, when there is one, is unrestricted in
Sections 1--5. Retain one full nonnegative physical contact/circle stress.
For every positive body pair i--j retain its positive magnitude mu_ij,
actual common unit support normal, and actual shared application point or
shared-side mean. No additional positive pair at a body is omitted.

Orient a pair from i to j. Its normal n points outward from i toward j,
and the actual support halfwidths are

    h_i(n)=(|n.u_i|+|n.v_i|)/2 >= 1/2.

The unchanged actual support equation is

    n.(c_j-c_i)=h_i(n)+h_j(n).                         (2)

An unloaded body has zero total selected circle weight, including zero at
every physical circle corner. Its complete translational equation is

    sum_(all positive neighbors j) mu_ij*n_ij=0.       (3)

All other original equations and all physical circle masks remain in the
certificate. The main inequality needs only (2)--(3), and consequently
also holds when the original certificate has full torque balance.

Let K be a nonempty set of unloaded bodies. Every positive edge leaving K
ends in a member of a specified terminal set T disjoint from K. The
terminals may have arbitrary degrees, loads, moments and outside neighbors.
Suppose the positive cut is nonempty. For a cut edge orient n from its
endpoint i in K toward its terminal t in T, and set

    C = sum_cut mu > 0,
    H = sum_cut mu*h_i(n),
    I = sum_internal mu*(h_i(n)+h_j(n)).               (4)

Every internal undirected positive pair is counted once in I. Different
original pairs and all cut edges are counted, including several contacts
with the same terminal. These are forces and widths of the full original
network. In particular

    H >= C/2,       I >= sum_internal mu >= 0.         (5)

No connectivity assumption is needed for the inequality. Connectivity is
used only for the sharp equality statement and the graph callers below.
Unstressed physical squares outside K and T remain in the packing.

## 2. The freely translated terminal-ball theorem

Choose any auxiliary point o and delta>=0 such that every terminal t in T
contains an actual point z_t with

    |z_t-o| <= delta.                                 (6)

This point o need not be the containing-circle center, a square center, a
contact point or an element of K. Choosing it changes no geometry or force.

**Theorem 1 (exact terminal-ball work).**

    delta*C >= I+H >= I+C/2.                          (7)

**Proof.** Dot the complete equation (3) at i with c_i-o and sum over all
i in K. For an internal edge i--j the two terms combine to

    mu*n.(c_i-o)-mu*n.(c_j-o)
       = -mu*(h_i(n)+h_j(n)),

by (2). Their total is exactly -I.

For a cut edge i--t, let p be its unchanged actual application. The
terminal square minimizes n at p, so

    n.p <= n.z_t.

The internal body maximizes n at p, so n.p=n.c_i+h_i(n). Therefore

    n.(c_i-o) <= n.(z_t-o)-h_i(n)
               <= delta-h_i(n).                     (8)

The summed full equations now give

    0 = -I + sum_cut mu*n.(c_i-o)
      <= -I+delta*C-H.

This is (7). Every internal term and every external positive force has
been retained, with its actual width and application. QED.

Equivalently, define the terminal hitting radius

    r(T)=inf_o max_(t in T) dist(o,t).

Taking the infimum in (7) gives

    r(T) >= (I+H)/C >= 1/2+I/C.                       (9)

There is no circle-origin assumption in this inequality. It may be used
at a convenient translated auxiliary point even though the physical
circle, its radial loads and every body pose remain fixed.

### 2.1 Positive-load forcing at arbitrary interfaces

If all terminal squares meet a single closed disk of radius delta<1/2,
no nonempty all-unloaded K with a positive cut to those terminals exists.
For delta=1/2, no such K with any internal positive edge exists.
Consequently a connected private network in either excluded circumstance
must contain at least one *positive selected circle load* in its full
original system. Physical circle contact with zero weight does not suffice.

For a single external terminal, choose o inside that terminal and delta=0.
This rederives the no-unloaded-one-body-appendage rule at arbitrary network
size. It also shows that any nontrivial unloaded network claimed to have
two terminals must actually have a positive contact with each of them.

The cut cannot simply be dropped. If a nonempty unloaded set instead has
no positive cut but has an internal positive edge, the same center-dot
sum reads 0=-I<0 and excludes it directly. An isolated zero-edge body is
not a nontrivial positive network and is outside these claims.

## 3. Two actual terminal sets: the full quantitative gap

Suppose the external positive neighbor set of K is contained in two
distinct actual squares A,B. Choose closest points a in A and b in B;
compactness gives such points. Put

    d=|b-a|=dist(A,B),       o=(a+b)/2.

Both terminal sets meet the closed ball of radius d/2 about o. Theorem 1
therefore proves the exact bound

    d*C >= 2(I+H).                                    (10)

This is the minimum possible terminal-ball radius: for any o, choose
closest points a_o in A,b_o in B. Then

    d <= |a_o-b_o| <= dist(o,A)+dist(o,B)
                         <=2 max(dist(o,A),dist(o,B)).

Thus r({A,B})=d/2, and (10) loses nothing at the step of choosing the ball.
With (5) it yields

    dist(A,B) >= 2(I+H)/C
               >= 1+2I/C
               >= 1+2(sum_internal mu)/C.             (11)

**Theorem 2 (whole-network terminal distance).** Equations (10)--(11)
hold for the original full unloaded network at arbitrary endpoint degree,
arbitrary internal degree and arbitrary graph size. No torque, boundary
contact, radius window, plane embedding or selected-normal genericity is
required. Any internal positive edge forces dist(A,B)>1. If dist(A,B)<1,
every nonempty connected component attached only to these two terminals
must carry a positive circle load.

The conclusion concerns the distance of the *whole terminal squares*.
It is not inferred merely from an auxiliary horizontal section or from
their centers. In particular physically touching terminals cannot enclose
an all-unloaded private network of any size behind their two-vertex cut.

## 4. Complete sharp equality and the original transmission-path caller

Assume K is connected in the positive body-pair graph and d=1. By (11),
I=0. Every internal edge would make I positive, so K has no internal
positive edge. Connectedness then forces K={U}, one actual body.

Section 2.1 shows that both A and B are actual positive neighbors. Since
there are no other positive neighbors, U is unloaded of *true full
positive degree two*. No branch has been suppressed to make this true.

Write e=b-a, so |e|=1 and a-o=-e/2,b-o=e/2. Equality holds in every
positive cut summand of (8) and (5). On the U--A edge this forces

    n_UA=-e,       h_U(e)=1/2,       e.(c_U-o)=0.

On the U--B edge it forces n_UB=e and the same support condition. The
Cauchy equality is literal: n_UA.(a-o)=1/2 and n_UB.(b-o)=1/2.
Since h_U(e)=(|e.u_U|+|e.v_U|)/2 and e is unit, h_U(e)=1/2 means that
e is one of U's own side axes. Full force balance makes the two original
positive magnitudes equal.

The terminal supports are the unchanged planes

    e.x=e.a on A's facing maximum side,
    e.x=e.b on B's facing minimum side,
    e.b-e.a=1.

There is no asserted common orientation of A and B. Nor is the transverse
position of U fixed by force balance alone.

If the original certificate has full torque balance, let p_A,p_B be its
two unchanged application means on U. Their origin moment gives

    (p_B-p_A) cross e=0.

Their two U support planes are separated by one, hence also
e.(p_B-p_A)=1. Therefore

    p_B-p_A=e.                                        (12)

This uses the original two means; it does not choose a new common force
line after extraction. The full physical circle masks at A and B and any
other positive contacts at A or B remain arbitrary.

### 4.1 Exact calibration on a genuine k-body unloaded channel

For a path A--U_1--...--U_k--B whose internal bodies are genuinely
unloaded of true positive degree two, the original force equations
propagate one signed normal e and one positive magnitude mu. Thus

    C=2mu,
    H=mu(h_(U_1)(e)+h_(U_k)(e)),
    I=mu sum_(j=1)^(k-1) (h_(U_j)(e)+h_(U_(j+1))(e)).

For k=1, the two cut incidences give H=2mu*h_U(e) and I=0.
In every case,

    2(I+H)/C=2 sum_(j=1)^k h_(U_j)(e).                (13)

This is precisely the usual full actual-width reserve of the path. When
every internal support width is one, the charge is k. With full torque,
a diagonal transmitter keeps its larger actual width sqrt(2).

For a branching network there is **no** general replacement of
2(I+H)/C by its number of bodies. Such a replacement is not claimed.
Different positive weights may distribute work among parallel routes.

## 5. A whole two-vertex-cut theorem, including branching private components

Now assume the retained physical graph has a compatible plane embedding
preserving physical contact order and physical circle-access spokes. This
is an additional explicit premise, not a consequence of Section 1's
force equations or an identification of separately selected certificates.

Let A,B be any two vertices of a connected positive component G. A
bilateral component means a connected component K of G-{A,B} having at
least one positive edge to A and at least one to B. It may contain any
number of branches, chords, blocks and attached trees.

**Theorem 3 (nearby terminals have at most two bilateral components).**
If dist(A,B)<1, G-{A,B} has at most two bilateral components.

**Proof.** By Theorem 2, each bilateral component contains an actual
positively circle-loaded body. If three such components K_1,K_2,K_3
existed, choose a simple A-to-B path P_j through each K_j. The three
paths are internally disjoint. They form a plane theta.

For each j, choose a loaded body Z_j in K_j and a path inside K_j from
Z_j to P_j, stopping at the first point of P_j. This path misses the
other two theta paths and has no earlier meeting with P_j. Its remaining
physical circle spoke supplies access from an internal point of P_j to
the unbounded face without crossing the theta.

But exactly two bridges of a plane theta bound its unbounded face; an
internal point of the third bridge is trapped behind their Jordan cycle.
It cannot have such exterior access. Contradiction. QED.

For completeness the theta fact follows by taking P_1 union P_2 as a
Jordan cycle. The interior of P_3 lies wholly on one side. If bounded,
P_3 is the interior bridge. Otherwise P_3 divides that exterior side
into one bounded and one unbounded face, leaving one of P_1,P_2 as the
interior bridge. The same argument works for arbitrarily bent paths and
the stipulated compatible resolutions of actual shared junctions.

In particular an actual positive edge A--B has dist(A,B)=0, so deleting
its endpoints cannot leave three bilateral components. This excludes
all such adjacent-terminal books at once, even when each page is a
branching network rather than one degree-two square. It applies at
orders five through nine and beyond, and does not require a long cycle.

**Quantitative remainder.** If there are three or more bilateral
components, at least one of them is all-unloaded by the same theta
argument. Each all-unloaded component obeys its own bound (11).
Consequently dist(A,B)>=1. If dist(A,B)=1, every all-unloaded bilateral
component is a single genuine side transmitter with the equality
structure of Section 4. If one has an internal positive edge, the
terminal distance is strictly greater than one with the explicit reserve
2I/C.

It is essential to delete A,B from the **full retained component**.
A component of a displayed block alone may have an outside attachment
carrying a load or an extra positive cut; it is not silently treated as
an unloaded complete private component.

## 6. The same occupied-arc budget charges real branching networks

For this section only assume actual square containment in

    79/40 <= R <= sqrt(Q),       Q=1105/256.

Take t>=2 distinct physical boundary squares B_1,...,B_t in their actual
circle-corner cyclic order. The complete force-free boundary-gap theorem
in

`OCCUPIED_INNER_ARCS_AND_TRUE_CHANNEL_GAPS_BOUND_EVERY_COMPATIBLE_CYCLE_BY_SEVEN_2026_10_30.md`,
Theorem 1, gives

    sum_i dist(B_i,B_(i+1)) < tau*(8-t),
    tau=5*pi/16<1.                                    (14)

That theorem proves a connected inner occupied arc of length greater
than pi/4 for every boundary square, proves the real corner/arc cyclic
order, and charges actual endpoint-set distances to intervening circular
arcs. Those full physical hypotheses, including its radius window, are
the only imported geometric input in this section.

For any chosen cyclic gap i, suppose K_i is a nonempty connected
all-unloaded network whose full positive outside neighbor set is
contained in {B_i,B_(i+1)}. Let C_i,I_i,H_i be its exact quantities (4).
Put

    W_i=2(I_i+H_i)/C_i

for such a gap, and W_i=0 for an uncharged gap. Theorem 2 and (14) give

    sum_i W_i < tau*(8-t).                            (15)

Every actual edge, arbitrary degree, load at the terminals, physical
circle mask, positive internal chord and original application mean has
been preserved. A network is not asserted to carry a common normal.

If there are several candidate networks on the *same* terminal pair,
their charges cannot be added just because they use disjoint bodies.
The one actual endpoint distance only supplies the maximum of their
individual charges. One may use that maximum in (15), or choose any
one of the networks. This is a necessary limitation of the metric, not
an unproved assignment of extra angular length.

If k cyclic gaps are charged, every W_i>=1, and (15) implies

    t+k<=7.                                          (16)

Thus among seven boundary marks no consecutive pair can host such an
unloaded private network; among six marks at most one cyclic gap can;
among five marks at most two can. In addition the actual continuous
reserve obeys

    k+2 sum_charged I_i/C_i < tau*(8-t).               (17)

For a genuine transmission path, (13) recovers its full actual-width
charge, hence the older marked-cycle estimate. For a branching module,
(15)--(17) are new quantitative full-star constraints; they are not an
integer upper bound on the number of all its internal bodies.

No compatible embedding is needed for (15) if the terminal order is
given directly by their actual circle corners. To obtain the same order
from a graph-theoretic cyclic arrangement, the caller must also retain
one compatible embedding and internally disjoint chosen terminal paths;
their Jordan cycle and actual boundary spokes give the order exactly as
in Section 5.1 of the occupied-arc source. This additional caller is not
automatically assigned to an arbitrary block or to all its two-cuts.

## 7. Transfer value and exact remaining boundary

The module inequality is uniform over all graph orders and true degrees.
It supplies a real quantitative gap for private branching networks and
transfers directly to the adjacent-terminal two-cut families of multiple
block sizes. The whole loaded-neighbor/classification issue is retained:
if a private module carries a positive circle load, the unloaded theorem
does not apply and that load must be accounted for as a real boundary
body. The planar two-cut conclusion addresses this alternative explicitly.

Neither theorem excludes every K2,3-shaped block: its terminals may be
at distance at least one and its exterior private components may carry
loads. Nor does it exclude 3-connected blocks having no relevant two-cut.
The weighted budget alone cannot count small positive-force branches as
one full extra width each. These are genuine limits, so no C1.6.b0,
C1.7.b0, C1.8.b0, C1.9.b0 or C2 parent is declared closed here.

Every one of the original nine actual squares stays physically present,
including completion squares and zero-stress contacts. There was no
normal reselection, square motion, stress thinning, numerical pose search,
angle mesh, Lean/Lake build, CI dispatch or remote publication. The exact
work identities are proved by the full original force sum; no numerical
observations are used as proof premises.
