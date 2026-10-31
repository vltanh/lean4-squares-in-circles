# Every long-channel endpoint is positively circle-loaded

Date: October 30, 2026 UTC.

**Status: complete proposed hand geometric and full-force theorems,
awaiting independent review. No original case, graph, ledger or roadmap
flag is changed here.**

The result is uniform over the entire positive graph. A genuine
two-internal unloaded channel can end only at positively circle-loaded
bodies, even when its endpoints have arbitrary additional positive
edges. The proof uses actual containment and translational force
balance. It does not use torque, a compatible embedding, a simple
cycle, an endpoint degree bound, or a new stress selection.

## 1. Geometric setup and two universal center facts

Let a finite family of actual unit squares have pairwise disjoint open
interiors and lie in a disk centered at O with squared radius at most

    Q=1105/256.

Set

    M=91/60, L=89/60, K=29/15, sigma=1/sqrt(2).

For a contained square S with center c and orthonormal side axes u,v,
its farthest actual corner has squared norm

    |c|^2+1/2+|c.u|+|c.v| >= |c|^2+|c|+1/2.

Since

    M^2+M+1/2-Q=31/57600>0,

every actual center satisfies

    |c|<M.                                                (1)

Every point of a unit square lies within sigma of its center. Any two
distinct actual centers are at distance at least one, because their
open radius-1/2 incircles have disjoint interiors. These facts require
no contact graph or stress.

## 2. Every physical contact lies inside the radius-29/15 disk

**Theorem 1 (universal contact-radius bound).** If a point p belongs to
two distinct actual closed squares, then

    |p|<K=29/15.                                          (2)

The conclusion applies to every actual physical contact, including
zero-stress contacts, side-interior points, shared-side endpoints and
multi-square junctions.

**Proof.** Suppose r=|p|>=K, and write e=p/r. For any actual square
containing p, let c be its center, v=c-p and t=|v|<=sigma.
The vector v is nonzero because |c|<M<K<=|p|.

We first prove that v points strictly within forty-five degrees of
the inward radial direction. Algebraically, this means

    -e.v > t/sqrt(2).                                   (3)

If (3) failed, then

    |c|^2=r^2+t^2+2*r*(e.v)
           >=r^2+t^2-sqrt(2)*r*t
           >=r^2-r+1/2.                                 (4)

For the second inequality, the quadratic in t decreases on
0<=t<=1/sqrt(2) when r>1, so its minimum is at t=1/sqrt(2).
Equivalently, subtracting its endpoint value factors as
(t-sigma)*(t+sigma-sqrt(2)*r)>=0 on that interval.

The function r^2-r+1/2 increases for r>=K, and its value at K is

    K^2-K+1/2=M^2+1/240.                                (5)

Thus (4) contradicts (1), proving (3).

Now apply (3) to the two centers c_1,c_2 of the alleged squares.
Choose a unit perpendicular e_perp and write

    v_i=-a_i*e+b_i*e_perp.

Equation (3) implies a_i>|b_i| and a_i>0. Consequently

    v_1.v_2=a_1*a_2+b_1*b_2
              >=a_1*a_2-|b_1|*|b_2|>0.

It follows that

    |c_1-c_2|^2=|v_1-v_2|^2
                  <|v_1|^2+|v_2|^2
                  <=2*sigma^2=1,

contradicting actual center separation. This proves (2), including
the closed threshold r=K. QED.

## 3. A support gap of two makes both outward own sides contact-free

For a square S and unit direction d, let

    h_S(d)=(|d.u_S|+|d.v_S|)/2

be its actual support halfwidth. Suppose two actual squares A,B have
one signed unit direction d with

    d.(c_B-c_A)>=2+h_A(d)+h_B(d).                       (6)

No contact relation, stress, or circle-contact premise is imposed on
A,B in this section.

Choose d as the horizontal axis and write c_A.d=-X_A,
c_B.d=X_B. Since h_A,h_B>=1/2 and every center has norm below M,

    L<X_A,X_B<M,
    h_A+h_B<2*M-2=31/30,
    h_A,h_B<8/15.                                       (7)

For A, choose its own side axis u_A pointing toward -d, with the
larger absolute projection on d. Choose its perpendicular side axis
v_A. Set

    a=-d.u_A, b=|d.v_A|.

Then a>=b>=0, a^2+b^2=1, and (7) gives

    a+b=2*h_A(d)<16/15.

Therefore

    (a-b)^2=2-(a+b)^2>194/225>81/100,
    a-b>9/10.                                          (8)

The exact reserve in the middle comparison is 47/900. In particular
the larger axis is unique, and a>0.

Consider the entire outward own side

    F_A={c_A+(1/2)*u_A+s*v_A : -1/2<=s<=1/2}.

Every p in this closed side has

    p.d<=-X_A-a/2+b/2
          <-L-(9/10)/2=-29/15=-K.                       (9)

Thus |p|>K, and Theorem 1 says that no other actual closed square
meets any point of F_A.

For B, choose its dominant own side axis u_B pointing toward +d.
The identical calculation gives p.d>K on the whole closed side

    F_B={c_B+(1/2)*u_B+s*v_B : -1/2<=s<=1/2}.

**Theorem 2 (contact-free outward own sides).** Under the actual
support-gap hypothesis (6), each endpoint has a uniquely selected
dominant outward own side, and that entire closed side is disjoint
from every other actual closed unit square.

The conclusion includes both corners of the side. The source does
not rotate either endpoint or replace d by an own axis; u_A,u_B
are their existing own axes, selected separately from their actual
frames.

## 4. Full force balance makes both endpoints positively circle-loaded

Keep any physical nonnegative contact/circle stress on the unchanged
actual packing. At a body S, each incident contact atom has a positive
magnitude mu and a unit normal n directed outward from S toward its
neighbor. Its application belongs to the actual common intersection
and is a maximum-support point of S in n. Circle atoms have
nonnegative coefficients lambda and occur at actual circle corners.
The full translational balance is

    2*sum_(circle atoms on S) lambda*z
       +sum_(all positive incident contact atoms) mu*n=0.     (10)

No torque equation is assumed. All the body's positive incident
forces, including forces outside a displayed path or block, occur
in (10).

For a square with an outward own axis u and its corresponding side
F, any support normal n with n.u>0 exposes only points whose u own
coordinate is +1/2. Every actual contact application for such n
would therefore belong to F.

Apply this observation to A and its contact-free side F_A. Every
actual positive contact normal n on A satisfies

    n.u_A<=0.                                           (11)

If A also has at least one positive contact normal n_* with
n_*.u_A<0, then the full contact sum in (10), dotted with u_A,
is strictly negative. A zero total circle load would make the
circle term zero and contradict (10). Thus A must have positive
total circle weight. The same conclusion holds for B and u_B.

In particular, d.u_A=-a<0, while (-d).u_B<0. We obtain:

**Theorem 3 (positive endpoint load).** Under (6), if A has a positive
actual contact force with normal d, then A has positive total circle
load in any full physical translational balance (10). If B has a
positive actual contact force with normal -d, then B has positive
total circle load. If both inward contacts are present, both endpoints
are positively circle-loaded.

The other endpoint in (6) is used only as an actual geometric witness
for the support gap. It need not be adjacent to the tested endpoint.
The positive inward contact may be with any actual third body.

## 5. The graph-size-independent long-channel corollary

Let the full positive body-pair graph of a physical stress contain a
path of four distinct bodies

    A -- U -- V -- B,

where U,V are unloaded of true positive degree two. Aggregated body
pairs carry their actual support normals and actual application means;
parallel side atoms may be aggregated without changing force balance.

The true degree and zero circle load make each internal body's two
positive forces equal and opposite. Propagation gives one signed
common normal d from A toward B on all three path edges. Actual
support equalities telescope to

    d.(c_B-c_A)=h_A(d)+h_B(d)+2*h_U(d)+2*h_V(d)
                 >=2+h_A(d)+h_B(d).

Thus (6) holds. The actual first path force on A has normal d and
positive magnitude; the actual last path force on B has normal -d
and positive magnitude. Theorem 3 applies at both endpoints.

**Corollary 4 (every long channel joins two positively loaded bodies).**
Every two-internal genuine unloaded true-degree-two channel has
positively circle-loaded endpoints in the same full physical stress.
Endpoint degrees and all other endpoint forces are unrestricted.

This excludes all long channels ending at an unloaded branching body,
whether that body is physically circle-clear or merely has zero
selected circle weight. It also excludes a long channel terminating
at an unloaded articulation, an unloaded ear endpoint, or an unloaded
hub of any true degree.

After suppressing only genuine unloaded true-degree-two runs, every
two-internal label therefore joins two positively loaded vertices.
The conclusion holds across arbitrary blocks and components, with
all original bodies retained. It is not a claim that every large
block contains such a label or that shorter runs have loaded ends.

The previously proved geometric two-channel capacity theorem gives
an additional joint corollary in an actual nine-square packing: all
two-internal labels, if any, have the same unordered pair of positively
loaded endpoints. That statement uses
`TWO_LONG_CHANNELS_FORCE_CAPACITY_EIGHT_AND_FOUR_LOAD_CYCLE_REDUCTION_2026_10_30.md`,
Corollary 1.1, on this same stress. Parallel channels with that same
endpoint pair are not excluded by these conclusions.

## 6. Exact scope and verification boundary

Theorem 1 is a force-free bound on every actual physical contact point.
Theorem 2 is force-free geometry for a support gap of two. Theorem 3
adds only the endpoint's complete translational balance and a positive
inward contact. Corollary 4 derives the common normal from the full
true-degree-two internal force equations. These scopes are kept
separate; no torque or compatible plane certificate is used anywhere.

The radius hypothesis is only R^2<=Q. There is no lower-radius window
or assumption that an endpoint was already known to touch the circle.
Positive circle load is proved, and actual circle contact follows from
the retained circle-atom complementarity.

The proofs preserve every square, positive force, original mean and
zero-stress physical contact. No force is removed to create a degree-two
body and no selection is changed. All exact rational comparisons are
displayed. No Lean compilation, CI, numerical pose search, finite
computational certificate, original ledger mutation or remote write is
claimed here.

The only optional external join is the final nine-body single-pair
corollary. Its frozen source SHA256 is
`e05fa0520279d957659f694fdaa5b08be750a848d5117f3792df4399476354f5`.
The main contact-radius, contact-free-side and positive-load theorems
are self-contained.
