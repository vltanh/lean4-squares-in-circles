# A decorated triangle cannot point inward from a small origin-root corner

Date: October 27, 2026.

**Status: complete proposed uniform theorem and complete original C2.34.b2
opposite-transmitter load-row exit, frozen for full root and separate
independent review.** No shared ledger or whole AP domain is changed.

Keep all nine actual units, the common canonical radius/Phi packing and
its one compatible selected physical certificate. Initially

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1, epsilon=max(d-1,0)<1/60.

All original forces, circle atoms, zero individual weights, physical
contacts and actual side means remain. The new geometric kernel below
does not require a further normal selection.

## 1. Uniform statement at the original degrees

Let H-A-B-H be an actual positive triangle, with O in int H. A has
exactly its two triangle edges and a genuine leaf AL. B is physically
circle-touching; its degree and other forces may be arbitrary. H retains
arbitrary further forces. Write the two original H outward triangle
forces as mu*f and nu*g, where f points H to A, g points H to B, and
mu,nu>0. Put

    M_T=mu*f+nu*g.

Suppose an actual H vertex V satisfies |V|<1/40. Let N_1,N_2 be its
two outward own unit axes. Then the two weak inequalities

    M_T.N_1<=0, M_T.N_2<=0                           (1)

cannot both hold.

This is a statement about the full two actual triangle forces at H.
It does not give H a degree-two equation, identify either force with
M_T, or assume a genuine terminal block elsewhere. Neither a leaf at H
nor an intact triangle is required.

## 2. The actual HA point is small, at arbitrary H and B degrees

We use precisely Sections 2--3 of

    ROOTED_ORIGIN_TERMINAL_FOUR_BLOCK_ADJACENT_LEAF_EXCLUSION.md
    SHA256 3f2c08dec933f0d88bd682c71b40e0b1d0abe8645492739fb37a1ea720c7387c.

Those sections are the complete genuine-A port calculation before the
terminal-four-block theorem is invoked. Their hypotheses are exactly
A's true three forces, a genuine leaf, O in int H, and a physical
boundary B. No HB edge, Q equation or degree at H or B is used there.
The present actual HB edge is needed later for the physical triangle.

For clarity, the full reduction and feature estimates in that kernel
are these. Every other closed unit avoids O. The genuine leaf is S,
d=1+epsilon>1, A is physically clear, and A contains the actual point
epsilon*e in its real leaf direction e. Thus for the unchanged HA
application p and normal f,

    0<h_H(f)=p.f<=epsilon*(e.f)<=epsilon.             (2)

The original true A3 concurrence lemma, with arbitrary contained
neighbors, covers its entire nonparallel and parallel domains. In a
strictly tilted own frame, the only negative-support proper HA features
are the near own side or near-lower vertex of

    A=[delta,1+delta] times [-beta,1-beta],
    0<delta<epsilon, 0<beta<11/60.

Their actual squared norm is at most delta^2+beta^2<122/3600<9/64.
The forbidden leaf corner, all upper features, side endpoints and zero
proper lengths are included in that full feature proof.

For an aligned nonparallel A, its proper concurrence is (tau,0) in
A=[epsilon,d] times [-b,1-b]. A coincident HA point has norm epsilon.
At a distinct actual near vertex, if tau<=d then

    |p|^2<epsilon^2+epsilon<1/3600+1/60<9/64.

If tau>d, the real B application is the opposite near-side vertex.
Every point of physical B has norm at least R-sqrt(2)>129/200.
Its positive height is therefore greater than16/25, leaving the HA
height magnitude b<9/25. Hence

    |p|^2<1/3600+(9/25)^2<9/64.

The aligned parallel pair has the same original inner wall. The two
actual transverse means have positive weighted average zero, so the
same real B height bound gives exactly the same bound for p. Neither
mean is centered. This exhausts all true A features and establishes

    |p|<3/8.                                        (3)

The cited source supplies its complete proof, including the genuine
leaf endpoint reductions and all actual proper-line cases. Only the
above local geometric conclusion is imported; its later genuine-Q
hypothesis and outside-path conclusion are not imported.

## 3. The two inward signs force impossible opposite H vertices

Set a_i=V.N_i. Open origin containment gives a_i>0, and
a_i<=|V|<1/40. In these own coordinates the two opposite H sides
have respective support heights

    h_H(-N_i)=1-a_i>39/40.                           (4)

Suppose first that f is an H own-side axis. Equations (2),(4) imply
f=N_1 or f=N_2. The complete physical unit-triangle side-normal
lemma gives f.g>=0, at arbitrary actual degrees and side means.
Consequently

    M_T.f=mu+nu*(f.g)>=mu>0,

contrary to (1). Thus f is not an H side axis. It strictly exposes
an actual H vertex, which is necessarily the actual point p.

Every H vertex other than V has norm at least1-|V|>39/40, since
any two different vertices of the unit have distance at least one.
Equation (3) therefore forces p=V. Strict exposure now gives

    f.N_1>0, f.N_2>0.

The unchanged equality M_T=mu*f+nu*g and (1) imply

    g.N_i=(M_T.N_i-mu*(f.N_i))/nu<0,
    i=1,2.                                          (5)

Thus g strictly exposes the opposite H vertex

    W=V-N_1-N_2.

Opposite strictly exposed vertices cannot be the two root ports of
three mutually touching unit squares. This is the degree-free physical
kernel in END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md Section2, SHA256
20a845eff8bee3e9c533162df0b32ea96f9dd104a3cfec41efb3b0cf92d6e9cf.
Here is its full support-span contradiction in the present signs.

The actual A lies in f.x>=f.V. The actual B minimizes g at W, and
f.g<0 by (5). For a unit square with minimum-g point W, the strict
support-span lemma gives

    max_{x in B} f.(x-W)<1.                         (6)

At a vertex minimum, write its inward orthonormal axes u,v. Both
g.u,g.v are nonnegative. Because f.g<0, at least one of f.u,f.v
is negative. The remaining positive span is strictly below one:
if a unit projection equalled one, f would be that inward axis and
f.g would be nonnegative. At a side-interior minimum the inward
normal has negative f-projection; only a length-at-most-one tangent
interval contributes, with unit projection strictly below one.
These arguments prove (6), including all normal-axis and side-mean
endpoints. In the current application W is already a strict H vertex;
B may have either kind of minimum feature there.

Since f is unit and both of its own components are positive,

    f.(V-W)=f.N_1+f.N_2>=1.

Equation (6) puts every point of B strictly below f.V in f-projection.
Every point of A lies at or above that value. Thus the two actual
closed units A and B cannot touch, contradicting their original
positive AB edge. This proves the whole uniform theorem, including
both equality endpoints of (1).

The side-normal input used above is
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, SHA256
b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207.
It is purely physical; no force equation at either private neighbor
is a hidden premise of this kernel.

## 4. Entire original b2 C4 AP opposite-transmitter load row

Keep the original shared-root graph

    triangle H-A-B-H, genuine leaf A-L_A,
    C4 H-P-K-Q-H, genuine leaf P-L_P.

These are eight distinct positive bodies; the ninth actual unit stays
in the same packing with no imposed force or boundary role. The true
degrees are H4, A3, P3, and B2,K2,Q2. Suppose K has positive total
circle load and Q has zero total circle load. Every physical circle
mask of these bodies, including physical circle corners with zero
weight at Q, is retained.

The complete origin theorem
ROOTED_DECORATED_TRIANGLE_AND_PRIVATE_LEAF_FOUR_BLOCK_ORIGIN_STRUCTURE.md,
SHA256 e77c19d2afefb96f4919788d5d69f987377d7b90b299037c0c35a1c717cd8968,
gives O in int H for this exact original graph, before removing any
circle force. B is positively loaded: a true unloaded B2 transmitter
cannot have its touching endpoints H,A. Thus B is physically boundary.
Both real leaves are S with d>1, and the actual A and P are physically
clear. H itself is physically clear because it contains O and every
one of its points has radius at most sqrt(2)<R.

Apply precisely Sections1--5 of

    ROOTED_ROOT_ADJACENT_LEAF_CHANNEL_SMALL_CORNER_EXCLUSION.md
    SHA256 7df1b687bc1a33cb10fdc171857773e9ef7a9b2968232cd146e4422a6d5cbac2,

with its X=P, U=K, V=Q. Its complete prerequisite is

    ROOTED_ORIGIN_ROOT_ADJACENT_LEAF_CHANNEL_RADIAL_TIP_REDUCTION.md
    SHA256 8d40238d0dad6a0f58534e26592d566c728188fe0820c5bb94aaf41a411e5d7f.

Those local sections allow arbitrary other original H forces and
give an actual H vertex V_0 with

    |V_0|<=sqrt(2)*epsilon<1/40,

such that the unchanged full two-edge C4 pair sum M_Q at H is strictly
outward in both actual own axes at V_0. They cover the original K2
parallel and nonparallel cases, its complete physical circle masks,
all real Q2 means, the genuine P3 feature domain and the canonical
unloaded-body motion before drawing this conclusion. Their separately
reviewed local theorem does not use a genuine terminal Q0.

Only now use the complete actual H equation. There are precisely the
two original block branches, no H leaf and no circle load:

    M_T+M_Q=0.

Therefore M_T is strictly inward in both V_0 own axes. Sections1--3
give the contradiction. This excludes the entire stated original
K-loaded/Q-unloaded row, including every original radial leaf slider,
corner-weight endpoint and all nine physical units.

## 5. Exact dependency and remaining-domain limits

The channel source's Section6 concerned a different caller with a
genuine terminal four-block. Its two missing historical terminal-block
sources are not used anywhere here. The full new caller instead uses
the currently available e77c19d2 origin theorem and the fully proved
decorated-triangle kernel in Sections1--3 above. In particular no
unread terminal-block theorem is a publication dependency of this exit.

The two complete local channel reviews are

* REVIEW_ORIGIN_ADJACENT_CHANNEL_RADIAL_TIP_C6_2026_10_27.md,
  SHA256 883ca4c5badbfc7c8c1aa724268cb9bd1baae2a31e882526ff6a7c2e5d605a15;
* REVIEW_ROOT_ADJACENT_LEAF_CHANNEL_SMALL_CORNER_GLOBAL_2026_10_27.md,
  SHA256 0ff5113e6ae018b0d7a185b017173d4e4b7063fa42eec5f40cdd12c19c092416.

The exact accepted 66=63+3 join remains
ROOTED_C2_34_TWO_BRIDGES_THREE_DOMAIN_REDUCTION.md, SHA256
8918c0e3e77cbc9f90899a29ebd2233c87858a00ecf1e0ffca2a684ccdd5cb0a.
The present result refines one original load row inside its C4 AP
domain. It does not remove that whole AP domain, the hub-diamond AP
domain, or the page-diamond AP domain. A C4 transmitter at K instead
of Q and the both-loaded C4 masks remain separate original obligations.

No original H force was deleted to obtain a lower-degree equation.
No circle resultant was split, no physical contact became a new
positive edge, and no application mean moved. No Lean compilation,
CI, workflow, remote write or shared-ledger mutation is used.
