# A forward unit-width barrier excludes a degree-two third neighbor in the complete single-axis hub domain

Date: October 29, 2026 UTC. Author: pentagon continuation.

**Status: complete proposed general support theorem, complete all-owner
local true-degree-two exclusion, and five literal D02 feature callers,
frozen for separate full independent review.** Every original positive
force, actual support, full shared-side mean, physical circle mask and
individual zero coefficient is retained. The general chain theorem has
no circle, endpoint-degree or endpoint-load hypothesis. The local hub
application uses the complete new all-owner theorem b1fbc607 at its
arbitrary-contained-T scope.

The new low-load callers are the whole same single-axis feature in
D02.L014 and D02.L0145. The same local theorem also applies to that
whole feature in L0134,L0135,L01345. It does not declare any of these
entire original rows closed. All nine actual units and all seven
positive edges remain in every original caller.

## 1. Radius-free forward support-width theorem for an actual unloaded chain

Fix a unit vector n in the actual Euclidean plane. Let

    A,T_1,...,T_m,C, m>=1,

be distinct actual closed unit squares with pairwise disjoint open
interiors and their original positive contacts along that displayed
path. Retain the original physical force and torque equations, normals,
applications and complete shared means. Suppose each actual T_i is
genuinely unloaded true degree two, with exactly its predecessor and
successor as positive neighbors. The degrees, circle loads, other
forces and physical circle masks of A and C are arbitrary.

Let the original A-to-T_1 normal be n and let P be its original actual
application or full shared mean. If the endpoint C is contained in the
closed half-plane

    n.z<=M,

then

    n.P+(m+1)<=M.                                   (1)

In particular, if C is contained in a disk D_R(O) about the unchanged
origin, then n.z<=R throughout C, and

    n.P<=R-(m+1).                                   (2)

The containing-circle version needs no physical boundary contact or
circle force at C. A and C are not made degree two. The original
unloaded transmitters may have zero-weight physical circle corners;
their unchanged full physical masks are allowed.

### 1.1. Every original force direction has the required sign

At T_1, the original normal pointing to A is -n. Its full circle load
is zero and its entire positive neighborhood is A,T_2, or A,C when
m=1. Write lambda>0 for the incoming pair magnitude, nu>0 for the
other magnitude and q for the original unit normal to the successor.
The complete true T_1 force equation is

    -lambda*n+nu*q=0.

Taking norms gives nu=lambda, and therefore q=n. No normal is
reselected. Inductively the same complete force equation at every
true unloaded T_i gives the same original outgoing direction n and
the same magnitude. The torque equations remain original; they are
not needed for this projection bound and have not been replaced.

Thus every actual path contact has direction n from its predecessor
to its successor. This is a consequence of the full equations at
the genuine transmitters, not an assumed contraction of the path.

### 1.2. Both actual support signs and all original means

At the first contact, P is a minimum-n support point of T_1, so

    min_(z in T_1) n.z=n.P.

At a T_i-to-T_(i+1) contact, its unchanged original application is
simultaneously a maximum-n point of T_i and a minimum-n point of
T_(i+1). The same is true with C in the last step. Thus the support
levels match in the original forward order:

    max_(z in T_i) n.z=min_(z in T_(i+1)) n.z,
    max_(z in T_m) n.z=min_(z in C) n.z.             (3)

For a positive shared segment, every point of that segment, including
both endpoints and the original mean, has exactly the same n
projection. Consequently no mean value is chosen in (3). For a
singleton, it is its actual fixed point. These cover every physical
contact set under the retained support normals.

Every actual unit square K has n-width at least one. If e,f are its
actual orthonormal axes, that width is

    w_n(K)=|n.e|+|n.f|>=sqrt((n.e)^2+(n.f)^2)=1.     (4)

Its equality case is included; no tilted-square strictness is used.
Summing the actual support differences in (3), then adding the
endpoint C width, gives the exact identity and inequality

    max_(z in C) n.z
       =n.P+sum_(i=1)^m w_n(T_i)+w_n(C)
       >=n.P+(m+1).                                (5)

The given endpoint half-plane bounds the left side by M, proving
(1). The disk specialization follows from n being unit. This proves
the whole general theorem for every actual chain length m>=1.

It is essential that the initial point is the actual minimum-n
support of T_1, and that the last original normal points from T_m
to C. Reversing either of those support signs would not give (5).
Both signs above were derived from the original positive pair
normals, not inferred from a picture of a transmitter.

### 1.3. One actual transmitter is enough for the local barrier

The m=1 consequence is especially useful:

    n.P>R-2                                        (6)

is incompatible with any genuine unloaded degree-two neighbor T
whose actual incoming normal is n, whose actual incoming application
is P, and whose actual other neighbor C is another contained unit.
No condition on C's degree, load, physical boundary status or force
equation is required. The full unit T is retained between A and C.

## 2. The complete all-owner single-axis hub domain

Now put Q=1105/256 and retain the unchanged disk and complete original
physical data, with

    2<R<=sqrt(Q).                                      (7)

Let U,V,W,T be distinct actual contained units satisfying exactly the
local premises of b1fbc607:

* U is unloaded true degree three with entire positive neighborhood
  V,W,T;
* V is positively loaded true degree two with entire positive
  neighborhood U,W;
* W is physical boundary, at arbitrary true degree, circle load and
  other original forces;
* the original UW normal is U-owned and the original UV normal is
  not U-owned;
* the common certificate retains the strict physical point-normal
  convention and the already compatible fixed-tip selection, chosen
  once before multiplier extraction.

T has arbitrary original degree, load, physical circle mask and normal
owner at entry. No T boundary, endpoint-concurrence, path, or
completion-pocket premise is imposed.

**Theorem.** Such a T must have true positive degree at least three.
In particular the entire stated all-owner feature is impossible if
the original T has true degree two, regardless of its original total
circle load or physical circle mask.

This is a complete exclusion of the stated true-T2 local domain,
not an inference that some forces could be deleted to meet it. The
arbitrary-degree statement is only the necessary degree lower bound
printed above; it is not a claim that every higher-degree domain has
already been excluded.

## 3. The full all-owner input supplies actual geometry and physical clearance

The complete b1fbc607 theorem was proved for an arbitrary contained
actual T. Its whole incoming-free, shared-UW, unique-V and VW-owner
cover has already been printed in that source. None of those domains
is omitted here. Its necessary surviving chart is

    U=[L-1,L]x[H-1,H],
    n_UV=(b,a), a,b>0,a^2+b^2=1,
    1/2<r<=a<=b,
    63/100<L<D<61/60,
    7/20<H<3/4,
    D=sqrt(R^2-1/4)-1.

The actual V is the physical-two unit in its real own frame, with
the full original nonnegative circle-weight interval retained. The
input conclusion is not obtained by treating a physical-two unit
with one zero coefficient as unique.

The actual UW physical contact is a singleton; keep its original
point in the enlarged complete side interval

    S=(L-1+p,H), 0<=p<=1.                           (8)

The original UT normal is strictly Southwest and its actual
application is the original U vertex

    P_T=(L-1,H-1).                                  (9)

The same theorem proves

    |P_T|^2<13369/40000<12/35<(2-sqrt(2))^2

and therefore proves that the whole actual T is contained in
int(D_R). This is physical circle clearance, derived before any
assumption on its degree or load. In particular T has no physical
circle corner and its entire circle contribution to its original
force equation is zero.

This input is the complete arbitrary-contained-T theorem b1fbc607.
It is not a boundary-T matching theorem or a local statement whose
proof secretly requires an immediate boundary neighbor. Its actual
clearance and coordinate conclusions are used at their printed
scopes, with no smaller substitute component.

## 4. The original full U3 puts the forward normal beyond the two-unit support threshold

Write the unchanged original UT unit normal as

    n=n_UT=(-alpha,-beta), alpha,beta>0,
    alpha^2+beta^2=1.

Let mu,omega,tau>0 be the actual original UV,UW,UT magnitudes. The
entire original U3 force and its torque about P_T are

    mu*(b,a)+omega*North+tau*(-alpha,-beta)=0,
    mu*(a-b)+omega*p=0.                             (10)

Thus

    tau*alpha=mu*b,
    tau*beta=mu*a+omega,
    mu*b=mu*a+omega*p<=mu*a+omega.

Every quantity divided out is strictly positive. It follows that

    beta>=alpha>0,
    beta>=1/sqrt(2)>7/10.                           (11)

The entire p interval in (8) is included: p=0 and p=1 do not cause
a division by p or an omitted normal endpoint. No original normal
at U or T has been changed.

At the same actual incoming T point (9),

    n.P_T=alpha*(1-L)+beta*(1-H)
           >-alpha/60+beta/4
           >=7*beta/30
           >49/300.                                (12)

The first strict inequality uses the whole original coordinate bounds
L<61/60 and H<3/4, with alpha,beta>0. The second uses the actual
coupled beta>=alpha, not independent component estimates.

The original upper radius gives R<21/10, since

    (21/10)^2-Q=599/6400>0.

Consequently

    n.P_T+2>649/300>21/10>R,                        (13)

where 649/300-21/10=19/300. Thus the actual original incoming port
violates the complete one-transmitter bound (6), with a strict
uniform reserve throughout the closed upper-radius endpoint.

## 5. Full true-T2 force and support prove the local contradiction

Suppose now that the actual original T has true positive degree two.
It has exactly its original neighbor U and a distinct actual other
neighbor C. The whole T is physically circle-clear by Section 3, so
its complete original circle force is zero. This includes every
possible initial T physical-mask and coefficient alternative: a
physical boundary T already contradicted the input theorem, while
a zero load was never used as a substitute for physical clearance.

Let lambda>0 be the original UT magnitude, nu>0 the original TC
magnitude and m the original T-to-C unit normal. Its entire true
force equation is

    -lambda*n+nu*m=0.

Therefore nu=lambda and m=n, with the exact forward sign proved in
Section 1. The original incoming point P_T is a minimum-n support
of T. The original TC application, including its full side mean
when appropriate, is a maximum-n support of T and a minimum-n
support of C. Thus

    max_(z in C) n.z
      =n.P_T+w_n(T)+w_n(C)
      >=n.P_T+2>R.

But C is the original actual contained unit, so n.z<=|z|<=R on C.
This is impossible. No true C degree, circle load, force, physical
boundary contact, original mean, or extra contact was altered.
The original U-to-C contact was not invented: the actual positive
path U--T--C and both original support levels are used in full.

If T had true positive degree one, its physical clearance and its
single positive UT force would make its full force equation a
nonzero vector equal to zero. This is also impossible. Since UT
is a positive edge, T has degree at least one initially. Therefore
every surviving general configuration must have true degree at
least three, proving the theorem in Section 2 and the complete
true-T2 local exclusion.

## 6. All exact D02 load rows with a load-forced physical W

The original short-chord graph has exactly the positive edges

    01,12,23,34,45,50,02.

Retain all six actual core units, these seven original edges and
all three arbitrary actual completion squares. The true positive
degrees in order 0,...,5 are

    (3,2,3,2,2,2).

For the common representative put

    U=2, V=1, W=0, T=3, C=4.                       (14)

Then the actual triangle is 2--1--0--2, the incoming third path is
the genuine 2--3--4 path, and the full positive neighborhoods are

    U:{1,0,3}, V:{2,0}, W:{1,2,5},
    T:{2,4}, C:{3,5}, 5:{4,0}.

The complete original graph/load cover gives the following five
representatives with V1 and W0 positively loaded and U2 unloaded.
They are exactly its load-forced matches for (14).

| Original entire load row | Positive circle-load set | Actual T3 load | Actual C4 load | Actual body5 load | Covered original feature |
| --- | --- | --- | --- | --- | --- |
| M6.B6.HEXAGON.D02.L014 | {0,1,4} | zero | positive | zero | n_20 U-owned and n_21 not U-owned |
| M6.B6.HEXAGON.D02.L0134 | {0,1,3,4} | positive | positive | zero | n_20 U-owned and n_21 not U-owned |
| M6.B6.HEXAGON.D02.L0135 | {0,1,3,5} | positive | zero | positive | n_20 U-owned and n_21 not U-owned |
| M6.B6.HEXAGON.D02.L0145 | {0,1,4,5} | zero | positive | positive | n_20 U-owned and n_21 not U-owned |
| M6.B6.HEXAGON.D02.L01345 | {0,1,3,4,5} | positive | positive | positive | n_20 U-owned and n_21 not U-owned |

In all five rows the true T degree is exactly two, without deleting
any force. W's actual three positive forces remain; the local
theorem requires only its load-forced physical boundary status.
V is truly loaded degree two, not a higher-degree surrogate. Every
row supplies the exact whole original U3.

The original declared closed radius window is

    79/40<=R<=sqrt(1105)/16.

Apply the complete same-nine lower theorem to all nine actual units.
It excludes every R<=2, including R=2, before invoking (7). The
upper endpoint remains included because every strict comparison
in (12)--(13) has its displayed exact reserve. No isolated component
is treated as a nine-square packing.

For each row, assume the covered original feature in the last table
column. It supplies exactly the U-owned UW and non-U-owned UV
premises of Section 2 in the common selected certificate. The local
true-T2 theorem now excludes that entire feature.

In the three rows where T3 has positive load, the input's actual
T-circle-clear conclusion already contradicts that positive load.
In L014 and L0145, T3 is genuinely unloaded true degree two; the
new forward-width contradiction uses its real other neighbor C4.
Neither the original 2--3 contact nor the 3--4 contact is replaced
by a false 2--4 edge. The complete mean on 3--4, all physical T/C
masks and all actual diagonal or side transmitter widths are
retained by the uniform width inequality (4).

In L014 the other actual unloaded path 0--5--4 remains unchanged.
In L0145, body5 is positively loaded instead. Both original exterior
pockets and the entire central region remain present with all three
extra squares arbitrary. This proof does not need to assign an
extra to either pocket, prove a spurious immediate boundary edge,
or impose a new force equation at W0 or C4.

Thus the theorem closes the **whole stated single-axis feature** in
each of the five existing rows, including the complete new low-load
features in L014 and L0145. It is not a whole-row closure in any of
them. No new fine ID, original flag, count or parent conclusion is
created by this source.

## 7. Every reflected actual choice and the exact unmapped rows

The graph-preserving reflection i -> 2-i modulo 6 exchanges its
two degree-three hubs and fixes the triangle tip1 and body4. Under
that reflection the same actual local substitution is

    U=0, V=1, W=2, T=5, C=4.                       (15)

Its exact original neighborhoods are U:{1,5,2}, V:{0,2},
W:{1,3,0}, T:{4,0}, C:{3,5}. The covered reflected feature is

    n_02 U-owned and n_01 not U-owned.

The five displayed load sets reflect, respectively, to

    {1,2,4},
    {1,2,4,5},
    {1,2,3,5},
    {1,2,3,4},
    {1,2,3,4,5}.                                   (16)

These are the same original five load orbits, not new rows. Every
actual square, contact normal, mean, circle coefficient and original
support point is reflected together. The proof maps to the real
0--5--4 path in (15), with the original degree-two body5 retained.
Any whole-configuration relabeling that places the short chord at
02 is covered by first making that graph identification and then
using (14) or (15).

The other three representatives in the original D02 load table are

    L134, L135, L1345.

In each, both degree-three triangle hubs0 and2 have zero total
circle load. That does not establish physical boundary contact at
either hub. The present theorem therefore gives only the conditional
local feature exclusion when the chosen W is independently proved
physically boundary in one of those rows. It does not claim a
load-forced application there and does not infer physical clearance
from their zero coefficients.

Within the exact D02 graph, the only triangle is012, whose only
degree-two tip is1. Thus (14) and (15) exhaust the true U3/V2
triangle choices. There is no omitted load-forced physical-W
choice obtained by exchanging V with a degree-three hub. This
establishes the complete original mapping scope claimed here.

## 8. Frozen inputs, verification boundary and independence

The full b1fbc607 all-owner theorem was read at its exact frozen
bytes. Its general arbitrary-T conclusion, including actual whole
T clearance, is the operative input. Its complete new source and
separate independent audit remain distinct obligations; this
extension is not offered as a review of it or of its root-authored
radial input f9e569.

The new forward support theorem is proved entirely in Section 1.
The new full U3 normal comparison and its actual projection margin
are Sections 4--5. These use no boundary-T diameter argument as
a hidden premise of the width transmission. The disk is used only
as the actual endpoint support upper bound.

| Complete frozen input | SHA-256 | Exact role |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full force/torque conventions, opposite pair normals, actual supports and all shared means |
| ONE_HUB_AXIS_EXTERNAL_TIP_ALL_OWNER_NEAR_ORIGIN_AND_D02_FOUR_LOAD_FEATURES.md | b1fbc607baef6e3d24fc00b4dd52d1a7f91efa1ab022379ad79ebfb2bd66f6d3 | Complete all-owner arbitrary-contained-T local geometry and physical clearance, with every initial contact/mask alternative |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | All exact D02 graph/load representatives, true degrees and original symmetry images |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Only the complete same-nine strict R>2 entry in every original caller |

Every direct pin has been checked. The physical input and the complete
graph/load and lower-window manuscripts were read; their accepted
recursive component reviews retain their existing scopes. No new
recursive audit of the whole analytic measure chain is claimed here.
The current theorem requires its own separate full independent review.
No reviewer supplied discovery for the forward-width extension.

Exact rational checks confirm (21/10)^2-Q=599/6400, the forward
reserve 19/300, and the half-normal comparison 1/2-(7/10)^2=1/100.
These are transcription checks of a continuous support proof, not a
sampled set of poses, a finite normal grid, or numerical optimization.

No original positive edge, force, actual square, true degree, physical
circle corner, individual zero coefficient, original application or
mean is changed. No post-extraction normal selection, false endpoint
degree, contracted contact, Lean/Lake operation, build, CI/workflow,
remote write, commit, original flag or metadata mutation is used.
