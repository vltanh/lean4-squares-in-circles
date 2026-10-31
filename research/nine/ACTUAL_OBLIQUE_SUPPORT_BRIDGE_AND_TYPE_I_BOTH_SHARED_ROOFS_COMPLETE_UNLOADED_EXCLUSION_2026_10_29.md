# Oblique support gaps and the complete Type I two-shared-roof unloaded-return exclusion

Date: October 29, 2026 UTC. Authors: root continuation, with the original
two-shared-roof chart and proposed application supplied by roofs.

**Status: complete proposed hand theorem, frozen for separate full
independent review.** A radius-free support-projection theorem applies
to arbitrary actual unit squares, all support owners and every original
side mean. It excludes every actual one-unit bridge when the displayed
oblique support gap exceeds that unit's full width.

Its Type I application excludes the entire domain in which both roof
interfaces AV and DV have positive physical shared length and the
original return N is unloaded true2. This is a whole feature of
D02.L135, with all original roof and hub means and all nine squares
retained. The point-only AD alternative is excluded for either load
of N, without any N force equation. The positive-shared AD alternative
with loaded N in D02.L1345 remains outside that closure.

## 1. A whole-unit oblique support theorem, including every side mean

Let S be an actual unit square, n and d unit vectors, and Q any actual
minimum-n support point of S. Q can be a strict vertex, either endpoint
of a support side, or any original mean on that whole side. If

    n.d>=0,

then every X in the entire actual S satisfies

    d.X>=d.Q-|det(n,d)|.                         (1)

Here the determinant is in either fixed oriented orthonormal chart;
its absolute value makes the choice of orientation immaterial.

For a strict vertex support, write the actual square as

    S=Q+[0,1]u+[0,1]v,
    |u|=|v|=1, u.v=0, n.u>0, n.v>0.

The condition n.d>=0 makes it impossible that both d.u and d.v
are negative: their positive n-coordinate combination would give
n.d<0. Thus at most one own edge can give a negative d increment.
For either edge u, its decomposition along n and a unit perpendicular
vector gives

    d.u=(n.u)(n.d)+epsilon*(n.v)*det(n,d)
         >=-|det(n,d)|,

with an appropriate sign epsilon. The corresponding identity for v
has the same lower bound. Since at most one increment is negative,
the minimum over both full edge intervals is at least the right side
of (1). The proof includes the possibility n.d=0 or an edge with
zero d increment.

For an owned side support, use its actual own unit tangent u and
inward unit normal n to write

    S=Q+[-lambda,1-lambda]u+[0,1]n,
    0<=lambda<=1.

The normal term has nonnegative d increment. The entire tangent
interval can decrease d by at most |d.u|=|det(n,d)|. This proves
(1) for every original side mean and both endpoints, without replacing
the original lambda. These two support cases exhaust the square.

Now let two actual squares B,C have minimum support points Q_B,Q_C
in their respective actual inward unit directions n_B,n_C. Suppose

    n_B.d>=0, n_C.d<=0.

Apply (1) to B with d, and to C with -d. Their whole sets satisfy

    min_B d-max_C d
      >=d.(Q_B-Q_C)-|det(n_B,d)|-|det(n_C,d)|.   (2)

Every actual unit square N, in every frame, has total d-width at most
sqrt(2): its width is |d.u_N|+|d.v_N|, bounded by Cauchy--Schwarz.
Consequently, if

    d.(Q_B-Q_C)
       >sqrt(2)+|det(n_B,d)|+|det(n_C,d)|,       (3)

no actual unit N can physically touch both B and C. Two such contacts
would be actual points of N whose d difference exceeds its whole
width. All weak physical contacts, support ties and side-mean endpoints
are included. No stress equation, radius, load, degree, circle mask,
owner selection or diagonal-avoidance assumption is used in (1)--(3).

## 2. Exact Type I entry and every physical shared placement

Keep the actual nine units in the original containing disk about O.
Retain every original positive force, selected normal, full application
or side mean, physical circle corner and individual coefficient. The
original complete local stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3, and V is loaded true2 with one unique PHYSICAL
circle corner. The actual return path is B--N--C. All three additional
physical units remain. No complete B,C,N star is shortened.

Use the canonical Type I chart from the complete three-port source:

    V=[a-1,a] x [b-1,b], Z=(a,b), a,b>1/2,
    P0=(a-1,b-1),
    R=P0+w*North, P=P0+h*East,
    0<=h,w<=1, (h,w)!=(0,0),
    mu=kappa*a>0, nu=kappa*b>0,
    mu*(1-w)=nu*(1-h).                          (4)

The unchanged V roof normals incoming from A,D are East and North.
Every original roof mean, including a side endpoint, remains in (4).
The last equality is the complete original V torque, not an imposed
relation between freely chosen means.

Assume now that BOTH actual AV and DV intersections have positive
physical shared length. Their real frames are then parallel to V.
With P0=(X,Y), their complete actual placements are necessarily

    A=[X-1,X] x [Y+delta_A,Y+delta_A+1],
    D=[X+delta_D,X+delta_D+1] x [Y-1,Y],
    -1<delta_A,delta_D<1.                       (5)

The strict shift intervals express positive physical overlap with V.
The original means in (4) also belong to their actual overlaps; no
larger interval is used to infer physical realizability.

For A,D to touch, the two horizontal intervals in (5) must intersect,
which requires delta_D<=0. Their vertical intervals must intersect,
which requires delta_A<=0. If both inequalities were strict, the
horizontal and vertical intersections would both have positive length,
so A,D would have overlapping open interiors. Hence exactly the full
following cover remains:

    delta_A=0, delta_D=-ell with 0<ell<1;
    delta_D=0, delta_A=-ell with 0<ell<1;
    delta_A=delta_D=0.                          (6)

In either first case AD is physically shared, with positive length
ell. In the last it is the single actual common vertex P0. There is
no omitted positive-overlap endpoint or additional placement.

## 3. Point-only AD is impossible for every actual bridge load

In the last case of (6), A and D meet only at P0. The original strict
point-contact convention gives the unchanged A-to-D separating normal

    g=u*East-v*North, u,v>0, u^2+v^2=1.          (7)

Both coefficients must be strict: an axis direction is not strict at
both vertices of this point-only interface. This uses the existing
physical normal convention, without selecting a new g or invoking
the later conditional nonfree-AD reduction.

Let rho>0 be the original AD magnitude. The complete A,D forces give
their unchanged exterior vectors

    F_B=-(mu+rho*u)*East+rho*v*North,
    F_C=rho*u*East-(nu+rho*v)*North.             (8)

They are respectively strict Northwest and strict Southeast. Their
actual maximum-support applications on A,D are therefore uniquely

    Q_B=(X-1,Y+1), Q_C=(X+1,Y-1).               (9)

At B,C these same original applications are minimum supports in the
directions of F_B,F_C. Write their normalized directions as

    n_B=(-a_B,b_B), n_C=(a_C,-b_C),
    a_B,b_B,a_C,b_C>0,
    a_B^2+b_B^2=a_C^2+b_C^2=1.

Choose the single fixed comparison direction

    d=(-East+North)/sqrt(2).

Then n_B.d>0, n_C.d<0, and

    d.(Q_B-Q_C)=2*sqrt(2),
    |det(n_B,d)|=|a_B-b_B|/sqrt(2)<1/sqrt(2),
    |det(n_C,d)|=|a_C-b_C|/sqrt(2)<1/sqrt(2).     (10)

The strict inequalities follow from (a_B-b_B)^2=1-2*a_B*b_B<1,
and likewise for C. Thus the right side of (2) is strictly larger
than sqrt(2). The general theorem excludes ANY actual unit N touching
both B and C, regardless of its original load, degree or orientation.

This covers the entire point-only AD alternative in both original
D02 rows. No N force equation, radius bound, circle-clearance claim,
completion allocation or diagonal-avoidance input was needed.

## 4. Positive shared AD: every original mean and full hub moment

Take the first case of (6): delta_A=0 and delta_D=-ell, 0<ell<1.
The full actual squares and original applications are

    A=[X-1,X] x [Y,Y+1],
    D=[X-ell,X+1-ell] x [Y-1,Y],
    R=(X,Y+w), P=(X+h,Y),
    W=(X-z,Y), 0<=z<=ell.                       (11)

W is the original full AD mean on its positive physical overlap.
The original normal A-to-D is South, fixed by that overlap. Neither
z nor h nor w is replaced by a convenient contact coordinate.

The complete original A force gives

    F_B=-mu*East+rho*North,
    Q_B=(X-1,Y+1).                              (12)

Both components are strict, so Q_B is its actual unique application
on A. The complete A torque about P0 is

    -mu*w+rho*z+mu-rho=0,
    rho*(1-z)=mu*(1-w)=nu*(1-h).                (13)

The last equality is the original V moment (4). In particular no
equation from either full star has been suppressed.

At D, the full force and complete torque give

    F_C=-(nu+rho)*North,
    Q_C=(X+q,Y-1),
    nu*h-rho*z-(nu+rho)*q=0.                    (14)

Here q is the original full DC side mean, including any actual side
endpoint. Combining (13),(14) gives exactly

    q=(nu-rho)/(nu+rho)=1-2*tau,
    tau=rho/(nu+rho), 0<tau<1.                  (15)

This expression is derived from both full moments; it is not a
reselection of that mean. Its original membership in D's bottom
side, -ell<=q<=1-ell, remains among the physical hypotheses.

Thus the actual exterior supports have the complete difference

    Q_B-Q_C=-2*(1-tau)*East+2*North.             (16)

The whole B minimum-support direction is strictly Northwest by (12).
The whole C minimum-support direction is South by (14). All original
exterior degrees, loads, side owners and physical circle masks remain.

## 5. The whole shared-AD feature with unloaded N

Assume now the original N is unloaded true2, with precisely its original
positive contacts BN,NC. Retain the same initial finite diagonal
avoidance from PHYSICAL_BODY_GRAPH_UNCROSSING.md and its original
preservation through the accepted stress construction. The simultaneous
prior selection compatibility is conditional as before; no new normal
is selected after multiplier extraction.

The complete generic theorem in

    VERTICALLY_SEPARATED_RETURN_SUPPORTS_NO_UNLOADED_TRUE_TWO_BRIDGE_AND_SHARED_D_L135_EXCLUSION_2026_10_29.md

requires: an actual B minimum with strictly negative horizontal and
strictly positive vertical inward components; an actual C minimum in
direction South; nonpositive horizontal support difference; vertical
support difference at least two; and the full actual unloaded true2 N
with the retained diagonal avoidance. Equations (12),(14),(16) supply
each support hypothesis literally, for every original tau in (0,1).

That theorem uses the entire B downward reach to make the actual N
application gap exceed one. The full unloaded star then forces a
diagonal transmitter. The same original diagonal-avoidance convention
gives both endpoint owners, and the two complete signs of the channel
direction contradict the original support data. All side means and
ties are part of its accepted proof. No degree or load equation at
B,C is needed for its general statement.

It therefore excludes the entire first case of (6) with unloaded N,
including every original ell,z,h,w, positive magnitude and DC mean.
The second case of (6) follows by exchanging the two actual own axes
of V and transporting the entire data A<->D, B<->C, mu<->nu,
h<->w. This is a reflection of the full physical configuration and
stars. The actual N and all its original equations are retained.
The original D02 load sets are invariant under this graph reflection.

Together with Section 3, this exhausts ALL of (6). Therefore no Type I
feature with both physically shared roofs survives when the actual
return N is unloaded true2.

## 6. Literal original loads and exact remaining scope

The original callers retain

    A=0,V=1,D=2,C=3,N=4,B=5,
    rim A--V--D--C--N--B--A, chord AD.

A,D remain unloaded true3; V,B,C remain loaded true2. In L135 the
actual N=4 is unloaded true2, exactly as required in Section 5. All
three additional actual squares remain in the same packing. Hence
the ENTIRE two-physically-shared-roof Type I feature of D02.L135 is
excluded, not merely selected means or the symmetric radial position.

In L1345, N=4 has positive total circle load and must retain that
full loaded star. Section 3 still excludes its whole point-only AD
alternative, because that section uses no N equation. Section 5 does
not apply to its positive-shared AD alternative, which remains open.

Type I with one or both genuinely singleton roof contacts is separate.
Types II/III, physical-two V, all full D02 rows and the unrestricted
n=9 theorem receive no additional whole-row closure credit here. The
complete Type III theorem remains independently accepted at its own
scope. All original flag arrays are unchanged.

## 7. Direct sources and verification boundary

The complete generic bridge source and three-port classification were
read, together with their actual owner, diagonal-avoidance, full-star
and original graph/load inputs. Exact operative source pins are recorded
with the separate review and adoption. The principal inputs are:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIQUE_CIRCLE_TRIANGLE_TIP_THREE_PORT_TYPES_AND_HUB_INTERFACE_OWNER_COVER_2026_10_29.md | 8266220efbb8ce769de90a90e27e86997400575d0b8bb80f5843af38ca447073 | Original Type I full V chart and force/torque system |
| VERTICALLY_SEPARATED_RETURN_SUPPORTS_NO_UNLOADED_TRUE_TWO_BRIDGE_AND_SHARED_D_L135_EXCLUSION_2026_10_29.md | 112510ba9d1ec141443b19bbcf4212879a628e2eab083335c3252640f32f36bd | Complete radius-free unloaded true2 bridge theorem, with original diagonal avoidance |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Same prior avoidance convention and preservation |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force and torque, actual shared means and strict point-normal convention |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Literal original graph, both load sets, true degrees and all three extra units |

The new oblique projection theorem and the point-only application need
no selection at all. Only the unloaded-bridge application uses the
already stated conditional initial diagonal avoidance. No new nonfree
AD selector, post-extraction perturbation or normal change is used.

Every argument is exact on its full continuous domain. No numerical
pose search, angle mesh, new packing certificate, force deletion, mean
replacement, mask relabeling, omitted unit, false loaded-transmitter
equation, Lean/Lake build, CI or merge was used. This new source must
receive a complete independent review before adoption or publication.
