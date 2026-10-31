# Vertically separated return supports have no unloaded true-two bridge

Date: October 29, 2026 UTC. Author: capacity continuation.

**Status: complete proposed radius-free hand theorem and entire original
shared-D L135 feature exclusion, frozen for full independent review.**
The theorem below excludes a real unloaded true-two bridge between two
actual return squares from two support inequalities. It permits arbitrary
degrees, loads, masks and means at those return squares.

In the entire original shared D-direction Type III row, the unchanged
A/D stars give precisely these inequalities, at every original angle
and every original shared mean. Thus the whole shared-D feature of
D02.L135 is excluded. No outer-angle reduction, circle-radius estimate
or completion-capacity premise is needed for this unloaded-N result.

The theorem explicitly retains the original common diagonal-avoidance
convention. It does not select or change a normal of an extracted
certificate, and it does not assert that a loaded true-two bridge
satisfies an unloaded equation.

## 1. A general actual-support theorem

Let B,C,N be distinct actual unit squares with disjoint open interiors.
Fix an oriented orthonormal frame (h,e). Suppose B contains an actual
minimum-support point or full side mean Q_B in inward unit direction

    f=-a h+b e, a,b>0, a^2+b^2=1.

Suppose C has an actual minimum-support point or full side mean Q_C
in inward direction -e. Require

    (Q_B-Q_C).h<=0,
    (Q_B-Q_C).e>=2.                              (1)

Retain the complete original stress at N: it has zero total circle
load and exactly two positive body-pair forces, toward B and C.
Both original magnitudes are positive, both applications are actual
common points, and its complete force and torque equations hold.

Finally, retain the original finite diagonal avoidance:

> At every physical point-only vertex/vertex contact, the unchanged
> selected strict common normal is not a diagonal direction of either
> incident unit.

This is exactly the existing optional choice in Sections 2,4,7 of

    PHYSICAL_BODY_GRAPH_UNCROSSING.md
    SHA256 bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe.

It is imposed in the initial common selection, before multipliers,
and is preserved by the source's uncrossing, thinning and aggregation.
Here it is an explicit premise on the same original certificate.

**Support-bridge theorem.** These hypotheses are impossible.

No boundary premise or equation at B,C is needed. Their support
points can be strict vertices, side points, genuine shared means or
either endpoint. Additional physical zero-weight contacts are allowed.
The theorem concerns the true complete two-force star at the actual N.

## 2. Whole B is strictly more than one unit above whole C

The following elementary support-span estimate keeps all original
side means:

    min_B e >= Q_B.e-a.                           (2)

At a strict minimizing vertex, let u1,u2 be the two inward unit
side directions. They have nonnegative f components. At most
one can have negative e component, because

    b=f.e=(f.u1)(u1.e)+(f.u2)(u2.e)>0.

For a downward inward edge w with w.e=-r<0, the support
condition gives

    -a(w.h)-br>=0,
    w.h<=-(b/a)r.

Its unit length then gives

    1=(w.h)^2+r^2>=r^2/a^2,
    r<=a.

The total possible downward displacement from Q_B is therefore
at most a, proving (2).

If the minimum is a side rather than a unique vertex, f is its
inward own normal, with positive e component b. Movement into
the square along f cannot lower e. Movement in either direction
along the minimizing side has e component of absolute magnitude
a and length at most one from any original side point or mean.
This proves (2) on the entire closed support face, including its
two endpoints and every zero own-component tie.

Because C has minimum support in -e,

    max_C e=Q_C.e.

Equations (1),(2) and a<1 consequently give

    min_B e-max_C e>=2-a>1.                       (3)

Let T be the actual N--B application and U the actual N--C
application. Since T belongs to B and U to C,

    (T-U).e>1.                                   (4)

This is a statement about the unchanged whole units and their
actual original applications.

## 3. The full N2 equations force the actual diagonal interface

Write the two outward original N normals as n_B,n_C and their
positive magnitudes as gamma_B,gamma_C. The entire unloaded N
force equation is

    gamma_B*n_B+gamma_C*n_C=0.

Since both normals are unit and both magnitudes positive, it
forces

    gamma_B=gamma_C=gamma>0,
    n_B=d, n_C=-d

for one unit direction d. Its full torque is

    gamma det(T,d)-gamma det(U,d)=0,
    det(T-U,d)=0.

The actual common support conditions make T a maximum-d point
of N and U a minimum-d point. Thus

    T-U=w*d, w>0.                                (5)

For completeness, the actual unit-square geometry gives exactly
two possibilities. If d is an own side axis of N, the parallel
support sides have distance one and (5) gives w=1. Otherwise the
two support points are unique opposite N vertices. Their difference
has length sqrt(2); (5) makes d exactly an N diagonal and gives
w=sqrt(2). This is the complete two-force transmission theorem,
with every original force and torque term retained.

The side case w=1 is impossible by (4), since a unit vector has
e component at most one. Therefore the actual N is diagonal and

    T-U=sqrt(2)*d,
    d=u h+v e, u^2+v^2=1,
    v>1/sqrt(2).                                 (6)

Both T,U are actual N vertices. The original diagonal avoidance
now supplies their exact endpoint owners. Neither contact can
have positive shared length, since d is not an own side axis
of N. If either point were also a vertex of its other square,
the original point-only vertex/vertex normal would be a diagonal
of N, contrary to the retained convention. Thus

    T is relative-side-interior in B,
    U is relative-side-interior in C,
    B and C both own the channel direction d.     (7)

The actual B and C frames are consequently parallel. This is
deduced from the original contacts; no physical frame is reset.

## 4. The entire channel-direction cover

The two alternatives u<=0 and u>0 exhaust (6), including the
vertical channel u=0. Put

    D_h=(Q_B-Q_C).h<=0,
    D_e=(Q_B-Q_C).e>=2.

### 4.1. All u<=0, including the exact vertical channel

Because C owns d and v=d.e>0, every maximum-e point of C
belongs to its maximum-d side. Thus Q_C and U are on that
same actual side and

    Q_C.d=U.d.

Because B owns d and

    f.d=-a*u+b*v>0,

every minimum-f point of B belongs to its minimum-d side.
Thus Q_B and T are on that same actual side and

    Q_B.d=T.d.

These conclusions include zero components along the other own
axis and every original side mean. Therefore (6) gives

    (Q_B-Q_C).d=(T-U).d=sqrt(2).                  (8)

But the actual coordinate inequalities give

    (Q_B-Q_C).d=D_h*u+D_e*v
        >=2v>sqrt(2),                            (9)

since D_h*u>=0. This contradicts (8). In particular no
separate radial-mask assumption is needed at u=0.

### 4.2. All u>0, with every possible B support tie

Now put

    w=-v h+u e.

The pair (d,w) is an actual orthonormal own frame for both B,C.
Since e has strictly positive components v,u in that frame,
Q_C is the actual joint maximum-d/maximum-w vertex of C.
Its maximum-d side contains U, so

    U=Q_C-alpha_C*w, 0<=alpha_C<=1.              (10)

The original relative-side-interior fact gives strict endpoints,
but their closed enlargement in (10) is harmless and keeps all
possible limiting support values explicit.

Because T is a minimum-d side point of B, write that same
actual square as

    B=T+[0,1]d+[-beta_B,1-beta_B]w,
    0<=beta_B<=1.                                (11)

The inward B support direction satisfies

    f.w=a*v+b*u>0.

Thus its actual minimum-support Q_B has the lower w coordinate
in (11). Its d coordinate is some xi in [0,1], giving

    Q_B=T+xi*d-beta_B*w, 0<=xi<=1.               (12)

This includes both strict signs of f.d and the exact tie
f.d=0. In that tie, xi is the entire original side point or
mean; no coordinate is selected.

Use (6),(10),(12):

    Q_B-Q_C=(sqrt(2)+xi)d-(alpha_C+beta_B)w.

Its h component is

    (sqrt(2)+xi)u+(alpha_C+beta_B)v>0.            (13)

This contradicts (1). The strict term sqrt(2)*u suffices
even at the enlarged zero side-parameter endpoints.

The two cases prove the complete support-bridge theorem.

## 5. The full shared-D Type III entry supplies exactly this theorem

Return to the same original Type III shared D-direction chart.
Keep all nine actual units, original forces, normals, applications,
full means, degrees, physical masks and individual circle coefficients.

Use the actual adjacent V vertices

    P1=(a0-1,b0), P0=(a0-1,b0-1),
    P1-P0=North,

and A's actual frame

    h=(c,-s), e=(s,c),
    c,s>0, c^2+s^2=1.

The shared D-direction identities are

    nD=e, tD=-h, g_(A->D)=-e,

    A=P1-[0,1]h+[-c,1-c]e,
    D=P0-[0,1]e+[-t,1-t](-h),

    0<t<1-s,
    W=P1-z h-c e=P0-(s+z)h,
    0<=z<=1-t-s.                                 (14)

This is precisely Section 3.4 of the complete original source

    UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md
    SHA256 f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb.

The full original stars are

    A:{V,D,B}, D:{V,A,C}, V:{A,D}.

A,D are unloaded true3 and the original AV,DV,AD magnitudes
mu,nu,rho are strictly positive. Their unchanged exterior data are

    F_B=-mu h+rho e,
    Q_B=P1-h+(1-c)e,

    F_C=-(nu+rho)e,
    Q_C=P0-e-z_D h,
    z_D=rho(s+z)/(nu+rho),                        (15)

and the complete A moment retains

    rho(1-z)=mu(1-c).

For Q_B, both own components of F_B are strict, so its displayed
actual A vertex is forced. For Q_C, the D torque about P0 is

    -rho(s+z)+(nu+rho)z_D=0.

Thus the entire original parallel-return mean in (15) is retained.
The z term is never discarded.

In A's frame,

    P1-P0=-s h+c e.

Subtracting the actual applications in (15) gives exactly

    Q_B-Q_C=-E h+2e,
    E=1+s-z_D.                                   (16)

Because nu>0, s+z>0 and the complete original mean interval
in (14) holds,

    z_D<s+z<=1-t,
    E>s+t>0.                                     (17)

Both original mean endpoints z=0 and z=1-t-s remain.
Strictness in (17) comes from the unchanged positive nu,
including at the upper original endpoint.

The actual inward unit direction into B is

    f=F_B/|F_B|
      =-[mu/sqrt(mu^2+rho^2)]h
        +[rho/sqrt(mu^2+rho^2)]e.

It has the exact positive components required in Section 1.
The actual inward direction into C is -e. Equations (16),(17)
therefore give both support inequalities (1), with a strict
horizontal inequality and equality in the vertical bound.

The complete support-bridge theorem applies at every original
angle, every t in (14), every original shared mean and every
positive force ratio. No radius or additional circle equation
is required for this implication.

## 6. Entire original D02.L135 shared-D feature is excluded

For the original D02.L135 caller, retain the exact labels

    A=0, V=1, D=2, C=3, N_original=4, B=5,

with the full rim A--V--D--C--N_original--B--A and chord AD.
Its complete true degrees and loads are:

| Actual body | Full positive neighbors | True degree | Total circle load |
| --- | --- | --- | --- |
| A=0 | V,D,B | 3 | zero |
| V=1 | A,D | 2 | positive |
| D=2 | V,A,C | 3 | zero |
| C=3 | D,N_original | 2 | positive |
| N_original=4 | C,B | 2 | zero |
| B=5 | N_original,A | 2 | positive |

Thus the actual N_original is precisely the unloaded true-two
bridge of Sections 1--4. Its two original magnitudes and its
entire torque are retained. The already selected diagonal
avoidance is the exact premise used to derive (7).

The full original shared-D Type III feature is therefore impossible
in D02.L135, including every original angle, shared mean, exterior
owner, physical circle mask and individual coefficient. All three
additional actual physical units remain. The contradiction is within
the unchanged six-unit core, so no allocation or removal of those
three completing units is needed.

The generic theorem imposes no new equation at B,C and does not
need their boundary status, so their actual loaded true-two stars
are retained without reduction. Nor is any original equation at V
discarded: its full unique-circle Type III system remains, although
the final radius-free support implication needs no additional V
identity beyond the exact entry (14).

For D02.L1345, N_original is loaded true2. Its positive circle
term prevents the unloaded equation in Section 3. That load
alternative is outside this theorem and must use its separate
complete physical-clear bridge argument. It is not made a
transmitter here.

## 7. Exact scope and source preservation

The complete mathematical inputs used above are:

| Source | SHA256 | Exact operative use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original two-force/torque equations and complete actual transmission geometry, reconstructed in Section 3 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Sections 2,4,7: retained original diagonal avoidance and its actual endpoint-owner consequence |
| UNIQUE_CIRCLE_TWO_STRICT_ROOF_PORTS_PERPENDICULAR_INTERFACE_EXCLUSION_AND_COMPLETE_SAME_AXIS_DOMAIN_2026_10_29.md | f8cce87f5bbc22ba898db4029676dd84f1fb1c448212a809ee6809cffc5056eb | Entire actual shared-D chart, all original means, complete A3/D3 stars and literal feature |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original D02.L135 graph, true degrees, loads and all three completing units |

All four complete sources were read. The support-span estimate,
complete signed direction cover and full shared-D application are
proved here; no incomplete pocket or sampled geometry is imported.

The theorem is conditional on the same initial compatible certificate,
including its existing finite diagonal avoidance. It supplies no new
global compatibility proof. No normal is changed after extraction,
and no vertex/vertex axis endpoint is silently substituted for an
original strict point normal.

This closes one entire original shared-D owner/load feature.
The other Type III owner rows, Type I/II, physical-two roof domains,
both full D02 parents, the sharp nine-square theorem and equality
classification retain their separate obligations.

No numerical pose search, angle mesh, packing certificate, changed
original mean, force deletion, circle-mask relabeling, removed unit,
false lower-degree star, metadata or flag mutation, remote write,
Lean/Lake build, CI/workflow or merge was used. Full independent
current-source and literal-join review is required before adoption.

