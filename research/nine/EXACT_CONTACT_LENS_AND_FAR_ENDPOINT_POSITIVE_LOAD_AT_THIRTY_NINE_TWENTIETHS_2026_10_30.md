# Exact contact lenses, unloaded-star restrictions, and positive loads at a 39/20 support gap

**Date:** October 30, 2026 UTC. **Status:** complete proposed force-free
contact theorem and full-force consequences, awaiting independent full
review. All earlier frozen sources remain unchanged.

Every actual contact point and its actual common normal obey a sharp
intersection-of-two-disks inequality. This gives the universal contact
radius `sqrt(R^2-1)`, a quantitative near-tangential restriction for outer
contacts, a full-star restriction on unloaded bodies with a distant own
side, and an improved continuous positive-load theorem for separated
endpoints. The proofs retain every actual body and every original force.
No planarity, degree bound, torque equation, orientation discretization,
or special circle mask is assumed.

## 1. Exact geometric setting and the whole supporting-face chord

Let actual closed unit squares have pairwise disjoint open interiors and
lie in the disk `D_R` centered at the unchanged origin O. For the numerical
consequences assume only

    R^2<=Q=1105/256.

A contact datum consists of an actual shared point p and a unit vector n
such that the first square A maximizes n at p and the second square B
minimizes n at p. The point may be an original application mean anywhere
on an actual shared segment. All support-side endpoints and point-only
contacts are included. No point or normal is selected in place of an
original one.

The inward unit-normal chord of a unit square is an existing input,
reproved here over its entire domain. Write a square as

    K=P_0+[0,1]u+[0,1]v,
    n=a*u+b*v, a^2+b^2=1.

Suppose p minimizes n on K. If a>0, p's u-coordinate is zero, and adding
t n for `0<=t<=1` changes it to `t a in [0,1]`. If a<0, that coordinate
is one, and it becomes `1+t a in [0,1]`. If a=0, the unchanged coordinate
may be any point of `[0,1]`. Apply the same argument to b and the
v-coordinate. Hence

    p+[0,1]n subset K.                                  (1)

Both nonzero components cover every supporting vertex and its full
normal cone; one zero component covers a whole supporting side and
both endpoints. In particular a vertex normal need not be an own axis.
The argument is valid for every actual point of the supporting face,
not merely one selected corner.

Applying (1) to the two squares of a contact gives actual points

    p-n in A, p+n in B.                                 (2)

These are occupied points of the original units. They need not be new
contacts, application means, corners or endpoints of a maximal chord.

## 2. The exact contact lens and universal contact radius

Both points in (2) lie in `D_R`. Expanding their squared norms yields

    |p|^2+1+2*p.n<=R^2,
    |p|^2+1-2*p.n<=R^2.

Therefore every actual contact datum satisfies

    |p|^2+1+2*|p.n|<=R^2.                               (3)

Equivalently, in the unchanged frame `(n,Jn)`,

    (|p.n|+1)^2+(p.Jn)^2<=R^2.                          (4)

**Theorem 1 (exact actual contact lens).** For each original common unit
normal n, its actual contact point belongs to the intersection of the
two closed disks of radius R centered at n and -n. Equations (3)--(4)
are the same exact statement. This locus is a lens, not an ellipse.

Dropping the nonnegative normal term gives the degree-free bound

    |p|<=sqrt(R^2-1)<=sqrt(849)/16.                      (5)

In particular there can be no pair contact if `R<1`. For `R>=1`, the
closed bound (5) applies to every physical pair contact, including pairs
with zero selected coefficient. For any shared point of two actual
units a common separating line exists by convexity and interior
nonoverlap, so the radius conclusion does not require a preassigned
force normal. When a normal is already part of a certificate, (3)
holds for precisely that unchanged normal.

The closed radius bound cannot be improved as a force-free statement
for two unit squares. For any `r>=1/2`, let the two actual units be

    [-1,0] x [r-1,r], [0,1] x [r-1,r].

They have disjoint interiors, lie in the circle of squared radius
`r^2+1`, and share `p=(0,r)` with common horizontal unit normal.
Their farthest corners are `(±1,r)`, because `r^2>=(r-1)^2`.
Thus equality holds in (5). This two-body sharpness check is not a
claim about a nine-body completion or a selected normalized stress.

### 2.1 Exact restrictions on the direction of an outer contact

For `r=|p|>0`, put `e=p/r`. Equation (3) gives

    |e.n|<=(R^2-1-r^2)/(2*r).                          (6)

The right side is nonnegative whenever such a contact exists. If
`r>R-1`, it is less than one and excludes an open cone around both
radial directions. At the extreme radius in (5), the contact normal
is exactly tangent to the circle about O through p.

The function `(Q-1-r^2)/(2r)` is strictly decreasing for r>0.
Consequently the whole target disk gives the rational implications

    r>=7/4  ==> |e.n|<=65/896<1/12,
    r>=9/5  ==> |e.n|<=163/7680<1/40.                   (7)

These restrictions concern the actual common contact normal, not a
line joining body centers. If n is radial at p, (3) instead gives
`(r+1)^2<=R^2`, hence the familiar sharp radial bound `r<=R-1`.

## 3. A distant own side restricts the complete unloaded star

Assume R>=1 in this section; the R<1 case has no pair contacts by
Section 2 and hence no positive body star to analyze.

Let S have actual center c and own orthonormal axes u,v. Consider its
entire closed positive-u side

    F={c+(1/2)u+t v : -1/2<=t<=1/2}.

Assume every point of F has norm strictly greater than
`sqrt(R^2-1)`. By (5), no other physical unit can meet any point of F,
including its endpoints. Every actual common outward normal n at a
contact of S therefore satisfies

    n.u<=0.                                            (8)

Indeed if n.u>0, its actual supporting face on S is contained in F,
even when that face is a single corner. Such a contact is impossible.
This is a conclusion about all physical contacts, not only positive
terms in a selected graph.

Now retain a full physical translational force equation at S,

    2*sum_(circle atoms) lambda*z + sum_(body pairs) mu*n=0,
    lambda>=0, mu>0.                                  (9)

The body normals in (9) are directed from S toward its neighbors and
are its actual outward supporting normals. If S has zero total circle
load, project (9) onto u. Every term is nonpositive by (8), so every
positive contact normal must satisfy `n.u=0`. Therefore all such
normals belong to the same pair `v,-v`.

**Theorem 2 (complete-star side-clearance alternative).** If an entire
own side is outside the closed universal contact disk, then an unloaded
positive star has only the two perpendicular own-axis normal directions.
If there is any positive original contact with `n.u<0`, the body instead
has strictly positive total circle load. The same is true if its positive
contact normals are not all parallel.

Every original positive force participates in this argument. A parallel
star can still have more than two distinct positive neighbors; the
conclusion does not assign it true degree two or license propagation
through it as a two-force transmitter. No torque equation is used.

### 3.1 A uniform necessary locus for every unloaded nonparallel star

The minimum squared norm on the positive-u side is

    (c.u+1/2)^2+max(|c.v|-1/2,0)^2.

Choosing the outward sign of each own axis gives this consequence of
Theorem 2. If S is unloaded and has two nonparallel positive contact
normals, then necessarily

    (|c.u|+1/2)^2+max(|c.v|-1/2,0)^2<=R^2-1,
    (|c.v|+1/2)^2+max(|c.u|-1/2,0)^2<=R^2-1.           (10)

In particular, throughout `R^2<=Q`,

    |c.u|>=4/3 ==> every positive normal is parallel to v
                   for an unloaded body,              (11)

and likewise after exchanging u,v. The strict geometric reserve is

    (11/6)^2-(Q-1)=103/2304>0.

These are whole-star restrictions at arbitrary true degree. They
apply to circle-clear branching bodies on an outer face or in its
interior, without deleting any chords. They are necessary geometric
conditions, not a bound on the number of such branching bodies.

## 4. Far separated endpoint squares have completely free outward own sides

For any actual contained unit with center c, the farthest-corner
formula gives

    R^2>=|c|^2+1/2+|c.u|+|c.v|
        >=|c|^2+|c|+1/2.

The right side is increasing for nonnegative |c|. With

    M=91/60,
    M^2+M+1/2-Q=31/57600>0,

it follows that every actual center satisfies

    |c|<M.                                             (12)

Take two distinct actual units A,B and one signed unit direction d.
Let h_A,h_B be their half-widths in direction d, each at least one
half. Suppose their whole support intervals have the genuine gap

    d.(c_B-c_A)-h_A-h_B>=39/20.                        (13)

No contact, force, load, degree or orientation assumption is imposed
on A or B for the geometric result in this section.

Equation (12) and (13) imply

    X_A:=-d.c_A>39/20+1-M=43/30,
    X_B:= d.c_B>43/30.                                 (14)

They also imply

    h_A+h_B<2M-39/20=13/12,
    h_A<7/12, h_B<7/12.                                (15)

Choose an actual own axis u_A pointing toward the outward side of A
away from B, with its component in direction -d at least the absolute
component of the perpendicular own axis v_A. Write

    a_A=-d.u_A>=b_A=|d.v_A|>=0.

Then `a_A^2+b_A^2=1`, and twice the actual half-width is
`a_A+b_A=2h_A<7/6`. Thus

    (a_A-b_A)^2=2-(a_A+b_A)^2>23/36>(19/24)^2,
    a_A-b_A>19/24.                                    (16)

The last rational reserve is `7/576`. For every point p of the whole
closed outward own side of A, retaining its full side parameter,

    d.p<=-X_A-(a_A-b_A)/2
        <-43/30-19/48=-439/240.                        (17)

Therefore `|p|>439/240`. The same proof, with u_B pointing toward d,
puts every point on B's whole outward own side in `d.p>439/240`.
The universal contact radius is strictly smaller, since

    (439/240)^2-(Q-1)=53/1800>0.                       (18)

**Theorem 3 (whole-side clearance from a 39/20 support gap).** Under
(13), the complete outward own side of each endpoint unit is disjoint
from every other physical unit. Both side endpoints, every inactive
physical contact, all arbitrary frames, and all other packing squares
are included in this conclusion.

Only actual support intervals were used. A distance lower bound without
a specified separating direction is not silently substituted for (13).

## 5. Positive endpoint loads at arbitrary true degree

Retain full equations (9) at the two actual endpoints satisfying (13).
Assume A has an original positive contact whose normal is exactly d,
and B has an original positive contact whose normal is exactly -d.
These contacts can be with intermediate units rather than with one
another. All remaining positive endpoint contacts and their actual
means remain in their complete stars.

The original inward contact at A has

    d.u_A=-a_A<0.

Every other positive body-contact normal has nonpositive u_A component
by Theorem 3 and (8). Hence the body-force sum has strictly negative
u_A component. If the endpoint had zero total circle load, its full
force equation would be impossible. Therefore A has positive total
circle load. The argument at B is identical.

**Theorem 4 (positive far-endpoint loads).** In any full physical
translational stress, support-separated endpoints with gap at least
39/20 and original positive contacts directed inward along that same
normal both have strictly positive total circle load. Their true
degrees are unrestricted. No graph embedding or torque premise is
needed.

A genuine unloaded true-degree-two run with two internal bodies is a
literal caller. Full force balance propagates one common signed normal
through both actual internal units, with their original magnitudes.
Tight support equalities give an endpoint support gap equal to the sum
of the two actual internal widths, which is at least two and hence at
least 39/20. The positive inward endpoint contacts are original terms
of the same certificate. Thus both retained endpoints are positively
loaded, regardless of additional chords, branches or attachments.

The result is also useful in continuous situations where a proved
support gap is below two but at least 39/20. It does not assert a new
integer run type or require any internal unit to have width exactly one.
The prior frozen positive-long-endpoint theorem remains unchanged.

## 6. Source boundary and remaining work

The inward supporting-face unit segment was already proved in Section 1
of `SUPPORT_POINT_UNIT_TRANSLATION_AND_PERPENDICULAR_PARALLEL_W_UNLOADED_TERMINAL_EXCLUSION.md`
(SHA256 `3da16659e2080884077c02d85e665814391611c357254ba08a57c3a5a4b75c30`)
and Section 4 of
`LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md`
(SHA256 `dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05`).
The whole chord proof is reproduced in Section 1, so no other theorem
from those sources is imported. In particular there is no loaded-star,
concurrence, long-channel, or full-torque premise in the contact lens.

The earlier source
`UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md`
(SHA256 `d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705`)
proved a weaker strict contact radius 29/15 by center-incircle geometry
and used support gap two for its endpoint-load corollary. The new source
keeps that proof frozen and independently derives the stronger exact
lens, sharper universal radius, whole-star restrictions, and 39/20 gap
threshold from actual occupied unit chords.

No arbitrary unloaded branching body is declared a two-force transmitter.
The restrictions (10)--(11) do not by themselves bound an outer face or
close every large biconnected block. Their role is to retain a uniform
geometric condition on those full stars for the remaining completion
analysis. All nine original units remain physically present in every
nine-body application.

This manuscript uses no pose search, finite orientation table, numerical
stress optimization, original ledger mutation, metadata change, Lean
compilation, CI run, graph re-selection or remote publication. All stated
inequalities and full-force consequences require this source's own
independent review before adoption.

