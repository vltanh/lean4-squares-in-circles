# The central and side-channel pockets cannot both be occupied in the whole two-unique regular chart

Date: October 31, 2026 UTC.

**Status: complete hand joint-capacity theorem.** In the entire regular
two-strict, both-hub-owned perpendicular-AD side chart with both exterior
endpoints physically unique, an occupied exterior N pocket makes the
actual central pentagon's free area strictly less than 39/40. Thus an
additional central unit and an additional unit in the exterior N pocket
cannot coexist. This covers every original side coordinate and every
transverse position of N, including both endpoints of its slider.

The argument retains the actual N area on the central side of its port
segment. It does not move N to a comparison position. Section 8 gives
the precise remaining allocation implication when a separate complete
theorem excludes the A hub pocket.

## 1. The entire original entry

Retain all nine actual independently oriented unit squares and the
entire original positive component of D02.L135:

    A=0, V=1, D=2, C=3, N=4, B=5,
    rim A--V--D--C--N--B--A, original positive chord AD,
    A,D unloaded true3; V,B,C loaded true2; N unloaded true2.

All original forces, torques, physical contacts, original means,
individual circle coefficients and the three completing squares remain.
Use the complete regular two-unique side entry in

`TWO_STRICT_REGULAR_PERPENDICULAR_SIDE_MASK_AND_ANGLE_COVER_2026_10_31.md`.

The original radius upper bound is R^2<=1105/256. The accepted whole-nine
theorem `NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md` supplies R>2 for this
same unchanged packing. In particular the complete force-free side
channel theorems with 2<=R<=sqrt(1105)/16 apply literally.

The operative hand-proof route for this input is
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` followed by
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, as recorded in
`ANALYTIC_CERTIFICATE_CHECKPOINT.md`, Section 3. The latter source proves
the fixed values analytically. No historical checker output or generated
parameter certificate is an input to the present use of R>2.

Retain the actual notation

    h=(c,-s), e=Jrot(h), k=(C,S), v=Jrot(k),
    theta=alpha+beta in (0,pi/4),
    H=sin(theta), J=cos(theta), F=J-H, Sigma=J+H,
    0<rho<1,
    x=1+s-H*rho in (0,1), y=1-c+J*rho in (0,1),
    m=x/y, n=F/(1-rho),
    p=sqrt(m^2+1), q=sqrt((n+H)^2+J^2),
    b=(-m*h+e)/p, a=((n+H)*k+J*v)/q,
    w=Jrot(b), z=Jrot(a).

The original genuine AD application W and actual exterior applications
K,L satisfy

    K-W=-x*h+e,
    W-L=k+v.                                       (1)

The complete physical-mask reduction gives

    pi/4<delta_B,delta_C<pi/2,
    Theta=delta_B+delta_C in (pi/2,3*pi/4),
    0<beta_B,beta_C<1,
    T=K+beta_B*w, U=L+beta_C*z,
    T-U=u, |u|=1,                                  (2)

where delta_B is the clockwise angle from b to u and delta_C the
clockwise angle from u to a. Both endpoints retain their actual unique
physical circle corners and their full original loaded stars. Every
torque, circle equation and additional nonoverlap condition is retained.

## 2. The actual transverse offset and its strictly positive port height

Put j=Jrot(u). The full original unloaded N force and torque, already
used in the unchanged side-channel entry, give a common port height

    h0=T.j=U.j,
    xi=T.u,

and the actual full unit is exactly

    N=[xi-1,xi]*u+[h0-tau,h0+1-tau]*j,
    0<=tau<=1.                                     (3)

Here tau is the original transverse offset. It is not chosen anew.

For clarity, the complete original B origin torque gives

    M+ell*det(T,u)=0,
    M=p*det(K,b), ell>0,
    h0=M/ell.                                      (4)

The actual regular chart expands the same moment as

    M=m*(d*s+c/2)+d*c+s/2-H*rho.                   (5)

This is positive. Indeed the original window gives d>9/10, while
c>2/3 and c+s>1. Therefore

    d*c+s/2=(d-1/2)*c+(c+s)/2>23/30.

Also H*rho<1/sqrt(2)<3/4. The last three terms of (5) consequently
exceed 1/60, and its first term is positive. Thus h0>0 without any
reflection or change of the original moment equations.

In the actual (u,j) frame, set

    X=C, Y=B, a0=1-xi, b0=xi.

The original supports give

    X subset {u-coordinate<=-a0},
    Y subset {u-coordinate>=b0},
    a0+b0=1,
    U=(-a0,h0), T=(b0,h0).

The complete arbitrary-degree theorem
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md`
therefore applies to the unchanged C--N--B channel. Its Sections 1 and 3
give

    h0>3/10, a0,b0>7/100.                          (6)

Its exact height derivation is

    h0^2 >= (R-sqrt(2))^2-1/4
           >= (2-sqrt(2))^2-1/4
           >9/100.

The last strict comparison uses sqrt(2)<283/200. The source proves the
strict port signs before taking the smaller port; there is no hidden
assumption that the origin was already between the two port lines.
Physical circle contact of both actual endpoints is sufficient. Their
other forces and true degrees are not changed by this geometric input.

## 3. The actual contact pentagon lies on the central side of TU

The inherited physical chorded-cycle embedding gives the central
contact pentagon with clockwise boundary

    P_c: W -> L -> U -> T -> K -> W.                (7)

Its bounded-side region, or its winding-one region in the inherited weak
routing convention with orientation reversed, is denoted G. Let A_poly
be its nonnegative polygon area. The actual central free union is a
subset of G outside the retained closed core squares.

We record a strict check of the side at TU, so that the endpoint tau=1
does not rely on TU being an interior chord of N. From (2),

    K.j=h0-beta_B*cos(delta_B)<h0,
    L.j=h0-beta_C*cos(delta_C)<h0.                   (8)

The actual (a,z) coordinates of k+v give

    (k+v).j
      =[(n-F)*cos(delta_C)-(n+Sigma)*sin(delta_C)]/q
      <0.                                          (9)

Indeed sin(delta_C)>cos(delta_C)>0, n+Sigma>0, and
Sigma+F=2*J>0. Equation (1) now gives W.j<L.j<h0.
Thus W,L,K are all strictly below the port line in this exact frame.
Every other selected pentagon edge lies strictly below that line apart
from its possible endpoint U or T. In particular the open segment UT
meets none of the other selected contact edges.

The local bounded-side label at a regular point of UT is therefore the
side j<h0. Equivalently, above this line the polygon has winding zero,
and its clockwise edge U->T has the bounded side immediately below it.
The same statement holds for the inherited weak physical routing:
the contact-polygon limit has only the original bounded-side winding
label, and the isolated open edge UT retains this local jump.

## 4. The full central N strip is an additional occupied area cut

If tau=0, the claimed cut has area zero. Suppose tau>0 and define the
open rectangle

    S_N={r*u+s*j : xi-1<r<xi,
                     h0-tau<s<h0}.                 (10)

It has area exactly tau and is contained in int(N), including when
tau=1. Every other selected edge of (7) lies in one of the original
closed units A,D,B,C. None can meet int(N): if a point of one closed
unit lay in the other's open interior, a small neighborhood would meet
both open interiors. This is incompatible with the actual packing.

The connected rectangle S_N consequently meets no other edge of P_c.
By Section 3, a point of S_N sufficiently close to the interior of UT
has the central bounded-side label. Constancy of winding on the
connected set S_N gives

    S_N subset G.                                  (11)

This argument explicitly includes tau=1. In that case TU is N's top
boundary side, but S_N is still its connected open interior below that
side. Equations (8)--(9) keep every other selected edge away from the
open segment UT, and the clockwise local label immediately below UT
is still the central one. Additional zero-weight contacts at TU may
subdivide a physical free region but do not change that selected-edge
winding or allow S_N to cross the occupied contact polygon.

The actual occupied A and D triangles are

    triangle(W,K,K-e), area x/2,
    triangle(W,L,L+v), area 1/2.                   (12)

Their exact inward placement and the full contact-pentagon winding are
proved in
`TWO_STRICT_REGULAR_PERPENDICULAR_UNIQUE_SIDE_CENTRAL_EMPTY_ANGLE_AND_PORT_COVER_2026_10_31.md`,
Sections 2--3. The three open pieces in (10),(12) lie respectively in
int(N), int(A), int(D), up to their measure-zero chord boundaries.
They therefore have disjoint interiors and can all be subtracted.
No part of the N strip is charged twice as an A or D cut.

Writing A_free for the area of the entire actual central free union
in this pentagon, we obtain

    A_free <= A_poly-(x+1)/2-tau.                  (13)

The connected-interior argument also handles any weak contact-junction
limit used to define the original face: first take compact subrectangles
strictly inside S_N. They avoid the closed other core units with a
positive margin and retain the same winding under the physical routing.
Exhaust S_N by those subrectangles to recover its full area tau.
Completing units likewise retain their original face labels by compact
inner subsets and closure. No contact point or force mean is perturbed.

## 5. The complete two-unique chart has pre-strip free area below five quarters

The exact area identity from the cited central-cover source is

    2*A_poly-x-1=C0+S_area,
    C0=x*(Sigma-1)+F-1<0,
    S_area=beta_B*cos(delta_B)
          +beta_C*cos(delta_C)
          +beta_B*beta_C*sin(Theta).              (14)

All angles and side coordinates in (14) are the original ones. By (2),

    S_area<1/sqrt(2)+1/sqrt(2)+1=1+sqrt(2).

Combining (13)--(14), and using sqrt(2)<3/2, gives the whole-domain
bound

    A_free <(1+sqrt(2))/2-tau<5/4-tau.            (15)

No central-occupancy restriction such as Theta<2*pi/3 or beta_B>3/4
was used. This estimate holds throughout the entire strict two-unique
side alternative reached by the complete physical-mask cover.

## 6. An occupied exterior N pocket forces a large actual central strip

Suppose a whole additional unit occupies the original exterior N pocket.
The complete theorem

`FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md`

applies to the unchanged actual boundary channel C--N--B. Its full
arbitrary-degree physical hypotheses and the original upper outer-gap
join are supplied by

`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md`,
Sections 1 and 8.

For this literal caller, V,B,C are the three original positively loaded
boundary units in the protected circular order. The actual outer chain
is C--N--B and the original AD chord is retained. The source chooses the
unchanged exterior-spoke corners and proves that this actual gap uses
the upper arc in the (u,j) frame with h0>0. It does not delete the chord
or impose a two-force equation at either endpoint. The unique physical
corners here are an allowed special case of its complete physical-mask
entry; all other original contacts remain.

The stated proximity conclusion is therefore literally

    dist(O,N)<1/40.                                  (16)

Every point of the same actual N has j-coordinate at least h0-tau.
An actual N point of norm less than 1/40, supplied by (16), consequently
gives

    h0-tau<1/40,
    tau>h0-1/40>11/40,                              (17)

where (6) was used in the last step. This inference needs no new
horizontal placement of O, and includes negative, zero and positive
original bottom coordinates h0-tau.

Finally (15),(17) imply

    A_free<5/4-11/40=39/40<1.                       (18)

An additional central unit contributes its full area one to this free
union. Equation (18) forbids it. This proves the joint exclusion.

## 7. Whole conclusion and retained weak cases

The central pentagon and exterior N pocket cannot both contain an
additional unit. The theorem covers all original theta, rho,
beta_B,beta_C and N side offsets in their stated physical domains;
tau=0 and tau=1 were not removed. It retains all zero-weight physical
contacts, every circle-load endpoint, and every weak subdivision of the
original face. The original actual nine units remain in the same disk.

The proof uses original torques to obtain the actual side channel and
the sign of h0, the complete degree-free channel height and proximity
theorems at their proved hypotheses, and three genuinely disjoint
occupied area cuts. It uses no guessed extra pose, shifted transmitter,
proper-concurrence transfer, new normal choice, numerical parameter
certificate, Lean/Lake invocation or CI.

## 8. Exact residual allocation if the A hub pocket is separately empty

This section is a conditional assembly statement. Assume, in addition,
a complete theorem at this same original chart has proved the entire
A hub pocket empty. The conclusion then excludes all nine-square
completions of this regular two-unique feature, as follows.

The selected physical rim, its original AD chord, and the actual
exterior circle spokes at V,B,C partition every possible completing
unit into the following original face regions:

1. The central A--V--D triangle, which has no whole extra.
2. The central A--D--C--N--B pentagon, with capacity at most one.
3. The exterior A hub pocket, empty by the additional theorem.
4. The exterior D hub pocket, with capacity at most one.
5. The exterior N side-channel pocket, with capacity at most one.

The first two claims are the complete accepted
`CHORDED_HEXAGON_CENTRAL_CAPACITY_ONE.md`, at its single-short-chord
row. The D pocket bound is the complete
`TWO_STRICT_REGULAR_PERPENDICULAR_BOTH_HUB_POCKETS_HALF_CLEAR_AND_CAPACITY_ONE_2026_10_31.md`.
The N pocket bound is the complete arbitrary-degree
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md` at the
literal channel entry checked in Section 6.

For clarity, the allocation uses the given compatible exterior order
V--A--B--N--C--D--V. Add the original physical V,B,C spokes to the
unchanged rim and AD chord. The two bounded graph faces are exactly
the triangle and pentagon above, and the three consecutive loaded gaps
give exactly the three indicated exterior chain pockets. Deforming a
center/contact route to a contact-polygon or occupied-boundary route
stays in the same original closed core union and preserves every
extra's winding label.

If both actual V circle corners are used as distinct spoke endpoints,
there is also the cap beyond V's outer side. Its width is

    R-(d+1)=R-sqrt(R^2-1/4)<1,

so it contains no whole unit square. The remainder of that routing
difference is inside occupied V. Additional zero-load physical circle
contacts and weak contacts only subdivide the listed regions; they
cannot allow a connected extra interior to cross the occupied network.
Using a compact subset of each extra interior first and then taking
closure retains its whole unit area and its same face assignment.

By the joint theorem, at most one of regions 2 and 5 can be occupied;
each separately has capacity one. Together they therefore contain at
most one extra. Region 4 contains at most one more. The other regions
are empty. The total number of completing squares is thus at most two,
contrary to the three actual completion squares in the original
nine-unit packing.

This conditional count is exhaustive but does not assert its additional
A-pocket emptiness premise. It is not a claim about loaded N in
D02.L1345 or a change to any unrelated original graph/load flag.
