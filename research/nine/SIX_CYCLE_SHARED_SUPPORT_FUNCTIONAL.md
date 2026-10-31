# Exact support functional for every all-unique alternating side-transmitter C6

Date: October 25, 2026.

**Status: complete hand identity and minimization implication; author and
independent root review passed.** See REVIEW_STRUCTURAL_INPUTS_2026_10_25.md. This source
does not close the remaining C6 completion gate. It retains every physical
shared-side mean and gives the exact whole-family replacement for the
singleton six-point functional. The associated numerical exploration is
explicitly separate from the proof below.

## 1. Full physical domain

Let the actual positive component be an alternating six-cycle with three
loaded units S_i and three unloaded side-normal transmitters, indexed
cyclically. Each S_i has one physical circle corner z_i on the same circle
of radius R. Every original loaded force has positive total weight. Keep
all genuine body equations, all physical contact sets, all original means,
and the three additional packing units.

Use the proper counterclockwise force polygon of
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. Write

    f_i = mu_i*n_i,       mu_i>0, |n_i|=1,
    F_i = f_(i-1)-f_i = k_i*z_i,       k_i>0.

Let p_i^- and p_i^+ be the original incoming and outgoing application
points on S_i. Since a side-normal transmitter has reserve one and its
two original applications have the same transverse coordinate, its
actual displacement is

    p_(i+1)^- - p_i^+ = n_i.                       (1)

No loaded singleton premise is imposed. In particular, p_i^+ or p_i^-
may be an endpoint of a genuine shared interval.

Let c_i be S_i's center and h_i its centered support function. For a unit
square with own orthonormal axes e_i,v_i,

    h_i(w) = (|w.e_i|+|w.v_i|)/2.

All h_i remain those of the actual physical squares.

## 2. One convex functional retains every mean

For t in the plane define

    Psi(t) = sum_i |f_i+t|
           + sum_i [h_i(f_(i-1)+t)+h_i(f_i+t)+h_i(F_i)].       (2)

Then

    0 is a subgradient of Psi at 0,
    Psi(0) = min_t Psi(t) = R*sum_i |F_i|.                    (3)

**Proof of minimization.** Each norm and each support function in (2) is
convex. The actual incoming application minimizes f_(i-1) on S_i and
the outgoing application maximizes f_i. Central symmetry therefore gives
the genuine supporting subgradients

    c_i-p_i^- in partial h_i(f_(i-1)),
    p_i^+-c_i in partial h_i(f_i).

At a shared side, the entire side is precisely the allowed support
subgradient interval, so these statements retain the original mean and
both endpoints. They require no choice of a preferred subgradient.
The norm contribution has gradient n_i. Summing these particular original
subgradients gives

    sum_i [n_i+(c_i-p_i^-)+(p_i^+-c_i)]
      = sum_i [n_i+p_i^+-p_i^-] = 0

by the actual channel identities (1). Hence 0 is a subgradient at 0;
convexity proves the asserted global minimum.

**Proof of the value.** The unique physical corner z_i maximizes F_i on
S_i, because F_i is a positive multiple of z_i and z_i is its unique
farthest containing-circle corner. Thus

    f_(i-1).(z_i-p_i^-) - f_i.(z_i-p_i^+)
      = h_i(f_(i-1))+h_i(f_i)+h_i(F_i).             (4)

This follows directly by writing all three points relative to c_i and
using their actual support values. Summation by parts and (1) now give

    sum_i F_i.z_i
      = sum_i f_i.(z_(i+1)-z_i)
      = sum_i mu_i
        + sum_i [f_(i-1).(z_i-p_i^-)-f_i.(z_i-p_i^+)]
      = Psi(0).

Finally F_i.z_i=R|F_i| for the original positive unique-circle load.
This proves (3). No force, corner, normal or original application has
been replaced. In particular this source makes no analogous equality
claim for a physical two-corner loaded body with unequal weights.

## 3. Exact adjacent-side version

The following coordinates are useful wherever the two actual applications
are distinct points of one inner side. Write that physical side as

    p_base+[0,1]u_i,       v_i=-J*u_i,
    p_i^- = p_base+t_i^-*u_i,
    p_i^+ = p_base+t_i^+*u_i,
    0<=t_i^-<t_i^+<=1,
    ell_i = t_i^+-t_i^-,
    z_i = p_base+chi_i*u_i+v_i,       chi_i in {0,1}.

Define

    K_i = (chi_i-t_i^-)*f_(i-1)+(t_i^+-chi_i)*f_i,
    g_i = K_i+J*F_i.

The original loaded torque about z_i is

    det(u_i,K_i)+u_i.F_i = 0.

Equation (4) also shows u_i.g_i>0, so

    u_i=g_i/|g_i|,
    |g_i|=h_i(f_(i-1))+h_i(f_i)+h_i(F_i).

Consequently the equally exact convex functional

    Phi(t)=sum_i |f_i+t| + sum_i |g_i+ell_i*t|

has gradient zero at t=0 and has the same physical value

    min_t Phi(t)=Phi(0)=R*sum_i|F_i|.               (5)

Here the gradient contribution is ell_i*u_i, the actual side chord.
Replacing it by a unit vector is valid only in the all-singleton case.

For a strict force turn theta in (pi/2,3pi/4], at most one application on
such a side is in its relative interior. The complete shared formulas
follow from the same original torque:

| Actual interface | Corner and side direction | Original chord length |
| --- | --- | --- |
| Incoming shared, outgoing vertex | chi=0, u=J*n_previous | ell=1-(mu_next/mu_previous)(sin(theta)+cos(theta)) |
| Incoming vertex, outgoing shared | chi=1, u=-J*n_next | ell=1-(mu_previous/mu_next)(sin(theta)+cos(theta)) |

For example in the first row, n_previous=v and
n_next=sin(theta)*u+cos(theta)*v. The circle force has negative u
component and positive v component, giving chi=0. Substituting
t^+=1 and t^-=1-ell into the torque gives the displayed length.
The reflected calculation gives the second row. Endpoint means are
retained whenever their original physical contact is shared. The
theta=pi/2 case with applications on different sides belongs to the
whole-family functional (2); it is not silently put in this chart.

## 4. Eliminate each transmitter's transverse position exactly

There is also a complete geometric way to retain the circle-forced
occupation of the central side of every original channel. It needs no
shared or singleton assumption at either loaded endpoint.

For a channel write p=p_i^+, p+n=p_(i+1)^-, j=J*n and

    m=p+n/2,       alpha=n.m,       j.m=-h,       h>0.

The actual transmitter has center m+t*j and own axes n,j. Since p and
p+n are its two original supporting-side applications, its original
transverse parameter obeys -1/2<=t<=1/2. Strict singleton applications
give strict endpoints; keeping the closed interval enlarges the estimate.
Its exact farthest-corner squared norm is

    (|alpha|+1/2)^2 + (|t-h|+1/2)^2.

Consequently physical circle containment is equivalent to

    B=sqrt(q-(|alpha|+1/2)^2)-1/2 >= 0,
    t in [-1/2,1/2] intersect [h-B,h+B],           (6)

where q=R^2. This keeps the whole original interval; it does not replace
the transmitter by a preferred extremal placement.

Let

    t_min=max(-1/2,h-B),
    w=max(0,h+1/2-B)=1/2+t_min.

Every possible original transmitter in (6) contains the same closed
rectangle

    alpha-1/2 <= n.x <= alpha+1/2,
    -h <= j.x <= -h+w.                            (7)

Indeed its lower j face is -h+t-1/2<=-h and its upper j face is
-h+t+1/2>=-h+w. The n interval is independent of t. Thus every central
completion unit must be interior-disjoint from the entire rectangle (7),
for every allowed original transmitter position. This supplies a real
occupied obstacle in addition to the contact-polygon half-planes.

For the familiar contained-unit support threshold

    d=sqrt(q-1/4)-1,

one has B<=d+1/2. In particular an exterior-empty channel with h>d has
the strict lower bound

    w>=h-d>0.                                    (8)

Thus the same high channel which excludes an exterior unit also forces
its original side transmitter to occupy a positive-width part of the
central side. This is a whole-domain necessary geometric constraint,
not a completed central-capacity or coupled-pockets theorem.

## 5. What the identity does and does not prove

The all-singleton theorem uses ell_i=1 and consistent chi_i to identify
its translated vectors with the six derived corners in
TRIANGLE_SQUARE_CORNER_FERMAT_BOUND.md. For a shared interface, neither
ell_i=1 nor that derived-corner identification follows. The exact
identities (2)--(5) therefore do not justify applying the old Fermat
constant to the full remaining physical domain.

Exploratory numerical solutions of the local six-body equations were
found near R=1.9896, above 79/40, with mixed chi=(1,1,0), exactly one
outgoing shared interface and three distinct port chords. They pass
numerical circle, force, torque, actual channel, nonoverlap and strict
singleton-side-interior checks. These are **diagnostic data, not accepted
exact counterexamples or proof premises**. They make a proposed universal
core contradiction suspect even after coincident ports have been excluded.

The corresponding diagnostic contact hexagons have area below two and
one exterior channel height above the contained-unit support threshold.
Their contact hexagons nevertheless admit a whole central unit. Thus a
transfer of the one-diagonal central-empty proof is not justified by
those tests. A promising remaining obligation is a uniform coupled
capacity bound for the central region and the two potentially nonempty
exterior pockets, retaining the three actual transverse transmitter
positions. No such capacity bound is proved here.

No existing gate is closed or subdivided by this source. The full
all-unique/shared C6 gate, all equality claims and the unrestricted bound
remain open. No Lean compilation or CI was run.

## 6. Subsequent complete double-share exclusion

SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md now excludes every
original transmitter genuinely shared with both loaded neighbors.
Its complete exact circle/torque proof and 209-coefficient certificate
have independent full-source and global-normalization review in
REVIEW_SIX_CYCLE_DOUBLE_SHARED_CHANNEL_2026_10_25.md.

Together with at most one genuine share per loaded body, this makes
the remaining shares a matching in the original alternating cycle.
If there are three, they are one of the two cyclic perfect matchings:
all incoming with chi_i=0, or all outgoing with chi_i=1, in the
unchanged Section 3 chart. No remaining mean or chord is replaced
by a singleton value. The one-, two- and three-share completion
problems remain open with all original transverse intervals and
all three physical extras retained.

## 7. Subsequent complete three-share exclusion

SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md now excludes both
complete three-share matchings. The incoming matching has the exact
mean-preserving value R sum |F_i| = sum mu_i(2+sin(theta_i)-cos(theta_i)).
A whole-angle inequality for every positive force triple gives
R<79/40. Its full saved-source and independent 45-coefficient/inverse
review is REVIEW_SIX_CYCLE_THREE_SHARED_MATCHING_2026_10_25.md.

At that checkpoint, exactly one or two genuine shares remained in the all-unique C6,
with the entire original support functional, all actual means,
full transmitter sliders and all three extras unchanged. Their
original three-extra completion capacity remains open.

## 8. Current complete contact cover and actual completion residue

The independently reviewed full assembly
SIX_CYCLE_TWO_SHARE_COMPLETE_EXCLUSION.md now excludes the entire
two-share family over all three original contact orbits.
SIX_CYCLE_ONE_SHARE_FULL_ORBIT_COVER_AND_RESIDUE.md then gives the
exact four-orbit one-share cover. Constant corner bits, mixed sole
outgoing share 1, and mixed sole incoming share 2 are all excluded.
Only canonical mixed bits 110 with sole outgoing share 0 remain,
up to the exact physical symmetries.

Every identity and actual-slider constraint in this support source
is retained. The remaining chord is strictly shorter than one by
actual closure; its endpoint has an explicit contradiction.
SIX_CYCLE_ALL_SIDE_CENTRAL_CAPACITY_ONE.md gives at most one central
extra, and SIX_CYCLE_REMAINING_ONE_SHARE_CHANNEL_1_EMPTY.md proves
the entire actual exterior pocket 1 empty, with its height exceeding
the whole-unit support threshold by more than 1/100. The latter
theorem also gives an occupied inward transmitter rectangle for
every original allowed slider.

The exact remaining three-extra completion has seven count
allocations in pockets 0 and 2 and the possible central region.
Repeated occupancy of a pocket remains included. These contact-type
and cap reductions do not exclude the remaining completion or the
strictly obtuse one-radial family. The numerical diagnostics in
Section 5 remain diagnostics, not proof premises.

