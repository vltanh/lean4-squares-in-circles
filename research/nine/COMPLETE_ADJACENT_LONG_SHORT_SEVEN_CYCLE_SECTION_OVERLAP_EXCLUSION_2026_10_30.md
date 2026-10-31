# Every adjacent long/short seven-cycle forces overlapping actual sections

Date: October 30, 2026 UTC.

**Status: complete proposed continuous family exclusion, awaiting full
independent review. Both aligned and tilted long endpoints are included.**

The exact aligned overlap argument was developed by the root agent.
The tilted extension combines the actual return-wrapper profile of
axial_chain with the coupled endpoint-height estimate. The endpoint's
horizontal tilt is charged to the same width excess that strictly raises
the sum of the two actual endpoint support heights. The resulting overlap
has the uniform exact reserve 461/56160.

The previously frozen aligned conditional source remains unchanged.
All squares, original force normals, means, individual circle weights and
full stars in the caller below are retained. No common frame is imposed
on the return squares or their transmitter.

Put Q=1105/256, z=5/4, and g(Y)=sqrt(Q-Y^2).

## 1. A force-free obstruction with a quantitative tilt budget

Let actual unit squares C,D have disjoint open interiors and lie in
a centered disk with 2<=R<=sqrt(Q). Suppose C physically touches the
circle and its center direction is in (75 degrees,105 degrees).
Let E,b,x,f_A,f_B satisfy

    0<=E<=1/30,
    0<=b<=2E+(30/13)E^2,
    x<61/60+b,
    3/8<=f_A,f_B<=1/2,
    f_A+f_B>=7/8+L(E),
    L(E)=2E-(320/39)E^2.                            (1)

Suppose y=z lies strictly between D's two horizontal supports and
write r_D for the right endpoint of its actual section. Require

    (c_D)_x<-1/2,
    r_D>=1-g(f_A+1).                                (2)

Finally let n=(-alpha,beta), alpha,beta>0, alpha^2+beta^2=1,
be an actual direction such that every actual point c in C satisfies

    n.c>=n.(x,f_B)+1.                               (3)

No force equation, contact ownership, endpoint frame or orientation of
C,D is required for this geometric statement.

**Theorem 1 (uniform asymmetric section obstruction).** Conditions
(1)--(3) are impossible. Their actual sections would satisfy both

    r_D<=ell_C

and

    r_D-ell_C>461/56160>0.                          (4)

Here ell_C is the left endpoint of C's full actual section at y=z.

### 1.1 The actual section width and interval order

The complete one-unit near-vertical estimate gives

    C subset {y>83/160},
    length(C intersect {y=z})>=1,
    (0,z) in int(C).                                (5)

This is a one-unit consequence of physical boundary contact, the sector
(75,105 degrees), and the radius window. It does not require the presence
of three returns. Its full proof is in Sections 2--3 of the frozen
high-middle/unit-section source, with the one-unit scope explicitly
restated in Section 1 of the frozen three-return ordering source.

Every horizontal interior section of a unit square contains an actual
point with x coordinate in [c_x-1/2,c_x+1/2]. Join the bottom and top
support vertices, whose horizontal offsets have magnitude at most one
half; in the aligned case use the supporting-side midpoints. The joining
segment lies in the square. Applied to D and (2), this gives a negative
point in its section.

The section of C contains zero in its open interval by (5). The two
open intervals are disjoint because they are subsets of the original
open square interiors. D's interval cannot be to the right of C's.
Therefore their physical order is

    I_D on the left, I_C on the right, r_D<=ell_C.    (6)

The order follows from actual contained points, not merely from center
angles or an assumed horizontal separation of the squares.

### 1.2 The original supporting halfplane controls the whole C section

Put k=z-f_B, so 3/4<=k<=7/8. For every actual section point (X,z)
of C, condition (3) gives

    X<=x+(beta*k-1)/alpha.

The positive square-root comparison

    (1-beta*k)^2-alpha^2*(1-k^2)=(beta-k)^2>=0

shows that r_C<=x-sqrt(1-k^2). Since the actual section width is
at least one by (5),

    ell_C<=x-sqrt(1-k^2)-1.                         (7)

This uses the full occupied section. No floor or own-axis direction is
assigned to C or to an omitted intermediate square.

### 1.3 The extra actual height pays for horizontal tilt

The coupled height premise in (1) gives

    f_A+1>=k+5/8+L(E).                              (8)

On 0<=E<=1/30, L(E)>=0. Also k+5/8 is in [11/8,3/2], and
(8), together with f_A<=1/2, keeps the whole intervening height
interval at most 3/2. On this interval,

    -g'(Y)=Y/g(Y)>=22/sqrt(621)>7/8.                (9)

The final strict comparison is equivalent after positive squaring to
176^2>49*621, with exact reserve 547. Integrating the derivative
bound, including L(E)=0, yields

    g(f_A+1)<=g(k+5/8)-(7/8)L(E).                   (10)

As in the aligned proof, the function

    H(k)=g(k+5/8)-sqrt(1-k^2)

is strictly increasing on [3/4,7/8]. Its derivative sign, after
clearing positive denominators and squaring, is equivalent to
Q*k^2>(k+5/8)^2. This follows from Q>4 and k>5/8.
Consequently

    H(k)<=23/16-sqrt(15)/8<153/160,                 (11)

where sqrt(15)>77/20 is an exact positive squared comparison.

Using (2), (7), (10), (11), and x<61/60+b, one obtains

    r_D-ell_C
      >=2-x-g(f_A+1)+sqrt(1-k^2)
      >=2-x-H(k)+(7/8)L(E)
      >13/480-b+(7/8)L(E).                         (12)

The same E controls the allowed horizontal loss:

    b-(7/8)L(E)
      <=2E+(30/13)E^2-(7/8)*(2E-(320/39)E^2)
       =E/4+(370/39)E^2
      <=1/120+37/3510.                             (13)

Substitution in (12) gives the exact strict overlap

    r_D-ell_C
      >13/480-1/120-37/3510
       =461/56160>0.

This contradicts (6) and proves Theorem 1. The entire closed scalar
interval and every original normal direction in the declared quadrant
are covered. At E=0 the same proof also contains the aligned case.

## 2. Complete unchanged-certificate adjacent-cycle domain

Retain one physical force-and-torque certificate containing the positive
simple cycle

    A -- U -- V -- B -- W -- C -- D -- A.            (14)

The actual marked units A,B,C,D physically touch the containing circle.
The internal units U,V,W are unloaded and have full true positive degree
two in that same certificate. A and B also have full true positive degree
two. The marked returns C,D may have arbitrary additional positive edges.
All other physical squares, their poses and all their restrictions remain
present. The cycle has the compatible physical routing and circle spokes
required by the adopted marked-order theorem.

Rotate about the unchanged disk center so that the signed long normal
from A to B is e_x. No endpoint alignment is assumed. No mean is
identified with a center. No physical boundary contact is assigned to W.

**Theorem 2 (complete adjacent long/short seven-cycle exclusion).**
There is no configuration satisfying this whole domain with q<=Q.
The conclusion covers the entire adjacent run-count orbit (2,1,0,0),
including every endpoint tilt, actual side-mean interval and circle mask.
It holds even at Q and permits arbitrary full positive degree at C,D.

### 2.1 Literal entry from the frozen adjacent reduction

The complete source

`ADJACENT_LONG_SHORT_CYCLE_ORIGINAL_NORMAL_CONE_AND_ENDPOINT_VERTEX_REDUCTION_2026_10_30.md`

has SHA256
`9884cab15c74c2e15e44ad05c5d1665c93a46244aa7321c2b4a8c1675e65611b`.
Its full unchanged-certificate domain is exactly (14). It gives, after
one common reflection,

    C,D subset {y>1/120},
    88 degrees<arg(c_C)<103 degrees,
    129 degrees<arg(c_D)<144 degrees.                (15)

It also determines the unchanged B--W--C normal to be strict northwest,
and the actual B--W mean to be B's upper-inner vertex, even though W
may be circle-clear. This is the original normal, not a later geometric
selection. The full angular equations at the long transmitters give

    q_A=(s-1,t), q_M=(s,t), q_B=(s+1,t),
    |s|<1/60, |t|<=9/16,
    (2+|s|)^2+t^2<=q.                               (16)

The long signed support gap is two, so the endpoint center projection
gap is at least three. At least one actual endpoint center has norm at
least 3/2. The universal farthest-corner estimate therefore gives

    q>=17/4>4.                                     (17)

Thus every lower-radius premise used below follows from the actual long
channel; it is not a separate window assumption.

### 2.2 Actual heights and the common tilt budget

For each endpoint let a_i>=b_i>=0 be the absolute coefficients of
its dominant near-horizontal own axis. Put

    w_i=a_i+b_i, delta_i=w_i-1,
    E=(delta_A+delta_B)/2.

The actual coupled endpoint theorem gives

    0<=E<1/30,
    1-a_i<=(15/26)delta_i^2,
    |y_A|+|y_B|<=1/8-E+(320/39)E^2<=1/8.             (18)

The full endpoint equations in the adjacent reduction and the literal
A--D boundary contact-locus input give nonpositive center heights at
both endpoints. Here is the whole mixed-case check. If both endpoints
are aligned, this is the aligned conclusion already proved in that
input. If either is tilted, the actual common force line satisfies
t<-1/2. A tilted endpoint has the negative tilt sign and negative
center height. An aligned other endpoint contains its long mean on
its inward vertical side, so y_i<=t+1/2<0. This last geometric
statement does not assume that W is physically boundary.

Define the highest actual horizontal support heights

    f_i=y_i+w_i/2.                                  (19)

If an endpoint is aligned, f_i=y_i+1/2 lies in [3/8,1/2]. If it
is tilted, its reflected right-endpoint chart has axes
u_i=(a_i,-b_i), v_i=(b_i,a_i), with
a_i>399/400 and b_i<7/100; its upper-inner vertex is the highest
vertex and has height f_i=t+a_i. Therefore

    87/200<f_i<1/2

in that branch, by (16). Thus in every case

    3/8<=f_A,f_B<=1/2,
    f_A+f_B>=7/8+2E-(320/39)E^2.                    (20)

The last inequality follows directly from (18) and
(w_A+w_B)/2=1+E. It uses the actual support heights, not horizontal
sides artificially assigned to tilted squares.

In the actual B chart its upper-inner vertex is

    p_B=(x_B,f_B), x_B=s+1+b_B,                     (21)

also when b_B=0. Moreover

    b_B=delta_B+(1-a_B)
       <=delta_B+(15/26)delta_B^2
       <=2E+(30/13)E^2.                            (22)

Together with |s|<1/60, this supplies all scalar premises (1) of
Theorem 1 using b=b_B and x=x_B. The zero-at-E=0 bound (22) avoids
an unnecessary constant loss in the tilt correction.

### 2.3 The complete D profile at its actual endpoint height

The center direction of D in (15), its physical boundary status and
R>=2 imply

    (c_D)_x<-(1/2)(R-1/sqrt(2))<-5/8<-1/2.          (23)

It remains to give its actual interior section and right profile at
f_A, retaining every original contact alternative.

If A is aligned, the complete above-side boundary contact locus and
the frozen aligned corner-wrapper theorem apply to the actual A--D
contact. The above-floor alternative uses the full unequal-floor
profile; the below-floor alternative uses the actual side slider.
After reflection in the y axis, they give a section strictly between
D's horizontal supports and

    r_D>=1-g(f_A+1).                                (24)

If A is tilted, use the new complete tilted-wrapper source

`TILTED_LONG_ENDPOINT_RETURN_WRAPPERS_OBEY_THE_SHARP_SECTION_PROFILE_2026_10_30.md`,
SHA256 `c7553b418c64c12bda69bcccb565e6f5d7cdd1613dbb8eecfe282ce6126a26c3`.

Its geometric Theorem 2 applies after reflecting A to the right.
The actual parameters are s'=-s, the unchanged t, and a_A,b_A;
equations (16)--(20) supply its entire geometric window. The actual
A--D return point is the upper-inner vertex by the frozen adjacent
reduction and the literal full true-degree-two endpoint theorem.

For completeness, the needed strict global northwest normal in this
reflected chart is local to A's own full equations. Its original
return has positive y component. With X=1-s and tau=-t, the complete
two-circle calculation in Section 5 of the new source gives

    -n_x/n_y
      >=[tau*(a_A-b_A)-b_A*(X+b_A)]/[a_A*(tau+b_A)]
      >7401/10960>2/3.                              (25)

This calculation retains both physical circle weights and uses only
the full original star at A and its physical boundary neighbor D.
It does not require a boundary neighbor at the other endpoint B and
does not apply the two-boundary-neighbor caller to W. Thus the
geometric profile theorem's original-normal premise is supplied
literally at A. Its complete vertex/side cover gives (24) and the
actual interior section also in the tilted branch.

Equations (23)--(24) establish every D premise in (2). The profile
is not imposed at a fictitious flat side of a tilted endpoint.

### 2.4 The near-vertical C section and original short support

By (15), C's center lies in the sector (75,105 degrees), so the
one-unit result (5) applies to the actual C. In particular it has
the required full section width and contains (0,z) in its interior.

The full unloaded degree-two force equation at W propagates the same
unchanged normal n=(-alpha,beta), alpha,beta>0, on B--W--C.
Telescoping the two actual support equalities gives the support gap
from B to C equal to the original width w_W(n)>=1. Since B's actual
support point in this normal is precisely (21), every point c in C
satisfies

    n.c>=n.p_B+w_W(n)>=n.(x_B,f_B)+1.                (26)

No mean is centered and no frame is assigned to W. Equation (26)
is exactly premise (3), in the original normal already proved by
the adjacent reduction.

All hypotheses of Theorem 1 now hold. Its strict actual overlap
reserve 461/56160 contradicts nonoverlap of C,D. This proves
Theorem 2 for all aligned, mixed and both-tilted endpoints.

## 3. Scope and frozen inputs

The result excludes an actual compatible marked cycle wherever it occurs
in the unchanged positive graph. It need not be an entire connected
component: C,D may carry arbitrary additional positive edges and all
other physical units remain. The full true-degree-two assumptions at
A,B,U,V,W are literal and cannot be replaced by degrees only in the
drawn cycle.

No set distance between C,D is inferred from their horizontal sections.
The proof instead obtains their actual interval order and a positive
overlap in that same horizontal slice. Neither the earlier opposite
return-alignment theorem nor its set-gap hypothesis is needed.

The exact six-unit subcritical diagnostic in the adjacent reduction is
preserved. It lacks the actual boundary return D with its required
contact and profile, and lacks the remaining complete endpoint data.
The present contradiction uses precisely that additional geometry.

The remaining frozen inputs are:

| Source | SHA256 | Role |
| --- | --- | --- |
| THREE_BOUNDARY_RETURNS_FORCE_A_HIGH_MIDDLE_UNIT_AND_A_UNIT_SECTION_2026_10_30.md | `99c6d7fc3bb50cf65f8ee36ef1e041dafb344671a5a09830e691746ef1f7f528` | One-unit near-vertical interior point and full section width |
| THREE_RETURN_SECTION_ORDER_AND_ALIGNED_LONG_PAIR_SHARP_COMPLETION_2026_10_30.md | `95918400fc3aa701d8e62beff8047f4b01ff4e20a5dd8e234fe37ea319885db8` | Explicit one-unit scope and actual central-band section point |
| TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md | `78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6` | Coupled heights and quadratic orientation estimate |
| LONG_ENDPOINT_RETURN_CONTACT_LOCUS_FORCE_LINE_SIGN_AND_TILTED_VERTEX_REDUCTION_2026_10_30.md | `cf942c1069e451ad043c80c8075fd67c85d2b71faa05c29b9baa3dae32f66fe3` | Literal boundary return locus and full endpoint tilt equations |
| UNIFORM_UNEQUAL_FLOOR_SECTION_PROFILE_AND_TWO_UNIT_CAP_METRIC_2026_10_30.md | `abfb4887037851d2715c8ff746ff11dc238109692b2cc0fbc42598bb4dae9d94` | Complete above-floor section profile |
| ALIGNED_ENDPOINT_CORNER_WRAPPERS_OBEY_THE_UNEQUAL_FLOOR_SECTION_BOUND_2026_10_30.md | `55607f2ab5a25c056fcc12e893b3d4c7e60814c6d2e607c21b806277d29de5bc` | Every actual aligned-endpoint boundary wrapper |
| ALIGNED_ADJACENT_LONG_SHORT_SEVEN_CYCLE_SECTION_OVERLAP_EXCLUSION_2026_10_30.md | `f7694cc75e45b49bd05fa106f03267c7465c622d44d6896d8090d3f09704e686` | Earlier frozen aligned proof, preserved unchanged |

The two principal adjacent-normal and tilted-wrapper sources are pinned
at their literal uses above. Every new comparison is an exact analytic
inequality over a continuous domain. This source uses no numerical pose
search, orientation grid, altered force certificate, removed square,
original ledger mutation, Lean compilation, CI run or publication.
