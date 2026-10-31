# The full four-load house reduces to a collinear wall or one specified free endpoint

**Status: complete hand endpoint-owner and physical-mask reduction;
root and separate independent full hand audits passed.** The parent
four-load house remains open. Work in
\[
 79/40\le R\le\sqrt{1105}/16
\]
with the exact house graph of `FIVE_BODY_BICONNECTED_REDUCTION.md` and
loads1,2,3,4. Write
\[
 H=5,\quad A=3,\quad B=1,\quad C=4,\quad D=2.
 \tag{1}
\]
The boundary path is A--B--C--D. The clear hub has exactly the three
positive spokes HA,HB,HD. In particular HC is absent. The true
endpoint bodies A,D have positive degree two; B has degree three and
C degree two. All four completion squares, every physical circle
mask and every actual side mean remain.

**Theorem.** Every surviving selected four-load house belongs to at
least one of the following two full domains:

1. Both endpoint normals are H-owned. They and the inner hub normal
   are collinear: \(n_A=n_B=-n_D\), with the actual weighted transverse
   mean identity in Section8.
2. HD is genuinely free, D has exactly one physical circle corner,
   and the actual boundary intersection CD is a positive-length shared
   side. The whole other endpoint HA remains arbitrary in this domain.

These are remaining domains, not assertions that either admits a
positive core. The proof gives all mixed transfers with the missing
HC edge explicitly absent. No normal is changed after selection.

## 1. Common physical facts and the true-origin estimate

Let F_A,F_B,F_C,F_D be the original circle resultants. The actual
three-body path B--C--D and `THREE_BOUNDARY_PATH_RESULTANT_CONE.md`
give positive u,v with
\[
 F_C=uF_B+vF_D,\qquad
                   F_A+(1+u)F_B+(1+v)F_D=0.
 \tag{2}
\]
The second identity rewrites the full component balance using only
the three actual H neighbors. Normalizing its positive physical
corner weights gives exactly the geometric estimate
\[
                       R^2+|c_H-O|^2\le\frac92.
 \tag{3}
\]
Here O is the true disk origin in any translated contact coordinates.
Every included corner is within \(3/\sqrt2\) of c_H by its actual H
contact. This is only a convex-combination identity; every subsequent
force and torque equation is the original, unmodified certificate.

`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` gives distance greater
than1 between every pair of actual HA/HD applications, a minor
endpoint center angle greater than150 degrees, and a minor endpoint
resultant angle greater than120 degrees. Every resultant is within
15 degrees of its own center. All nonconsecutive boundary bodies are
physically closed-disjoint: an extra contact AC or BD makes a boundary
triangle, and an extra AD makes a boundary four-cycle. These are
excluded by the physical boundary-contact theorem.

The selected planar house has exterior cycle H,A,B,C,D,H. Thus the
one actual inner hub spoke HB lies on one of the two H boundary arcs
between the endpoint contacts, with that physical order. There is no
HC spoke, force or application in this assertion.

## 2. The mixed hub-owned domain and its entire corner-mean limit

Suppose precisely one endpoint normal is an H axis. Reverse the
boundary path if needed and call that endpoint S, the other E. Rotate
and translate for contact geometry:
\[
 H=[0,1]^2,\quad P=(p,1),\quad n_S=e_y,\quad
 Q=(0,0),\quad n_E=(-a,-b),\quad a,b>0,
 \quad0<p\le1.
 \tag{4}
\]
This is the full endpoint-set argument of
`FAN_ENDPOINT_OWNER_REDUCTION.md`, Section2: the other contact is an H
vertex, and every actual point of the first top-side contact has
positive first coordinate. P may be an endpoint-valued shared mean.

In each of the tip-owned and radial-free cases treated below, the
actual inner HB application is distinct from Q. For a tip-owned E,
the tangent half-plane of E and the H quadrant exclude every third
square at Q. For a radial-free E=D, B is nonconsecutive to D and is
physically disjoint from it. For a radial-free E=A, the genuine
triangle H,A,B gives the local radial routing of
`BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md`, Section1: the AB contact
is the other inner vertex, so B does not contain Q. This last routing
uses only A's true degree-two equations; it does not treat B as a tip.

On the short top/left H arc from P to Q, the inner normal has
nonpositive first coordinate. The only possible exception is a
coincident application at P when p=1. If S=D, the sole inner body B
is nonconsecutive to D, so there is no such coincidence. If S=A, the
full p=1 check in `FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md`, Sections2--3,
applies unchanged to B, its actual boundary neighbor: it retains the
whole shared endpoint interval, excludes the coincident degree-two
tip applications, and routes any horizontal rightward contact onto
the long arc. Its final aligned corner limit would force a zero
boundary moment and is impossible. That local check uses no other
inner hub spoke.

Thus, on a genuine short-arc order, the three actual hub forces have
zero, nonpositive and strictly negative horizontal components. Their
positive sum cannot vanish. The physical path follows the long
top/right/bottom arc, clockwise. The endpoint torque at S then gives
\[
                          O_x>p>0.
 \tag{5}
\]
The directed moment sign used here is the complete physical boundary
normal sign, valid for every shared mean. Only the three true hub
forces were used to obtain (5).

## 3. Either mixed hub/tip-owned assignment is impossible

Suppose E in (4) is a singleton in a relative side interior of its
boundary tip. With (3)--(5), all hypotheses of the local parts of
`FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md`, Sections4--7, are now present.
We record their precise remaining data so this is not a deletion of a
fan force equation.

Proper concurrence applies only to the two genuine endpoints. Their
resultants are respectively northwest and southwest: both have
negative first coordinate by (5), and the strict120-degree separation
excludes either possible same vertical sign. Estimate (3) gives
\(O_y<13/10\). The all-mask own-frame check therefore puts their
centers in the corresponding left quadrants. Write their angles from
the upper and lower vertical axes as \(\delta_S,\delta_E\ge0\).
The actual clockwise three-link path gives
\[
 \delta_S+\delta_E<\alpha:=3\arccos(9/25)-\pi<\pi/6,
 \quad\cos\alpha>89/100,\quad\sin\alpha<9/20.
 \tag{6}
\]
Put \(\sigma=1/\sqrt2\), \(d=\sqrt{R^2-1/4}-1>9/10\).
The first endpoint's actual supporting height gives
\[
 1-O_y\ge(R-\sigma)\cos\delta_S-\sigma.
\]
The full side-interior chart at E, including either physical circle
mask and its true side parameter, gives
\[
 O_y\ge d\cos\delta_E-\frac35\sin\delta_E.
 \tag{7}
\]
These are the scalar calculations in the cited Sections5--6; neither
uses a hub force or an internal body equation. Concavity at fixed
angle sum leaves the two endpoint lower bounds
\[
                       727/560>1,
                       \qquad1081/1000>1
\]
for the sum of the right sides of (7) and the preceding inequality.
They contradict \((1-O_y)+O_y=1\). Thus both assignments
S=A,E=D and S=D,E=A are fully excluded.

## 4. Either mixed hub-owned/radial-free assignment is impossible

Now let E in (4) have two physical circle corners and a free contact
at Q. Write its physical radial square as
\[
                [d,d+1]e+[-1/2,1/2]f,\qquad f=Je,
 \quad d=\sqrt{R^2-1/4}-1.
 \tag{8}
\]
A circle point cannot be shared, so its free vertex Q is one of the
two inner vertices. The strict normal is inward at that vertex.
The actual clockwise endpoint torque makes
\(\det(Q-O,n_E)>0\): the incoming boundary-edge moment is negative.
At the upper inner vertex the inward normal is
\(\cos\eta\,e-\sin\eta\,f\), \(0<\eta<\pi/2\), and its
moment is \(-d\sin\eta-(1/2)\cos\eta<0\). Therefore the full
physical mask, without any assumption on the other contact feature,
necessarily has
\[
 Q-O=d e-\tfrac12 f,\qquad
 n_E=\cos\eta\,e+\sin\eta\,f,
                      \qquad0<\eta<\pi/2.
 \tag{9}
\]
This derivation is essential for E=D, where HC is absent. No triangle
H,D,C or opposite-inner-vertex conclusion about DC has been used.

Equation (3) gives \(-1/2<O_y<3/2\). Since n_E is strictly southwest,
(9) initially puts the direction of e between90 and270 degrees. A
northwest e would make \((Q-O)_y\ge1/2\), contrary to \(O_y>-1/2\).
Thus e is southwest. Writing its angle from the lower vertical axis
as \(\delta_E\in(0,\pi/2)\), (9) gives exactly
\[
                      O_y=d\cos\delta_E-\tfrac12\sin\delta_E.
 \tag{10}
\]
The all-mask center calculation for the H-owned endpoint in
`FAN_HUB_OWNED_RADIAL_FREE_ENDPOINT_EXCLUSION.md`, Section4, uses
only (5), \(O_y<3/2\) and its true proper concurrence. It puts its
center northwest, at angle \(\delta_S\ge0\) from the upper vertical.
The three actual boundary contacts again give (6), and its true
application height gives
\[
 1-O_y\ge(R-\sigma)\cos\delta_S-\sigma.
 \tag{11}
\]
Adding (10)--(11) and minimizing the concave expression at the two
endpoint angle allocations gives, exactly as in the cited Section6,
the strict lower bounds269/250 and101/80 for a quantity at most1.
This contradiction covers both endpoint assignments and every radial
corner-weight split. Only the physical radial frame, the endpoint
torque and the actual three-link path were used at D.

## 5. A physically unique free roof endpoint A is always impossible

If AB is a singleton, the existing fixed-tip selection excludes the
free HA normal. Its coincident radial-D exception cannot be a contact
with a boundary neighbor. It remains to retain a genuine AB shared
side and all of its actual means.

The complete local chart of
`FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md`, Sections2.1--2.2, applies
to the actual triangle H,A,B: it gives a positive parallel offset,
the exact endpoint normal slope and the strict H vertex at Q. It
does not use the other endpoint or give B a degree-two equation.

If HD is not H-owned, the two H endpoint vertices are opposite by
the whole-path distance theorem. Section2.3 of that source then
provides the strict wrong-sign hub torque about the opposite vertex.
Its one actual inner HB force has nonpositive moment and the HA
force has strictly negative moment. The opposite HD force has zero
moment. The absent HC contribution is not needed. Thus this case is
impossible regardless of D's physical mask.

If HD is H-owned, use the complete local and scalar proof in
`FAN_UNIQUE_FREE_SHARED_ENDPOINT_EXCLUSION.md`. The actual H--B
contact forces its exact shift t=c, the inner normal e_x, and the
complete two-body circle equations. Its first opposite-side option
already contradicts the three actual hub moments. In the second,
the original three-force w-coordinate and torque equations are
\[
 \mu_B c=\mu_A A_0,
 \qquad
 \mu_A(A_0-pB_0)+\mu_B\bigl(d_0(1-p)-c\bigr)=0,
 \tag{12}
\]
in that source's notation, where
\(A_0=b d_0-a c>0\), \(B_0=a d_0+b c>0\), and
\(c^2+d_0^2=1\). No fourth hub force appears in (12). These equations
give the stronger equality
\[
 p=\frac{A_0d_0}{A_0d_0+B_0c}\le d_0(d_0-c).
 \tag{13}
\]
The complete all-mask circle and scalar argument in its Sections3--8
uses only this upper bound. It gives \(|P-O|<11/20<R-\sqrt2\) for
the actual HD application P, impossible because D touches the circle.
All of its interval endpoints and both masks of B remain. Thus HA
cannot be a positive physically unique free endpoint in either
owner assignment of HD.

## 6. Neither endpoint H-owned: all remaining tip/radial mixtures are excluded

Discard only the specified remaining domain2 of the theorem for this
step. A free unique D with a singleton DC contact is removed by the
existing fixed-tip selection; Section5 removes every free unique A.
Thus, when neither endpoint is H-owned, both are either tip-owned
side-interior contacts or physical radial-free contacts.

Their actual H applications are opposite vertices. The sole internal
HB application is distinct from both: at a tip-owned endpoint this is
the tangent-sector fact; at radial A it follows from the true H,A,B
triangle routing; at radial D it follows from the physical noncontact
BD. Consequently the same one-inner-port order and full hub moments
as in `HOUSE_FOUR_LOAD_TIP_OWNED_ENDPOINT_EXCLUSION.md` apply.

Rotate about the true origin so the endpoint chord is horizontal,
and reflect the path so the inner H arc is the lower one. With
\(\sigma=1/\sqrt2\), the resulting actual data are
\[
 P_A=(-X_A,h),\quad P_D=(X_D,h),\quad
 X_A,X_D>0,\quad X_A+X_D=\sqrt2,\quad h>0,
\]
\[
 n_A=(-\cos\phi_A,\sin\phi_A),\quad
 n_D=(\cos\phi_D,\sin\phi_D),\quad0\le\phi_i\le\pi/4.
 \tag{14}
\]
The true-origin step uses (3), and only the one HB force enters the
two endpoint moment signs. The boundary path is counterclockwise.

Each tip-owned endpoint has the complete all-mask scalar bound
\[
                       X_i\ge d\cos\delta_i-\tfrac35\sin\delta_i
 \tag{15}
\]
from the already audited house tip-owned source. This is a local
one-endpoint calculation. Each radial-free endpoint has the stronger
exact formula
\[
                        X_i=d\cos\delta_i-\tfrac12\sin\delta_i.
 \tag{16}
\]
To justify (16) also at D without an H,D,C triangle, use the endpoint
origin-moment sign in (14). It fixes the radial inner-vertex sign
exactly as (9), with reflection at the other endpoint. Strictness of
the actual free normal then gives the same radial direction and
formula as `FAN_NON_HUB_OWNED_ENDPOINT_EXCLUSION.md`, Section4.
No statement about D's other contact feature is needed for this
calculation. Its center lies in the strict upper quadrant; tip-owned
centers allow the horizontal endpoint.

Both actual center angles obey (6) with the horizontal endpoint rays
in place of the vertical ones. The complete scalar concavity argument
therefore gives
\[
 \sqrt2=X_A+X_D>
 d(1+\cos\alpha)-\tfrac35\sin\alpha
 >\frac{1431}{1000}>\sqrt2.
 \tag{17}
\]
This excludes all the remaining neither-H-owned mixtures, with the
single internal hub force and the true two endpoint equations.

## 7. Exhaustion of the free and owned alternatives

If HD is unique and free, either its other boundary contact DC is
a singleton or a positive-length shared side. Fixed-tip selection
excludes the former, and the latter is precisely remaining domain2.
No midpoint or fixed mean has been assigned to that surviving side.

Outside domain2, Section5 removes every unique free HA endpoint.
If exactly one endpoint is H-owned, its other endpoint is therefore
tip-owned or radial-free, excluded by Sections3--4. If neither is
H-owned, Section6 excludes every surviving physical mask. Hence the
only remaining owner alternative is that both endpoints are H-owned.

## 8. The entire both-H-owned alternative is a three-collinear-normal wall

Let the two endpoint side axes of H be n_A,n_D, with the actual
inner normal n_B. The physical triangle H,A,B gives
\(n_A\cdot n_B\ge0\) by the side-normal triangle theorem. The full
three-force hub balance is
\[
                  \mu_A n_A+\mu_B n_B+\mu_D n_D=0,
                       \qquad\mu_A,\mu_B,\mu_D>0.
 \tag{18}
\]
Dotting with n_A forces \(n_A\cdot n_D<0\). Since both are H side
axes, they are opposite: n_D=-n_A. The perpendicular component of
(18), followed by \(n_A\cdot n_B\ge0\), gives
\[
                 n_B=n_A=-n_D,\qquad\mu_D=\mu_A+\mu_B.
 \tag{19}
\]
This conclusion retains every actual endpoint and inner side mean.
Let \(t_i=(Jn_A)\cdot P_i\) for those true applications. The hub
torque is precisely
\[
                         \mu_Dt_D=\mu_At_A+\mu_Bt_B.
 \tag{20}
\]
The strict endpoint-distance theorem gives t_D!=t_A, since their
normal coordinates differ by exactly1. Hence t_A!=t_B and (20)
puts t_D strictly between the other two actual transverse means.
The entire physical endpoint contact intervals are disjoint in this
transverse coordinate, again by their all-pairs distance greater
than1. No width, common frame or midpoint is imposed on A,B,C,D.

Sections1--8 prove the stated exhaustive two-domain reduction. The subsequent
HOUSE_FOUR_LOAD_COLLINEAR_WALL_EXCLUSION.md now excludes the entire
collinear wall, with root and independent full audits. Only the
unique-free D/shared-DC domain still requires a full core/radius or
joint exterior-completion exit. All four extra
squares and all actual zero-stress contacts remain. No numerical
cover, Lean compilation or CI is used as a premise.
