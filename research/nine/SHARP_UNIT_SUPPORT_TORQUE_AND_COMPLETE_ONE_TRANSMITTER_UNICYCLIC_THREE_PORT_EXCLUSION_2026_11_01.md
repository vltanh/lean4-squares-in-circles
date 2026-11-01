# Sharp unit-square support torque closes the entire one-transmitter unicyclic three-port module

Date: November 1, 2026 UTC. Constructor: four_chain continuation.

**Status: complete new hand proof, frozen for clean independent review.**
The proof includes every support owner, side-interior application mean,
side endpoint and original outside terminal identity. No mathematical
script, numerical pose, angle sample, Lean, build or CI was used.

## 1. Complete original theorem and exact inputs

Keep all nine actual closed unit squares with disjoint open interiors in
the same disk centered at O, in the original research window

    79/40 <= R <= sqrt(1105)/16,    Q=1105/256.

Retain the same compatible complete positive force-and-torque certificate,
all original magnitudes, normals, applications and full shared-side means,
every physical contact, circle corner and individual zero coefficient.
Use the original strict-singleton and compatible-selection premises of
the accepted common-side theorem below. No new normal is selected.

Suppose the entirely unloaded actual region K consists of four bodies
A,B,C,U. Its induced original positive edges are exactly

    AB, BC, AU, UC.

Its FULL original positive outside cut has exactly three edges: one at
each of A,B,C, and none at U. Thus the complete stars of A,B,C have
degree three and U has genuine full degree two. The three actual outside
neighbors may coincide; no terminal distinctness or outside equilibrium
assumption is added.

**Theorem 1. This entire original four-body module is impossible.**
It is exactly the remaining unicyclic row (t,s)=(1,0): one genuine
internal transmitter and three direct exits. The direct triangle row
(0,0) is not claimed closed by this manuscript.

Two previously reviewed exact inputs enter the local proof:

* `UNIT_BYPASS_NORMAL_CHANNEL.md`, Sections 1--2: the genuine U channel
  between A,C has side-normal width one because the actual unit B
  touches both A,C. The complete original U translation and torque
  propagate equal magnitudes and the actual common normal.
* `CYCLIC_THREE_PORT_COMMON_SIDE_EXCLUSION_AND_OBTUSE_DOMINANT_PAIR_2026_11_01.md`,
  Theorem 1: the original AB and BC applications cannot lie on one
  common closed B side. In particular their two outward B normals
  have nonpositive dot product. That theorem retains all original
  singleton and shared-side alternatives, including its full equality
  bypass case. Only this already proved common-side conclusion is
  imported; the sharper localization needed here is proved below.

The method of constructing disk points near both ends of a dominant
unloaded pair is credited to
`DOMINANT_UNLOADED_CONTACT_PAIR_IS_CENTRAL_2026_10_31.md` and its wider
constant version in the common-side source. Sections 2--3 below reprove
that entire local estimate using a new sharper support-torque bound.
No unprinted stronger localization is imported.

## 2. Sharp support torque at every actual application

**Lemma 2.** Let S be an actual unit square, q any maximum support point
for a unit normal n, and x any actual point of S. Then

    |det(x-q,n)| <= 1.                              (1)

The point q may be any closed side mean, including an endpoint.

### Proof

Use S=[0,1]^2 in its own orthonormal frame. If both components of n
are nonzero, q is the corresponding support vertex. Write

    x-q=(-sign(n_1) a, -sign(n_2) b),  0<=a,b<=1.

Up to one overall sign the determinant is |n_1| b-|n_2| a. It lies
between -|n_2| and |n_1|, so its absolute value is at most one.

If one normal component is zero, n is an own-side axis. The determinant
is, up to sign, the tangential coordinate difference of two actual
points of the unit square. Both tangential coordinates lie in the
same interval of length one. This also proves (1) for every interior
side mean and both side endpoints. QED.

Consequently, when moments are taken about any actual p of an unloaded
unit, a complete collection of other positive pair forces of total
magnitude r has total moment of absolute value at most r. This uses
each force's own actual support application; none is moved to p.

## 3. A dominant pair has its common application within 11/12 of O

**Lemma 3.** Let two actual unloaded units have a direct original
positive pair of magnitude d, unit normal n from the first to the
second, and common original application p. At each endpoint distinguish
one other positive force, retaining every remaining original force.
Let r_1,r_2 be the sums of all remaining magnitudes. If

    (r_1+r_2)/d < 3/40,

then

    |p-O| < 11/12.                                  (2)

This is a local theorem with arbitrary remaining degrees and means.

### Complete one-endpoint estimate

At the first endpoint write z,u,q for its distinguished force magnitude,
outward unit normal and unchanged actual application; put t=r_1/d.
Complete translation gives

    |d n+z u|<=r_1,    z>=d-r_1>0.

For delta=|u+n|, the exact identity

    |d n+z u|^2=(d-z)^2+d z delta^2

gives

    delta <= t/sqrt(1-t) <= sqrt(40/37)t < (26/25)t. (3)

The final strict numerical comparison follows from 25000<25012.
For t=0 all these quantities are zero. Complete torque about the SAME
original p, using Lemma 2 for every remaining force, gives

    |det(q-p,u)| <= r_1/z <= (40/37)t.              (4)

Here is the full disk-point construction. If a unit square maximizes
a unit normal n at p, it contains p-n: in each own coordinate, a
nonzero normal component begins at its signed support endpoint and
subtracting that component moves inward by at most one; a zero
component does not move. The minimum-support version therefore puts
q+u in the distinguished force's immediate actual neighboring square.

Write q-p=s u+v Ju and lambda=1-u dot n. Since q maximizes u and
p-n belongs to the first square, s>=-u dot n. Also delta<1 by (3),
so lambda>0 and s+1>=lambda. The point

    y=p+[lambda/(s+1)](q+u-p)
      =p+lambda u+[lambda/(s+1)]v Ju

lies in the original disk, by convexity between its two actual disk
points p and q+u. It is an auxiliary disk point, not a new contact.
Direct expansion gives

    |lambda u+2n|^2=delta^2(4-3delta^2/4)<=4delta^2.

Thus (3)--(4) imply the complete one-endpoint estimate

    |y-(p-2n)| <= 2delta+|v|
       <= (52/25+40/37)t
       = (2924/925)t < (19/6)t.                    (5)

The final rational comparison is 17544<17575. At t=0 the error
vanishes. Every original weak force and every moment is retained.

### Combine the original endpoints

The same argument at the second endpoint, using normal -n and the
SAME original p, supplies two points of the disk with errors whose sum
E satisfies

    |p-O-2n|<=R+epsilon_1,
    |p-O+2n|<=R+epsilon_2,
    E=epsilon_1+epsilon_2 < (19/6)(3/40)=19/80.

Squaring, adding and using epsilon_1^2+epsilon_2^2<=E^2 gives

    |p-O|^2+4 <= Q+R E+E^2/2.

The exact bound R<25/12 follows from Q<625/144. Hence

    |p-O|^2 < 81/256+95/192+361/12800
             =32233/38400 <121/144=(11/12)^2.       (6)

The reserve in the final comparison is exactly 101/115200.
This proves Lemma 3 in its complete local scope. QED.

## 4. Two incoming support gaps force a distant actual exit point

**Lemma 4.** Let C be an unloaded unit whose complete positive forces
are -b g, -mu e and z u, with b,mu,z>0 and unit normals g,e,u.
Let P be any actual reference point for which the whole actual C obeys

    g dot(x-P)>=1,    e dot(x-P)>=1    for every x in C. (7)

Then its actual neighboring unit on the z u force contains a point w
such that

    u dot(w-P)>=3.                                  (8)

No assertion that P belongs to C or to either incoming neighbor is
needed, provided the two actual support inequalities (7) are proved.

### Proof

Complete translation gives z u=b g+mu e, and z<=b+mu. Thus every
actual x in C satisfies u dot(x-P)>=(b+mu)/z>=1. The directional
width of the actual unit C is at least one, so its original maximum-u
exit application r satisfies u dot(r-P)>=2. The immediate outside
unit minimizes u at the same r and contains r+u by the unit support
segment fact proved above. Take w=r+u. This proves (8), with the
complete C forces and every actual application retained. QED.

In particular (8) is impossible whenever |P-O|<11/12: it would give

    |w-O| >= u dot(w-P)-|P-O| >3-11/12=25/12>R.    (9)

## 5. Exact original four-body work and force budget

The genuine U equations and the accepted bypass theorem give magnitude
mu>0 on AU and UC, a unit direction e from A toward C, and actual
applications a_0 in A and c_0 in C with

    c_0-a_0=e,
    max_A e dot x=e dot a_0,
    min_C e dot x=e dot c_0=max_A e dot x+1.          (10)

Every original U application height is retained. The width-one theorem
does not replace it by a side midpoint.

Interchange A and C if necessary so the original AB magnitude a is
at least the original BC magnitude b>0. Write f for the original
normal A-to-B, and g for B-to-C. Let p and q be the SAME original AB
and BC applications. The imported common-side theorem gives

    p,q do not lie on a common closed side of B,
    (-f) dot g<=0, hence f dot g>=0.                 (11)

Here is the full original work bound, without contracting U. Every
actual unit center c satisfies |c-O|<M=91/60. Its farthest-corner
formula gives |c-O|^2+|c-O|+1/2<=Q, and substitution of 91/60 has
strict positive reserve 31/57600. For an original cut from an inside
unit i to an actual outside unit j with normal v,

    v dot(c_i-O)=v dot(c_j-O)-h_i(v)-h_j(v)<M-1=31/60.

Dot and sum the complete translations of ALL FOUR members of K with
their centers relative to O. Every original internal pair contributes
its actual support work. This work is at least a+b+2mu, because the
four original internal edges have magnitudes a,b,mu,mu and width sums
at least one. If C_0 is the complete three-edge cut magnitude sum,

    a+b+2mu < (31/60) C_0.                          (12)

Complete translation at A,B,C and (11) give respectively

    z_A<=a+mu,
    z_B=|a f-b g|<=sqrt(a^2+b^2),
    z_C<=b+mu.

Thus

    29(a+b+2mu)<31 sqrt(a^2+b^2).                   (13)

Put t=b/a and tau=mu/a. Initially 0<t<=1. Dropping only the positive
2mu term from this necessary inequality and squaring gives

    120(1+t^2)-1682t>0.

This polynomial is strictly decreasing on [0,1] and has value
-219/40 at t=3/40. Therefore t<3/40. Returning to (13),

    t+2tau < (31/29)sqrt(1+t^2)-1
            < (31/29)sqrt(1609)/40-1 <3/40.         (14)

The last comparison follows from
31^2*1609=1546249 <1555009=1247^2 and 1247=29*43.

For the actual AB pair, distinguish the original outside exit at A
and at B. Their entire other original magnitude sums are mu and b.
Thus (14) implies (r_A+r_B)/a=t+tau<3/40, and Lemma 3 gives

    |p-O|<11/12.                                    (15)

## 6. Every B-vertex and every non-axis side-mean case closes

By (10) and the actual membership p in A, the whole C satisfies

    e dot(x-p)>=1.                                  (16)

It also satisfies g dot(x-p)>=g dot(q-p). We now prove

    g dot(q-p)>=1                                   (17)

in every case except one explicitly handled own-axis mean family.

### 6.1. The original strong application p is a B vertex

Place B=[0,1]^2 and p=(0,0) by an own-frame symmetry. If g has both
components nonzero, q is its uniquely exposed B vertex. By (11), q
can be neither p nor an adjacent vertex: each such pair belongs to
one closed B side. Thus q=(1,1), g has positive components, and
g dot(q-p)=g_1+g_2>=1.

If g is a B own-axis, its support side cannot be incident to p,
because then p and every permissible mean q would share that side.
The support side is therefore one unit away in direction g, giving
g dot(q-p)=1. This includes all q side endpoints and interior means.
No assumption about the owner or normal of AB was made here.

### 6.2. The original strong application p lies in a B-side interior

Use local own coordinates

    B=[0,1]^2, p=(0,h), 0<h<1, f=(1,0),
    g=(gamma,delta), gamma^2+delta^2=1.

These are local square coordinates; O remains the actual containing
disk center and is not identified with the chart origin. If gamma<0,
the support point q lies on the same left side as p, forbidden by
(11). Hence gamma>=0.

First let gamma>0. If delta=0, g=(1,0) and every permitted right-side
mean q gives (17) with equality. If delta is nonzero, reflect the
vertical coordinate so delta>0. Then q=(1,1). Since a>b, the full
B exit vector a f-b g has strictly positive first and strictly
negative second component. Its original B application is exactly
r_B=(1,0). Complete torque about r_B, retaining the actual AB and
BC forces, gives

    a h-b gamma=0, hence h=t gamma.

Consequently

    g dot(q-p)=gamma+delta-t gamma delta.

Both gamma and delta are positive. The exact identity

    gamma+delta-1=2 gamma delta/(gamma+delta+1)

and gamma+delta<=sqrt(2)<2 give

    g dot(q-p)-1
      =gamma delta[2/(gamma+delta+1)-t]>0,

because t<3/40<2/3. This proves (17), including the reflected
delta<0 family. No side mean at p has been replaced by an endpoint;
its exact height was obtained from the full original B moment.

### 6.3. Close all cases just covered

At C, its complete outward pair forces are -b g, -mu e and its
original outside force z_C u. Equations (16)--(17) are precisely
Lemma 4's two full-square support inequalities with P=p. It supplies
an actual point of the original outside unit at projection at least
three from p, contradicting (15) by (9).

Thus every B-vertex p and every gamma>0 side-interior p is excluded.
The only remaining possibility is gamma=0 in the exact side-interior
chart. It is treated next, including all its closed mean endpoints.

## 7. Complete adjacent-axis side-mean exception

Reflect vertically so the remaining normal is g=(0,1). Write

    p=(0,h),    q=(s,1),    0<=s<=1,
    f=(1,0),   t=b/a<3/40.

The full B exit is

    z_B u_B=a(f-t g),
    u_B=(f-t g)/sqrt(1+t^2).

Both its components are nonzero, so its original application is
r_B=(1,0). Taking complete moments at that actual r_B gives

    a h+b(s-1)=0, hence h=t(1-s),   0<=h<=t.         (18)

In the genuinely side-interior case 0<h<1, the noncommon-side condition
also gives 0<s<1. Keeping the closed endpoints in the calculations
does not omit or alter a mean; the p-vertex endpoints were already
covered by Section 6.1.

Let p_0 be the ACTUAL lower-left corner of B, locally (0,0). It is
an auxiliary anchor, not claimed to belong to A or to be the AB mean.
The actual channel and p in A, q in C imply

    e dot(q-p)>=1.

Here q-p=(s,1-h), with 0<=s<=1 and 1-h>0. A negative second
component e_2 would give e dot(q-p)<=s+e_2(1-h)<1, impossible.
Therefore e_2>=0. Since p-p_0=h g, (10) now gives on the ENTIRE C

    e dot(x-p_0)>=1+h e_2>=1.

The actual BC support is its lower horizontal support y=1, so also

    g dot(x-p_0)>=1.                                (19)

Both gaps have therefore been restored at the actual B corner p_0
by valid support inequalities, without pretending it is in A.

### A stronger localization of this corner

Use the one-endpoint estimate (5) at A, with residual ratio tau=mu/a.
It supplies a point y_A of the original disk with

    |y_A-(p-2f)|< (19/6)tau,
    |y_A-(p_0-2f)|<=h+(19/6)tau.

The immediate actual B-exit neighbor contains y_B=r_B+u_B. Since
r_B=p_0+f,

    |y_B-(p_0+2f)|=|u_B-f|<=t.                     (20)

For completeness, the last inequality follows exactly from

    |u_B-f|^2
      =2t^2/[sqrt(1+t^2)(sqrt(1+t^2)+1)]<=t^2.

The sum E_0 of the two endpoint error bounds therefore satisfies

    E_0 <= 2t+(19/6)tau <2(t+2tau)<3/20             (21)

by (14). Squaring the distances from p_0 to these two disk points,
exactly as in Lemma 3, yields

    |p_0-O|^2 < Q-4+(25/12)(3/20)+(3/20)^2/2
               =4097/6400 <169/256=(13/16)^2.       (22)

The last comparison has reserve 1/50. This corner localization keeps
both immediate original exit units and every original side mean.

Apply Lemma 4 to the same complete C forces, now using (19) and the
proved e inequality at P=p_0. Its actual outside unit contains w with
u dot(w-p_0)>=3. Equation (22) gives

    |w-O|>3-13/16=35/16>25/12>R,

the final contradiction. This excludes the entire adjacent-axis mean
family, rather than inferring that its original AB mean is a vertex.

## 8. Exhaustiveness and literal original unicyclic caller

Every point of the boundary of B is either a vertex or lies in the
relative interior of one side. Section 6.1 treats every vertex, whatever
the normal owner. For a side-interior AB application the original B
normal must be its own axis. In that exact chart gamma<0 is the already
excluded common-side case, gamma>0 is Section 6.2, and gamma=0 is
Section 7. Unit length forces the latter normal to be exactly one of
the two adjacent axes, both covered by reflection. These alternatives
include all shared-side means, their endpoints and all normal-cone
boundaries. No opposite-port assumption or missing free-normal case
is hidden in the argument.

The original four-body graph and three FULL exits supplied in Section 1
are exactly the (t,s)=(1,0) row of
`THREE_PORT_UNICYCLIC_UNLOADED_MODULES_AT_MOST_FIVE_WITH_COMPLETE_INTERNAL_ENDPOINT_SCOPE_CORRECTED_2026_10_31.md`.
The unique internal transmitter is genuine U; it has no discarded outside
force. Every original force at A,B,C is one of its two displayed internal
pairs or its one original outside exit. Thus Theorem 1 closes that
entire row, with arbitrary actual outside terminal multiplicity and all
remaining physical squares retained.

Together with the separately reviewed no-transmitted-exit theorem and
the earlier complete (2,0) exclusion, this leaves only the direct
three-body triangle (0,0) among the original unicyclic three-port rows.
The separate complete multicycle theorem is unchanged. The new support-
torque and localization lemmas have the broader scopes printed above;
their use here does not imply that every other open feature has a
three-unit support-distance contradiction.

No original coarse flag is closed solely by this row theorem. No
unrestricted nine-square inequality, global equality classification,
recursive prerequisite audit, or Lean result is claimed. No original
force, normal, mean, circle atom, physical square, frozen source,
ledger or remote object was removed or changed.
