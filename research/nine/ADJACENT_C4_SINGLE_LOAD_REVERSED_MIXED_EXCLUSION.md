# The reversed mixed adjacent-leaf four-cycle is excluded at one block load

Date: October 27, 2026.

**Status: complete hand original-family proof, submitted for full root
and separate independent review.** The common support/cap calculations
and finite compatible owner selection are supplied in full by
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md and retain that source's
separate full-review requirement. No shared coarse or fine label is
changed.

Keep the original nine physical unit squares and the common compatible
radius/Phi-minimizer and minimum-positive-original-scalar-atom certificate,
with

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60,
    r=R-sqrt(2),       s=1-r,
    1/2<r<2/3,       s>1/3.

The actual graph is A--B--C--D--A, with a genuine S leaf L at A
and a genuine D leaf M at B. The sole positive block-circle load
is C; D is the true unloaded degree-two transmitter. The genuine
degrees are A3,B3,C2,D2,L1,M1, and all three other original units
stay arbitrary and present. Keep every original force, normal,
application mean, physical mask and individual zero weight.

**Theorem.** The entire ordered original fine family

    M6.B4L2.C4.ADJACENT.LC.SA_DB

is impossible. The ordering is essential: the single-C load
representative does not identify it with the opposite D/S assignment.

## 1. Full first-root reduction and the actual narrow cap

At d<=1 the genuine D root B contains O openly and the genuine
S root A contains O closed. Their interiors overlap, so only
d>1 remains. Write epsilon=d-1>0.

The real B is origin-interior. Thus the actual support from A to
B is at most zero, in particular at most epsilon. The true
channel A--D--C has width exactly one by the physical bypass B,
and its original A support is at most d-1=epsilon. The support-
only theorem GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md makes
A aligned with its own S direction. The complete support-only
normal cover in Sections 4--5 of
RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md then gives
precisely the two alternatives recorded in Section 1 of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md:

* the two real A normals are both west, with all their actual
  parallel application means retained; or
* A=[epsilon,d] times [-b,a], a+b=1, a,b>0, and its true
  AB and AD normals and applications are

      (-cos(phi),sin(phi)) at (epsilon,a),
      (-cos(psi),-sin(psi)) at (epsilon,-b),
      0<phi,psi<pi/36,
      sin(phi),sin(psi)<=4epsilon,
      a=tan(phi)/(tan(phi)+tan(psi)),
      b=tan(psi)/(tan(phi)+tan(psi)).                   (1)

Only the two actual support bounds and A's unchanged full star
are used. B is never assigned a channel or a boundary equation.

The actual C cap has the complete physical conclusions of Section 2
of the companion source. In coordinates X toward C along the real
channel and Y perpendicular to it,

    X_C>89/60,
    |c_C|<91/60,
    |Y_C|<1/3,
    w_C<16/15.                                         (2)

Here w_C is its directional width along the channel. Its nearest
own axis to the reverse channel direction has angle theta with

    |sin(theta)|<1/14,       cos(theta)>13/14.            (3)

At a corner exposed strictly between that own axis and the
adjacent positive-Y axis, the corner's Y coordinate exceeds
the actual center's by more than 23/50. The same statement
holds for either choice of transverse sign. These are pure
square/center estimates and retain every C circle mask and mean.

## 2. Every nonparallel A case keeps a genuine B-owned side axis

In (1), the two unchanged A applications are distinct vertices
at nonzero heights a,-b. The compatible fixed-point determinant
preselection proved in Section 4 of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md therefore applies
verbatim: it forces the actual AB normal to be B-owned. This
uses no boundary premise at B. The real D channel already owns
its normal. The finite physical exclusions are imposed before
extracting the certificate, alongside the previous compatible
strict/nonradial/matched-junction requirements; no force is
changed after extraction.

Use B's actual owned AB normal toward A as e_x and its
counterclockwise perpendicular as e_y. Put

    delta=phi+psi,
    kappa=epsilon cos(phi)-a sin(phi),
    t=epsilon sin(phi)+a cos(phi)>0.

The actual AB point is (kappa,t), and B has horizontal support
interval [kappa-1,kappa]. Its origin-interior property gives

    0<kappa<=epsilon.                                  (4)

The genuine D direction is an own side axis of B by the original
radial D-root chart. It cannot be horizontal: that would give
horizontal origin margins r and s, both greater than epsilon,
contradicting (4). It is therefore exactly north or south.

The actual C channel port and its normal toward D are

    P_D=(kappa+sin(phi)-cos(delta),
         t-cos(phi)-sin(delta)),
    v=(cos(delta),sin(delta)).                          (5)

The second coordinate of P_D is strictly negative, because it is
epsilon sin(phi)-b cos(phi)-sin(delta), and 0<phi<delta<pi/2.

For use in the north case, the exact support calculations also
give

    sin(delta)<1/10,       cos(delta)>99/100.             (6)

Here is their full root-only derivation. Let T=tan(phi)+tan(psi).
Equation (4) gives a^2 T<=epsilon. The actual AD support gives
b^2 T<=epsilon(1+sec(psi))<(201/100)epsilon, since
cos(psi)>199/200. Adding square roots yields
T<(121/50)^2 epsilon<1/10; then sin(delta)<T. No S-root
assumption at B is used in this calculation.

### 2.1. A north D leaf contradicts the actual C cap

Here the real B rectangle is

    B=[kappa-1,kappa] times [r-1,r].

Its original force toward A is mu e_x, mu>0, and its genuine
leaf force is alpha e_y, alpha>0. Its full force toward C is
strictly southwest, so its real BC application is

    Q=(kappa-1,r-1).

The complete B torque gives

    alpha/mu=(t+1-r)/(1-kappa)>1/3.                     (7)

The same ratio is below two, since t<d<61/60, 1-r<1/2 and
1-kappa>59/60. Thus the C-to-B normal has slope strictly
between 1/3 and two in the displayed frame.

Equations (3),(6) place C's nearest own outward axis to v
at slope of absolute value less than 1/5, exactly as follows:

    |sin(delta+theta)|<1/10+1/14=6/35,
    cos(delta+theta)>1277/1400,
    |tan(delta+theta)|<240/1277<1/5.

The force in (7) lies strictly between that axis and its upper
adjacent axis. Consequently Q is the corresponding actual upper
corner of C. In channel-transverse coordinates its height is

    Y_Q=(1-kappa)sin(delta)+(r-1)cos(delta)<1/10.

The corner increment in (2),(3) forces

    Y_C<1/10-23/50=-9/25<-1/3,

contradicting (2). Every nonparallel north-D case is excluded.

### 2.2. A south D leaf contradicts two original support inequalities

Now

    B=[kappa-1,kappa] times [-r,1-r].

The full B equation makes its force toward C northwest. Its
actual application is Q=(kappa-1,1-r), and the opposite force
from C toward B has positive x and negative y components.
But (5) gives

    (P_D)_x>Q_x,
    (P_D)_y<0<Q_y.

Thus that C-to-B normal has strictly larger scalar product at
the actual point P_D in C than at its proposed supporting point
Q. This is impossible. It covers the whole south-D alternative
without a circle-load or application-owner restriction at C.

## 3. The full parallel A case in the actual D-root frame

The two actual A pair normals now agree. Let n be the real normal
from B toward A, which is also the genuine S direction of L.
The aligned A has longitudinal interval [epsilon,d] along n.
The true side transmitter D has longitudinal interval
[epsilon-1,epsilon], while

    B subset {z:n.z<=epsilon},
    C subset {z:n.z<=epsilon-1}.                        (8)

All original transverse side means remain. The genuine D root
B contains O openly and has its actual D leaf M to the east:

    B=[-s,r] times [h-1,h],       0<h<1,
    p_BM=(r,0).

Write n=(u,v). Both horizontal origin margins are greater than
one third, and h_B(n)=epsilon. Consequently |u|<3epsilon<1/20.
Reflect vertically if needed so v>0. The actual top origin margin
and these exact inequalities satisfy

    v>19/20,
    0<h<=epsilon/v<1/57.                               (9)

Let m=(v,-u), the actual transverse direction pointing almost
east. The cap (2) now reads

    |m.c_C|<1/3.                                       (10)

The real physical bypass B and the side transmitter D are
separated transversely along m by Section 4 of
UNIT_BYPASS_NORMAL_CHANNEL.md. No contact between B,D is inferred.

### 3.1. For u<=0 the real D leaf forbids the transmitter on its east side

Suppose D lay on the positive-m side of B. Its actual m interval
would be [k,k+1], with

    k>=max_B(m.z)>=m.(r,0)=r v,
    k<=d.

The second inequality is the sharp contained-unit support bound
at the real D, not an endpoint force equation. The real D square
is exactly the rectangle with n interval [epsilon-1,epsilon]
and m interval [k,k+1]. The point (x,0) with x=k/v obeys

    r<=x<=d/v<61/57<R,
    -1/10<u x<=0<epsilon,
    u x>epsilon-1.

For x slightly larger, all inequalities defining that rectangle
are strict. At the same time r<x<R puts the point strictly
inside the real radial D leaf M along its interior east ray.
The two actual interiors would overlap. This excludes the whole
positive-m side for u<=0, including every transmitter slider.

Hence D lies on the negative-m side. Since O belongs to int B,

    max_D(m.z)<=min_B(m.z)<0.

The actual AD application therefore has negative m coordinate.
A's complete two-west-force origin moment, with its radial leaf
moment exactly zero, forces its actual AB application P to have

    m.P>0.                                              (11)

If u<0, however, P is the actual upper-left vertex (-s,h) of B,
and (9) gives

    m.P=-s v+|u|h
        <-(1/3)(19/20)+(1/20)(1/57)<0.

This contradicts (11), excluding every u<0 case. If u=0,
(11) simply says that the genuine mean P=(x,h) satisfies x>0;
that mean is retained for the next calculation.

### 3.2. The u=0 case forces a forbidden east corner of C

Now n=e_y, h=epsilon, and the full B equation consists of its
real A force mu e_y, genuine leaf alpha e_x, and the opposite
southwest force toward C. The actual BC point is

    Q=(-s,epsilon-1).

The complete B torque at the retained AB mean (x,epsilon) gives

    alpha/mu=(x+s)/(1-epsilon),
    1/3<alpha/mu<2.                                    (12)

The upper bound uses x<=r and r+s=1. This is the actual ratio
of the east and north components of C's force toward B.
Its direction lies strictly between C's own axis nearest north
and the adjacent east axis, by (3),(12). Thus Q is the real
corner on the positive-m, or east, side of that cap frame.

Its m coordinate is -s<-1/3. The corner increment exceeds
23/50, forcing m.c_C<-1/3-23/50, contrary to (10). No assumption
was made that the original AB mean is a midpoint or endpoint.

### 3.3. Every u>0 case has the same strict cap contradiction

Here P=(r,h) is the actual AB point. The full B equation writes
its force toward C as

    -(alpha e_x+mu n),       alpha,mu>0.

Both components are negative, so the actual BC application is
Q=(-s,h-1). The full origin moment, with the radial leaf term
zero, gives the exact ratio

    alpha/mu=(v-u)/(1-h)>0.                             (13)

The vector from C toward B consequently has components along
n and m proportional to

    F_n=v(u+v)-h,
    F_m=v(v-u).

Both are positive, and (9) gives

    57/70<F_m/F_n<2.                                   (14)

For the lower bound use F_m>(19/20)(18/20)=171/200
and F_n<21/20. For the upper bound use F_m<1 and
F_n>(19/20)^2-1/57=20177/22800>1/2.

Again (3),(14) put the real force strictly between C's own axis
nearest n and its adjacent positive-m axis. Therefore Q is
that actual east corner of C. Its transverse coordinate obeys

    m.Q=-s v+u(1-h)
        <-(1/3)(19/20)+1/20=-4/15.

Subtracting its corner-to-center increment, which exceeds 23/50,
contradicts |m.c_C|<1/3 in (10). This completes every u>0 case
and hence the entire parallel A domain.

## 4. Whole ordered family and exact single-load parent join

The actual low/critical interval is excluded by physical overlap;
the strict-high nonparallel and parallel A stars are exhausted
by Sections 2 and 3. The genuine B3 force and torque were kept
throughout. In the parallel analysis the true D transmitter was
separated from the actual B by the geometric bypass theorem,
and its forbidden side was excluded using the unchanged physical
D leaf. It was never substituted for that leaf or given a false
boundary equation.

Thus M6.B4L2.C4.ADJACENT.LC.SA_DB is entirely excluded, subject
to the stated full-source reviews. Together with the companion
whole S/S proof, the existing D-at-A/S-at-B proof in
GENUINE_LEAF_ROOT_SMALL_NONLEAF_SUPPORTS.md, and the original
distinct-D-root overlap, this supplies every leaf-type alternative
of the original adjacent-C4 single-C load representative. The
reflection changing C to D is included by the original attachment
symmetry, while the two mixed assignments at fixed C remain
separate and both have their own full proofs.

The double-load representative CD and the whole adjacent-root
attachment require their own original joins. No whole C1.4.b2
closure is asserted here. Every original mask, weight endpoint,
mean and all nine physical units remain.

No numerical pose, post-extraction force change, altered application,
Lean compilation, CI, remote action or shared-ledger edit is used.
