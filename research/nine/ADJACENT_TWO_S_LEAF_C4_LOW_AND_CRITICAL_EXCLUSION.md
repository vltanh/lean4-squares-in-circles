# Adjacent S-leaf roots in a C4 are excluded through the critical radius

Date: October 27, 2026.

**Status: complete hand theorem for the entire strict-low and critical
radius domain, submitted for full root and independent review.** The
high-radius portion of the original LCD.SS gate remains separate;
this source does not claim that whole fine gate closed.

Keep all nine original actual unit squares, their disjoint open
interiors, the common selected physical certificate, and

    79/40<=R<=sqrt(17)/2,
    d=sqrt(R^2-1/4)-1<=1,       r=R-sqrt(2).

The exact positive component is the cycle A--B--C--D--A with
genuine S leaves L at A and M at B. The true degrees are
A3,B3,C2,D2,L1,M1. C and D have positive total circle loads.
Every original force, normal, actual shared mean, physical circle
mask, individual zero weight and all three arbitrary extras remain.

**Theorem.** This entire low/critical original family is impossible.

## 1. The strict-low root geometry gives a direct contact contradiction

Every genuine S-leaf root contains O closed when d<1, by the
inward unit segment from its actual radial application d e.
A tilted S root contains O openly: its two inward own coordinates
of O are positive and at most d<1. An aligned root contains O
openly unless zero is an endpoint of its transverse side interval.

Neither A nor B can contain O openly, since the other actual unit
contains O closed and would then overlap it. Both roots are
therefore aligned with their own S-leaf directions, with O in
the relative interior of a transverse side. Their occupied local
half-planes must be opposite. Thus their actual side frames agree
and their leaf directions are parallel. Those directions cannot
be equal, because the unique genuine S square S(e) at that
direction would make L and M the same physical unit.

Rotate and, if necessary, reflect the entire packing to obtain

    A=[d-1,d] times [0,1],
    B=[-d,1-d] times [-1,0],
    e_L=e_x,       e_M=-e_x.

The actual A-to-B normal is south, with its arbitrary original
mean on their genuine common side. The full A3 and B3 force
equations consequently make their other outward cycle normals

    n_AD=(-c,t),       n_BC=(a,-b),
    a,b,c,t>0,       a^2+b^2=c^2+t^2=1.

Their actual root ports are the unique support vertices

    P_D=(d-1,1),       P_C=(1-d,-1).

For any unit square with a minimum-n support point P and n_y>0,
its downward span from P is at most |n_x|. At a side this is
the tangent projection over a length at most one. At a vertex
at most one inward unit side can point down; its nonnegative
n projection gives vertical component at least -|n_x|. Side
endpoints are included in the vertex alternative. Reflection
gives the corresponding upward-span assertion for n_y<0.

Apply these purely physical bounds to D and C. Their entire
units satisfy

    min_D y>=1-c>0,
    max_C y<=-1+a<0.

They cannot physically touch, contrary to the original edge CD.
This proves the strict-low theorem. This paragraph itself did
not use the C/D circle loads, but no such larger critical scope
is inferred from it.

## 2. The full critical contact and leaf-axis cover

Now d=1 and R=sqrt(17)/2. Both actual roots again contain O
closed. A tilted S root has two positive inward coordinates
strictly below one, hence contains O openly. Thus both roots
are aligned with their own genuine leaf directions. Their
longitudinal own intervals are exactly [0,1]; O may be on
a side or a vertex, and every transverse endpoint is retained.

The actual boundary edge C--D has nonzero origin moment by
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma 1.1. Orient the
cycle A to B to C to D to A. Its directed origin moments
are all equal: each original C2/D2 torque transports that
moment, and at A/B the additional genuine radial leaf force
has zero origin moment. Thus the actual AB application P
cannot be O.

Both A and B contain O and P, so their physical intersection
contains the nontrivial segment [O,P]. Two disjoint-interior
squares with such an intersection share an actual side line.
The line passes through O and their side frames agree. The
original positive AB normal is its own perpendicular axis;
its application remains the original mean P, not a new point.

Each genuine S direction is an own axis of this common frame.
On the common side line, equal tangential leaf directions
would duplicate the physical leaf. Opposite tangential leaf
directions would put the two roots in opposite longitudinal
half-lines from O, making their intersection only O, also
impossible. The side-normal directions must point into their
respective root half-planes. Therefore exactly two alternatives
remain, up to exchange and reflection:

* the two leaves point in opposite normal directions;
* one leaf points in its inward normal direction and the other
  along the common side line toward the nonzero contact P.

This includes roots with O in a side interior as well as the
two origin-vertex possibilities. No own-axis endpoint of a
physical shared contact has been discarded.

## 3. Opposite normal leaves contradict the actual acute boundary pair

Normalize the first alternative so the A leaf points east and
the B leaf west. Then A has longitudinal interval [0,1], B
has [-1,0], and AB is westward from A. The full A3 equation
makes AD horizontal. An eastward AD normal would place the
actual D beyond x=1=d; the sharp contained-unit support
equality theorem would identify it with the actual S leaf L.
Since D is distinct, AD must point west. Similarly BC points
east. Hence

    D subset {x<=0},       C subset {x>=0}.

Every physical circle point of C has strictly positive x,
and every one of D strictly negative x. Indeed a circle
point on x=0 is impossible for a unit wholly on one side:
its short inward radial segment lies in the open unit,
whereas that segment would remain on the supporting line.
Thus their full original resultants satisfy

    (F_C)_x>0,       (F_D)_x<0.

The full component balance has only the original C,D loads
and the two horizontal leaf resultants. Consequently
(F_C)_y+(F_D)_y=0 and

    F_C.F_D=(F_C)_x(F_D)_x-((F_C)_y)^2<0.

But the degree-free physical boundary-pair theorem
ACUTE_LOADED_CONTACT_GRAPH.md makes every pair of actual
circle corners from the touching C,D strictly acute. Their
positive-total nonnegative weighted sums therefore have
F_C.F_D>0. This contradiction retains both physical masks
and all individual zero corner weights.

## 4. The perpendicular leaf axes give two incompatible exact bounds

Normalize the second alternative as

    A=[0,1] times [-z,h],       h,z>=0, h+z=1,
    B=[-1,0] times [0,1],
    e_L=e_x,       e_M=e_y,
    P_AB=(0,s),       0<s<=h.

The strict inequality s>0 follows from P_AB!=O and the
actual overlap ray. The full A3 force equation again makes
AD west: its east alternative would duplicate L. Write
P_AD=(0,y). With positive original AB and AD magnitudes
mu,nu, A's actual torque is

    mu s+nu y=0.

Thus y<0. D is a physical boundary unit, so |y|>=r. Since
y>=-z, this gives

    0<s<=h<=1-r<1/2.                                  (1)

Rotate coordinates by a quarter turn so B's genuine north
leaf points east. Its real frame is then [0,1]^2, its
actual BA mean is (s,0) with south normal, and its other
cycle normal has the form

    n=(-a,b),       a,b>0,       a^2+b^2=1.

Its actual BC port is P=(0,1). The full B3 vertical force
and origin torque give exactly

    a/b=s.                                             (2)

The genuine loaded C2 has the actual boundary neighbor D.
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, gives
its actual positive proper radial concurrence

    q_C=P+t n,       t>=0,
    q_C is a strictly positive multiple of F_C.         (3)

No equation at A or B has been replaced by degree two.

### 4.1. P cannot be a vertex of C

If it were, every adjacent C corner would have norm at
most |P|+1=2<R. The only possible circle corner Z is its
opposite vertex. Its distance from P is exactly sqrt(2),
so at R^2=17/4,

    Z_y=(R^2-1)/2=13/8,
    |Z_x|=sqrt(103)/8.

Equation (3) makes Z a positive multiple of
(-ta,1+tb), whose absolute horizontal-to-vertical ratio
is strictly less than a/b=s (or zero when t=0). But

    |Z_x|/Z_y=sqrt(103)/13>1/2>s,

contradicting (1)--(3). This includes a vertex at an
endpoint of a minimum side.

### 4.2. The entire actual C-side domain is also impossible

Thus P is in a relative side interior of C, and n is its
actual inward side axis. Put k=(-b,-a). The full frame is

    C=P+[0,1]n+[-rho,1-rho]k,       0<rho<1.

Its normal support is P.n=b>0, so every physical circle
corner is on the far normal side. The two far corners
cannot both be on the circle. If they were, the center
tangent coordinate would be zero and

    R^2=(b+1)^2+1/4.

At this critical radius that forces b=1 and a=0,
contradicting (2). Hence C has exactly one physical
circle corner. By (3) its tangent sign is that of
q_C.k=P.k=-a<0. The farthest tangent endpoint must
therefore be the negative endpoint, so that corner is

    Z=P+n-rho k=(-a+rho b, 1+b+rho a).

The same positive radial proportionality in (3) gives
Z_x<=0, since (q_C)_x=-ta<=0. Hence

    rho<=a/b=s.

The exact corner norm, increasing in rho>=0, now yields

    R^2=2+2b+rho^2+2rho a
         <=2+s^2+2/b
          =(1+sqrt(1+s^2))^2.

Together with (1), this would give

    R<=1+sqrt(1+(1-r)^2).                              (4)

The inequality is false at R=sqrt(17)/2 and r=R-sqrt(2).
Indeed

    (R-1)^2-[1+(1-r)^2]=2sqrt(2)(R-1)-3>0.

For the final strict sign,
R>1+3sqrt(2)/4 follows by squaring positive quantities:

    17/4-(1+3sqrt(2)/4)^2
       =(17-12sqrt(2))/8>0,

where 17^2>12^2 times 2. Both sides in (4) are positive,
so this exact squared comparison contradicts (4).

Sections 3--4 cover every critical side/frame/mean endpoint,
completing the theorem.

## 5. Exact scope and remaining high domain

This supplies the entire d<=1 portion of

    M6.B4L2.C4.ADJACENT.LCD.SS.

Its strict-low argument also applies without the C/D load
assumption, but the critical argument uses both true C2/D2
positive circle loads and their physical boundary contact.
That premise is not exported to the single-C load orbit.

The high domain d>1, and the mixed S/D family, are not
asserted closed here. All six actual component units,
three arbitrary extras, physical masks and weights, and
actual higher-degree root equations remain throughout.
No numerical pose, changed normal, force deletion, Lean
compilation, CI, remote action or shared-ledger edit is used.
