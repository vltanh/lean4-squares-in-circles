# A boundary unit cannot touch three distinct units meeting the small origin disk

Date: October 27, 2026.

**Status: complete fresh geometric proof and two complete decorated-
diamond role joins, frozen for full root and independent review.**
The old dd5847fa point-kernel bytes were lost in the executor rollback.
This is a newly written proof with a new pin, not byte recovery or an
inherited historical acceptance. No shared ledger is changed.

Keep the actual nine-unit packing in R^2<=1105/256. Whenever the
physical conclusions below are used, retain the accepted same-nine
lower bound R>2. Write

    epsilon=sqrt(R^2-1/4)-2, 0<epsilon<1/60,
    q=29/40.

The main geometric result is independent of all forces, physical
contact owners, circle weights and graph degrees.

**Theorem.** No physical boundary unit can touch three distinct actual
units each meeting the closed disk D_epsilon.

In particular the theorem applies when one of those three units
contains O closed. No pairwise physical contact among the three near
units is assumed.

## 1. A complete point theorem in a closed disk

Let E,F,A be three points in the closed disk D_q, with all three
pairwise distances at least one. Let C satisfy

    |C-E|<=sqrt(2), |C-F|<=sqrt(2).

If C is on the same closed side of line EF as A, then

    |C|^2<2651/1600<5/3.                              (1)

The three near points cannot be collinear: in a collinear triple
with all pairwise distances at least one, the extreme pair has
distance at least two, whereas 2q<2.

Use an orthonormal coordinate system with the origin unchanged and
write

    E=(s-a,t), F=(s+a,t), A=(s+x,t+y),
    a>=1/2, s>=0, y>0.

Reflect along EF if needed to obtain s>=0. The endpoint containment
gives

    (s+a)^2+t^2<=q^2,
    1/2<=a<=q, 0<=s<=q-a,
    s^2+t^2<=q^2-a^2.                                (2)

Since A is in D_q,

    |x|<=q+s<=2q-a<2a.

The last strict inequality follows from 2q=29/20<3/2<=3a.
The smaller of |x-a| and |x+a| is therefore at most a. The two
distance lower bounds from A to E,F imply

    y>=b:=sqrt(1-a^2),
    t<=q-b,
    sqrt(1-q^2)<=b<=sqrt(3)/2,
    b>2/3.                                           (3)

The last comparison is exact: 1-q^2-4/9=431/14400>0.

Write C=(s+z,t+w), w>=0. The two common-distance upper bounds say

    (a+|z|)^2+w^2<=2.                                (4)

Replacing z by |z| can only increase the squared norm, because s>=0.
Set v=a+|z|. Then a<=v<=sqrt(2),
0<=w<=sqrt(2-v^2), and

    |C|^2<=(s+v-a)^2+(t+w)^2.                         (5)

## 2. All half-lens extrema reduce to two actual endpoints

For fixed v, the right side of (5) is convex in w. Its maximum is
therefore at w=0 or w=sqrt(2-v^2).

On w=0 it increases with v, giving the side endpoint

    S=(s+sqrt(2)-a)^2+t^2.                            (6)

On the curved edge the right side is

    G(v)=(s-a)^2+t^2+2+2(s-a)v+2t sqrt(2-v^2).

Here s-a<=q-2a<0. If t>=0, G is strictly decreasing, so its
maximum is the top endpoint v=a. If t<0, then

    G''(v)=-4t/(2-v^2)^(3/2)>0

on the open interval, so convexity and continuity put its maximum
at v=a or v=sqrt(2). The latter is already (6). The top endpoint is

    T=s^2+(t+sqrt(2-a^2))^2.                          (7)

This covers t=0, w=0, a=q, v=sqrt(2), and the entire closed
same-side boundary of the half-lens. No sign of t was suppressed.

### 2.1. The side endpoint

If a<=1/sqrt(2), put delta=sqrt(2)-2a>=0. By (2),

    sqrt(S)=|(s+a,t)+(delta,0)|
           <=q+delta<=q+sqrt(2)-1<q+1/2=49/40.

Thus S<2401/1600. If a>=1/sqrt(2), then
0<=s+sqrt(2)-a<=s+a, so S<=q^2=841/1600.
Both inequalities are strictly below 2651/1600. The equality case
a=1/sqrt(2) belongs to both valid arguments.

### 2.2. The top endpoint and its whole continuous interval

Since sqrt(2-a^2)=sqrt(1+b^2), (2) and (3) give

    T<=F(b):=q^2+2b^2+2(q-b)sqrt(1+b^2).              (8)

Its exact derivative is

    F'(b)=2[q b-(sqrt(1+b^2)-b)^2]/sqrt(1+b^2).

For the whole interval in (3),

    (sqrt(1+b^2)-b)^2
      =1/(sqrt(1+b^2)+b)^2
      <1/(1+b)^2<9/25<29/60<q b.

The strict reserve 29/60-9/25=37/300 is positive. Therefore F is
strictly increasing over the entire allowed interval, including
either sign of q-b. At its upper endpoint,

    F(b)<=q^2+3/2+q sqrt(7)-sqrt(21)/2
          <q^2+3/2+(53/20)q-229/100
          =2651/1600<5/3.                             (9)

The radical comparisons are exact:
(53/20)^2-7=9/400 and 21-(229/50)^2=59/2500.
The final reserve is 5/3-2651/1600=47/4800.
Together with the complete side-endpoint cover, this proves (1).

## 3. Exact physical consequence for a common boundary neighbor

If an actual unit T meets closed D_epsilon, its center c_T satisfies

    |c_T|<=epsilon+1/sqrt(2)
          <1/60+17/24=29/40=q.                        (10)

The inequality sqrt(2)<17/12 is strict. Distinct actual unit centers
have distance at least one by their disjoint open incircles. Physical
contact of two units gives center distance at most sqrt(2).

For a physical boundary unit B its actual circle corner gives

    |c_B|>=R-1/sqrt(2)>2-17/24=31/24,
    |c_B|^2>961/576>5/3,                             (11)

where 961/576-5/3=1/576. The full boundary definition is physical;
no positive circle weight is required at the chosen corner.

Apply (1) to three distinct actual near units E,F,A. Every boundary
unit touching E and F must lie on the strict opposite side of their
center line from c_A. This includes exclusion of a boundary center
on the line itself. No actual E-F contact is needed.

## 4. Three strict opposite sides cannot occur simultaneously

Suppose a boundary unit B touched all three distinct near units.
Their centers e,f,a are noncollinear by Section1. Orient them
counterclockwise, so det(f-e,a-e)>0. Section3 applied to each pair
would give all three inequalities

    det(f-e,c_B-e)<0,
    det(a-f,c_B-f)<0,
    det(e-a,c_B-a)<0.

Their left sides sum identically to det(f-e,a-e)>0. They cannot
all be negative. This proves the complete geometric theorem.

No force equation, ray sign, graph embedding or virtual concurrence
has entered Sections1--4. All distance and side endpoints were
included in the closed half-lens argument.

## 5. Two entire original two-private-leaf diamond role families

Keep the exact original shared genuine-Q0 / two-private-leaf diamond
scope of

    GENERAL_TWO_PRIVATE_LEAF_DIAMOND_OPEN_ORIGIN.md
    SHA256 b6f062b700518677a3cea9e9ee2fbfadbde84c0413ea76ea83352fff98cc4520.

Its separate full review is required; this geometric source does not
substitute for that changed-parent origin proof. Its conclusion puts
O openly in H and makes both actual leaf roots meet closed D_epsilon,
with epsilon in (0,1/60). Thus these are three distinct actual near
units. Every original Q0 mask and both actual leaf forces are retained.

### 5.1. H a hub, with both private tips carrying leaves

The other hub K is untouched, genuinely degree three, and physically
boundary by NO_UNLOADED_DIAMOND_HUB.md. Its actual positive neighbors
are precisely H and the two decorated private tips. It therefore
touches all three actual near units, contradicting Section4.

This closes the entire root-hub / two-tip-leaf placement, every tip
leaf orientation and actual circle mask, with both tips true degree
three and K true degree three.

### 5.2. H a tip, with one private hub and the other tip carrying leaves

Call the decorated hub X, the decorated other tip Y, and the untouched
hub K. K is truly degree three and physically boundary. Its original
three positive neighbors are H,X,Y. It again touches all three actual
near units, contradicting Section4.

This closes the entire root-tip / one-hub-and-other-tip-leaf placement,
including either symmetric choice of decorated hub. The decorated
hub retains true degree four, the decorated tip true degree three.

The other two roles, namely root hub with the other hub and one tip
decorated, and root tip with both hubs decorated, are not covered by
this common-neighbor join. Their full decorated hub equations remain
separate obligations. No whole C2.44.b2 closure is claimed here.
