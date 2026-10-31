# A near square with a prescribed oblique support forces a small vertex of the origin square

Date: October 27, 2026.

**Status: complete proposed physical theorem, frozen for full root and
independent review.** The direct support-frame and crossing construction
was developed jointly with rooted_blocks; the complete geometry is
written here separately from its original C4 caller. No force mean,
body, load or graph edge is changed.

The theorem uses only actual unit squares and the following numbers:

    0<epsilon<1/60,
    0<k<19/30,
    A>48/5,
    L=sqrt(A^2+k^2),
    N=(epsilon,k), g=(A,-k)/L.                        (1)

Let H contain O openly. Suppose an actual outward own normal of H is

    h=(s,c), s,c>0, s^2+c^2=1,
    0<c/s<1/22,
    sigma=h_H(h), 0<sigma<=epsilon.                  (2)

Let j=Jh=(-c,s), so in these actual own coordinates

    H=[sigma-1,sigma]h+[-w,1-w]j, 0<w<1.

Suppose every actual H vertex has norm greater than 1/40.

Let B be another actual unit, interior-disjoint from H, satisfying:

- B avoids O closed and meets the closed disk D_epsilon;
- N is an actual maximum-g support point of B;
- at least one of B's two actual own-coordinate intervals contains
  zero.

The last condition is a purely geometric property of every origin-free
genuine S-leaf root in the present d<61/60<sqrt(2) radius window, as
verified in Section1. No B force equation, concurrence or physical
HB contact is assumed.

**Theorem.** This entire configuration is impossible.

An actual shared-side mean at N is permitted. All axial-frame,
point-only, side-owner and support-endpoint alternatives are included.

## 1. The own-interval condition for a genuine S-leaf root

For completeness, keep a true radial S leaf attached to an origin-free
root B, with real support point d e and d=1+epsilon<61/60.

If the radial normal is an own side axis of B, its other own interval
contains zero because d e belongs to that actual support side. If it
strictly exposes a vertex, choose the two outward own directions at
that vertex. Its coordinates there are d a,d b with a,b>0 and
a^2+b^2=1. The actual own intervals are

    [d a-1,d a], [d b-1,d b].

Both cannot avoid zero: that would require d a>1 and d b>1, hence
d^2>2. Thus at least one actual interval contains zero. The axis
endpoints are already included by the side case. This fact concerns
the actual leaf geometry, independently of the number of B's other
forces or their magnitudes.

## 2. H has only one own side within the epsilon disk

The side opposite h has height 1-sigma>59/60>epsilon.
If either adjacent H own side had height at most epsilon, its
intersection with the h side would be an actual vertex of squared
norm at most 2epsilon^2<1/1600. This contradicts the stated vertex
margin. Hence every other own side of H has distance greater than
epsilon from O.

It follows that every point p with |p|<=epsilon has its other three
H own inequalities strictly satisfied. If such a point belongs to
B, it cannot belong to int H. Thus necessarily

    p.h>=sigma>0.                                    (3)

Equality is deliberately retained. Any subsequent crossing argument
must also handle a B corner initially lying on the actual H side.

The slope bound in (2) gives

    0<c<1/22, s>99/100.                              (4)

Also (1) gives

    k/A<19/288<1/15.                                 (5)

## 3. B with a unique maximum-g vertex

Suppose first that the maximum-g support face of B is the vertex N.
Choose its two inward orthonormal axes in their complete order as

    w_B=(-r,-z), v_B=(-z,r),
    r>0, r^2+z^2=1.                                 (6)

Here z is signed; negative, zero and positive z are all retained.
This orientation is always possible: -g is in the inward vertex
quadrant and points left/up. The clockwise edge of that quadrant
has positive y component, and is v_B; the other is w_B=Jv_B.
The actual supporting inequalities imply

    g.v_B<=0,
    z/r>=-k/A.                                      (7)

No upper sign of z has yet been assumed.

Set

    beta=epsilon r+k z,
    delta=k r-epsilon z.

The real coordinates of N in (w_B,v_B) are (-beta,delta), so

    B=[-beta,1-beta]w_B+[delta,1+delta]v_B.            (8)

We have beta<epsilon+k<13/20. If beta<=0, then z<0 and delta>0.
Both intervals in (8) are then nonnegative, and the nearest B point
is their lower-endpoint corner N itself. Its norm is strictly larger
than epsilon because k>0, contradicting the near-disk premise.
Therefore beta>0.

If delta<=0, then -epsilon<delta<=0. Together with 0<beta<13/20<1,
both actual intervals in (8) contain zero. That would put closed O
in B, also impossible. Consequently

    0<beta<13/20,
    0<delta<=epsilon,
    p=delta v_B is the actual nearest B point to O.   (9)

Equation(3) gives delta(r c-z s)>=sigma. In particular

    E:=r c-z s>0,
    z/r<c/s<1/22.

With (5),(7), this proves

    |z|<1/15,
    r>99/100,
    0<E<1/22+1/15=37/330.                            (10)

Put

    D:=r s+z c.

The crude bound D>(99/100)^2-1/(15*22)>0 fixes its sign.
The exact identity D^2+E^2=1 and (10) then give

    D>49/50.                                        (11)

The whole unique-vertex frame has now been covered, including z=0
and either signed tilt. No use of B's genuine-leaf equation or
positive radial concurrence was made.

## 4. B owns the maximum-g support side

Now g is an actual B own normal and N may be any original point
or shared mean of that side. Use the actual orthonormal axes

    w_B=-g=(-r,-z), v_B=Jg=(-z,r),
    r=A/L>0, z=-k/L<0.

Write

    beta=N.g=(epsilon A-k^2)/L<=epsilon,
    B=[-beta,1-beta]w_B+[rho,rho+1]v_B.               (12)

The actual side contains N, whose v_B coordinate is

    N.v_B=k(A+epsilon)/L>0.                          (13)

If beta<0, the w_B interval avoids zero. The own-interval premise
therefore makes the v_B interval contain zero. The actual nearest
point is p=(-beta)w_B, with |p|<=epsilon. But its h projection is
negative, since w_B.h=-(r s+z c)<0 by (4)--(5). This contradicts
(3).

Thus 0<=beta<=epsilon<1. The w_B interval contains zero. Origin
avoidance and (13) force rho>0. Its actual nearest point is

    p=delta v_B, delta=rho in (0,epsilon].

The same E,D definitions now satisfy (10)--(11): here z/r=-k/A
already lies strictly between -1/15 and zero, and (3) again gives
E>0. Every original side mean and both endpoints are retained.
In particular beta=0 is permitted; then p is an actual B corner,
and the next argument includes its zero crossing parameter.

## 5. A real B side crosses the shallow H side before its small upper vertex

Both complete cases have supplied the following actual geometry:

    B=[-beta,1-beta]w_B+[delta,1+delta]v_B,
    0<=beta<13/20, 0<delta<=epsilon,
    p=delta v_B,
    w_B.h=-D, w_B.j=E,
    v_B.h=E, v_B.j=D,
    0<E<37/330, D>49/50.

By (3), delta E>=sigma. The actual near-side segment of B contains
p+t w_B for -beta<=t<=1-beta. Define the real crossing parameter

    lambda=(delta E-sigma)/D>=0.

Its full bound is

    lambda<epsilon*(37/330)/(49/50)
             <epsilon/8<1/480<7/20<1-beta.           (14)

Thus the actual point K=p+lambda w_B belongs to the actual B side,
and this side continues a positive length past K in direction w_B.
We have

    K.h=sigma,
    K.j=delta D+lambda E>0,
    |K|^2=delta^2+lambda^2
            <(65/64)epsilon^2.                      (15)

The norm identity uses the actual orthogonality of w_B,v_B. It
retains lambda=0 and beta=0; the continued positive w_B segment
still exists in that corner endpoint.

Let U_H=1-w be H's positive upper own height along j. If U_H>K.j,
then K lies in the relative interior of the shallow H side. For
small t>0 the real B side point K+t w_B has h coordinate strictly
less than sigma and j coordinate still below U_H and above H's
negative lower side. Its other H coordinate inequality is strict
as well. Hence it lies in int H, impossible for a point of closed B
when the actual unit interiors are disjoint. This also treats the
initial endpoint lambda=0; no new HB edge is assumed.

It follows that U_H<=K.j. The actual upper vertex of H on that side
therefore satisfies

    |sigma h+U_H j|^2
        <=sigma^2+(K.j)^2=|K|^2
        <(65/64)epsilon^2
        <65/230400<1/1600.                           (16)

This contradicts the assumed H vertex margin. The final strict
reserve is 79/230400.

Sections3--4 exhaust B's actual maximum-support face, so the theorem
is complete.

## 6. Exact intended scope and the separate original caller

The proof is physical geometry. It keeps the actual B unit and every
point of the original support segment, including a variable aggregate
mean. No true B3 is shortened to B2, no force is placed on a nonexistent
HB edge, and no common-concurrence equation is needed at B.

For the intended aligned exterior-A C4 caller, the real H geometry
must still supply the actual own axis and vertex margin in (2), and
the full actual A equations must supply (1) and the maximum-g point N
of B. Those statements are proved in the separate original-family
source. This file does not assume them merely from a schematic drawing.

The genuine-B-leaf premise supplies exactly the own-interval property
of Section1, origin avoidance and the actual closed epsilon-disk point.
It does not license deleting the original B leaf, its third force or
the true loaded C star in that caller.

No original family is closed by this geometric file alone. Its full
independent review and the separate exact original caller review remain
required before any parent assembly or ledger update.
