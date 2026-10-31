# A high-support side channel with a touching-return junction forces both physical circle corners and both positive weights

Date: October 28, 2026 UTC. Author: fan_low continuation.

**Status: complete proposed uniform hand reduction, frozen for separate
full independent and root review.** This theorem covers the entire
displayed side-channel chart. It excludes every unique physical circle
mask at the loaded endpoint, and then excludes either zero individual
coefficient in its surviving physical two-corner mask. It leaves a real
two-corner radial-S remainder and claims no original-family closure.

The root and triangle tip keep arbitrary true degrees and all their
original forces. The proof uses the full true unloaded B2, loaded C2
and unloaded D3 systems, the actual physical AT contact, and all
original applications and shared-side means. No BD contact exists in
the statement or proof.

## 1. Whole actual chart and conclusions

Keep actual interior-disjoint closed unit squares in the unchanged
circle, with

    sqrt(17)/2 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon, 0<=epsilon<1/60.

The actual positive edges are AB,BC,CD,DA,AT,DT. The complete
neighborhoods used by the proof are

    N(B)={A,C}, B unloaded;
    N(C)={B,D}, C positively circle-loaded;
    N(D)={A,C,T}, D unloaded.

T is physically a boundary unit. A and T may have arbitrary additional
positive forces, circle loads and physical contacts. Every other actual
packing unit remains present. Use the original side-channel chart
about the unchanged circle origin:

    B=[h,h+1] times [b,b+1],
    P_AB=(h,q), P_BC=(h+1,q), b<=q<=b+1,
    A subset {x<=h}, C subset {x>=h+1},
    max_D y<=b<=q,
    -epsilon<=h<=epsilon.                              (1)

The full positive-mean theorem 5a160, with exactly these hypotheses,
gives q>0. Put H=h+1 and denote the original D-to-C unit normal by g
and its original common application by Q. Write the two unchanged
positive magnitudes at C as mu,nu. Its full circle resultant is

    F_C=mu*(1,0)+nu*g, mu,nu>0.                        (2)

**Theorem.** C has exactly two physical circle corners and both of
their original coefficients are strictly positive. Its actual square
is radial S. The whole remaining geometric cover is precisely the
following necessary alternative:

* C is parallel to the channel:

      C=[d,d+1] times [-1/2,1/2],
      H=d, h=epsilon, 0<q<=1/2.                        (3)

* C is tilted to the channel. There are actual radial axes
  e=(a,s), f=(-s,a), with a,s>0 and a^2+s^2=1, such that

      C=[d,d+1]e+[-1/2,1/2]f,
      P_BC=d*e+(1/2)*f,
      H=d*a-s/2, q=d*s+a/2,
      0<s<=4*epsilon<1/15,
      1/2<q<=sqrt(1/4+4*epsilon), H<d.                 (4)

In every nonparallel-force row, the original g satisfies

    g_x>0, g_y>0.                                     (5)

If the two actual C force lines are parallel, only (3) is possible;
g=(1,0), both circle coefficients are equal and positive, and the
unchanged Q has negative height with

    mu*q+nu*Q_y=0.                                    (6)

The weights in the nonparallel rows need not be equal. All original
one-zero-coefficient possibilities are retained until they are
explicitly contradicted in Section 8. No original mean is moved.

## 2. Uniform inward reach and the full D3 strict support inequality

At any actual minimum-x support point P of a unit square, P+(1,0)
belongs to that same unit. At a side-interior support this is its
complete unit normal segment. At a vertex, express the inward unit
direction (1,0) in the two inward orthonormal side axes: its two
coefficients are in [0,1], so it gives an actual point of the square.
This also covers both side endpoints.

Apply this fact to the unchanged P=P_BC=(H,q) in C. Containment gives

    (H+1)^2+q^2<=R^2,
    H>=1-epsilon>59/60,
    q^2<=1/4+8*epsilon<23/60<25/64.

Thus

    0<q<5/8.                                          (7)

At the true unloaded D3, its other two actual neighbors A and T
physically touch. The complete all-normal touching-return theorem
406f therefore applies with third neighbor C and gives

    g.Z<g.Q for every actual Z in the whole A union T.   (8)

In particular it holds at the unchanged P_AB=(H-1,q). The full
equation and moment of D3 are the premises of (8). No equation at A
or T is shortened to obtain it. The original side mean Q, its
endpoints and every owner or free normal are covered by that theorem.

## 3. Parallel C forces and the complete strict sign reduction

First suppose g is horizontal. If g=(-1,0), Q is on C's maximum-x
support. Its x coordinate is at least H+1, because every unit has
x width at least one. The actual D also contains a point of its
physical AD contact, whose x coordinate is at most h=H-1. D would
therefore have x width at least two, exceeding its diameter sqrt(2).
This excludes the opposite-normal alternative with all means intact.

If g=(1,0), both original C applications lie on its minimum-x face.
For a tilted C that face is the single P=(H,q), and the full C
moment is -(mu+nu)*q=0, contrary to q>0. Thus C is parallel to the
channel, say [H,H+1] times [z,z+1]. Since H>0, every physical circle
corner is on the far side x=H+1. A positive vertical center would
make its sole farthest corner have positive height, and a negative
vertical center would make its sole farthest corner have negative
height. Both contradict the zero vertical component of (2).
Consequently z=-1/2, H=d, and the two actual circle coefficients
are equal and positive. The original full moment is exactly (6),
so Q_y<0. This proves the parallel row without a boundary-neighbor
assumption at C or a fictitious leaf equation.

Now suppose g is not horizontal. The boundary-free full two-application
theorem 3808 applies to the actual C2 on this radius window. It retains
the coincident-application possibility and gives proper concurrence

    c=(H+r,q)=t*F_C, t>0, r>=0,
    c=Q+ell*g, ell>=0.                                (9)

If C has one physical circle corner, c belongs to the actual C.
No such inside conclusion is asserted for the two-physical-corner
mask. Equation (2) and c_y=q>0 give g_y>0. By (1), the original Q
satisfies Q_x>=H and Q_y<=q. If g_x<=0, then

    g.(Q-P_AB)=g_x*(Q_x-H+1)+g_y*(Q_y-q)<=0,

contradicting (8). This proves (5), including all possible signs and
the g_x=0 axis endpoint. It also shows why the actual AT contact and
the full D3 star are essential to this reduction.

## 4. A unique physical corner with an aligned C is impossible

Assume that C is parallel to the channel and has a unique physical
circle corner. The parallel-force row was already excluded for this
mask, so (5) and (9) hold. Since H>0 and c_y=q>0, its sole circle
corner is its upper-right corner

    Z=(H+1,Y), Y>1/2,
    C=[H,H+1] times [Y-1,Y], F_C=k*Z, k>0.

Its physical circle equation and H>=1-epsilon give

    Y^2=R^2-(H+1)^2<=1/4+8*epsilon<25/64,
    1/2<Y<5/8.                                        (10)

The original BC mean obeys 0<q<=Y. Since g is strictly northeast,
the original CD application is the unique lower-left corner

    Q=(H,Y-1).

Set tau=Y-q>=0 and K=(H+1)/Y. From (9) and F_C=kZ,

    r=q*(H+1)/Y-H=1-K*tau,
    u=q+1-Y=1-tau>0,
    ell*g=(r,u), ell>0.                               (11)

The actual P_AB is one channel unit left of P_BC, so
Q-P_AB=(1,-u). The strict support condition (8) requires

    0<ell*g.(Q-P_AB)=r-u^2.

But the full exact identity is

    r-u^2=tau*(2-K-tau)<=0,                            (12)

because

    K>(119/60)/(5/8)=238/75>2.

This contradicts (8). The endpoint tau=0 gives equality in (12),
which is still excluded by the genuinely strict inequality (8).
The whole original q interval and both possible mean endpoints have
been retained. No numerical position or radius subdivision is used.

The same calculation will be used in Section 8 with Y=1/2 and a
second physical circle corner of zero weight. It only needs the
displayed circle resultant kZ, the actual rectangle, (5) and (9);
it does not need the absence of that second physical corner.

## 5. A tilted C with an opposite sole physical corner is impossible

Suppose C is genuinely tilted to the channel. Its actual minimum-x
point is its unique leftmost vertex P=(H,q). Write its two actual
inward axes as

    u=(a,s), v=(s,-a), a,s>0, a^2+s^2=1,
    C=P+[0,1]u+[0,1]v.                                (13)

Here both tilt signs are included: u is the one inward axis with
positive y component. Since P.u=H*a+q*s>0, the only possible
physical farthest corners are P+u and P+u+v.

Assume C has one physical circle corner and it is Z=P+u+v. Put

    N=a+s>0, M=s-a, N^2+M^2=2,
    Z=(H+N,q+M).

The full properness theorem (9) puts c in this actual unique-mask C.
Write c=theta*Z. Since Z is on the circle and c is contained,
0<theta<=1. Its unchanged y coordinate gives q=theta*(q+M),
so M>=0. Its x coordinate at least H then gives

    q*N>=H*M.

Consequently

    R^2=(H+N)^2+(q+M)^2
        >=(1+H/N)^2*(N^2+M^2)
        >=(H+sqrt(2))^2.                              (14)

This is impossible: H>59/60 and sqrt(2)>7/5 give
H+sqrt(2)>143/60, whereas R<25/12=125/60. The latter
strict upper bound has squared reserve 55/2304 above 1105/256.
Thus the entire opposite-sole-corner alternative is excluded.
The inside-concurrence premise was used only for this actual
unique-physical-corner case.

## 6. The full adjacent-circle-force obstruction at a tilted endpoint

Keep the actual tilted chart (13), and suppose the complete positive
circle resultant is a positive multiple of Z=P+u. Assume

    q*a-H*s>=1/2.                                     (15)

This includes a unique physical circle corner there, for which the
other actual corner Z+v is strictly inside the disk and

    |Z+v|^2-|Z|^2=1+2*(H*s-q*a)<0.

It also includes the physical two-corner tie with only this upper
corner positively weighted; then equality holds in (15).

The original g is strictly northeast, so g.u>0. Its complete
minimum-support feature in C is therefore

    Q=P+eta*v, 0<=eta<=1.                              (16)

This is an exhaustive feature cover, not a choice of the original Q.
It retains both actual endpoint vertices and every original side mean.
Properness and the actual radial line through Z give

    c=(H+r,q), r=(q*a-H*s)/(q+s)>0,
    r<1,                                             (17)

where the strict upper inequality follows from
q*(a-1)<s*(H+1). No assertion that c is inside C is needed.

If eta=0, both original positive applications coincide at P. The
full C torque and (2) imply det(P,F_C)=0. But

    det(P,Z)=H*s-q*a<=-1/2,

contradicting F_C=kZ, k>0. This covers the original coincident-port
case by its full equation rather than deleting an actual force.

If 0<eta<1, its actual support side forces g=u. Thus (2) gives

    det(u,F_C)=-mu*s<0,

while F_C=kZ gives

    det(u,F_C)=k*(a*q-s*H)>=k/2>0.

This excludes the complete original open side-mean interval.

Finally eta=1 gives Q=P+v. From (9), its y difference to c is a>0,
so ell>0 and

    ell*g=(r-s,a), Q-P_AB=(1+s,-a).

The exact strict support expression is now

    ell*g.(Q-P_AB)
      =(r-s)*(1+s)-a^2
      =(1+s)*(r-1)<0,                               (18)

again contradicting (8). Equations (16)--(18) exhaust the entire
actual CD feature, including its two endpoints, independently of
which unit owns the normal or whether it was a free contact.

Sections 4--6 exclude every unique physical circle corner of C.
The physical circle-mask classification leaves exactly two actual
circle corners. No positive corner coefficient has yet been omitted.

## 7. The complete physical two-corner remainder

The actual two-corner classification gives orthogonal unit axes e,f
and exactly

    C=[d,d+1]e+[-1/2,1/2]f.                           (19)

This is a geometric statement about the original C2, not a force-leaf
replacement. Its full two positive pair forces remain. If C is parallel
to the channel, its positive minimum-x support H and actual q>0 give
exactly (3).

Otherwise its center has positive x component, because the whole C
lies in x>=H>0. Hence the radial axis e=(a,s) has a>0. The minimum-x
vertex of (19) is an inner corner: an outer circle corner cannot be an
actual common application with a different contained square. Equivalently
the direct minimum-x formula is

    H=d*a-|s|/2.

If s<0, that minimum-x vertex has height d*s-a/2<0, contrary to
q>0. Thus s>0, f=(-s,a), and the actual P=d*e+f/2 gives the first
three equations in (4). In particular

    H<d,
    H^2+q^2=d^2+1/4,
    q>1/2,
    q^2<=d^2+1/4-(1-epsilon)^2=1/4+4*epsilon.

Moreover H>=d-2*epsilon gives the exact complete bound

    d*(1-a)+s/2<=2*epsilon,
    0<s<=4*epsilon<1/15.                              (20)

This is a whole interval of actual radial axes, not a sampled angle
cover. When epsilon=0 the tilted row is impossible. Every physical
equality and the closed upper radius endpoint remain in these formulas.

## 8. Both original circle coefficients are strictly positive

The parallel-force row already proved equal positive coefficients in
Section 3. In the nonparallel rows (5) gives (F_C)_y=nu*g_y>0.

First take the aligned two-corner row (3). If only the lower corner
(d+1,-1/2) had positive coefficient, (F_C)_y would be negative.
If only the upper corner (d+1,1/2) had positive coefficient, the
complete aligned calculation (11)--(12) applies with H=d, Y=1/2,
0<q<=1/2. Its unchanged strict support inequality is contradicted
exactly as before, including q=1/2. Thus both coefficients are positive.

Now take the tilted two-corner row (4). Its upper and lower physical
circle corners are

    Z_+=P+e,
    Z_-=P+e-f.

The lower one's y coordinate is (d+1)*s-a/2. From (20),
a>14/15 and d+1<121/60, so

    (Z_-)_y<121/900-7/15=-299/900<0.                  (21)

It cannot be the sole positively weighted corner, because (F_C)_y>0.
If Z_+ alone had positive coefficient, use (13) with u=e, v=-f.
The actual P=d*e+f/2 gives q*a-H*s=1/2 exactly. Thus the complete
adjacent-circle-force obstruction of Section 6 applies, including
the equality in (15) and every actual CD mean. It gives a contradiction.

At least one physical corner coefficient is positive by the original
C load. We have excluded both possible one-zero endpoints without
changing the physical mask or original forces. Therefore both actual
coefficients are strictly positive, proving the theorem.

## 9. Literal house use and precise remaining obligation

The original M6.B5L.HOUSE.HUB.LTC.S has exactly

    AT,DT,AD,AB,BC,CD,AL,
    true A4,D3,B2,C2,T2,L1,
    positive circle loads precisely at T,C,L.

The actual genuine S leaf and the complete channel reduction in 5a160
supply the high-radius chart (1), with all nine units retained. Thus
this theorem applies to that entire original S family, whether the
root is aligned or tilted to its own genuine leaf and whether the B
channel is parallel, perpendicular or oblique to it. It uses no A3
inference, no boundary assumption on B or D, and no fictitious BD edge.

For the original house it eliminates every unique physical C mask and
both individual-zero endpoints of every physical two-corner C mask at
once. The exact surviving domain is (3) or (4), with both circle
coefficients positive and the full original nonparallel or parallel
C force alternatives retained. The actual D force and torque, the
actual T2 equations and the full A4 star remain available to a later
proof. They have not been replaced by a lower-degree problem.

The original whole family is not closed by this necessary-domain
reduction. In particular (3) with arbitrary original q and two positive
weights, and the small but complete tilted radial interval (4), require
their own further contradiction. The same local result applies to any
other actual caller satisfying (1) and the displayed true B/C/D
neighborhoods, with arbitrary other A/T forces and actual extra units.

## 10. Exact operative sources and preservation

| Source | SHA-256 | Exact use |
| --- | --- | --- |
| SIDE_CHANNEL_UNLOADED_TRIANGLE_BYPASS_POSITIVE_MEAN.md | 5a1607a588e45d0702c46c3d74074561f31109dccc0b8f94c665991cd4a9f5ee | Complete stated channel hypotheses, q>0, and literal genuine-house entry into the full high-support chart |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Original true C2 proper rays, coincident application, unique-mask inside conclusion only where stated, and unrestricted two-corner exterior concurrence |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 | Whole original D3, original DC normal and mean, actual AT contact, strict separation of both whole returned units |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original force/torque, actual common applications, physical support and nonnegative circle coefficients |
| C7_FORCE_POLYGON.md | d50d8ca48ea19156175e651bfa74be30ef3e58065ec14d8d1834670a41559089 | Complete one-/two-physical-circle-corner classification and impossibility of sharing a physical circle point |
| FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md | e5c84071363e8dc43b09f9033c7cb3a7684f1de19bcd169d53c9eab55d51963b | Literal original house labels, edges, genuine leaf, true degrees and TC load family only |

All new comparisons are continuous hand identities or single full-interval
inequalities. No numerical pose, angle mesh, computational exclusion
certificate, normal reselection, mean substitution, force deletion,
discarded actual unit, Lean/Lake invocation, CI/workflow, staging,
commit, remote action or original-flag/count edit is used. Existing
frozen sources remain unchanged. Separate independent full review and
root adoption are required for these exact new bytes.
