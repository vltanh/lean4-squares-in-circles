# A genuine axis port closes the 45-degree full-star cone boundary

Date: October 29, 2026 UTC. Author: common-selection continuation.
The same-side loaded-two moment argument in Section2.3 was supplied
by the Type II A-owner continuation; its complete arbitrary-degree
extension in Section2.2 is proved here.

**Status: complete proposed uniform hand theorem, frozen for separate
full independent review.** Every positive force of an actual loaded
star is retained. The entire closed 45-degree side cone, including its
boundary directions, forces physical radial alignment when one original
own-axis force acts at a genuine relative-side-interior port. The true
positive degree is arbitrary. Every physical circle mask and every
individual zero circle coefficient is included.

This complements the existing open-side-cone theorem: its strict
direction inequalities require no axis port, whereas the present closed
inequalities use the strict position of one actual axis application.
A second full-star theorem restricts a same-side support star to an
external-axis radial mask or a unique physical circle corner with a
strict own-coordinate order. Together these results supply a complete
physical-mask and angular alternative for the remaining A-only side
row. They do not exclude its radial alternatives or close an entire
original Type II side row.

## 1. Entire actual-star hypotheses

Let E be an actual unit square contained in the disk of radius R about
the unchanged origin O=0, where

    R>1/sqrt(2).

Fix its actual orthonormal own axes e,f, initially with det(e,f)=1.
Keep its complete finite collection of positive original pair forces

    -mu_i*n_i at P_i,
    mu_i>0, |n_i|=1,

where P_i is the unchanged actual minimum-n_i support application in E.
It may be a vertex or the entire original mean on a shared support
segment, including either endpoint. Keep every physical circle corner
Z_j and every original nonnegative coefficient c_j, with

    sum_j c_j>0.

As in the physical-stress convention, absorb the common positive factor
two into the circle coefficients. The full original equations are

    F:=sum_j c_j*Z_j=sum_i mu_i*n_i,
    sum_i det(P_i,-mu_i*n_i)=0.                  (1)

Circle-force moments about O vanish individually. No term at E or any
other actual body is removed. The original neighboring bodies may have
arbitrary degrees, loads, other contacts and physical circle masks.

Write the actual components

    a_i=n_i.e, b_i=n_i.f.

Assume every positive pair term lies in the closed own-side cone:

    a_i>=|b_i|.                                  (2)

In addition, at least one original term, indexed by j, satisfies

    n_j=e,
    P_j lies in the relative interior of E's minimum-e side.  (3)

This is a premise about the original actual mean or point. It is not a
choice of another mean on the side. In particular (3) is available at a
genuine exterior-owned singleton whose actual point is side-interior.

## 2. Closed-cone full-star theorem

**Theorem 2.1.** Under (1)--(3), E has exactly two physical circle
corners and its entire actual position is

    A_R=sqrt(R^2-1/4)>1/2,
    E=[A_R-1,A_R]*e+[-1/2,1/2]*f.               (4)

Both actual corners A_R*e+f/2 and A_R*e-f/2 lie on the same original
circle. Their original coefficients remain arbitrary nonnegative
values consistent with (1); either individual coefficient may be zero.
No equality of those coefficients is asserted.

*Proof.* The complete force satisfies

    F.e-|F.f|
       >=sum_i mu_i*(a_i-|b_i|)
       >=mu_j>0,                                (5)

since the designated own-axis term has a_j=1 and b_j=0. Thus
F.e>|F.f| and F.e>0.

For completeness, write the actual square as

    E=c+[-1/2,1/2]*e+[-1/2,1/2]*f,
    c=x*e+y*f.

The squared corner norm maximizes its e and f coordinates
independently. There is one farthest corner when x,y are both nonzero,
two adjacent farthest corners when exactly one center coordinate is
zero, and four when both vanish. Positive total circle weight makes
the farthest corner radius equal to R, so every tied farthest corner
is physically on the circle, even if its individual coefficient is
zero. The four-corner mask would have R=1/sqrt(2), contrary to the
hypothesis. A side-interior point cannot create another physical
circle mask, because its squared norm is strictly below the larger
endpoint squared norm on a nondegenerate segment. Thus only one or
two physical circle corners are possible.

Suppose first that there is exactly one physical circle corner Z.
Then F=c_0*Z with c_0>0. If F.f=0, then Z.f=0, impossible for a
farthest corner of a unit square: the larger absolute value of the
two actual f endpoints is at least1/2. Hence F.f is nonzero.

Treat F.f>0 first. By (5), Z.e and Z.f are positive. The unique
farthest-corner rule makes Z the upper-right corner in the actual
own coordinates. Write

    E=[u,u+1] x [v,v+1], Z=(u+1,v+1).

The full force balance permits torque to be taken about this same
actual Z. The original pair moments are exactly

| Actual transverse component | Actual support/application | Moment about Z |
| --- | --- | --- |
| b_i>0 | P_i=(u,v) | mu_i*(b_i-a_i)<=0 |
| b_i<0 | P_i=(u,v+1) | mu_i*b_i<0 |
| b_i=0 | P_i=(u,t_i), v<=t_i<=v+1 | mu_i*a_i*(t_i-v-1)<=0 |

Here a_i>0 follows from the unit-length condition and (2). The first
row uses the weak closed-cone inequality, so its exact45-degree
boundary remains. For the designated term j, (3) gives

    v<t_j<v+1,

and its third-row moment is strictly negative. Therefore the sum of
all original pair moments is strictly negative. The only circle force
acts at Z and has zero moment about Z. This contradicts the complete
torque equation.

If F.f<0, reflect the entire coordinate chart and all actual vectors
in the e line. All determinant equations reverse their signs together
and remain zero. The closed cone and the designated side-interior
condition are unchanged, while the reflected F.f is positive. The
same complete argument excludes this case as well. No single body,
normal, mean or coefficient is reflected independently.

The physical two-corner mask is the only remaining possibility.
If its radial direction were transverse to e, its physical corners
would be

    +/-e/2+sigma*A_R*f, sigma in {-1,1}.

Their full nonnegative weighted sum would obey

    |F.f|=A_R*sum_j c_j
       >(1/2)*sum_j c_j>=|F.e|,

contrary to (5). Thus the zero center coordinate is c.f=0. The
physical corners have the form sigma*A_R*e+/-f/2. Since F.e>0,
sigma=+1, giving the entire actual square (4). This proof retains
both individual zero-coefficient possibilities. QED.

### 2.1. Why the genuine port matters at the boundary

Without (3), the closed cone (2) alone does not give Theorem2.1.
A square can have a unique physical circle corner on its own diagonal,
with a positive radial diagonal force balanced at the opposite vertex.
That force lies exactly on a45-degree cone boundary. The designated
side-interior application produces the strict moment that is absent
in this example.

Conversely the existing open-cone theorem applies when every
a_i>|b_i| and no designated axis contact is known. Neither theorem
permits dropping a positive force that lies outside its printed cone.

### 2.2. Full same-side support stars have only two physical mask types

The following separate theorem does not require the closed cone(2).
Keep the entire actual-star setup(1), the radius R>1/sqrt(2), and the
genuine designated axis port(3). Replace(2) by the full quadrant
conditions

    a_i>0, b_i>=0 for every original positive pair term.       (6a)

Every term with b_i>0 is therefore supported at the same actual
minimum-e/minimum-f corner. Every b_i=0 term has n_i=e and retains
its full original application on the same minimum-e side.

**Theorem2.2.** Exactly one of the following physical mask types holds:

* E is radial along +e, with its entire position(4);
* E has exactly one physical circle corner Z=A*e+B*f, where
  A>B>1/2.

In the second case at least one original incoming force has b_i>a_i.
More precisely, if the actual square is

    E=[A-1,A]*e+[B-1,B]*f,

and the actual axis applications are

    P_i=(A-1)*e+(B-tau_i)*f, 0<=tau_i<=1,

then its unchanged full torque gives the exact weighted identity

    sum_{b_i>0} mu_i*(b_i-a_i)
       =sum_{b_i=0} mu_i*tau_i>0.                (6b)

The strict inequality comes from the same original designated port,
whose tau_j lies in(0,1). No other mean is made interior.

*Proof.* If every b_i=0, the whole star satisfies Theorem2.1, which
already gives the radial position. Suppose some b_i>0. Its full
resultant has F.e>0 and F.f>0.

Independent corner maximization, including either zero center
coordinate, makes the actual upper-right corner Z=A*e+B*f a
physical circle corner. Indeed a negative center coordinate would
make every physical circle corner negative in that coordinate,
contrary to the corresponding positive component of the full F.
Here A,B>=1/2: each adjacent actual vertex
is in the disk, so |Z-e|<=|Z| and |Z-f|<=|Z| give those two
inequalities. The corner classification in Section2 applies to
the full physical mask.

Write T=(A-1)*e+(B-1)*f. Every original b_i>0 application is this
same actual corner T. For the b_i=0 applications retain exactly
the tau_i displayed above. The full torque about O gives

    det(T,F)
       =sum_{b_i=0} mu_i*det(T-P_i,e)
       =sum_{b_i=0} mu_i*(1-tau_i)>0.           (6c)

Indeed the b_i>0 contributions cancel their unchanged torque terms
at T; the remaining terms are precisely the original axis terms.
All are nonnegative and the designated one is strictly positive.

Suppose the physical mask were radial along +f. Then

    A=1/2, B=A_R,
    F=kappa*(eta*e+A_R*f),
    kappa=sum_j c_j>0, 0<eta<=1/2.

The bound on eta follows from the actual two physical corners
+/-e/2+A_R*f and their unchanged nonnegative coefficients. Its
strict positivity follows from F.e>0. Formula(6c) would have

    det(T,F)
       =kappa*(-A_R/2-(A_R-1)*eta)<0.           (6d)

For A_R>=1 both terms give the strict negative sign directly.
For 1/2<A_R<1 use eta<=1/2 to bound the parenthesis above by
1/2-A_R<0. Thus the entire transverse-radial mask is excluded,
including an individual zero circle coefficient.

The other physical two-corner mask has its radial direction +e,
which gives(4). If the physical circle corner is unique instead,
F=kappa*Z for kappa>0. Formula(6c) becomes

    kappa*(A-B)>0.

Uniqueness gives A,B>1/2, so A>B>1/2. Finally take the entire
torque about Z. Every nonaxis original force has moment
mu_i*(b_i-a_i); every axis term has moment -mu_i*tau_i. Their
sum is zero, proving(6b). QED.

The direction condition a_i>0 is strict in this theorem. At a
purely transverse incoming direction the support is a whole other
side, and its actual original mean cannot be replaced by T.
The separate closed-cone theorem and the full two-endpoint
applications below handle their own relevant boundaries.

### 2.3. The same-side true2 consequence

At a loaded true2 endpoint let the entire incoming forces be
p*e and gamma*d, with p,gamma>0, the first applied at the genuine
minimum-e side-interior point Q. Suppose

    d=a*e+b*f, a>0, b>0.

Theorem2.2 applies to this complete star. Thus E is either radial
along its external incoming own axis e, or physically unique with

    Z=A*e+B*f, A>B>1/2.

In the unique case, writing the unchanged Q as
(A-1)*e+(B-tau)*f with 0<tau<1, the full moment identity is

    gamma*(b-a)=p*tau>0.                        (6e)

In particular b>a, so d makes an angle strictly greater than pi/4
with e. This statement does not assume a positive coefficient at
every physical corner: the complete physical-two case was
excluded or identified before the unique formula was used.

## 3. Complete two-endpoint angular alternative

Consider actual loaded true2 endpoints B,C of one retained unloaded
side or diagonal channel, or of a retained chain of actual unloaded
true2 bodies. Keep their full original endpoint equations

    G_B=p_B*b+gamma*d,
    G_C=-p_C*c-gamma*d,
    p_B,p_C,gamma>0.                              (6)

Assume b,c,d are unit, b,c are nonparallel, and d lies in the
closed positive cone generated by b,c. The full loaded-endpoint
cone theorem proves precisely this premise when the actual external
support difference is a strict positive combination of b,c; its
parallel, finite and coincident alternatives are all included.

Suppose the original external supports Q_B,Q_C are genuine owned
side interiors: Q_B is minimum-b in B, and Q_C is maximum-c in C.
Thus the incoming own axes in (6) are b at B and -c at C. Assume

    d.b>=0, d.c>=0.                               (7)

The following conclusion uses no unit width or path-length bound.

**Corollary 3.1.** If b.c>=0, then at least one actual endpoint has
the corresponding physical radial alignment

    B=[A_R-1,A_R]*b+[-1/2,1/2]*Jb,

or

    C=[-A_R,1-A_R]*c+[-1/2,1/2]*Jc.              (8)

Equivalently, if neither original endpoint has its radial position
in (8), then b.c<0. More precisely, the angle from b to d and the
angle from d to c within the same positive cone both exceed pi/4.

*Proof.* Let theta in (0,pi) be the smaller angle between b,c.
Because d is in their closed positive cone, its two nonnegative
intermediate angles delta_B,delta_C satisfy

    delta_B+delta_C=theta.

Condition (7) puts both intermediate angles in [0,pi/2]. If
delta_B<=pi/4, the two complete incoming directions b,d of B
satisfy the closed cone (2) about the actual own axis b. Its
unchanged genuine Q_B supplies (3). Theorem2.1 gives the first
position in (8). If delta_C<=pi/4, apply the same theorem at C
with the incoming own axis -c and the other incoming direction -d;
their angle is delta_C. Its unchanged Q_C supplies the genuine
minimum-(-c) port, giving the second position in (8).

Consequently, if neither radial position holds, both angles exceed
pi/4, and theta>pi/2. This is exactly b.c<0. In particular
theta<=pi/2 forces at least one radial alternative. The proof
includes both exact45-degree boundaries and both parallel
channel-endpoint possibilities. QED.

The radial alternative is physical, not a positive-weight count.
An endpoint with two physical circle corners and one zero coefficient
cannot be reclassified as unique to avoid (8). Conversely (8) fixes
the whole actual position, not only the side-frame direction.

## 4. A useful full radial torque consequence

The radial alternatives also give an exact original application test.
Let E have the actual position (4), with R>sqrt(5)/2, and retain its
complete loaded true2 equation with incoming own axis e at the
genuine point

    Q=(A_R-1)*e+q*f, -1/2<q<1/2,

and other incoming unit direction

    d=a*e+b*f, a>=0, b>0.

Let p,gamma>0 be the original corresponding magnitudes. The actual
minimum-d application T has the exact form

    T=xi*e-f/2,
    xi=A_R-1 when a>0,
    A_R-1<=xi<=A_R when a=0.                     (9)

The last row keeps the original full tied-side mean; it does not
replace it by an endpoint. All circle-force moments about O vanish.
The complete original torque therefore gives

    p*q=gamma*(xi*b+a/2)>0.                      (10)

Indeed the two pair moments in the right-handed actual frame are
p*q and -gamma*(xi*b+a/2). The strict inequality uses
xi>=A_R-1>0 and b>0. Thus

    0<q<1/2,
    gamma/p<1/(2*(A_R-1)*b+a).                   (11)

No equality of circle coefficients was used. The parallel b=0 case
is deliberately outside this strict-transverse corollary; its actual
support mean and full parallel-star theorem remain available.

This test applies even when d is outside the closed cone of
Theorem2.1, provided the physical radial position is independently
known. Its only degree requirement is that (10) uses the entire
actual two-force endpoint star.

## 5. Literal A-only side application

Use the complete original Type II A-only h side-return domain in

    TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md.

That source retains every original force, application, circle mask and
zero coefficient and proves, over its entire original domain,

    b=(-h-v*e)/sqrt(1+v^2),
    c=(-m*h+e)/sqrt(1+m^2),
    m>u, 0<u<v<1,
    d in the closed positive cone of b,c,
    d.b>=0, d.c>0.                               (12)

Its full true3 singleton argument makes Q_B and Q_C genuine owned
side-interior points. Therefore every hypothesis of Corollary3.1
is literal for the full loaded B2,C2. Since

    b.c=(m-v)/sqrt((1+v^2)*(1+m^2)),

the following exact alternative holds over the whole original row:

* if m>=v, B is physically radial along +b or C is physically
  radial along -c, or both;
* if neither physical radial position holds, then m<v and both
  unchanged endpoint incoming angles exceed pi/4.

No subinterval, single circle weight or perpendicular frame has
been silently removed. The previously excluded unloaded diagonal
N case is not reintroduced; this is a consequence for the actual
remaining side transmitter and its complete loaded endpoints.

For the actual own transverse axes used by the side source,

    w_B=-Jb, w_C=Jc,

the B radial alternative fixes the genuine external support height

    Q_B.b=A_R-1, |Q_B.w_B|<1/2,

and the C radial alternative fixes

    Q_C.c=1-A_R, |Q_C.w_C|<1/2.                  (13)

These are exact constraints on the unchanged absolute origin and
original hub chart. They do not reposition either endpoint.

If B is radial and d is not b, (12) gives d.w_B>0. Apply Section4
in the actual frame (b,w_B), with every determinant sign changed
together if this frame is left-handed. It gives Q_B.w_B>0.
Writing the original side source's x_B=1-beta_B then yields

    0<x_B=1/2-Q_B.w_B<1/2.                      (14)

This includes its possible d.b=0 tied application by (9).
Likewise, if C is radial and d is not c, use the frame (-c,-w_C).
It gives Q_C.w_C<0 and hence, in the unchanged side coordinates,

    0<x_C=1/2+Q_C.w_C<1/2.                      (15)

The parallel d=b or d=c alternatives remain covered by Corollary3.1
and by the original full parallel-star theorem; (14),(15) are not
asserted for their zero transverse component.

The physical positions and signs (13)--(15) can be combined with the
same complete side source's coupled corner budget. A contradiction
over all remaining original hub data is not proved here. This
manuscript supplies neither a whole A-only side exit nor any new
original graph/count credit.

### 5.1. The entire A-only physical-mask alternative

In fact the preceding alternative can be sharpened to a complete
mask statement. The exact directions in(12) give the cone angle

    theta=arctan(v)+arctan(1/m)<3*pi/4,          (16)

since 0<v<1 and m>0. Suppose neither radial position in(8) holds.
Section3 already gives both intermediate angles greater than pi/4.
The parallel d=b and d=c possibilities therefore cannot occur.

If d.b=0, its intermediate angle from b is pi/2. Equation(16)
would make the other angle strictly less than pi/4, contradicting
Section3. Hence d.b>0 as well as the already established d.c>0.
Both unchanged transverse components are now strictly positive:
d.w_B>0 and d.w_C>0, because d is strictly inside the same cone.

Apply Section2.3 to B in the actual frame(b,w_B), reversing all
determinant signs together if needed, and to C in(-c,-w_C).
The external ports are the unchanged genuine Q_B,Q_C. Both
actual endpoints have exactly two positive forces. The supposed
absence of their external-axis radial positions leaves only the
physical unique-circle mask at each endpoint.

Therefore the whole original A-only side row has this exhaustive
physical alternative:

1. B has the entire external-axis radial position in(8);
2. C has the entire external-axis radial position in(8);
3. both B and C have exactly one physical circle corner, m<v,
   and both unchanged incoming angles exceed pi/4.

The first two alternatives may overlap. In the third alternative,
the actual circle corners also satisfy the strict absolute
coordinate orders

    Z_B.b>Z_B.w_B>1/2,
    -Z_C.c>-Z_C.w_C>1/2.                         (17)

The coordinates are relative to the unchanged circle origin. These
are physical one-corner conclusions, independent of which individual
circle coefficients vanish in the discarded two-corner possibilities.
The original d.b=0 side tie was covered before any support point was
replaced by its uniquely exposed corner.

## 6. Scope, exact inputs, and independent review boundary

The generic theorem applies at every actual finite positive degree.
Its designated port and all other positive terms must coexist in
the same original full star. No neighbor is removed to manufacture
the closed cone, no application mean is chosen anew, and no physical
two-corner unit is treated as unique when one coefficient vanishes.

The two-endpoint corollary is independent of the length of the
retained unloaded chain. It uses only its unchanged endpoint
directions, the full loaded stars, actual owner interiors and
nonnegative own-direction projections. Every internal transmitter
and its original width remains present; no virtual longer square
or deletion is needed.

The complete physical-stress, prior open-cone, loaded-endpoint and
A-only side sources were read. The present closed-cone proof and
arbitrary-degree same-side extension are new constructions by the
common-selection continuation. The same-side loaded-two moment step
was supplied by the A-owner continuation, which is a contributor to
this manuscript and cannot independently review the entire result.
The prior open theorem was authored by the root continuation. The A-only support
projection m>u was contributed by the present author to the separate
side source; the present manuscript is not an independent review of
that contribution. It needs its own separate full independent
review before use as an adopted result.

| Complete source | SHA256 | Exact role |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Full original force, torque, support and mean conventions |
| LOADED_FULL_STAR_OPEN_SIDE_CONE_FORCES_PHYSICAL_RADIAL_ALIGNMENT_2026_10_29.md | dcbd7f5339899052dd8237858778c0bfb53c7a2f087a44d6edcd7db3a6c96952 | Complete strict-cone comparison and provenance; no closed-boundary conclusion is imported from it |
| LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md | 5f44ef77812f5626e69f70963f55d6b820bfdb8b1f51e3d1e54110cf695753e1 | Full endpoint cone with parallel, finite and coincident alternatives, and actual-chain scope |
| TYPE_II_A_ONLY_COMPLETE_SIDE_FORCE_SIGNS_AND_TWO_PHYSICAL_CIRCLE_CORNER_BUDGET_2026_10_29.md | 00e18446bab3fc7b97484fc33d700363ea41f415af5b1746ee4c020c87830033 | Whole original A-only side chart, genuine exterior owners, full sign cover and retained side coordinates |

No numerical pose search, angle mesh, packing certificate, new normal
selection, changed mean, shortened positive star, Lean/Lake build,
CI/workflow dispatch, original-flag edit, shared-metadata edit, commit
or remote mutation was used.

