# The full mixed-perpendicular stars force a strict endpoint cone and a radial endpoint

Date: October 31, 2026 UTC.

**Status: complete proposed hand theorem, for full root review.**
In the mixed free-roof/genuine-other-hub-perpendicular feature, the
original exterior support difference lies in the strict positive cone
of the two actual exterior own axes. Consequently every original
loaded2/side-transmitter/loaded2 continuation has a physical radial
endpoint. In particular its entire both-unique-circle-corner mask is
excluded. The proof is uniform in both original roof angles, all force
ratios, and the whole actual shared AB mean. No numerical calculation,
Lean, CI, or change of a selected normal is used.

## 1. The original physical chart and every full star

Retain the complete actual mixed chart of
`TWO_STRICT_FREE_ROOF_OTHER_HUB_PERPENDICULAR_COMPLETE_DIAGONAL_EXCLUSION_2026_10_31.md`
before making any assumption on the continuation N. Its relevant data are

    79/40<=R<=sqrt(1105)/16, d=sqrt(R^2-1/4)-1,
    P=(d,1/2), Q=(d,-1/2), 9/10<d<61/60,
    k=(C,S), v=(-S,C), C=cos(beta), S=sin(beta),
    0<beta<delta<pi/2, a=sin(delta), w=cos(delta),
    u=-a*k-w*v, b=-w*k+a*v, det(b,u)=1,
    W=P+u=Q-(a-S)*k+(C-w)*v.

The actual A unit is P+[0,1]u+[0,1]b. Its AB contact is physically
shared, and its original full mean is

    K=P+b+t*u, 0<=t<=1.                             (1)

The D-to-V force is nu*k and the D-to-A force is gamma*v,
with nu,gamma>0. D is the original unloaded true3. Its actual exterior
force to C_* is -nu*k-gamma*v, at the genuine D corner

    L=Q-k+(C-w-1)*v
     =P-(1+S)*k-(1+w)*v.                            (2)

Here C_* names the exterior unit, to distinguish it from C=cos(beta).
The unchanged singleton selector makes C_* own its exterior normal;
no C_* equation is used to derive that physical ownership.

The full D torque fixes

    r=nu/gamma=(1+S-a)/(1-C+w)>0,
    c=(r*k+v)/sqrt(1+r^2).                          (3)

Thus b is the actual inward exterior own axis of B at its minimum-b
support K, and -c is the actual inward exterior own axis of C_* at
its maximum-c support L. A and D remain unloaded true3, V remains
the actual loaded true2 with exactly A,D as its positive neighbors.

The complete physical support-cap theorem
`TWO_STRICT_FREE_ROOF_PERPENDICULAR_HUB_SUPPORT_CAP_AND_ACUTE_EXTERIOR_AXES_2026_10_31.md`
already excludes delta<=pi/4 from this entire chart. Hence

    pi/4<delta<pi/2,
    q:=a-r*w>0,
    0<b dot c=q/sqrt(1+r^2)<1.                     (4)

The last inequality also has a short direct check. Put B0=1-C+w>0.
Then

    B0*q=2*a*w+a-w-sin(delta+beta)>0,

because 2aw+a-w>1 when delta>pi/4. Indeed the two nonnegative
quantities w(2a-1),1-a have squared difference
2a(1-a)(2a^2-1)>0. The axes are not parallel because their
strict k-coordinate signs differ. Thus their smaller angle is acute.

## 2. The actual shared mean is fixed by the complete A,D,V moments

Let p>0 be the original AB force magnitude, so A's exterior force
is p*b. No midpoint is prescribed in (1). The original A torque
about P uses its actual AD force -gamma*v at W and its actual AB
force p*b at K. Since det(u,v)=-a and det(u,b)=-1, it gives

    gamma*a=p*t.                                   (5)

Define positive quantities

    x=delta-beta in (0,pi/2),
    F=d*sin(x)+(1/2)*cos(x)>0,
    V0=d*C+S/2>0,
    D0=d*S+C/2>0,
    H=V0+r*D0>0.                                   (6)

Sum the complete origin moments of A,D,V. Every internal pair force
cancels, and every actual circle force of V has zero origin moment.
The only remaining pair forces are p*b at K and -gamma*(r*k+v)
at L. Therefore

    p*det(K,b)=gamma*det(L,r*k+v).                  (7)

Since b=(-cos(x),sin(x)) and u=Jb,

    det(K,b)=F-t.

Using (2),(3),

    det(L,r*k+v)
       =d*(C+r*S)-1-S/2+r*(1+w-C/2)
       =d*(C+r*S)+(S+r*C)/2-a
       =H-a.                                       (8)

The middle equality uses precisely r*(1-C+w)=1+S-a from the
full D3; it is not an independent force-ratio choice. Equations
(5),(7),(8) now imply p*F=gamma*H. Thus the original full mean obeys

    t=a*F/H.                                       (9)

This is an identity for the unchanged actual mean, not a choice of
a better contact point. It retains the complete A3,D3,V2 stars.
There is no endpoint or N equation in (5)--(9), and the complete
physical masks and individual circle coefficients of V are retained.

## 3. A continuous algebraic cone inequality

Let Delta=K-L. Its actual own coordinates from (1),(2) are

    Delta_k=1+S-w-a*t,
    Delta_v=1+w+a-w*t.                             (10)

The positive c coefficient will follow immediately from

    a*Delta_k+w*Delta_v
      =a*(1+S)+w*(1+w)-t>0,                        (11)

since t<=1, a+w>1, and all omitted terms are positive.

The other required determinant is

    E=r*Delta_v-Delta_k
     =A+q*t,
    A:=r*(C+a)-a+w, q=a-r*w>0.                    (12)

The simplified expression for A uses (3). We prove E>0 on the
entire original continuous domain. If A>=0, this follows directly
from (9), since t>0. It remains to treat all A<0 at once.

First A<0 implies r<1. From (3), r<1 is equivalent to

    S+C<a+w.

Since 0<beta<delta<pi/2, the sum-to-product identity gives

    S+C-a-w
      =-2*sin((delta-beta)/2)
              *(cos((delta+beta)/2)-sin((delta+beta)/2)).

It follows that beta+delta<pi/2, and therefore

    C>a, S<w.                                      (13)

Expanding (9),(12) makes H*E affine in the actual radius parameter d:

    H*E=d*E_d+(1/2)*E_0,
    E_d=A*(C+r*S)+q*a*sin(x),
    E_0=A*(S+r*C)+q*a*cos(x).                     (14)

Define

    X=A+q*a^2
      =w*(1-a*w)+r*(C+a-a^2*w)>0,
    Y=r*A-q*a*w<0.                                (15)

The signs are strict: every term in the displayed X is positive,
while A<0 and q,a,w>0 make Y negative. The exact identities
sin(x)=a*C-w*S and cos(x)=w*C+a*S give

    E_d=C*X+S*Y,
    E_0=C*(r*A+q*a*w)+S*X.                         (16)

By (13),(15),

    E_d>a*X+w*Y
       =(a+r*w)*A+q*a*(a^2-w^2).                  (17)

Moreover A=w-a+r*(C+a)>w-a+2*a*r. Substituting this and
q=a-r*w into the last expression in (17), then expanding, gives

    E_d>
       a*w*(1-2*a*w)
       +r*(1+a^2-2*a^3*w)
       +2*a*r^2*w
       >r.                                         (18)

The last strict bound is immediate from 2aw<=a^2+w^2=1:
the first term is nonnegative, the middle term is at least r,
and the last term is strictly positive. Thus every algebraic step
uses an inequality on the whole domain, without a subdivision mesh.

For the constant coefficient, (15),(16) and 0<C<1 give

    E_0>C*r*A>r*A>-r.                              (19)

The final comparison uses A=w-a+r(C+a)>w-a>-1.
Unlike E_d, the coefficient E_0 need not be positive. Keeping it
with the actual radius term is essential. From (14),(18),(19),

    H*E>(d-1/2)*r>0.                              (20)

This proves E>0, including the complete A<0 alternative. The
algebraic lemma actually needs only d>1/2 once (3),(4),(9) and
the physical interval t<=1 are supplied.

## 4. The strict original support cone and the full loaded-endpoint consequence

Combining (11),(12),(20), define the strictly positive coefficients

    lambda=(r*Delta_v-Delta_k)/(w+a*r),
    eta=sqrt(1+r^2)*(a*Delta_k+w*Delta_v)/(w+a*r).

Solving in the orthonormal k,v frame gives the exact original identity

    Delta=lambda*b+eta*c, lambda,eta>0.            (21)

Now restore the actual original continuation B--N--C_*. B and C_*
are positively loaded true2 with their unchanged A and D exterior
contacts. N is unloaded true2. In its actual side alternative write

    T-U=n, abs(n)=1,

for the unchanged N--B and N--C_* applications, respectively.
The full loaded-endpoint theorem in
`LOADED_ENDPOINTS_FORCE_TRANSMITTER_CONE_AND_PHYSICAL_CORNER_CAP_2026_10_29.md`,
Theorem2.1, applies literally to (21). It keeps every actual side mean,
physical circle mask, and parallel or coincident endpoint alternative.
It puts the actual n in the closed cone generated by b,c. If neither
endpoint's two normal lines are parallel, n is in its strict interior;
at n=b or n=c the corresponding actual endpoint is already radial.

Let theta be the angle from c to b in (0,pi/2), by (4). Any direction
n in this closed cone has angular distance strictly less than pi/4
from at least one of b,c: the two distances sum to theta<pi/2.

If its distance from b is less than pi/4, the **entire** actual B2
star has incoming directions b,n in the same open own-side cone
about b. The full-star theorem
`LOADED_FULL_STAR_OPEN_SIDE_CONE_FORCES_PHYSICAL_RADIAL_ALIGNMENT_2026_10_29.md`
then makes B the actual physical radial unit

    B=[d,d+1]*b+[-1/2,1/2]*Jb.                    (22)

If its distance from c is less than pi/4, the entire actual C_*2
star has incoming directions -c,-n in the same open own-side cone
about -c. The same theorem makes

    C_*=[d,d+1]*(-c)+[-1/2,1/2]*Jc.               (23)

The open-side-cone theorem retains either individual zero circle
coefficient, every original contact mean, and the complete physical
two-corner mask. The conclusion does not replace a side application
by its midpoint. At least one of (22),(23) therefore holds for every
actual side continuation in the whole mixed-perpendicular feature.

**Theorem.** The entire original side feature with both B and C_*
having unique physical circle corners is impossible. Every surviving
side feature has a physical radial endpoint with exactly the full
position (22) or (23). The other endpoint remains unrestricted by
this statement; both-radial possibilities are retained.

## 5. Whole-channel extension and exact remaining boundary

The same support identity (21) does not use any N equation. If the
single N is replaced in a larger actual component by a full positive
path of unloaded true2 transmitters between the same loaded true2
endpoints, all original internal forces and application differences
telescope to T-U=L*n with L>0. The complete chain version of the
loaded-endpoint cone theorem gives the same closed cone for n. Thus
the radial-endpoint consequence and the both-unique exclusion remain
valid for the whole retained chain. No transmitter is compressed into
a virtual unit, and no higher-degree body is assigned a true2 equation.

For the original D02.L135 caller, the other mixed-perpendicular
diagonal feature is already excluded by the separate complete
own-axis theorem. The present source closes its whole both-unique
side mask and supplies the exact strict support cone for its remaining
radial masks. It does not exclude the mixed radial/unique or
radial/radial side masks by itself, and does not close the entire
original row or any coarse parent. Loaded N in L1345 is outside the
transmitter consequence and retains its full positive circle force.

No original normal, physical frame, full mean, load, force ratio,
positive chord, or completion unit is altered. No external numerical
script or computer-assisted certificate is used. No Lean/Lake run,
CI, remote write, proof-ledger flag, or total gate count is changed
by this source itself.
