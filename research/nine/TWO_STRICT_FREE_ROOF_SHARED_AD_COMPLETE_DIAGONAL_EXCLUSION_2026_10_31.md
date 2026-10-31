# A free strict roof and a shared hub interface admit no diagonal N

**Date:** October 31, 2026 UTC. **Complete hand exclusion of the original
diagonal-N feature.** Input PR #11 head:
`d896360d49bbdae72567ebe43fee939366ab2c20`.

This proof retains the full A3/D3/V2/B2/C2/N2 stars in D02.L135. It
eliminates all original angles, positive magnitudes, shared-interface
means and physical circle masks in the mixed free/owned strict-roof
chart with physically shared AD and diagonal N. In particular, neither
of the perpendicular endpoint support ties is discarded. The remaining
side-N feature and loaded-N D02.L1345 are outside this conclusion.

## 1. Literal original chart and all full-star identities

Keep all nine actual units and the original six positive stars

    A:{V,D,B}, D:{V,A,C}, V:{A,D},
    B:{A,N}, C:{D,N}, N:{B,C}.

A,D,N are unloaded, and V,B,C have positive total circle load. Every
physical circle corner and every individual zero coefficient remains.
Keep the same initial incident-diagonal avoidance and the original
applications or entire shared-side means. No normal is selected again.

The radius lies in the original window

    79/40 <= R <= sqrt(1105)/16.

Put d=sqrt(R^2-1/4)-1. Exact squaring gives

    9/10 < d < 51/50,       R^2=(d+1)^2+1/4.          (1)

For the lower comparison, (19/10)^2=5776/1600<5841/1600;
for the upper, 1041/256<(101/50)^2. These are the two bounds
obtained after subtracting 1/4 from the squared radius window.

Use the actual physical-two V and its adjacent strict inner corners

    V=[d,d+1] x [-1/2,1/2],
    P=(d,1/2), Q=(d,-1/2).

Suppose AV is free, DV is genuinely D-owned, and AD has positive
physical shared length. Write the original A-to-V direction as
h=(c,-s), with c,s>0 and c^2+s^2=1. In the mixed shared-interface
chart, let

    k=(C,S), g=(S,-C),
    C=cos(beta), S=sin(beta), 0<beta<pi/2.

Here is the exhaustive physical derivation of this chart. Positive shared
AD length makes the A,D frames parallel and its original normal an own
axis of both units. The D-owned roof k is a common own axis. The physical
triangle normal inequality at D gives k.(-g)>=0, excluding g=k.
At A the same inequality gives h.g>=0. Because h is genuinely free at
the A vertex P, it is not an A own axis and this comparison is strict.
Thus P belongs to A's maximum-g side, the shared AD support line.

If g=-k, the D roof Q belongs to the very same AD support line. Then
P-Q=(0,1) is tangent to that line, making g and k horizontal,
contrary to C,S>0. The only possibilities left are the two common axes
perpendicular to k. With v=(-S,C), one has h.v=-c*S-s*C<0;
therefore g=v is impossible at A. Necessarily g=-v=(S,-C), as above.

Because Q is relative-interior to D's maximum-k side, initially write
D=Q-[0,1]*k+[-ell,1-ell]*g with 0<ell<1. The original shared line
has height P.g, so ell=(Q-P).g=C. The free roof h has a nonzero
k component. If h.k<0, its strict vertex P is on A's minimum-k side,
and every A point has k coordinate at least P.k. But every D point has
k coordinate at most Q.k=P.k-S<P.k, contradicting shared AD. Hence
J=h.k>0. Since also h.g>0, the entire A is P-[0,1]*k-[0,1]*g.

Intersecting the two actual AD side intervals now gives exactly
k coordinates from P.k-1 to P.k-S. Consequently the actual
parallel-frame hub units and original shared mean are

    A=P-[0,1]*k-[0,1]*g,
    D=Q-[0,1]*k+[-C,1-C]*g,
    W=P-t*k,        S<=t<=1.                         (2)

These are whole units. Both endpoints of the original shared mean are
retained; a mean at t=S or t=1 is not called a singleton.

Write the original free A-to-V direction and three positive magnitudes
as

    h=(c,-s)=J*k+H*g,
    c=cos(alpha), s=sin(alpha), alpha>0,
    J=cos(alpha+beta)>0, H=sin(alpha+beta)>0,
    AV:mu>0, DV:nu>0, AD:gamma>0.

The full hub forces expose the actual exterior vertices

    F_AB=-mu*J*k-(mu*H+gamma)*g, K=P-k-g,
    F_DC=-nu*k+gamma*g,          L=Q-k+(1-C)*g.

In particular

    Delta:=K-L=S*k-2*g.                              (3)

The original full torques at A,D,V are respectively

    mu*(J-H)=gamma*(1-t),
    nu*(1-C)=gamma*(1+S-t),
    mu*(d*s+c/2)=nu*(d*S+C/2).                       (4)

For example det(k,g)=-1, so A's moment about P is
gamma*t+mu*(J-H)-gamma=0. D's moment about Q is
gamma*(S-t)+gamma-nu*(1-C)=0. Thus (4) uses the actual
shared mean, not a substitute endpoint or midpoint.

The first equality and t<=1 imply J>=H. Consequently

    0<alpha+beta<=pi/4,       0<beta<pi/4.             (5)

The equality alpha+beta=pi/4, which requires t=1, remains included.

## 2. Two useful strict facts about the original endpoint directions

Define only positive normalizations of the original forces:

    r=gamma/nu, m=gamma/mu,
    A0=d*s+c/2, B0=d*S+C/2,
    b=F_AB/|F_AB|=-a*k-z*g,   a,z>0, a^2+z^2=1,
    cvec=-F_DC/|F_DC|=p*k-q*g,
    p=1/sqrt(1+r^2), q=r/sqrt(1+r^2).

K is the original minimum-b support of B; L is the original
maximum-cvec support of C. Equations (4) give

    1-C<=r<=(1-C)/S=tan(beta/2),
    m=r*A0/B0,
    H+m-J=m*t>0.                                   (6)

Thus

    z>a>0,        p>q>0.                            (7)

We also need the strictly negative actual endpoint dot product

    b.cvec<0.                                      (8)

Here is a complete rational estimate that proves it throughout the
whole chart, including t=1. By (1),(5),

    J>7/10, H<3/4, S<3/4, C>7/10,
    r<sqrt(2)-1<5/12,
    0<A0<=sqrt(d^2+1/4)<5/4, B0>=d*S.

Since r<=S/(1+C),

    r*H < 5/16,
    r^2*A0/B0
      <= S*A0/[d*(1+C)^2]
       < [(3/4)*(5/4)]/[(9/10)*(17/10)^2]
        =625/1734 < 3/8.

Therefore

    r*H+r^2*A0/B0 < 11/16 < 7/10 < J.

The sign of b.cvec is the sign of
-J+r*(H+m)=-J+r*H+r^2*A0/B0, proving (8).
Every division here is by a strictly positive original magnitude or
an explicitly positive scalar; no singular support case is removed.

## 3. All diagonal possibilities reduce to exactly two own-axis ties

The actual support difference lies strictly in the positive cone of
the original endpoint directions b,cvec. To verify this without an
acute premise, use their unnormalized vectors

    b0=-mu*J*k-(mu*H+gamma)*g,
    c0=nu*k-gamma*g,
    D0=mu*J*gamma+nu*(mu*H+gamma)>0.

Direct expansion of (3) gives

    Delta=lambda0*b0+eta0*c0,
    lambda0=(2*nu-S*gamma)/D0>0,
    eta0=[S*(mu*H+gamma)+2*mu*J]/D0>0.              (9)

Indeed S*gamma/nu=S*r<=1-C<1, so the first numerator is
positive. Normalizing b0,c0 preserves strict positivity.

If the original N is diagonal, its full unloaded true2 equations give

    T-U=sqrt(2)*n, |n|=1,

where T is its original B application and U its original C application.
The retained incident-diagonal avoidance makes both B,C own n at these
physical contacts. No endpoint frame is assigned afresh.

Apply the complete signed support classification in Sections 1--4 of
[NONACUTE_SUPPORT_CONE_DIAGONAL_BRIDGE_GAP_AND_COMPLETE_A_ONLY_CONE_REDUCTION_2026_10_29.md](NONACUTE_SUPPORT_CONE_DIAGONAL_BRIDGE_GAP_AND_COMPLETE_A_ONLY_CONE_REDUCTION_2026_10_29.md).
Its premises are (9), the full N equation and those actual owned ports.
It includes all original side-support ties and their entire means.
Since

    3<4+S^2=|Delta|^2<5<(1+sqrt(2))^2,

the classification leaves exactly one of

    b.n=0, cvec.n>0;     or     cvec.n=0, b.n>0.     (10)

In particular no continuous sector of diagonal directions remains.
The following two sections exclude the full original ties, without
replacing their support side by a strict vertex.

## 4. The tie cvec.n=0 forces an impossible radial B

The sign Delta.n>0 fixes

    n=-q*k-p*g.

The opposite perpendicular has negative dot product with Delta.
By (7),(8),

    b.n=a*q+z*p > |-a*p+z*q|=|b.cvec|.

For instance b.n+b.cvec=p*(z-a)+q*(a+z)>0;
b.cvec<0 supplies the other strict comparison. Both original
incoming directions at B, namely b and n, lie in the open own-side
cone about n. The full loaded-star theorem
[LOADED_FULL_STAR_OPEN_SIDE_CONE_FORCES_PHYSICAL_RADIAL_ALIGNMENT_2026_10_29.md](LOADED_FULL_STAR_OPEN_SIDE_CONE_FORCES_PHYSICAL_RADIAL_ALIGNMENT_2026_10_29.md)
therefore fixes the actual B as

    B=[d,d+1]*n+[-1/2,1/2]*cvec.

This theorem retains both physical circle corners and arbitrary
nonnegative individual weights. Because b.n>0 and b.cvec<0,
its actual minimum-b vertex K must satisfy

    K=d*n+cvec/2,       K.cvec=1/2.                 (11)

We now bound the same original K directly. Put

    X=K.k=d*C+S/2-1,
    Y=K.g=d*S-C/2-1.

The whole chart has X<1/4 and Y<-1/2. The first follows from
sqrt(d^2+1/4)<5/4. For the second, the increasing function
d*sin(beta)-cos(beta)/2 is at most (d-1/2)/sqrt(2)<1/2
on 0<beta<pi/4. Hence

    K.cvec=(X-r*Y)/sqrt(1+r^2)

is strictly increasing in 0<=r<=tan(beta/2)<1/2: its derivative
has numerator -Y-r*X>1/2-1/8>0.

Let phi=beta/2, x=sin(phi), y=cos(phi)>9/10. By (6),

    K.cvec
      <=d*cos(3*phi)+sin(3*phi)/2-cos(phi)+sin(phi)
       =(d-1)*cos(3*phi)+(5/2)*x-4*x^2*y-2*x^3
       <1/50+(5/2)*x-(18/5)*x^2
      <=1/50+125/288
       <1/2.                                      (12)

The penultimate inequality is just completion of a square in x.
Also cos(3*phi)>0, so (d-1)*cos(3*phi)<1/50 even when d<1.
The bound y>9/10 follows from 0<phi<pi/8.
Thus (12) contradicts (11), excluding this entire tie.

## 5. The tie b.n=0 forces a strict whole-unit transverse gap

Here Delta.n>0 fixes

    n=z*k-a*g.

By (7),(8),

    cvec.n=p*z+q*a > |-p*a+q*z|=|cvec.b|.

Thus the entire two-force star of C, whose incoming directions are
-cvec and -n, lies in the open own-side cone about -n. The same
full loaded-star theorem fixes the actual C as

    C=[-d-1,-d]*n+[-1/2,1/2]*b.

Since cvec.n>0 and cvec.b<0, its unchanged maximum-cvec support is

    L=-d*n-b/2,       |L|^2=d^2+1/4=|Q|^2.          (13)

### 5.1. The actual radial corner forces beta<pi/6

Using L=Q-k+(1-C)*g from (2), exact expansion gives

    |L|^2-|Q|^2=2-C+S-2*d*(C-S+S*C).              (14)

Here C-S+SC>0. If pi/6<=beta<pi/4, (1) makes the right
side strictly greater than

    F(beta)=2+(76/25)*(S-C)-(51/25)*S*C.

Its derivative is

    F'(beta)=(76/25)*(C+S)-(51/25)*(C^2-S^2)>0.

At beta=pi/6 it equals

    F(pi/6)=(352-203*sqrt(3))/100>0,

since 352^2=123904>123627=3*203^2. This contradicts (13).
Consequently the entire remaining tie satisfies

    beta<pi/6,       S<1/2.                         (15)

### 5.2. The whole endpoint squares have disjoint transverse projections

By (3),(13), K.b=-1/2+2*z-S*a. Since z>a>0,
a^2+z^2=1 and S<1/2,

    Delta.b=2*z-S*a>3*sqrt(2)/4>1,
    K.b>1/2.                                        (16)

The original support K makes every actual B point have b projection
at least K.b>1/2. But the entire radial C has b projection in
[-1/2,1/2]. Thus every actual T in B and U in C satisfies

    (T-U).b>0.

This contradicts T-U=sqrt(2)*n and b.n=0. Equivalently, (16)
contradicts the exact |Delta.b|<=1 conclusion for the corresponding
axis tie in the signed support theorem. The whole-unit argument
retains every original support mean and does not require a further
B circle-corner comparison. It excludes the second complete tie in (10).

### 5.3. A reusable tie theorem for any actual channel length

The proofs in Sections 4--5 do not use the value sqrt(2) of the
channel length, except when Section 3 obtains endpoint ownership.
Consequently the following stronger conditional statement holds.
Keep the entire shared-interface chart, full V2/B2/C2 equations and
all original support data above. Suppose an actual channel has

    T-U=ell*n, ell>0,

with n an actual own axis of **both endpoint units** B,C. If either
b.n=0,cvec.n>0 or cvec.n=0,b.n>0, that channel is impossible.
In the cvec.n=0 case, Section 4's actual radial B and fixed-support
cap proof are unchanged. In the b.n=0 case, Section 5.1's actual
radial C is unchanged and the strict transverse gap (16) contradicts
(T-U).b=ell*(n.b)=0 for every positive ell.

In particular this excludes both own-axis ties for an original side N
when the endpoint ownership premise is separately present. The fact
that a side transmitter owns n itself does not establish ownership
by either endpoint, and no such inference is made here.

### 5.4. The whole side feature with both endpoints owning n is excluded

Suppose now the original N is a side transmitter and both actual
endpoint units B,C also own n. This includes the whole feature in which
both N contacts have positive physical shared length. Keep their full
side means T,U and the relation T-U=n.

Choose an actual perpendicular axis w. The endpoint squares have

    B=T+[0,1]*n+[-u,1-u]*w,
    C=U+[-1,0]*n+[-v,1-v]*w,
    0<=u,v<=1.

As in the signed support proof, the original exterior supports obey

    Delta.n=1+xi_B+xi_C, 0<=xi_B,xi_C<=1,
    |Delta.w|<=1.                                  (17)

The second inequality uses only the positive cone (9) and the two
actual support faces: same strict signs for b.w,cvec.w would make
their support difference have the opposite sign, and opposite signs
or either zero sign give the bound one, with the original full side
coordinates retained. Thus the signed calculation applies unchanged
with channel length one in the first equation.

The positive cone and Delta.n>0 prevent both b.n,cvec.n from being
nonpositive. If both are strictly positive, xi_B=xi_C=0 and (17)
gives |Delta|^2<=2, contradicting (3). If one is zero, Section 5.3
excludes the whole original tie. If one is negative and the other
positive, the actual support faces give {xi_B,xi_C}={1,0} and hence

    Delta.n=2.

Solving this exact equation with Delta=S*k-2*g and |n|=1 gives just

    n=-g,
    n=[4*S*k+(S^2-4)*g]/(4+S^2).                   (18)

For n=-g, both b.n=z and cvec.n=q are positive. For the second
direction, cvec.n>0 immediately, while

    (4+S^2)*(b.n)=z*(4-S^2)-4*a*S
       >a*(4-S^2-4*S)>0.

The last strict inequality follows from 0<S<3/4, which gives
4-S^2-4*S>7/16. Thus both directions in (18) contradict the
required negative endpoint component. All sign cases are exhausted.

Therefore no original side N in this shared-interface chart can have
its normal owned by both actual endpoints. In particular its two
physical contacts cannot both be shared segments. A remaining side N
must have at least one genuine endpoint singleton at which only N
owns its normal; this is a necessary remaining feature, not a claim
that such a configuration exists.

### 5.5. At a unique-circle singleton endpoint the exterior port is owned

The remaining endpoint singleton has a useful complete owner reduction.
Suppose B does not own the side-channel normal n. Its actual N contact
is then a genuine N-owned singleton at a B vertex T and a relative-
interior point of an N side. Its exterior AB contact K is also a physical
singleton, since F_AB strictly exposes A's vertex K.

These two actual applications are distinct. Indeed if K=T, the local
interior sector of N at that point is an open half-plane, of angle pi.
The A and B vertex sectors each have angle pi/2. Pairwise disjoint
interiors put both closed right-angle sectors in the complementary
closed half-plane. Two such sectors with disjoint interiors can fit
there only by filling it, so they have a common boundary ray. Along
a sufficiently short nondegenerate segment of that ray, both actual
unit squares A and B are present. This contradicts their physical
singleton intersection. The same argument applies at C and its hub D.

If B has exactly one physical circle corner, both of its pair contacts
are therefore distinct fixed singleton points. Apply the existing
common-certificate theorem
[GENERAL_FIXED_TIP_NORMAL_SELECTION.md](GENERAL_FIXED_TIP_NORMAL_SELECTION.md)
with precisely these full original premises. It excludes a free AB
normal. The direction is strictly inside A's vertex cone, so A does
not own it; hence **B owns its exterior normal b** at K. No new
selector or post-extraction normal change is introduced.

Thus every remaining N-only singleton endpoint obeys the exhaustive
alternative: it has two physical circle corners, or it owns its
exterior hub normal. The same statement holds for C and -cvec.
An individual zero circle coefficient does not turn the two-corner
case into the unique-corner case. At an endpoint whose N contact is
physically shared, the variable original N mean is retained and this
fixed-application selector is not applied.

### 5.6. Both physical-two endpoints cannot both have free exterior ports

There is a further complete original-mask exclusion that does not
assume a radial circle resultant. Suppose B and C each have two actual
physical circle corners, while B does not own b and C does not own
cvec. The individual circle weights, including zero weights, are
unrestricted. This argument works for either original channel type.

For the unchanged nine units the complete analytic theorem
[NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md](NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md)
first excludes R<=2. Thus the present caller has

    R>2,       d>14/15.                              (19)

Indeed R^2-1/4>15/4>(29/15)^2, with reserve 11/900.
This lower bound is taken from the same nine-unit packing, not from
the six-star component alone.

Any actual unit with exactly two physical circle corners has those
corners adjacent. In its actual own frame it is
[d,d+1] times [-1/2,1/2], up to one rigid rotation about O.
Its two other, inner vertices therefore have squared norm d^2+1/4.
An actual pair contact cannot occur at one of its circle corners:
at a common radius-R point each unit's right-angle interior sector
would lie strictly inside the same inward tangent half-plane, making
two such sectors overlap. This is independent of the circle weights.

Since the two exterior normals in the present feature are not owned
by B,C, they strictly expose their actual vertices K,L. Those vertices
must consequently be inner vertices, and hence

    |K|^2=|L|^2=d^2+1/4=|P|^2.                     (20)

Using K=P-k-g and the already expanded formula (14), these exact
physical equalities give

    d=(2+C-S)/(2(C+S)),
    d=(2-C+S)/(2(C-S+S*C)).                         (21)

All denominators are positive because 0<beta<pi/4. Put

    q=C-S, p=C+S=sqrt(2-q^2), 0<q<1.

Equality of the two expressions in (21) is exactly F(q)=0, where

    F(q)=1+(5/2)q-q^3/2-(2-q)*sqrt(2-q^2).

Throughout 0<=q<=1 its derivative is

    F'(q)=5/2-(3/2)q^2+p+(2-q)q/p>0.

At q=12/25, one has p=sqrt(1106)/25<7/5, and therefore

    F(12/25)>33511/15625-266/125
              =261/15625>0.

Consequently the actual root must satisfy q<12/25. The positive
function (2+q)/(2*sqrt(2-q^2)) is strictly increasing on [0,1],
so the first equation in (21) now yields

    d<31/sqrt(1106)<14/15.                           (22)

The last strict comparison follows by positive squaring:
196*1106-465^2=551>0. This contradicts (19).

Thus the entire feature with both physical-two endpoint masks and
both exterior ports unowned by those endpoints is impossible.
No force symmetry, equality of the two corner weights, endpoint
normal reselection, or contraction of the side transmitter is used.
Together with Section 5.5 this has a useful complete conditional join:
if both N contacts are genuine N-only singletons, at least one
endpoint must own its exterior hub normal. Otherwise Section 5.5
would make both endpoints physically two-corner, contradicting the
present proof. A physically shared N port retains its original mean
and is outside that fixed-application join.

## 6. Complete original feature consequence and exact remaining scope

The signed support theorem and Sections 4--5 exhaust the entire
diagonal-N alternative. Thus the mixed free/owned strict-roof chart
with physically shared AD has **no actual unloaded diagonal N** in
the whole original D02.L135 radius window. Reflecting the complete
data and exchanging A,D and B,C gives the free-D-roof counterpart.

Both physical coefficient endpoints at V,B,C, both shared-AD mean
endpoints, the equality J=H, and both previously exceptional exterior
own-axis ties are included. All six actual stars and all three
completion units remain. The proof uses elementary support geometry,
full force/torque identities, one complete existing signed-support
table and explicit rational inequalities only.

The actual unloaded N must therefore be a **side transmitter with at
least one endpoint not owning its channel normal** if this shared-
interface chart survives. The full side feature with both endpoints
owning the normal is excluded in Section 5.4. This source does not
exclude the remaining side alternative or loaded N of D02.L1345. It changes no
original row or coarse flag by itself and makes no claim that the
unrestricted n=9 theorem is closed. No numerical search, external
computational certificate, Lean compilation or CI was used.
