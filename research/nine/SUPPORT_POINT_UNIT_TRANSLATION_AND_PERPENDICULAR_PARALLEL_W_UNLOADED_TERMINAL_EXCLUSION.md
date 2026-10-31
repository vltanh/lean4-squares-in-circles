# Support-point unit translations and the entire perpendicular parallel-W unloaded-terminal feature

Date: October 29, 2026 UTC. Author: pentagon continuation.

The first theorem restates and proves a radius-free, force-free fact
already established in Section 3 of frozen 3808b2b7, credited there
to root's actual-point radial test: from any actual minimum support
point or mean of a unit square, the entire inward unit-normal
segment belongs to that same square. The next theorem
uses only the full equations of actual unloaded true-degree-two
transmitters. It supplies actual points of the real successor square,
with exact coupled circle inequalities as well as support bounds.

The main local application excludes the entire perpendicular hub-axis
feature when W is parallel to U. V is allowed every frame, physical
circle mask, return owner and original mean. W and the real successor
C have arbitrary true degrees, circle loads and other forces. T is
the actual unloaded true-degree-two neighbor of U. No boundary status
or proper concurrence at T or C is assumed.

The full new original callers are the W-parallel perpendicular
features in D02.L014 and D02.L0145. A second whole feature, with V
parallel and physically unique and its outer height at most two,
exits for arbitrary W frame. The source states precisely the further
local quarter-disk and free-return exits used in the complete cover.
No entire original low-load row or parent is declared closed.

## 1. Every actual supporting face has an inward unit segment

The endpoint fact and its entire side/vertex/mean scope are already
proved in Section 3 of LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md.
The following direct coordinate proof records that fact for reuse
without any loaded-star or concurrence premise. The new application
in this manuscript is to the actual unloaded path and its unchanged
successor, followed by the complete perpendicular feature below.

Let K be an arbitrary actual closed unit square in the Euclidean
plane. Let n be any unit vector, and let P be any point of its
minimum-n supporting face:

    n.P=min_(z in K) n.z.

No origin, containing circle, other square, force, contact owner,
degree or load is a hypothesis.

**Theorem A.** For every 0<=t<=1,

    P+t*n belongs to K.                              (1)

In particular P+n is an actual point of the unchanged square. The
statement holds simultaneously for every point on the support face,
including every side-interior point and both side endpoints. It
therefore applies to an original full contact mean without choosing
or moving that mean.

### 1.1. Whole face and vertex proof

Write the actual square in its own orthonormal axes as

    K=P_0+[0,1]e+[0,1]f,
    n=a*e+b*f, a^2+b^2=1.

If a>0, every minimum-n point has e-coordinate zero. Its
e-coordinate after adding t*n is t*a, which lies in [0,1]
because 0<=t<=1 and 0<a<=1. If a<0, every minimum point
has e-coordinate one, and the new coordinate 1+t*a lies
in [0,1]. If a=0, the e-coordinate is unconstrained in [0,1]
and does not change. The identical argument applies to b and
the f-coordinate. This proves (1) for the entire supporting face.

Both nonzero coordinates give a vertex, with either sign choice
included. One zero coordinate gives an entire side. They cannot
both vanish because n is unit. Thus no face, endpoint or normal
direction is omitted. The proof does not equate a support normal
with one of K's own axes in the vertex case.

More precisely the same proof gives the entire segment

    0<=t<=1/max(|a|,|b|).                            (2)

The denominator is positive. Formula (1) is the uniform consequence
because max(|a|,|b|)<=1. At a maximum-n face, applying the same
statement to -n gives P-t*n in K over the same interval.

## 2. Actual unloaded paths give actual successor points

Keep a real positive path of distinct actual contained units

    A--T_1--...--T_m--C, m>=1,

with every T_i genuinely unloaded and of true positive degree two,
with exactly its predecessor and successor as positive neighbors.
A and C have arbitrary degrees, loads, masks and other forces.
Keep all original normals, positive magnitudes, actual applications,
full shared means, force and torque equations, and every physical
unit. Let n be the original A-to-T_1 unit normal and P its original
application or full mean.

At a transmitter T_i the full force equation, with original
incoming magnitude lambda>0 and original outgoing unit normal q,
is

    -lambda*n+nu*q=0, nu>0.

Hence nu=lambda and q=n. Induction gives the same original forward
normal and magnitude throughout the actual path. At its incoming
and outgoing original points P_-,P_+, the entire torque equation is

    lambda*det(P_+-P_-,n)=0.

The difference is parallel to n. The two points realize its actual
minimum and maximum n supports, so exactly

    P_+-P_-=w_i*n,
    w_i=w_(T_i)(n)>0.                              (3)

Every actual shared segment has constant n projection. Equation
(3) retains the two original means and follows from their unchanged
full torque; it does not select equal transverse coordinates as an
extra assumption.

The complete transmitter alternatives are also immediate. If n
is a side axis of T_i, its width is one. Otherwise its two supports
are opposite vertices, whose difference has length sqrt(2); (3)
forces a diagonal normal and width sqrt(2). Thus

    w_i in {1,sqrt(2)}.                              (4)

At the actual last contact, put W_*=sum_i w_i. Its original point
or mean is

    P_C=P+W_*n,
    n.P_C=min_(z in C) n.z.                         (5)

Apply Theorem A to this actual support face of C. It gives

    P+(W_*+t)n in C for every 0<=t<=1.              (6)

The endpoints and all intermediate path squares remain actual;
there is no direct A--C contact. By convexity, (3) also puts the
whole segment between each successive original pair of points
inside its corresponding transmitter. Equations (3),(6) are an
occupied straight path through the unchanged units, rather than
an abstract replacement for them.

### 2.1. Coupled circle inequalities and the one-transmitter point

If C is contained in the unchanged disk D_R(O), taking O as zero,
the actual endpoint in (6) gives

    |P+(W_*+1)n|^2
      =|P|^2+(W_*+1)^2+2(W_*+1)*n.P<=R^2.          (7)

This retains the transverse coordinate of the original P. A
bound only on its scalar support need not imply (7).

For exactly one actual transmitter T, (4) gives
1<=w_T<=sqrt(2)<2. Therefore 0<2-w_T<=1, and (6) gives
the particularly useful **actual successor point**

    P+2n in C,
    |P|^2+4+4*n.P<=R^2.                            (8)

This includes both the side and diagonal transmitter. It does
not require a prior high-radius reduction to a side transmitter.
At a side transmitter the parameter in C is one; at a diagonal
transmitter it is 2-sqrt(2). Every physical circle corner of T,
including a corner with zero coefficient, remains allowed.

### 2.2. A second uniform consequence from the actual successor center

Put

    d=sqrt(R^2-1/4)-1.

An arbitrary contained unit with center c and own axes e,f has
farthest squared corner norm

    |c|^2+1/2+|c.e|+|c.f|
       >=|c|^2+|c|+1/2.

Consequently |c|<=d+1/2. Its n width is at least one, so

    min_(z in C) n.z
      =c_C.n-w_C(n)/2<=|c_C|-1/2<=d.

Using (5) and w_i>=1 proves

    n.P+W_*<=d,
    n.P<=d-m.                                      (9)

For one actual unloaded true-two T this gives n.P<=d-1.
No boundary contact or force equation at C is used in (7)--(9).
The inequality permits arbitrary original means and all frames of
C. It is not a claim that zero load alone makes T circle-clear.

## 3. Entire local perpendicular domain and theorem

Put Q=1105/256 and assume

    2<R<=sqrt(Q).                                    (10)

Retain distinct actual contained U,V,W,T, their original compatible
physical certificate and all original equations. Assume:

* U is unloaded true degree three with its entire positive
  neighborhood exactly V,W,T;
* V is positively loaded true degree two with its entire positive
  neighborhood exactly U,W;
* W is physically boundary, at arbitrary true degree, circle load
  and other forces;
* the original U-to-V and U-to-W normals are perpendicular own
  side axes of U;
* T is genuinely unloaded true degree two, with original other
  neighbor C, an actual contained unit of arbitrary degree/load;
* the certificate retains its strict physical vertex/vertex
  normal convention and already simultaneous fixed-tip selection.

**Theorem B.** If W is parallel to U, this entire actual domain
is impossible, with V arbitrary frame and physical circle mask,
every original VW owner and all original shared means retained.

**Theorem C.** Without any W-frame restriction, suppose V is
parallel to U and has a unique physical circle corner. In the
normalized actual chart of Section 5 below, the entire y<=2
feature is impossible.

**Additional complete local exits.** For V nonparallel to U,
the V-owned VW domain, the unique-opposite W-owned VW domain,
and the free VW domain are impossible at the same original
true-T2 scope for arbitrary W frame. The quarter-disk cases
use (9), so their new local contradiction does not require an
eight-extra-unit argument. Their full accepted local inputs
remain unchanged.

None of these statements requires T or C to be boundary. No
equation at W or C is shortened. The actual C2 or W3 in an
original caller keeps all its original forces, although the local
theorem permits higher degrees there.

## 4. Common full-U3 entry and exact quantitative bounds

Rotate or reflect the whole original configuration about O so
that n_UV=North and n_UW=East, without exchanging V and W.
Write

    U=[L-1,L] x [H-1,H].

With original UV,UW,UT magnitudes mu,omega,tau>0, full U force
gives

    mu*North+omega*East+tau*n=0,
    n=n_UT=(-alpha,-beta), alpha,beta>0,
    alpha^2+beta^2=1.

Its actual UT support is the single Southwest U vertex

    P_T=(L-1,H-1),
    h=n.P_T=alpha*(1-L)+beta*(1-H).                 (11)

No original U force or chord term has been omitted. The actual
T--C path has precisely the hypotheses of Section 2, so throughout
all cases we may use both

    |P_T+2n|^2<=R^2,
    h<=d-1.                                        (12)

The radius gives the exact common bounds

    187/200<d<61/60,
    R<21/10,
    R^2-9/4<=529/256=(23/16)^2.                   (13)

For the first lower comparison use R>2 and
15/4-(387/200)^2=231/40000>0. The upper bound for d
uses (121/60)^2-(Q-1/4)=31/57600>0. The upper radius
comparison has reserve (21/10)^2-Q=599/6400>0.

At R>2, a physical boundary unit has either exactly one circle
corner or exactly two adjacent circle corners: its farthest
own-coordinate endpoints are chosen independently, and two
coordinate ties would put its center at O with radius 1/sqrt(2).
This is a classification of physical circle corners, retaining
every individual zero circle coefficient.

## 5. Parallel unique-circle V: the actual successor point closes the entire low-height domain

The complete arbitrary-U/W-degree local theorem of frozen
592b6968, Sections 2--7, applies before any T premise. It gives
the entire all-W-frame/owner/mean chart

    V=[-x,1-x] x [y-1,y],
    Z_V=(-x,y), x^2+y^2=R^2,
    U=[-a,1-a] x [y-2,y-1],
    1/2<x<1, sqrt(3)<y<121/60,
    a=x+kappa<1, 0<=kappa<1/5.                     (14)

These are actual supports of the unchanged U and V. The local
input includes the initial W vertex endpoints, shared W frames,
both original W physical masks and all original means; its later
loaded-T capacity theorem is not used. The original UV contact
has positive length by the strict point-normal convention.

Thus P_T=(-a,y-2). The actual point inequality (12) and (14)
would require the following exact difference to be nonpositive:

    |P_T+2n|^2-R^2
      =(a^2-x^2)+4*(1+beta)*(2-y)+4*alpha*a.        (15)

If y<=2, the first two terms are nonnegative because a>=x>0,
whereas the last is strictly positive. This contradicts (12),
including y=2 and a=x. This proves the complete Theorem C for
every actual W frame, owner, mask and original mean.

Every survivor of this parallel unique-V feature must therefore
satisfy

    2<y<121/60,
    1/2<x<9/16,                                   (16)

because x^2=R^2-y^2<Q-4=81/256. This is a derived remaining
domain, not a whole-feature closure for nonparallel W. It will
now be excluded completely for parallel W using its full means.

## 6. The entire parallel unique-V, parallel-W domain

For W parallel to U, the complete local shared-frame calculation
in 592b6968, Section 3, gives kappa=0 and hence a=x. Its entire
actual chart is

    L=1-x, H=y-1,
    U=[-x,1-x] x [y-2,y-1],
    V=[-x,1-x] x [y-1,y],
    W=[1-x,2-x] x [y-1-sigma,y-sigma],
    0<sigma<1,
    x=1-sigma*y/2+sigma^2/4.                        (17)

The initial sigma=1 vertex contact is not omitted: the whole
local source proves it impossible using the actual circle equality.
The parallel W's actual circle corner is (2-x,y-sigma), derived
from its full physical mask. Its original VW normal is East.

Keep all original means:

    P_UV=(p,y-1),
    M_VW=(1-x,y-1+t), 0<=t<=1-sigma,
    M_UW=(1-x,y-1-delta_0), 0<=delta_0<=sigma.       (18)

The full original V resultant is a positive multiple of its
unique physical corner: F_V=Lambda*(-x,y), Lambda>0. Its
unchanged pair force equation F_V=mu*North-nu*East gives

    mu=Lambda*y, nu=Lambda*x.

Its full torque about O, with the exact original means (18), is

    mu*p+nu*(y-1+t)=0.

Therefore, with A=p+x and B=1-delta_0,

    A=x*(1-t)/y>=x*sigma/y>0,
    0<B<=1.                                        (19)

The complete U torque about P_T=(-x,y-2) is mu*A=omega*B.
Together with full force, it gives

    n=-(A,B)/sqrt(A^2+B^2).                         (20)

No mean in (18) has been chosen, and every closed t and delta_0
endpoint is retained. In particular B is strictly positive because
delta_0<=sigma<1.

Section 5 already excludes y<=2. In the remaining (16), equation
(17) gives

    sigma>2*(1-x)/y
          >(7/8)*(60/121)=105/242>2/5.             (21)

The first sign is strict because sigma^2/4>0. Hence (19),
x>1/2 and y<21/10 imply

    A>2/21,
    alpha=A/sqrt(A^2+B^2)
          >=A/sqrt(A^2+1)>2/sqrt(445)>1/12.         (22)

The last strict comparison has squared numerator reserve
4*144-445=131>0. Since beta<1, y-2<1/60 and a=x,
the complete difference (15) is strictly greater than

    4*[1/24-2/60]=1/30>0.                          (23)

This contradicts the actual C point in (12). Thus every original
parallel unique-V, parallel-W mean and mask is excluded. The
proof uses neither W force nor T/C boundary status or concurrence.

## 7. The entire parallel physical-two V, parallel-W domain

The whole physical-two local theorem 1458e073 applies to actual
V2, physical-boundary W and the two original perpendicular U axes.
Its complete parallel-frame mask cover first excludes radial-West
V by actual U containment and leaves exactly

    V=[-1/2,1/2] x [d,d+1],
    H=d,
    U=[L-1,L] x [d-1,d].

Both physical V circle corners and the entire original nonnegative
coefficient interval remain. Since W is parallel to U, its complete
return cover gives L=1/2. Thus

    U=[-1/2,1/2] x [d-1,d],
    P_T=(-1/2,d-1).                                (24)

### 7.1. Every parallel W contact and its complete actual circle mask

The retained East UW normal between parallel U,W has positive
physical shared length by the strict point convention. Write

    W=[1/2,3/2] x [q,q+1].

Positive UW length implies d-2<q<d. The actual V--W contact
requires q+1>=d. If equality holds, W is
[1/2,3/2] x [d-1,d]. Its maximum squared corner norm is
9/4+d^2, strictly below R^2=(d+1)^2+1/4 by 2d-1>0.
This contradicts physical boundary W. Thus

    d-1<q<d,
    Y:=q+1 in (d,d+1).                              (25)

The two actual W center coordinates are positive, because its
horizontal coordinate is one and q+1/2>d-1/2>0. Its full
physical circle mask is therefore its upper-right corner, and

    Z_W=(3/2,Y),
    Y=sqrt(R^2-9/4)<=23/16.                        (26)

The actual VW intersection is now a positive-length vertical
segment, whose original normal is East. Its whole original mean
height m lies in [d,Y]. The original UV mean is (p,d) with
-1/2<=p<=1/2. The original UW mean is (1/2,z), with q<=z<=d.
None is replaced by a segment endpoint.

### 7.2. Full physical-two coefficients force a uniform original U3 direction

Let mu,nu>0 be the original UV,VW magnitudes. The full original
V outward resultant has the form

    F_V=Lambda*(xi,d+1), Lambda>0,
    -1/2<=xi<=1/2,
    F_V=mu*North-nu*East.

Thus mu=Lambda*(d+1), -nu=Lambda*xi, and

    nu/mu<=1/[2*(d+1)].                            (27)

Both individual zero-weight endpoints are included in this bound.
The whole original V torque gives mu*p+nu*m=0. Hence

    p=-(nu/mu)*m>=-Y/[2*(d+1)].                   (28)

The entire U force already makes n strictly Southwest. In the
chart (24), h=alpha/2-beta*(d-1). If d<=1 this is strictly
positive, whereas (12) says h<=d-1<=0. That entire interval
is therefore impossible without any stronger coefficient estimate.

In the only remaining interval d>1, equations (26),(28) give

    p>-23/64,
    A:=p+1/2>9/64.

Set B=z-(d-1). Equation (25) and the complete z interval give
0<B<=1. Full original U torque about P_T is mu*A=omega*B,
so again n=-(A,B)/sqrt(A^2+B^2). Therefore

    alpha>9/sqrt(4177)>1/8.                        (29)

The exact squared reserve is 81*64-4177=1007>0. Put
epsilon=d-1 in (0,1/60). It follows that

    h=alpha/2-beta*epsilon
       >1/16-epsilon>11/240>1/60>epsilon.          (30)

This contradicts h<=d-1=epsilon in (12). The strict middle
reserve is 11/240-1/60=7/240. Thus all original means,
coefficient endpoints and physical masks in this branch exit.

## 8. Nonparallel V: the complete owner and physical-mask entry

Now V is nonparallel to U. Its actual UV intersection is its
unique bottom vertex

    P=(L-p,H),
    e_1=(c,s), e_2=(-s,c),
    c,s>0, c^2+s^2=1,
    V=P+[0,1]e_1+[0,1]e_2.                         (31)

The full physical degree-two boundary-neighbor common-point
theorem gives P not in W. The force-free perpendicular-neighbor
direction lemma gives the entire closed Southeast cone for the
unchanged V-to-W normal. These inputs require no equation or
degree restriction at W. They retain every original U-side mean.

First assign every V-owned VW normal to the complete local
8f564d69 theorem, even if W also owns it or the contact has
positive shared length. Its whole original mean, including
endpoints, remains. The local conclusion is

    closed D_(1/4) contained in int U.

It follows that h_U(n)>1/4 for every unit n: the point n/4
is an interior point of U, so it can be advanced a positive
amount in direction n while staying in U. But (12) gives
h_U(n)<=d-1<1/60. This contradicts the complete local input.
This exit works for arbitrary W frame and every physical V mask.

If the original VW normal is owned by neither unit, its contact
is a physical singleton at strict vertices. Its e_2 component
is negative; its e_1 component cannot be zero and cannot be
negative, since the latter would expose P itself in V. Thus
its actual fixed singleton point is M=P+e_1, different from P.
For physical-unique V the already common fixed-tip selection
applies at exactly these two distinct physical singletons and
excludes the free normal. For physical-two V the complete e8be6a0d
geometry excludes it without any selector. No physical-two mask
is identified with the support of only its positive coefficients.
The whole free-return theorem and its separate full review retain
arbitrary U/W degrees and have no terminal premise.

The remaining original VW normal is W-owned and not V-owned.
Its V point is again M=P+e_1. Neither P nor M can be a physical
circle point, since each belongs to two interior-disjoint
contained units. Thus a unique physical V circle corner is
either the adjacent P+e_2 or the opposite P+e_1+e_2.

The complete opposite-corner local theorem 94611e1b gives the
same closed quarter disk inside int U for every W frame,
including aligned W and its entire original mean. The preceding
support contradiction excludes that whole feature too.

Consequently, for the proof of Theorem B the only remaining
nonparallel-V branches have a W-owned return and either the
physical-two V mask or the unique-adjacent V mask. Both are
treated next at W parallel to U, with no owner or mean omitted.

## 9. Every remaining aligned-W chart keeps the full original UW mean

In the W-owned charts of the complete 1458e073 and 66ac183e
local theorems, write

    f=(C_0,S), g=(S,-C_0),
    C_0>=0, S>0, C_0^2+S^2=1,
    W=M+[-b_W,1-b_W]f+[0,1]g,
    p=c-b_W*C_0,
    delta=b_W*S-s>=0.

The endpoint S=0 is excluded by the actual V support sign,
not by a frame choice. Because W is parallel to U in the
present theorem, its exact remaining frame is

    C_0=0, S=1, f=North, g=East,
    p=c,
    delta=b_W-s>=0.                                (32)

The original UW mean is not replaced by W's lower-left
corner. Its complete height interval is

    M_UW=(L,H-delta_0),
    0<=delta_0<=delta.

Both full local inputs prove

    0<b_W<2/5,
    0<s<2/5, c>9/10,
    0<L<1/2,
    A:=1-p=1-c in (0,1/10),
    B:=1-delta_0>3/5,
    B<=1.                                          (33)

The enlarged closed delta_0 interval includes every original
shared mean and both endpoints. It is not fixed to delta.

Full U torque about P_T=(L-1,H-1) gives

    mu*A=omega*B,
    n=-(A,B)/sqrt(A^2+B^2).

In particular its original downward component satisfies

    beta=B/sqrt(A^2+B^2)>6/sqrt(37)>1/2.            (34)

The first bound follows from A/B<1/6. All divisions are
by strictly positive actual magnitudes or lengths.

The two actual V masks have different exact heights, but
both give

    H<d-s/2.                                       (35)

For the physical-two case the full local chart is

    P=-e_1/2+d*e_2,
    H=d*c-s/2<d-s/2.

For the unique-adjacent case, in the actual V own frame,

    Z_V=(-x,y), P=(-x,y-1),
    x>1/2, x^2+y^2=R^2,
    H=c*(y-1)-s*x.

Here y<sqrt(R^2-1/4)=d+1, so (35) again follows, with
strictness at every stated endpoint.

If d<=1, (35) gives H<1 and (33) gives L<1. The full
h in (11) is strictly positive, contradicting (12).
Thus any survivor must have d>1 and epsilon=d-1 in
(0,1/60). Because alpha*(1-L)>0, equations (11)--(12)
and (34) give

    beta*(1-H)<h<=epsilon,
    H>1-epsilon/beta>1-2epsilon.

Combining with (35),

    1-2epsilon<H<1+epsilon-s/2,
    s<6epsilon<1/10.                               (36)

These inequalities are a consequence of the full original
U3, all original mean endpoints and the actual successor C.
They do not require T to be boundary or radial and do not
invoke a loaded-T capacity theorem.

## 10. Both complete nonparallel physical V masks contradict the small tilt

### 10.1. Physical-two V, with the full weight interval

In the whole radial local theorem 1458e073, the unchanged
force and torque imply

    gamma*[2*(d+1)*alpha_V+kappa_V]>=1,

where gamma=c*C_0+s*S, alpha_V=s/S and kappa_V=c/S.
This is its complete physical-two necessary inequality,
derived from the entire original coefficient interval
-1/2<=xi<=1/2. It assumes neither equal weights nor an
inside-square physical-two concurrence.

At the actual aligned frame (32), gamma=s,
alpha_V=s and kappa_V=c. Thus

    s*[2*(d+1)*s+c]>=1.                             (37)

But (13),(36) and c<=1 give the strict opposite bound

    s*[2*(d+1)*s+c]
       <(1/10)*[(121/30)*(1/10)+1]
       =421/3000<1.                                (38)

This contradiction covers both original physical corners
and every individual zero weight.

### 10.2. Unique-adjacent V, with its actual unique circle point

The whole local theorem 66ac183e retains the genuine
loaded V2 and its real physical-boundary neighbor W.
Its original unique-mask force and proper concurrency
give, in the actual V frame,

    x=K*gamma*alpha_V,
    y=K*(1-gamma*kappa_V), K>1,
    1/2<x<3/4,
    0<y<121/60.

At the same exact aligned frame (32),

    x/y=s^2/(1-s*c).                                (39)

The denominator is positive; already sc<=1/2. The
actual unique corner and radius bounds give

    x/y>30/121.

In contrast (36) and c<=1 give

    x/y<(1/100)/(9/10)=1/90,
    30/121-1/90=2579/10890>0.                       (40)

This is impossible. The properness input is used only
at the actual loaded V2 with real boundary neighbor W.
No such premise is invented at T or C.

Sections 5--10 cover every V frame, physical mask,
original VW owner and full original mean while W is
parallel to U. This proves Theorem B at its entire
printed arbitrary-W/C-degree local scope.

## 11. Literal complete low-load features and every reflected image

Retain all nine actual units and the original D02 positive graph

    01,12,23,34,45,50,02.

The true positive degrees at 0,...,5 are (3,2,3,2,2,2).
The two original load sets and actual substitutions are

    L014:  {0,1,4},
    L0145: {0,1,4,5},
    U=2, V=1, W=0, T=3, C=4.

The entire neighborhoods remain

    U:{1,0,3}, V:{2,0}, W:{1,2,5},
    T:{2,4}, C:{3,5}, 5:{4,0}.

In both rows U is unloaded true3, V is loaded true2,
W is loaded true3 and therefore physically boundary,
and T is unloaded true2 with its actual other neighbor
C4. The full W3 force toward5 and the full loaded C2
force toward5 remain. Body5 is unloaded in L014 and
loaded in L0145. The actual 2--3--4 path is retained,
with no false 2--4 contact or transmission through W3.

The complete same-nine lower theorem excludes R<=2
over the original closed window

    79/40<=R<=sqrt(1105)/16.

It is applied to all nine original units before any
local theorem. Every displayed upper-radius reserve
is strict at R=sqrt(1105)/16, so that endpoint remains.

Assume the original normals n_21,n_20 are perpendicular
own axes of U. If the actual W0 frame is parallel to
U2, all premises of Theorem B hold literally, with
every original V1 mask, VW owner and mean. The whole
W-parallel perpendicular feature is therefore impossible
in both original rows.

For arbitrary W0 frame, if V1 is parallel and physically
unique with actual normalized circle height y<=2,
Theorem C excludes that whole feature. The additional
local owner/mask exits of Section 8 likewise apply at
their complete stated scopes, independent of the other
path-body load. These are whole feature conclusions,
not a claimed whole-row owner cover.

The reflection i -> 2-i modulo6 sends the complete
actual data to U0,V1,W2,T5,C4 and the real path0--5--4.
It sends the two load sets to {1,2,4} and {1,2,3,4},
respectively. Every force, normal, coefficient, application
and mean is reflected together. These are symmetry images
of the same original rows and create no new IDs.

Both original exterior regions and the full central
region remain with all three arbitrary completing units.
The local contradictions need no allocation of those
units. Other W frames and the remaining V masks/owners
outside the complete printed features remain separate
proof obligations. No whole original row, parent, coarse
gate or count is changed by this source.

## 12. Exact frozen inputs and independence

The existing support-point fact is rederived in Section 1, with its
exact earlier provenance pinned below. The new coupled successor-point
theorem is proved in Section 2. Sections 6--7 and
9--10 supply the new complete parallel-W force/height
contradictions; Section 5 supplies the all-W low-height
unique-V exit. The complete old local owner/mask inputs
are invoked only before their later loaded-path or
pocket-capacity consequences.

| Exact complete source or review | SHA-256 | Literal operative scope |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original supports, full true-degree equations, strict physical point convention and all mean endpoints |
| LOADED_TWO_APPLICATION_FULL_STAR_BOUNDARY_FREE_CONCURRENCE_DICHOTOMY.md | 3808b2b767a9e15c7270b50c4fbbb434ae0d69fe42c567d4da01f7d167f7fa78 | Existing Section 3 actual inward support-point translation, at its full side/vertex/mean scope, credited there to root; rederived here without importing its loaded-star theorem |
| PERPENDICULAR_HUB_TWO_CIRCLE_TIP_ALL_OWNER_NEAR_ORIGIN.md | 1458e073a4b9174e3b239115594383e740dd0d9af090b8b9c194c383944ea8b8 | Complete arbitrary-U/W-degree physical-two frame/owner/mask chart and full original-weight inequality |
| REVIEW_PERPENDICULAR_TWO_CIRCLE_ALL_OWNER_NEAR_ORIGIN_REVIEW_RESUME_2026_10_28.md | 0c63f30732a3ca0f165a41a5234cc865092d47dfff4c1acafdbe5d46fb4923ff | Separate full independent audit of that entire local theorem |
| PERPENDICULAR_PARALLEL_UNIQUE_TIP_NEAR_ORIGIN_CHAIN_CAPACITY_AND_FOUR_LOAD_FEATURES.md | 592b6968e21d5817f89543bece01529aae210ad203939501e8cbb643dedbf6f9 | Only its complete arbitrary-U/W-degree local Sections 2--7, all W frames/masks/means; no boundary-T or capacity premise |
| REVIEW_PERPENDICULAR_PARALLEL_UNIQUE_NEAR_ORIGIN_CHAIN_BOTH_FOUR_LOADS_REVIEW_RESUME_2026_10_28.md | 1084c651185a63202b13aee185703917c836586def4a820ff2be1fcb96f8f107 | Complete separate review, including exact local scope and beta/sigma/mean endpoints |
| EQUAL_CIRCLE_HEIGHT_COMPARISON_AND_PERPENDICULAR_ADJACENT_TIP_NEAR_ORIGIN.md | 66ac183e666a008390f27c650b5d4107d7ac920eb9b8a94049d8da727053abcf | Entire arbitrary-U/W-degree adjacent-mask local chart, original V2 ratios and full aligned-W mean interval |
| REVIEW_EQUAL_CIRCLE_HEIGHT_PERPENDICULAR_ADJACENT_NEAR_ORIGIN_REVIEW_RESUME_2026_10_28.md | 3217165ee08c63c06181597dec87db51d478f8e711f8cb71e3cb778333f68e56 | Complete independent local and scalar review, distinct from the author's discovery checks |
| PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_OWNED_RETURN_QUARTER_DISK_EXCLUSION.md | 8f564d6904cc8744175ec1664a88cbf84f51d74d146d4536a647662aac8a1487 | Entire local quarter-disk conclusion, arbitrary U/W degrees, all original V-owned means/masks |
| REVIEW_PERPENDICULAR_HUB_TIP_OWNED_RETURN_QUARTER_DISK_CYCLES_2026_10_28.md | 7a269028eb8b6dd0e7898f5b79fff5243eaf0ed4110a615ae58e5c2b3a2f9eda | Full independent local audit |
| PERPENDICULAR_HUB_W_OWNED_OPPOSITE_CIRCLE_TIP_QUARTER_DISK_EXCLUSION.md | 94611e1ba90d9b669d754b6ba7e8bb589afcb4a419e3c4c5d96bbffa7c5e4fe6 | Entire local opposite-mask quarter disk, including aligned W and all original side endpoints |
| REVIEW_PERPENDICULAR_W_OWNED_OPPOSITE_QUARTER_DISK_CYCLES_2026_10_28.md | a0eef290d1fff15f501099abfd296f8fd0e64ee981a09ca7be99f481a9f03a4e | Full independent opposite-mask local audit |
| PERPENDICULAR_HUB_AXES_NONPARALLEL_TIP_NO_FREE_RETURN.md | e8be6a0daca1cbd50000c7167139ebb546e4dec96bdfdb889c65d2c0e04db0ef | Entire free-return theorem at its literal unique-singleton or full physical-two scope |
| REVIEW_PERPENDICULAR_NONPARALLEL_TIP_NO_FREE_RETURN_PENTAGON_2026_10_28.md | 0615b90201a5e9698517cec8765021effc0c38b1d322572834e640c6fdcda4d1 | Older full independent free-return audit; its author does not thereby independently review the present extension |
| LOADED_TWO_FORCE_BOUNDARY_NEIGHBOR_COMMON_POINT_EXCLUSION.md | 5a95c3255a634f603a47c8311971902f2b8b699e4ebf2d076b21b01fddf941ba | Complete actual P not in W at the true loaded V2 with real physical-boundary W |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Only the already common unique-V selector at the proved two distinct physical singleton points |
| BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md | 3cd327d293d58daf2dcb8eb828dbee00efbc728171e8d17de60c3c9bc071f281 | Only Section 2's whole force-free neighbor-normal cone; no two-tip force equation at W |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Exact original D02 graph/load/degree cover and reflected images |
| LOWER_WINDOW_FROM_NINE_ANALYTIC_MEASURE.md | 3b3f40af8f62beee8a55b8d4c8d26398097362d88e91d32116885b4ceea96e90 | Full same-nine strict R>2 entry; no smaller-component inference |

The complete operative local sources and their separate complete
reviews have been read in this continuation, with the older full
physical/analytic review boundaries retained. The free and both
quarter-disk sources and all three complete paired records were
freshly read again for this extension. No new recursive audit of
the whole analytic measure chain is claimed. Every exact pin is
checked before freezing.

The existing actual support-point translation is credited to the
root contribution identified in frozen 3808b2b7. The author supplied
the new unchanged-transmitter-chain application and parallel-W
arguments. No discovery contribution from the eventual independent
reviewer is claimed or requested. Earlier authorship of the local
near-origin sources and of the old free-return review is disclosed;
their separate records do not provide an independent review of this
new source. The complete extension requires its own full audit.

Exact arithmetic checks verify the displayed radius, force-ratio
and strict contradiction reserves, the original degree list and
the two reflected load images. They check transcriptions of full
continuous arguments. No orientation sample, pose mesh, numerical
optimizer or computational exclusion packet is a proof premise.

All original actual squares, true degrees, positive edges, forces,
normals, physical corners, individual zero coefficients and means
remain. No positive chord is deleted and no false boundary neighbor
is introduced. No source or review is edited after freezing, and
no Lean/Lake operation, build, CI/workflow, commit, remote mutation,
metadata, original flag or count change is made.
