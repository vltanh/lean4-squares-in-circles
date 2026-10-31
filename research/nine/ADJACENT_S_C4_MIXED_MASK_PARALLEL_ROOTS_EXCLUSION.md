# A mixed boundary mask cannot have both adjacent S roots owning their common axis

Date: October 27, 2026.

**Status: complete original-domain hand proof, submitted for full root and
separate independent review.** This excludes the entire high mixed physical
mask with both roots owning the actual AB normal. It does not claim the
remaining one-owner mixed interface or the whole LCD.SS gate.

Keep the same nine actual squares and the full selected component

    AB,BC,CD,DA,AL,BM,
    A3,B3,C2,D2,L1,M1.

The genuine leaves L,M are S, the roots A,B are physically clear, and C,D
have positive total circle load. Suppose C has two physical circle corners,
D has exactly one, and both A,B own the original AB normal. Work in

    d=1+epsilon=sqrt(R^2-1/4)-1,
    0<epsilon<1/60,       R^2<=Q_*=1105/256.

In particular R<25/12 and d<61/60. All actual means, original owners,
individual zero C weights and three completion squares remain present.

The geometric idea is to retain C as the actual radial square. Its two
possible contact features put the other root's genuine application in a
short finite list. In the last feature, the genuine D2 concurrence excludes
one possible circle corner of D; the other forces its CD contact onto a
side which the original C corner cannot reach. No D2 equation is placed
at either root.

## 1. The actual common frame and two elementary consequences

Use the full accepted reduction
RADIAL_BOUNDARY_UNIT_ADJACENT_GENUINE_ROOT_OWNER_REDUCTION.md.
Because B owns AB, its aligned-leaf alternative is impossible. In B's
actual own frame we have

    B=[U-1,U] times [V-1,V],
    U^2+V^2=d^2,       U>=1-epsilon,       0<V<4/15.

Write

    delta=U-1,       a=2-U=1-delta,
    59/60<a<61/60,       |delta|<=epsilon.

The actual BC normal is South and its actual point is

    P_BC=(t,V-1),       delta<t<U.

If alpha>0 scales the full genuine M force to alpha*(U,V), the full
B3 equations give

    |F_BA|=alpha*U,       |F_BC|=alpha*V,
    P_AB=(delta,y),       y=V*t/U in (0,V).                 (1)

Both original roots own AB, so A's actual x interval is [-a,delta].
Its vertical unit interval contains y. No mean in (1) is replaced by
an endpoint.

Use C's radial frame e,j, expressed in this B frame as

    e=(s,-c),       j=(-c,-s),
    c,s>0,       c^2+s^2=1,
    1-V=d*c-s/2,       t=d*s+c/2.                          (2)

The change of frame may reverse orientation; every zero moment equation
is unchanged. The actual C square is

    C=[d,d+1]e+[-1/2,1/2]j.

Its inner upper corner, denoted Q_C, is

    Q_C=(d*s-c/2, -d*c-s/2)
       =(t-c,V-1-s).                                     (3)

The complete original CD cover is precisely:

* a strict Northwest C normal at Q_C; or
* C-owned North, at Q_C+z*e with 0<=z<=1, retaining the actual z.

In both cases the original D-to-C normal g has strictly positive B-frame
x component. The second case has g=(c,s). All C points have y<=V-1.

We will use the following crude bounds throughout:

    s<5/12,       c>9/10,       V<s,
    s<2(V+epsilon),       Q_C,x<-19/720<-epsilon.          (4)

Indeed 1-V>11/15. If s>=5/12, then c<=sqrt(119)/12<11/12 and
d*c-s/2<521/720<11/15. This proves the first bound and hence c>9/10.
Equation (2) gives V<1-c+s/2<s, since 1-c=s^2/(1+c)<s/2.
It also gives V>-epsilon+s/2. Finally
d*s-c/2<(61/60)(5/12)-9/20=-19/720.

Thus every possible CD point has height strictly below -1:

    Q_C,y=V-1-s<-1,
    (Q_C+z*e)_y=V-1-s-z*c<-1.                            (5)

Two general facts will be used with their full scopes. First, a contained
unit beyond minimum support d in a unit direction is the unique radial S
square in that direction. This is the degree-free sharp equality statement
of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1. Second, the genuine
D2 lemma TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies because
D's other neighbor C is boundary: its two lines have a positive radial
concurrence q_D, and q_D lies behind each outward application. Because D
has one physical circle corner Z_D, it also gives

    q_D=lambda*Z_D in D,       0<lambda<=1.               (6)

We use (6) only for this unique physical mask.

## 2. The complete A-leaf feature cover

A's genuine radial application has norm d. Its possible actual support
features, given the interval [-a,delta] and the point y>0, are:

* an owned West leaf, with a=d;
* an owned North leaf, with vertical interval [epsilon,d];
* a strict upper-right leaf (delta,k), with delta>0 and k>1;
* a strict lower-left leaf (-a,-w), with w>0;
* a strict upper-left leaf (-a,k), with k>0.

This is exhaustive. An owned East leaf would require delta=d. An owned
South leaf gives top height -epsilon<0. A strict lower-right leaf has
depth sqrt(d^2-delta^2)>1 and likewise puts A's top below zero.
Zero vertex coordinates belong to the stated owned-axis cases.

### 2.1. A lower-left leaf gives two D points too far apart

Here A's top is 1-w, with a^2+w^2=d^2. The full A3 equation makes
the AD normal's vertical component positive, so its actual application
has height 1-w. D also contains its actual CD point, whose height is
at most V-1. But

    w^2+V^2=2(d^2-1-delta^2)<121/1800,
    w+V<11/30.

The two actual D points have vertical gap greater than 49/30>sqrt(2),
contradicting the diameter of a unit square.

### 2.2. North and upper-right leaves contradict the full circle sum

Both alternatives require U>=1, so V<11/60. For an owned North leaf,
let ell>0 be its full vertical force. The actual AD feature is Southwest
at (-a,epsilon). Keeping the full A3 moment and (1) gives

    ell/alpha=(V*t-U*epsilon)/a < (60/59)V*t.             (7)

For a strict upper-right leaf, write its full force as beta*(delta,k),
with k>1. Its actual AD feature is Southwest at (-a,k-1), and

    (beta/alpha)(k-delta)=V*t-U*(k-1),
    beta*k/alpha < (60/59)V*t.                          (8)

The horizontal leaf component in (8) is nonnegative.

Consider the actual lower outer circle corner of C,

    z_C=(t+s,V-1-c).

Its positive horizontal component is t+s and its negative vertical
component has absolute value below two. The full M force is
alpha*(U,V). Thus (7) or (8) gives

    z_C dot (F_L+F_M)/alpha
      > t*(1-120*V/59)+s-2V
      > (3/5)t+s-2V
      > 27/100-(7/30)s
      > 311/1800>0.                                    (9)

For the penultimate line use t>s+9/20 and
V<1-c+s/2<s^2+s/2<(11/12)s.

On the other hand every actual C circle corner has positive dot product
with every actual circle corner of C and D: within C this is immediate,
and across the physically touching pair C,D it is the full acute-contact
theorem. Therefore positive total C,D loads imply
z_C dot(F_C+F_D)>0, including zero individual C weights. The unchanged
whole component equation is

    F_L+F_M+F_C+F_D=0.

It contradicts (9).

### 2.3. An owned West leaf contradicts the two actual D2 rays

Now a=d, delta=-epsilon, and A's vertical unit interval contains zero.
Its full equation makes AD horizontal. West would put D beyond support
d in the actual L direction, hence make D the same radial S unit as L
by the sharp equality statement in Section 1. The AD edge is positive,
so its only alternative is East.

The actual AD point is (delta,y_D), with y_D>=-1, and all of D lies
in x>=delta. By (4), Q_C cannot be in D. Thus CD is C-owned North,
whose actual point has height below -1 by (5). The genuine D2 rays give

    q_D=(delta,y_D)+rho*(1,0),       rho>=0,
    q_D=Q_CD+sigma*j,               sigma>=0.

The first has height at least -1, and the second has height below -1
because j_y=-s<0. This is impossible. No D orientation is assumed.

It remains only to exclude the strict upper-left A leaf.

## 3. The remaining true A3 star

Write its actual square and leaf as

    A=[-a,delta] times [k-1,k],
    d*e_L=(-a,k),       a^2+k^2=d^2,       k>0.

Then

    k^2+V^2=2(d^2-1-delta^2)<121/1800,
    k+V<11/30,       k<4/15,
    0<y=V*t/U<=k.                                      (10)

Scale the full actual A leaf force as beta*(-a,k), beta>0, and put
p0=beta/alpha. The full AD vector divided by alpha is

    (p0*a-U,-p0*k).                                    (11)

Its vertical component is strictly negative. There are precisely three
original features: Southwest at (-a,k-1), Southeast at (delta,k-1),
or the South side with its original mean.

## 4. Southwest is excluded by one actual inward unit segment

Suppose the first component in (11) is negative. Put

    X=U-p0*a>0,       Y=p0*k>0,       w=1-k.

The actual AD point is Q=(-a,-w). Its exact full moment gives

    X=U*k-V*t,
    p0*a=U(1-k)+V*t,
    r:=X/Y=a*X/[k(U-X)]<a/w.                            (12)

The original unit normal into D is
n=(-r,-1)/sqrt(1+r^2). At any unit-square minimum support point Q,
the inward unit segment [Q,Q+n] belongs to that same square: at a side
it is the perpendicular unit segment, and at a vertex the inward unit
normal has two coefficients in [0,1] in the actual inward orthogonal
frame. Hence Q+n is an actual point of D.

Its squared norm is

    |Q+n|^2=d^2+2-2k+2 S,
    S=(a*r+w)/sqrt(1+r^2).                              (13)

On 0<=r<a/w, S increases with r. It suffices to prove

    S>d-3/8+k,                                         (14)

because R^2=d^2+2d+5/4.

If k<=43/240, then S>=w=1-k>d-3/8+k directly from d<61/60.

Suppose k>43/240. Equation (10) gives V<3/16, since

    (3/16)^2-[121/1800-(43/240)^2]=1/28800.

Also

    t^2/U^2=1+(2V-3/4)/U^2
       <1-1350/3721<16/25.

Consequently y=V*t/U<3/20, and (12) gives

    r=a*(k-y)/[k(1-k+y)]>a*(k-3/20)/k.                  (15)

For 43/240<k<=1/4, (15) implies r>4/25 and w>=3/4.
Monotonicity in (13) therefore gives

    S>1361/(60*sqrt(641))
      >1361/1524>107/120>d-3/8+k.

Here sqrt(641)<127/5 and the last rational comparison has numerator
reserve 252. For k>1/4, (15) gives r>59/150>3/8, while w>11/15.
Hence

    S>529/(60*sqrt(73))>1>109/120>d-3/8+k.

Thus (14) holds in every actual Southwest feature, and Q+n lies
outside the original containing circle.

## 5. Southeast is excluded by the original proper rays

Now the actual AD point is Q=(delta,k-1), with an incoming D normal
of strictly positive horizontal component. Its C-tangent projection is

    Q dot j=-c*delta+s(1-k)
       <=epsilon+s<13/30<1/2.                          (16)

If CD were C-owned North, all of D would lie in the half-plane
j dot x>=1/2, contrary to (16). Therefore CD uses Q_C.

The unchanged D2 proper rays now give, at AD and CD respectively,

    q_D,x>=delta,
    q_D,x<=Q_C,x<-epsilon<=delta.

This contradiction excludes Southeast, with no D-owner hypothesis.

## 6. The South mean and a short original-distance bound

Only the actual A-owned South force remains. Its full force and torque
give

    p0=U/a,
    |F_AD|=alpha*U*k/a,
    P_AD=(-X,k-1),       X=a*V*t/(U*k),       0<X<=a.      (17)

The upper bound in (17) is exactly the fact that the original mean
belongs to the South side; its endpoint X=a is retained.

Here the bounds sharpen to

    s<1/3,       c>14/15.                               (18)

For if s>=1/3, then c<=sqrt(8)/3<17/18, so
V>223/1080 by (2). Also t>47/60 and U<61/60. From the actual
AB-mean inequality k>=V*t/U,

    k^2+V^2>(223/1080)^2*(1+(47/61)^2)
             =121/1800+1568401/2170087200,

contrary to (10). This proves (18).

Let E,F be the horizontal and downward coordinate differences from
the actual South mean to C's inner upper corner:

    Q_C-P_AD=(E,-F),
    E=X+d*s-c/2,       F=k-V+s.

By (4), (10), (17), and (18),

    -1/2<E<61/60+61/180-7/15=8/9,
    0<F<k+V+2epsilon<2/5.

Therefore the actual two points satisfy the strict physical bound

    |Q_C-P_AD|^2<64/81+4/25=1924/2025<1.                (19)

The rest of the proof keeps the complete actual D feature at P_AD.

## 7. D cannot own the South contact axis

If D owns this axis, its actual frame is parallel to A,B, with vertical
interval [k-2,k-1]. The positive radial concurrence (6) has horizontal
coordinate -X<0. Its unique physical circle corner must therefore be
the lower-left corner: the lower corners strictly exceed the corresponding
upper corners, and the unique farther horizontal endpoint has negative
coordinate. Write

    D=[-T,1-T] times [k-2,k-1],       T>1/2,
    Z_D=(-T,k-2).

The original D-to-C normal g has g_x>0. If g_y>0 its actual point
is the upper-right D vertex, of height k-1>-1, contradicting (5).
If g_y<0 its point is the lower-right vertex. Then CD cannot be
C-owned North, and equality with Q_C would give

    k-2=V-1-s,       k=1+V-s>7/12>4/15,

also impossible. Thus g is the actual East own axis of D, CD uses
Q_C, and

    T=1-d*s+c/2.                                      (20)

From c>9/10, d<61/60 and s<2(V+epsilon),

    T>A0-B0*V>0,
    A0=2549/1800,       B0=61/30.                       (21)

The actual circle corner now violates containment. The following identity
makes the full range explicit:

    (A0-B0*V)^2+(2-k)^2-Q_*
       +11*(V^2+k^2-121/1800)
     =(B0^2+11)*(V-A0*B0/(B0^2+11))^2
        +12*(k-1/6)^2+53631019/784569600.               (22)

The added term on the left is negative by (10). Equations (21)--(22)
therefore imply |Z_D|^2>Q_*. Every actual side endpoint is included.

## 8. D's opposite circle corner is impossible at a tilted South port

The remaining actual D contact is its strict uppermost vertex

    P=P_AD=(-X,-w),       w=1-k>11/15,
    D=P+[0,1]f+[0,1]j_D,
    f=(p,-q),       j_D=(-q,-p),
    p,q>0,       p^2+q^2=1.                            (23)

This uses its physical frame, not a selected change of normal. Since

    P dot j_D=X*q+w*p>0,

a farthest corner has j_D coordinate one. Its unique circle corner is
therefore either P+j_D or P+f+j_D. These are the only possibilities.

Suppose it is the opposite corner Z=P+f+j_D. The original AD proper
ray puts q_D on the vertical line through P, below P. By (6),
q_D=lambda Z with 0<lambda<=1. If p>q, the x coordinate of Z
is greater than -X, so no such lambda can give q_D,x=-X.
Consequently p<=q.

Put M=q-p>=0 and N=p+q. Then

    Z=(-X-M,-w-N),
    lambda=X/(X+M),
    lambda*(w+N)>=w,
    X*N>=w*M.

It follows that

    |Z|^2=(X+M)^2+(w+N)^2
      >=(M^2+N^2)*(1+w/N)^2
      =2*(1+w/N)^2
      >=(sqrt(2)+w)^2>R^2.                             (24)

The last inequality follows from sqrt(2)>7/5,
w>11/15 and 32/15>25/12>R. It includes p=q and every
zero proper-distance endpoint.

Thus the unique circle corner is necessarily

    Z_D=P+j_D=(-X-q,-w-p),
    P dot f=-X*p+w*q<-1/2.                             (25)

The strict inequality follows because equality would put both
j_D-side corners on the circle, contrary to the physical unique mask.

## 9. The full D2 force locates CD on its far actual side

Let nu>0 be the original AD magnitude, kappa>0 the original CD
magnitude, and g the original D-to-C unit normal. The full D2 force is

    F_D=nu*(0,-1)-kappa*g.

Its f component is negative by (25), because F_D is a positive
multiple of the actual Z_D. On the other hand (0,-1) dot f=q>0.
Consequently

    g dot f>0.                                        (26)

Every actual supporting point for g on D has f coordinate one in
(23). Thus the original CD mean lies on the entire far-f side,
including its two endpoints, and has distance at least one from P.

If CD uses C's strict inner upper corner Q_C, this contradicts (19).
No assumption about which unit owns that original normal was made.

It remains only C-owned North.

## 10. C-owned North gives an actual circle corner beyond R

Now g=(c,s). By (26), g dot f>0, while

    g dot j_D=-c*q-s*p<0.

The actual CD point is therefore the strict right vertex

    T=P+f.

It is also the original C-side mean Q_C+z*e, 0<=z<=1.
Put r=s/c. The original D proper line at T and its vertical AD line
give, without moving either application,

    q_D=T-(p/c)g=(-X,-w-q-p*r).

From (25) and (6),

    q_D=[X/(X+q)]*(-X-q,-w-p).

Their vertical coordinates give the exact identity

    X*[p(1-r)-q]=q*(w+q+p*r).                           (27)

In particular p>q. Express the actual vector Z_D-T=j_D-f in the
original C frame:

    A_r=(Z_D-T) dot e=p(c-s)-q(c+s),
    B_t=(Z_D-T) dot j=p(c+s)+q(c-s),
    A_r^2+B_t^2=2.

The tangent component B_t is positive. Equation (27) gives

    A_r=(c*q/X)*[w+q+r(p-X)]>0.                         (28)

Indeed r<5/14 by (18), X<=a<61/60, and

    w-r*X>11/15-(5/14)(61/60)=311/840>0.

The actual C-side point has C-frame coordinates (d+z,1/2), so the
actual unique D circle corner has coordinates

    Z_D=(d+z+A_r)e+(1/2+B_t)j.

Because A_r,B_t>0 and A_r^2+B_t^2=2, we have
A_r+B_t>sqrt(2). Keeping the actual z>=0,

    |Z_D|^2-R^2
      >=(d+A_r)^2+(1/2+B_t)^2-[(d+1)^2+1/4]
       =1+B_t+2d(A_r-1)
       >1+sqrt(2)-2d+(2d-1)A_r
       >11/30>0.                                      (29)

This contradicts the actual radius, and finishes the last tilted D case.

## 11. Exact whole-interface join

The radial-boundary owner theorem gives the entire original B chart when
both A,B own AB. Section 2 exhausts all A genuine-leaf supports and
removes every one except the strict upper-left feature. Section 3 retains
its full actual A3 equation. Sections 4--5 remove its two strict lower
AD vertices. Section 6 retains its original South-side mean. Sections
7--10 exhaust D's owned-axis and strict-vertex supports at that mean,
its unique physical circle corner, and both original C contact features.

Hence no original high LCD.SS component with one physical two-corner
boundary square, one unique-corner boundary square, and both roots owning
AB exists in the common compatible certificate. Interchanging the two
root/boundary pairs covers the other mixed-mask labeling.

This is a whole mixed-mask/both-owner exit. The separate both-two-corner
source already covers that physical mask. The exactly-one-owner mixed
case and the unique/unique cases remain their separately stated domains.
No completion square, original force, individual circle weight, side mean,
normal owner or physical contact was removed. No numerical pose, compilation,
CI, remote write or shared-metadata change is used.

