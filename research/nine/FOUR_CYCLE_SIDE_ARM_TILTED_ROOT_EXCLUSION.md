# A surviving S-side arm cannot meet a tilted four-cycle root

Date: October 27, 2026.

**Status: complete hand theorem for the entire tilted-root domain,
submitted for full root and separate independent review.** This does
not yet exclude the whole S-side-arm gate: the aligned root has a
separate opposite-vertex alternative, recorded explicitly below.

Keep the original nine physical units, the common compatible selected
certificate and the radius/Phi-minimizer pose, with

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    r=R-sqrt(2).

The actual graph contains H--B--C--D--H and the exact arm H--X--L.
The true degrees are H3,B2,C2,D2,X2,L1. B and D have positive
circle loads; C may have positive or zero circle load. X is the
genuine unloaded side transmitter and L the genuine S leaf. The
remaining three physical squares stay arbitrary and in place.
Every original normal, application mean, physical circle mask and
individual zero weight remains.

FOUR_BODY_BLOCK_SHORT_ARM_NEGATIVE_APPLICATION_EXCLUSION.md excludes
the entire negative arm-application domain. Hence the remaining
S-side arm has

    d=1+epsilon,       0<=epsilon<1/60,
    p_HX=epsilon e,    H subset {z:e.z<=epsilon},           (1)

where e is its actual unit direction toward X and L. Its actual
positive root force is beta e, beta>0. An inward normal segment
of length one from a supporting point of a unit square lies in
that square: in an own frame its coordinate decrements have
absolute value at most one. Therefore

    [epsilon-1,epsilon]e subset H,       O in H.            (2)

The original arm point has norm epsilon<r, so H is physically
circle-clear. In particular its full equation is

    u+v=-beta e=:M,                                      (3)

where u,v are its actual H-to-B and H-to-D forces. No arm force
has been discarded. R>2 in this remaining domain, and the elementary
contained-square bounds give

    |c_T| <= d+1/2 < 91/60,
    h<=d for any actual contained unit beyond support h.  (4)

These are the exact center and support bounds of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 1.

**Theorem.** Under these original hypotheses, e must be an own side
axis of H. Thus every original LBD and LBCD S-side arm with H tilted
relative to its actual arm direction is impossible, including the
critical d=1 endpoint and every private-circle mask.

## 1. The actual root concurrence and strict proper ports

When C is loaded, Sections 1--3 of
ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md give the following
complete local facts: opposite parallel root normals are impossible;
in the nonparallel case their actual concurrence is

    q=-t M=s e,       t,s>0.                             (5)

When C is unloaded, the actual width-one channel and the full
B2/D2 equations give precisely the same conclusions by Sections
2--5.2 of ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md.
Only its local channel, endpoint and negative-concurrence proof is
used. Its separate forbidden-ray premise and subsequent one-improper
conclusion are not imported. In either case these local proofs retain
all B/C/D equations and impose no extra root equation.

In a same-direction parallel pair, (3) makes both normals -e.
The same true endpoint moment and proper-concurrence argument in
those sources makes their transverse root heights strictly opposite.
Their ports are distinct, so H owns the common side axis -e. This
already proves the theorem in the entire parallel case.

Suppose henceforth the root pair is nonparallel. Write

    P_i=q+l_i n_i

for its actual unit normals and real coefficients. Both P_i belong
to physical boundary units, so |P_i|>=r.

If 0<s<=epsilon, (2) puts q in H. A negative l_i would place q
on a strict outward normal ray of H, which is impossible for a
point of H. If s>epsilon, q is on the outward normal ray from
the actual arm point p=epsilon e, and its unique closest point
in H is p. If some l_i<0, its unchanged P_i would be the same
unique closest point: for any x in H and lambda>0,

    |P_i+lambda n_i-x|^2
       >=lambda^2+|P_i-x|^2.

This would give P_i=p, contrary to epsilon<r. A zero l_i is
also impossible: for s<=epsilon it makes |P_i|<=epsilon<r;
for s>epsilon it puts q outside H. Consequently every actual
root port is strictly proper:

    P_i=q+l_i n_i,       l_i>0.                          (6)

This nearest-point argument is independent of the old forbidden-ray
hypothesis and is the full properness statement needed here.

## 2. The complete tilted-root support cover

Assume e is not an own side axis of H. Choose the two inward side
axes at its actual arm vertex and their positive signs so that

    e=(-a,-b),       a,b>0,       a^2+b^2=1,
    H=[-epsilon a,1-epsilon a]
        times [-epsilon b,1-epsilon b],
    q=(-s a,-s b).                                      (7)

If s>epsilon, both coordinates of P_i-q are strictly positive
for every P_i in H. By (6), both actual normals have two positive
coordinates. Both root applications would therefore be H's same
far opposite vertex. Two nonparallel lines at that vertex cannot
concur at the different q. Thus

    0<s<=epsilon.                                       (8)

In particular a tilted root is already impossible at epsilon=0.
Put v=epsilon-s, so 0<=v<epsilon.

All actual root support features can now be listed without any
normal reselection. The near-near vertex is the arm point and is
too close to O for B or D. A negative own-axis normal on a near
side has its transverse coordinate fixed by (6) at the corresponding
coordinate of q; that port also has norm at most epsilon. The two
remaining mixed-sign vertices are

    (1-epsilon a,-epsilon b),
    (-epsilon a,1-epsilon b).                            (9)

At the first the actual normal is proportional to
(1-v a,-v b), and at the second to (-v a,1-v b).
Positive own-axis normals give their genuine far-side means;
their transverse coordinates again agree with q. No mean has
been replaced by a chosen point.

The far opposite vertex P=(1-epsilon a,1-epsilon b) is impossible.
Indeed, for its proper unit normal n, (6) gives

    P.n >= |P|-2|q| >= sqrt(2)-3epsilon > 61/60 > d.

This contradicts (4) for its actual contained neighbor. The strict
comparison follows already from sqrt(2)>7/5 and epsilon<1/60.

Thus every root contact lies in one of exactly two groups:

* the right far face or its lower endpoint, with n_x>0 and n_y<=0;
* the top far face or its left endpoint, with n_y>0 and n_x<=0.

Equation (3), in these actual coordinates, is M=beta(a,b), with
both components positive. Two contacts in the first group cannot
give its positive second component; two in the second cannot give
its positive first component. Hence, after naming the actual tips,
B is in the first group and D in the second.

## 3. Each boundary tip stays beyond a nearly unit coordinate

The supporting half-plane at B gives a simple bound on every
physical point z=(x,y) of B. For the axis endpoint it is
x>=1-epsilon a. For the mixed vertex in (9), its exact inequality is

    x >= 1-epsilon a + [v b/(1-v a)](y+epsilon b).

Since y>=-R and 0<=v<epsilon, in both cases

    x >= 1-epsilon a - epsilon b R/(1-epsilon a).

Here R<21/10 and 1-epsilon a>59/60. By Cauchy--Schwarz,

    a+[R/(1-epsilon a)]b
       < sqrt(1+(126/59)^2) < 12/5.

The last exact comparison is 25(59^2+126^2)<144(59^2).
Therefore every point of B satisfies

    x>24/25.                                           (10)

The reflected calculation gives y>24/25 for every point of D.
The unchanged actual C touches both, so

    max_C x>24/25,       max_C y>24/25.                 (11)

Meanwhile H contains the whole closed square [0,59/60]^2.
The following elementary separating-axis lemma now applies to
the real C, whether it is loaded or unloaded.

## 4. A unit cannot go around that square within the center disk

**Geometric lemma.** No unit square T with center norm less than
91/60 can have disjoint open interior from [0,59/60]^2 and satisfy
both max_T x>24/25 and max_T y>24/25.

Put A=59/60, t=24/25, M_*=91/60. If the common coordinate width
of T is w, then 1<=w<=sqrt(2), and its center coordinates satisfy

    c_x,c_y>t-w/2>1/4.                                 (12)

The last strict inequality follows from sqrt(2)<17/12. A separating
axis of two rectangles is an own side axis of one of them. We
check the full cover, including all equality and axis endpoints.

If a coordinate axis separates them, the positive projections in
(11) rule out the negative side. Suppose T lies to the right.
Then c_x>=A+w/2 and c_y>t-w/2. Their squared sum is increasing
for w>=1, because A>t, and therefore

    |c|^2>(A+1/2)^2+(t-1/2)^2 > M_*^2.

The upper-side case is symmetric.

Otherwise an own unit axis n of T separates it outward from the
smaller square. Thus

    c.n >= A(n_x^++n_y^+)+1/2.                          (13)

The two negative components are impossible by (12). In the mixed
case write n=(a,-b), a>0,b>=0, with the reflected case symmetric.
Now w=a+b and (13) gives

    c_x >= A+1/(2a)+(b/a)c_y
          >= A+1/2+(b/a)/4.

The center bound therefore forces b/a<2/15. Hence w<17/15 and
c_y>t-17/30=59/150, while c_x>=89/60. The resulting strict
squared-norm reserve is

    (89/60)^2+(59/150)^2-(91/60)^2=1231/22500>0.

In the nonnegative case, exchange axes and write n=(a,b) with
a>=b>=0. Equation (13) and the center bound imply

    w=a+b<61/59,
    ab=(w^2-1)/2<120/3481.

Since a>=1/sqrt(2)>7/10, it follows that
b<1200/24367<1/20 and a>99/100. Equation (12) gives

    c_y>24/25-61/118>11/25.

Using c_y<M_* in (13),

    c_x >= A+1/(2a)+(b/a)(A-c_y)
          >89/60-(5/99)(8/15)
           =8651/5940 >131/90.

This yields the other exact positive reserve

    (131/90)^2+(11/25)^2-(91/60)^2=9691/810000>0.

Every possible separating axis is excluded. This proves the lemma.
It uses only ordinary square separation and the center disk; no
force, circle-weight or application assumption was made on T.

## 5. Exact conclusion and remaining aligned alternative

The original C satisfies (11), is disjoint from the smaller square
inside H, and obeys the center bound (4). Section 4 is a contradiction.
This proves the theorem for every tilted H in both whole private-load
orbits LBD and LBCD, retaining the actual positive C force whenever
present and the actual unloaded C channel whenever absent.

Together with the negative-arm theorem, it removes every D-side or
S-diagonal arm and every tilted-H S-side arm in these two load orbits.
It does not claim to remove every aligned S-side arm.

In an aligned H write

    H=[epsilon-1,epsilon] times [h-1,h], 0<=h<=1,
    q=(s,0), s>0.

The full proper-port statement of Section 1 still holds. Besides
same-far-face contacts, there can be opposite-vertex applications
(epsilon,h) and (epsilon-1,h-1), with 0<s<=epsilon. The strict
case s<epsilon has nonzero components of the two normals; its
s=epsilon own-axis endpoint is retained as well. Reflection gives
the other orientation. This is a real remaining family; it is not discarded
by the tilted proof or called a common-face pair. Its original
forces, private loads and arbitrary completion squares remain open
in the present source.

No Lean compilation, CI, numerical pose, normal reselection, remote
action or shared-ledger edit is used.
