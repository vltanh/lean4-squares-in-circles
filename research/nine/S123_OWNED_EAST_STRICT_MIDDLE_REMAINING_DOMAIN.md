# The remaining strict middle frame lies above the actual radial C side

Date: October 27, 2026.

**Status: complete necessary-domain and conditional zero-channel slider
theorem, submitted for full independent and root review.** This retains
both remaining physical middle masks and all nine original squares.
It is not an exterior completion theorem or a whole S123 exclusion.

## 1. Literal original scope and complete mask cover

Keep the original A--B--M--C--U--A, A--L, with true A3, loaded
B2/M2/C2, unloaded side transmitter U2 and the genuine S leaf.
Use the actual common owned-East return chart of
S_LEAF_C5_OWNED_EAST_STRICT_MIDDLE_UPPER_CORNER_EXCLUSION.md:

    B=[-W,1-W] times[F,F+1],
    1/2<W<1, 37/50<F<1,
    Q=(u,y), u=1-W in(0,1/2), F<=y<F+1,
    B-to-M normal East,
    M=Q+[0,1]v+[0,1]w,
    v=(c,s), w=(s,-c), c,s>0, c^2+s^2=1.

The physical far endpoint and its unchanged actual return are

    n=(x,-t), f=(t,x), x>0,t>=0,x^2+t^2=1,
    C=[d,d+1]n+[-1/2,1/2]f,
    1<d<61/60, epsilon=d-1,
    R^2=(d+1)^2+1/4<=1105/256,
    P=X*n+(1/2)f, d<=X<=d+1,
    h_n<=0<h_f, X=d whenever h_n<0.                 (1)

The accepted RADIAL_SIDE_BOUNDARY_NEIGHBOR_HALFPLANE.md also gives
every actual M point n>epsilon. In particular

    Q_n=xu-ty>epsilon>0,
    Q_f=tu+xy>=y>37/50.                              (2)

For t>0 the second inequality is strict: Q_n>0 gives
u>ty/x, and hence tu>(1-x)y. At t=0 it is equality.

The source cited above completely excludes the unique upper-adjacent
physical circle corner Q+v. Its full independent review is
REVIEW_OWNED_EAST_STRICT_MIDDLE_UPPER_CORNER_ROOTED_BLOCKS_2026_10_27.md.
The unique lower-adjacent corner Q+w is impossible directly: the
actual M2 proper concurrence has height y>0 and is a positive
multiple at most one of its unique physical circle corner, whereas
(Q+w)_y=y-c<y. Q itself is a physical shared point and cannot be
on the containing circle.

Thus the entire strict-M domain has only two physical alternatives:

* the unique opposite circle corner Z=Q+v+w;
* a physical radial S middle with two circle corners and all its
  original individual weights, including a zero weight.

The local proper theorem used here is Lemma2.1 of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, applied to actual M2 and
its physical boundary neighbors B,C. No whole-simple-cycle theorem
is used in a component that retains A--L. Inside-M concurrence is
used only in the unique physical mask.

## 2. Every unique-opposite M contact owner

Assume M has the unique opposite physical circle corner. As in the
accepted upper-corner proof, GENERAL_FIXED_TIP_NORMAL_SELECTION.md
forces CM to have an actual side-axis owner. If CM were free, both
actual applications Q and P would be fixed physical M vertices;
they are distinct because P_y=-Xt+x/2<=1/2<y. Thus the original
finite prelist applies before extraction. A shared-side mean is
never made fixed in this argument.

Write the actual M axes in the n,f frame as

    v=b*n+a*f, w=a*n-b*f,
    a=s*x+c*t>0, b=c*x-s*t, a^2+b^2=1.               (3)

The actual h has strictly positive world y component. If M owns it,
the only possible axes are v and -w. If C owns it, (1) gives h=f.
These include every axis shared by both bodies.

### 2.1. M cannot own h=v

In this case h_n=b<=0, and its full actual M-side mean is
P=Q+sigma*w, 0<=sigma<=1. By (2),(3),

    P_f=Q_f-sigma*b>=Q_f>37/50>1/2,

contradicting (1). This is a purely physical exclusion of the
whole side mean; it does not use the unique mask or M torque.

### 2.2. M cannot own h=-w

Here h=-a*n+b*f, so a,b>0 and X=d. Retain its full original
M-side mean in

    P0=d*n+(1/2)f=Q+w+sigma*v, 0<=sigma<=1.

Put A=d*b+a/2 and B=d*a-b/2, the actual v,w coordinates of P0,
and k=1-sigma in[0,1]. Then

    Q=(A-sigma,B-1), Z=P0+k*v.

The unique opposite physical mask requires B>1/2: subtracting
the squared norm of Q+v from that of Z gives exactly2B-1.
Since A>0 and A^2+B^2=d^2+1/4, it follows that A<d. Thus

    |Z|^2=|P0|^2+2kA+k^2
          <=d^2+1/4+2A+1
          <d^2+1/4+2d+1=R^2,

a contradiction. Both mean endpoints were retained until the
strict physical-mask inequality excluded them.

### 2.3. The complete surviving unique mask is C-owned h=f

By (3), h.v=a>0. If b<0, both h-axis components are positive
and its unique minimum on M is Q, whose height exceeds1/2. If
b=0, then h=v and Section2.1 applies. Therefore b>0 and its
actual minimum is exactly

    P=Q+w=X*n+(1/2)f.

Consequently the complete physical chart is

    Q=(X-a)n+(1/2+b)f,
    Z=P+v=(X+b)n+(1/2+a)f,
    M=P-w+[0,1]w+[0,1]v,
    a,b>0, a^2+b^2=1.                               (4)

In particular **every point of M has f coordinate at least1/2**.
The original selected h is f, and its actual X remains in[d,d+1].

## 3. Exact unique-mask equations and uniform frame bounds

Let p=t/x>=0. The unchanged proper lines are

    q_M=Q+ell*East=P+rho*f=tau*Z.

Their exact n and f components give

    ell=a/x>0, rho=b+a*p>0, tau=X/(X+b)<1,
    X[a-b-a*p]=b[1/2+b+a*p].                         (5)

All are original-force consequences, without choosing a side mean.
In particular a-b-a*p>0. The actual circle equation is

    R^2=(X+b)^2+(1/2+a)^2.                           (6)

The original world coordinates are still

    u=x(X-a)+t(1/2+b),
    y=-t(X-a)+x(1/2+b).                              (7)

Since u<1/2 and x+t>=1, equation(7) implies X-a<1/2.
Indeed otherwise both coefficients X-a and1/2+b would be
at least1/2. Combining X<a+1/2 with (5), and then decreasing
only the nonnegative comparison parameter p to zero, gives

    b(1/2+b)/(a-b) <= X < a+1/2.

The denominator is positive. Rearranging and using a^2+b^2=1
gives exactly

    (2b-1)(b+1+a/2)<0.

Thus the entire unique-mask domain satisfies

    0<b<1/2, a>sqrt(3)/2>6/7.                        (8)

In (6), 1/2+a>19/14 and R^2<=1105/256 force

    X+b<8/5.                                        (9)

The strict squared reserve is

    (8/5)^2+(19/14)^2-1105/256
      =26791/313600>0.

One further useful bound is b<12/25. If b>=12/25, then a<9/10.
For fixed positive b, the function (1/2+a)/(a-b) decreases in a.
Equation(5) would therefore give

    X+b>=b(1/2+a)/(a-b)
          >b(7/5)/(9/10-b)
          >=(12/25)(7/5)/(21/50)=8/5,

contradicting(9). All denominators are positive by a>b.

These are uniform actual-frame bounds for both original root types
and every retained strict or zero channel. They do not change a pose.

## 4. The complete physical radial-M mask

Suppose M has two physical circle corners. The force-free radial-pair
calculation in Section1 of
ADJACENT_TWO_S_LEAF_C4_BOTH_TWO_CORNER_MASK_EXCLUSION.md applies to
the actual radial C,M. It states that their radial directions differ
by2theta, tan(theta)=1/(2d), and they touch only at their two inner
corners. The upper C return in (1) fixes that actual point as P0.

The actual Q cannot be either M circle corner, and cannot be P0
because y>37/50 while P0_y<=1/2. It is therefore the other inner
M corner. In the actual strict-minimum-x frame it has P0=Q+w.
The complete physical chart is again (4), now with

    X=d,
    a=4d/(4d^2+1),
    b=(4d^2-1)/(4d^2+1)>0.                           (10)

Here v is M's radial direction. Formula(10) is simply the sine and
cosine of the actual angle2theta. In particular M again lies wholly
on f>=1/2, and P0+v is an actual circle corner.

No equation(5), no inside-M assertion, and no C-owned normal is
assigned to this physical radial mask. Its actual free near-bisector
normal, its full C/M2 forces and both M circle weights are retained.
The initial radial-pair selection remains exactly the existing one.

## 5. Exact zero-channel U consequence at the canonical minimizer

Now restrict to the original tilted t=0 row. Thus x=1, f=North,
F=1-V, V=2sqrt(epsilon), and 0<=T<=V. The entire original
channel mean is retained, and the actual U is

    U=[epsilon,d] times[z,z+1], with -T in[z,z+1].

Use the complete physical hole/conditional slider theorem
S123_ZERO_CHANNEL_OWNED_RETURN_HOLE_EMPTY.md, independently accepted
in REVIEW_S123_ZERO_CHANNEL_HOLE_AND_SLIDER_TRIANGLE_BRIDGES_2026_10_27.md.
The canonical choice is the existing minimum of the sum of squared
center norms among radius minimizers, made before normal selection.

Both remaining M masks lie wholly at y>=1/2 by Sections2 and4.
If U.top<1/2, it has no physical M contact. The exact conditional
slider therefore gives the contradiction U.top>=1/2. Hence

    U.top>=1/2.                                      (11)

The actual lower M edge from Q=(X-a,1/2+b) to P=(X,1/2)
has height1/2+(b/a)(X-d) at x=d. Its left endpoint has
x=u<1/2<d<=X. If U.top were strictly above that height,
points with x<d sufficiently close to d and y just above that
edge would be interior to both actual U and M. The bottom of U
is at most -T<=0, so it cannot avoid this local overlap by being
wholly above M. Consequently physical nonoverlap gives

    U.top<=1/2+(b/a)(X-d).                           (12)

For the radial mask, X=d, so (11),(12) center U exactly at
transverse zero. Its complete original mean -T remains on both
of its actual channel sides.

For the unique mask, (8),(9), d>1 and completing a square give

    (b/a)(X-d)<(7/6)b(3/5-b)
                  <=(7/6)(3/10)^2=21/200.

Thus the complete conditional unique-mask conclusion is

    1/2<=U.top<121/200<5/8.                          (13)

It does not center U when X>d. No movement of an obtained
certificate or stress is used; the source gives necessary geometry
at the existing canonical packing.

Both complete zero-channel masks also satisfy

    V>1/50.                                         (14)

For the unique mask, (7) at t=0 gives y=1/2+b<49/50,
while its original B-side mean has y>=F=1-V. For the radial
mask, (10) gives a>3/4 throughout1<d<61/60. Hence
u=d-a<4/15 and W=1-u>11/15. If V<=1/50, the actual
B circle identity would give

    R^2=W^2+(2-V)^2
         >(11/15)^2+(99/50)^2>1105/256.

The last strict reserve is204151/1440000. Thus (14) holds
without assigning a unique mask to a radial M or using its
inside-concurrence statement. In particular the original tilted
identity V^2=4epsilon supplies epsilon>1/10000 here.

## 6. Remaining original obligation

The entire strict-minimum-x M domain is reduced to (4)--(7) with
unique opposite circle corner, or the physical radial alternative
(10). Both lie above the actual upper C side; every actual application,
force and weight is retained. The zero-channel canonical consequences
are precisely (11)--(13), with radial U centered and unique U still
allowed its stated interval.

The three other original packing squares have not been placed or
discarded. This theorem supplies no exterior capacity by itself and
does not declare the owned-East interface, S123 family or parent
coarse cell closed. No compilation, CI or remote operation is used.
