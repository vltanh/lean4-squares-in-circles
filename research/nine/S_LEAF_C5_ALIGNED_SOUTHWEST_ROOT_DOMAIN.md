# The aligned S123 Southwest root has a shallow slider and an owned far channel

Date: October 27, 2026.

**Status: complete hand necessary-domain theorem, submitted for full
independent and root review.** In the unique-C mask it also excludes
both strict B return corners in full. The remaining owned B return
and the radial-C returns are explicit; no whole S123 gate is claimed.

## 1. The original component and actual root equations

Keep the original component A--B--M--C--U--A, A--L, with true A3,
true loaded B2,M2,C2, actual unloaded U2, genuine S leaf L and all
nine physical units. Retain every actual normal, owner, shared-side
mean, physical circle mask and individual zero weight.

Use the accepted high aligned domain from
FAR_SUPPORT_THREE_BOUNDARY_PATH_EXCLUSION.md:

    d=1+epsilon, 0<epsilon<1/60,
    R^2=(2+epsilon)^2+1/4,
    A=[epsilon,d] x [-b,a], a+b=1,
    n=(-c0,s0), c0,s0>0, c0^2+s0^2=1,
    -epsilon<=h_A(n)<=epsilon, w_U=1.

This source treats the actual Southwest direct normal

    m=(-c,-t), c,t>0, c^2+t^2=1.

The two root ports are the distinct actual West vertices
(epsilon,a),(epsilon,-b). Full A3 torque puts their intersection
at q_A=(epsilon+K,0), with

    K=a*c0/s0=b*c/t>0.                                 (1)

Both a,b are strictly positive: either zero endpoint in these
two equal line equations would contradict the other positive
height and strict normal. Consequently

    n=(-K,a)/sqrt(K^2+a^2),
    m=(-K,-b)/sqrt(K^2+b^2),
    a^2<=2*epsilon*K+epsilon^2.                        (2)

The last inequality is exactly the original channel support
inequality, as in Section2 of the aligned Southeast source.
No upper bound on K is assumed.

## 2. The direct boundary square owns its actual incoming normal

The actual U is a side transmitter, so its incoming normal n
is a fixed actual own axis at the singleton root port. The other
port is a distinct singleton, and both root vertices are
noncollinear with the real leaf direction because a,b>0.
The globally compatible genuine-three-force singleton determinant
selection in Section4 of
ADJACENT_C4_SINGLE_LOAD_S_LEAVES_EXCLUSION.md therefore applies
literally. Its proof requires no boundary or degree assumption
at the other neighbors. A free AB normal would satisfy its one
forbidden nontrivial determinant direction. Thus B owns m.

This uses the existing selection before extraction, not a new
normal choice. No shared-side mean is fixed by that argument.

Put j=Jm=(t,-c), L_B=sqrt(K^2+b^2). The actual incoming point
(epsilon,-b) has own B coordinates

    N=b*t-epsilon*c=(b^2-epsilon*K)/L_B,
    z=epsilon*t+b*c=b*(K+epsilon)/L_B>0,
    N^2+z^2=epsilon^2+b^2.                             (3)

Since -epsilon<N<b<1, the actual minimum-m support N is none
of d,-d-1,-1/2. A physical two-corner radial B owning m is
therefore impossible. B is physical unique. As N>-1/2, its
circle corner lies on the outer m face. Its full B2 positive
radial concurrence has j coordinate z>0, so that corner is
the positive-j endpoint. Thus the entire actual box is

    B=[N,N+1]m+[W-1,W]j,
    W=sqrt(R^2-(N+1)^2),
    eta=z+1-W in[0,1],
    q_B=(N+lambda,z),
    lambda=z*(N+1)/W-N in[0,1].                       (4)

The inside-unit concurrence is used only in this proved unique
mask. The actual boundary neighbor M supplies its full original
local theorem. Every mean and zero proper length remains.

## 3. The whole original slider satisfies a<29/100

Suppose a>=29/100, so b<=71/100. Set r=t/c=b/K. By (2),

    r<=2*epsilon*b/(a^2-epsilon^2)<2/7,                (5)

where the reserve between2/7 and the resulting endpoint bound
is89/26404. The actual circle and eta>=0 give

    R^2=(N+1)^2+W^2
        <=epsilon^2+b^2+2(N+z)+2,
    N+z=b(c+t)-epsilon(c-t).                          (6)

If r<=1/4, then c+t<=5/sqrt(17)<49/40. Equation (6) is
strictly less than17/4, with exact reserve551/90000.

If r>1/4, (2) gives

    epsilon>=a^2*r/(2*b+epsilon*r)>a^2/6
             >=841/60000>7/500.

Here2*b+epsilon*r<3/2. Equation (5) also gives

    c+t<9/sqrt(53)<99/80,
    c-t>5/sqrt(53)>2/3.

Consequently (6) is again less than17/4, now with reserve
1267/180000. Both contradictions use R^2>17/4. Therefore

    a<29/100,
    |P_AU|^2=epsilon^2+a^2<(291/1000)^2<9/100.         (7)

The first squared comparison has reserve2729/9000000.

## 4. The actual far channel normal is owned by C

In the original n,f frame, f=Jn, the genuine far application is

    P_C=(X,-T), X=1+h, h=h_A(n),
    59/60<X<61/60,
    T=epsilon*s0+a*c0>0,
    T<291/1000.                                       (8)

Suppose n were not C-owned. P_C would then be its strict
minimum-n vertex. The vector to its opposite corner has n
component k in(1,sqrt(2)] and absolute f component sqrt(2-k^2).
Its squared norm is at least

    X^2+T^2+2+2[X*k-T*sqrt(2-k^2)].

This expression increases strictly with k, because X,T>0.
At k=1 it equals(X+1)^2+(1-T)^2. Thus the actual opposite
corner would have squared norm greater than

    (119/60)^2+(7/10)^2
       =1105/256+247/2304.

This contradicts containment. Hence C genuinely owns n, with
all incoming side means retained.

Its physical radial mask is exactly

    h=epsilon,
    C=[d,d+1]n+[-1/2,1/2]f,
    a*s0=epsilon*(1+c0),
    K=(a^2-epsilon^2)/(2*epsilon), T=a.                (9)

The equality follows from the two physical outer corners, not
from an assumed equality of their individual weights.

Otherwise its unique physical corner has negative f coordinate,
and its complete original frame and proper concurrence are

    C=[X,X+1]n+[-D,1-D]f,
    D=sqrt(R^2-(X+1)^2)>1/2,
    q_C=(T(X+1)/D,-T),
    T>59/238.                                        (10)

Only this unique mask uses the inside-unit clause. Equations
(8)--(10) are necessary domains, not an assertion that either
remaining mask is empty.

## 5. Exact additional bounds in the unique-C mask

Assume (10). Since T^2<=epsilon^2+a^2, its lower bound gives

    a>49/200, b<151/200,
    r_P:=sqrt(epsilon^2+b^2)<19/25,
    K>7/4.                                           (11)

The first squared reserve is5868851/5097960000. The K reserve
after (2) is509/12000. Also

    N<b^2/sqrt(K^2+b^2)<3/10,                         (12)

with squared reserve3197999/1600000000 at the stated b,K bounds.
The original eta>=0 gives W<=z+1<44/25. Hence

    (N+1)^2=R^2-W^2>17/4-(44/25)^2>1,
    0<N<3/10,
    8/5<W<44/25.                                     (13)

Properness at C and (8) also give

    1/2<D<=T*(X+1)/X<35211/59000<3/5,
    F:=1-D in(2/5,1/2).

Put rho_C=T(X+1)/D-X. Its original full interval obeys

    0<=rho_C<5711/30000<1/5,
    3/5<F+T<4/5.                                     (14)

The full C2 equation makes its return normal have positive f
component. A positive n component would use its far upper
corner and have direction proportional to(1-rho_C,F+T).
By (14) its n component exceeds1/sqrt(2), giving minimum
neighbor support greater than119/(60 sqrt(2))>5/4>d.
Thus this entire return is impossible. Every remaining actual
C-to-M support has either the inner corner(X,F), with negative
n component and slope magnitude below1/3, or its original
owned-f side mean at height F. No C mean is changed.

## 6. The unique-C mask excludes the strict near B return

B's unique circle force has positive j component, while its
force toward A has none. Its actual return normal g therefore
has g.j<0. The complete supporting features are the lower-near
corner(N,W-1), the original owned -j side mean, and the lower-far
corner(N+1,W-1).

For the near corner, its squared norm is

    R^2+2-2[W+sqrt(R^2-W^2)].

On (13), W>R/sqrt(2), so this expression increases with W.
It also increases with R^2 because sqrt(R^2-W^2)=N+1>1.
Using W<44/25,R^2<=1105/256 and

    sqrt(1105/256-(44/25)^2)>11/10

therefore bounds its squared norm by less than

    1105/256-93/25<16/25,

with reserve279/6400. The radical square reserve is1409/160000.
But this actual BM application is shared by two physical boundary
units. BOUNDARY_PAIR_CONTACT_SHARP_INNER_RADIUS.md requires its
norm to exceed4/5 throughout the present high-radius interval.
This contradiction excludes the entire strict near return,
regardless of its actual point-normal or proper-distance endpoint.

## 7. The unique-C mask excludes the strict far B return

Write delta=W-z=1-eta. First delta>7/8. Indeed r_P<19/25
and N<3/10 imply

    2N+(7/4)z<19/10.

For N<=7/25 use z<19/25; for N>7/25 use
z^2< (19/25)^2-(7/25)^2<(71/100)^2. These two actual
ranges prove the displayed bound. On the other hand

    R^2-r_P^2-1-49/64>19/10+271/40000.

Subtracting proves W^2>(z+7/8)^2, as asserted.

We need one further exact mean bound:

    eta<(3/5)N-1/25,
    N>1/15.                                          (15)

For clarity define on0<=N<=3/10

    phi(N)=sqrt((19/25)^2-N^2)+1
             -sqrt(17/4-(N+1)^2).

The actual eta is strictly below phi. One has phi(0)<-1/25.
Also phi'(N) is at most

    psi(N)=(N+1)/sqrt(17/4-(N+1)^2)-(25/19)N.

Its derivative is negative, since it is at most
2125/2048-25/19<0. Thus phi'<psi(0)=2/sqrt(13)<3/5.
This proves (15), including the zero eta endpoint.

At the far B corner, original properness makes the return
direction proportional to

    ((N+1)*delta/W,-eta).

Its angle from the positive m axis has tangent

    tau=eta*W/[(N+1)*delta]
        <=(352/175)*eta
        <t(N):=(352/175)*[(3/5)N-1/25].                (16)

No division by eta or a zero proper length is used. The far
proper m difference is positive because delta>7/8.

The actual minimum support required of its neighboring unit
is therefore greater than

    G(N)=(N+1)*(1-t(N)^2/2)-(19/25)*t(N).

Here cos(arctan(tau))>=1-tau^2/2 and sin(arctan(tau))<=tau
were used with the actual positive corner coordinates. G is
concave on[1/15,3/10]: its second derivative is
-2t't-(N+1)(t')^2<0. Its endpoint values satisfy

    G(1/15)=16/15>61/60,
    G(3/10)=4040781/3906250
            =61/60+416561/23437500.

Thus the actual neighboring unit would have minimum support
strictly greater than d. The sharp contained-unit support theorem
forbids this. The entire strict far B return is excluded.

## 8. Exact remaining original obligations

For every original aligned Southwest root, (1)--(8) hold and C
owns its actual incoming channel axis. The direct B owns m and
has the complete unique physical box(4). The radial C retains
exactly(9), including both original weights and all three B
return features.

In the unique-C mask, all bounds(10)--(15) and the complete C
return cover in Section5 hold. Both strict B return corners
are excluded. Its sole remaining B return is the actual owned
-j side mean

    Q_BM=(z*(N+1)/W,W-1), g=-j.

This is a necessary mean forced by the original B2 equation,
not a newly chosen side application. That whole return and the
radial-C returns remain open here. The separate aligned South
direct normal also remains outside this source.

All nine units, true degrees, physical masks, zero individual
weights, original positive forces, applications and means are
retained. No sampled pose, altered normal, deleted middle load,
new B--C contact, compilation, CI, shared metadata change or
remote action is used.
