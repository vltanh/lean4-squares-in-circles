# Outer envelopes for the five-square cap

This chapter supplies the complete two-square estimates used in the
[five-square cap](FIVE_SQUARE_CAP.md). Its proofs use the physical preliminaries
and weighted pair cap in [FOUNDATION.md](FOUNDATION.md), elementary calculus,
and the displayed rational comparisons. Every original orientation and
separating-axis owner is retained.

Put

    Q=1105/256, r=sqrt(Q), A=46, B=27/2, K=207/16, T=211/4.

For an original square V, H_V(w) is its centered support in the vector w,
h_V=H_V((1,0))=H_V((0,1)), and g_V=1/(4h_V). Let E,S be two original
unit squares with disjoint open interiors in the centered disk of radius
R<=r. Write their centers as (x,y),(X,Y), and assume

    89/60<=x<=91/60, |y|<=1/8, h_E<=8/15,
    0<=X<=13/12, Y>=3/5.

Define

    ell(z)=(29/2)z+(3/2)min(0,max(-1,z)),
    F(z)=A(x-h_E)+B[X+zY-H_S((1,z))].

**Outer-envelope theorem.** For every real z,

    F(z)<=T+ell(z).

At R=r the inequality is strict whenever z is nonzero. At R<r it is
strict for every z. At z=0, equality is exactly the equality of the
weighted physical pair cap in FOUNDATION.md; in the present upper-shoulder
domain this requires aligned squares with centers

    c_E=(3/2,-1/16), c_S=(1,15/16).

The allowed endpoint frame is genuinely small. If its reduced absolute
slope is e in [0,1], then h_E=(1+e)/(2sqrt(1+e²)), an increasing function.
At e=7/100 its square exceeds (8/15)², since
11449*225-10049*256=3481>0. Therefore |e|<7/100. Every later closed
interval |e|<=7/100 is a valid outward enlargement.

For fixed original squares F is piecewise affine in z: the only support
breakpoints are directions of S's two original side axes. This permits
the reductions in Parts A and C. It does not change S's frame or replace
a genuine original separator by one from an independently chosen square.

## A. Positive slopes

Set

    Q=1105/256, r=sqrt(Q), rho=sqrt(Q-1/4)-1/2,
    A=46, B=27/2, K=207/16, T=211/4,
    d=rho-1/2<61/60.

Let physical, interior-disjoint unit squares E,S lie in the Q-disk,
with centers (x,y),(X,Y), and assume

    89/60<=x<=91/60, |y|<=1/8, h_E<=8/15,
    0<=X<=13/12, Y>=3/5.

The center bound gives every center norm <91/60 and, more sharply,
<=rho. Reducing E's frame modulo a quarter turn gives a slope in
[-7/100,7/100], as follows from h_E<=8/15.

We prove for every z>=0 that

    F(z):=A(x-h_E)+B[X+zY-H_S((1,z))] <= T+(29/2)z.   (P)

The inequality is strict for z>0. At z=0 it is the established physical
weighted two-square cap. All constants and interval arguments below
are hand estimates; no sampled angles or external arithmetic program
are used.

### A.1. Only an original side-axis slope needs to be checked

For fixed original squares, F(z)-(29/2)z is a concave piecewise-linear
function of z. Its possible positive breakpoint is precisely the slope
w of the physical side axis of S in the first quadrant. At that point
m=(1,w) is parallel to an original side axis and

    H_S(m)=sqrt(1+w^2)/2.

If there is no positive breakpoint, the function is linear on z>=0.
Its eventual slope is B(Y-h_S)-29/2 < B(61/60)-29/2=-31/40.
Thus it is enough to prove (P) at z=0 and at that positive breakpoint.
This reduction does not choose S's frame separately from its separator.
Write M=sqrt(1+w^2) below.

### A.2. All side-axis slopes w>=4/5

In its own side direction, a square's center projection is at most rho.
Consequently, at the breakpoint,

    F(w)<=d[A+B sqrt(1+w^2)]
         <(61/60)[A+B sqrt(1+w^2)].

The difference between T+(29/2)w and the last expression has derivative
at least 29/2-(61/60)B=31/40>0. At w=4/5 it is positive because

    sqrt(41)<10550/1647,
    10550^2-41*1647^2=85531>0.

This proves the entire large-slope range, independently of owner.

### A.3. Complete separator list when 0<=w<=4/5

Choose S's physical frame as

    u=(1,w)/M, v=(-w,1)/M.

Put D=x-X>=2/5 and V=Y-y>=19/40. Also
D<91/60 and V<197/120. A directed original separating axis goes
from E toward S, whose displacement is (-D,V).

If S owns the axis, its normal can only be v or -u. Indeed -v has
negative dot product with the displacement, while the unnormalized
axis (1,w) has dot product at most

    -2/5+(4/5)(197/120)=137/150<1,

less than its two support halfwidths, whose sum is at least |(1,w)|.
Thus the S-owned cases are

    up: n=(-w,1),       left: n=(-1,-w).

If E owns the axis, write its frame as

    u_e=(1,e)/N, v_e=(-e,1)/N,
    |e|<=7/100, N=sqrt(1+e^2).

The right normal (1,e) has negative dot product with (-D,V), since
-2/5+(7/100)(197/120)<0. The down normal (e,-1) also does, since
(7/100)(91/60)-19/40<0. The only E-owned cases are therefore

    up: n=(-e,1),       left: n=(-1,-e).

Every original axis, both owners, and weak physical contacts are included.

### A.4. Both left-owner cases are strict by direct bounds

#### A.4.1. S-owned left normal

Here n=-m. The physical separator gives

    m.c_S <=m.c_E-H_E(m)-H_S(m).

Since H_E(m)>=M/2 and H_S(m)=M/2,

    F(w)<A(61/60)+B[91/60+w/8-(3/2)M]
         <=5639/120+(27/16)w < T+(29/2)w.

The last comparison holds already at w=0 and improves with w.

#### A.4.2. E-owned left normal

The separator (-1,-e) gives D-eV>=H_E(n)+H_S(n)>=1. Hence

    X<91/60-1+(7/100)(197/120)=7579/12000=:C.

At S's side-axis breakpoint,

    F(w)<A(61/60)+B[C+(91/60)w-M/2].

The difference between the target and this upper bound is decreasing
on [0,4/5]: its derivative is at most

    29/2-B(91/60)+(B/2)(4/5)=-23/40<0.

At w=4/5, use M>32/25. The difference is greater than
31607/24000>0. This proves the second left-owner case.

### A.5. E-owned up normal: the endpoint frame maximizes at zero tilt

Keep n=(-e,1), and use multiplier K on its original separator.
Containment in the directions A e_x-Kn and Bm+Kn gives F(w)<=Phi(e,w),
where direct evaluation of the supports in the SAME two original frames
is

    Phi(e,w)=
      r sqrt(A^2+2AKe+K^2(1+e^2))
      -A(1+max(e,0))/N-KN
      +r sqrt((B-Ke)^2+(Bw+K)^2)
      -BM-K[1+ew+max(w-e,0)]/M.                    (5.1)

The relevant frame-coordinate signs are fixed: the first vector's
components in E's frame are A/N and -(Ae+KN^2)/N; the second vector's
components in S's frame are BM+K(w-e)/M and K(1+ew)/M. The first
components and Ae+KN^2 are positive on the stated rectangle. Thus
(5.1) includes both changes at e=0 and e=w.

We prove Phi(e,w)<=Phi(0,w).

For e<0, the derivative of the first norm term is greater than
(90/49)K: its horizontal component exceeds 45, its norm is below 49,
and r>2. The derivative of the second norm term is greater than
-(5/3)K. For the latter estimate, its horizontal-component-to-norm
ratio is below 4/5, because its horizontal component is less than
B+(7/100)K<15 while its vertical component is at least K>12,
so three times the former is less than four times the latter.
Use also r<25/12. The remaining terms have derivative at least

    -161/50 +K(1-w)/M > -161/50+K/7.

Therefore

    Phi_e > (46/147)K-161/50
           > (46/147)*12-161/50=1311/2450>0.

For e>0, the first norm derivative is less than (25/12)K and the
second is negative. Moreover

    (1-e)/N^3 >93/101>23/25,

using N^3<101/100. Thus the derivative of -A(1+e)/N is less than
-1058/25. The derivative of the last support term is at most K,
whether e<w or e>w; that of -KN is nonpositive. It follows that

    Phi_e < (37/12)K-1058/25
           <(37/12)*13-1058/25=-671/300<0.

Continuity at the two break lines proves the asserted maximum.

At e=0 put

    f(w)=10327/256
      +r sqrt(B^2+(Bw+K)^2)-BM-K(1+w)/M.

Then f(0)=T. Its second derivative is

    f''=r B^4/[B^2+(Bw+K)^2]^(3/2)
        +(K-B)/M^3+3Kw(1-w)/M^5 >0.

Indeed K-B=-9/16, the first term exceeds
2*13^4/28^3>2, and the third is nonnegative on [0,4/5].
At w=4/5, the norm term is less than 57, BM>17, and
K(1+w)/M>18. The checks are

    1105*4772601=5273724105 <(57*1280)^2,
    27 sqrt(41)/10>17,      1863/(16 sqrt(41))>18.

Thus f(4/5)<15959/256<T+(29/2)(4/5).
The convex function f(w)-T-(29/2)w is below its endpoint chord.
This proves (P), strictly for w>0, in the whole E-owned up case.

### A.6. S-owned up normal: reduce the endpoint's original frame

Here n=(-w,1), orthogonal to m=(1,w). Use the nonnegative multiplier

    k=K(1-w),   0<=w<=4/5.

The S contribution to the containment-plus-separation upper bound is

    M G(w),  G(w)=r sqrt(B^2+k^2)-B-k>0.              (6.1)

For the endpoint put q=(A+kw,-k), x_q=A+kw. The exact center support
of a square whose frame-coordinate magnitudes of q are P>=J>=0 is

    C(q)=rho P,                         P>=nu J,
         r sqrt(P^2+J^2)-(P+J)/2,       P<=nu J,
    nu=sqrt(4Q-1).

This follows by maximizing P s+J t over
s,t>=0, (s+1/2)^2+(t+1/2)^2<=Q: the maximum is respectively on t=0
or at the circular stationary point.
The first frame component has the larger magnitude throughout the
endpoint frame interval: the relative angle is at most
atan(9/32)+atan(7/100)<pi/4, whose tangent is 1124/3137<1.

The endpoint contribution is C(q)-A h_E-kH_E(n). Its maximum over
E's whole frame interval |tan(theta)|<=7/100 is attained at theta=0.
Here are the derivative checks, including support and center-support
branch changes.

For theta=beta>=0, the circular-branch support penalty is

    [A+k(1+w)]cos(beta)+[A-k(1-w)]sin(beta), beta<=atan(w),
    (A+k)cos(beta)+(A+kw)sin(beta),           beta>=atan(w).

Both increase for tan(beta)<=7/100: their sine coefficients exceed
33, whereas their cosine coefficients are below 59. In an axis
branch the endpoint contribution is C_0 cos(beta)+C_1 sin(beta)
with C_0>0 and C_1<0; this follows immediately by substituting
P=x_q cos(beta)-k sin(beta) and either of the two expressions for
A h_E+kH_E(n). It therefore decreases as well.

For theta=-beta<=0, an axis-branch contribution is

    C_0 cos(beta)+C_1 sin(beta),
    C_0=A d+k(dw-1/2)>0,
    C_1=k(d+w/2)-A/2<0.                            (6.2)

The last inequality uses (1-w)(d+w/2)<=d and Kd<13(61/60)<23.
For w>=1/10 the endpoint is on this axis branch throughout the
negative angle interval. At beta=0,

    x_q/k=A/[K(1-w)]+w
        >=3281/810>121/30>nu.

Rotating the frame toward q and then, if necessary, less than atan(7/100)
past q keeps the absolute relative angle below atan(1/nu), so the
axis branch persists. For w<=1/10, any circular branch has support
penalty

    [A+k(1+w)]cos(beta)+k(1-w)sin(beta).

Its derivative is positive, since k(1-w)>12(9/10)^2 and the cosine
coefficient is below 59, while tan(beta)<=7/100. All axis portions
are already covered by (6.2). These formulas are continuous at their
branch transitions and prove the maximum at theta=0.

Consequently, writing M=sqrt(1+w^2), it suffices to bound

    J(w)+M G(w),

where for 0<=w<=1/10 the valid circular upper bound is

    J(w)=r sqrt((A+kw)^2+k^2)-A-k(1+w),              (6.3)

and for 1/10<=w<=4/5 the exact axis expression gives

    J(w)=A d+k(dw-1/2)
        <A(61/60)+k[(61/60)w-1/2].                 (6.4)

### A.7. Three exact scalar intervals for the S-owned up case

#### A.7.1. The interval 0<=w<=1/10

Let Phi(w) denote the sum of (6.3) and M G(w). Then
Phi(0)=T and Phi'(0)=K. Also Phi''<26 on this interval.

For completeness, put v=(A+Kw-Kw^2,-K+Kw). The second derivative
of (6.3) is

    r K^2[A+K(1-w)^2]^2/|v|^3
       -2rK v_x/|v|+2K <0.

Here v_x>=46, |v|<49, 12<K<13 and r<25/12. Its positive first
term is below 13, its negative term is below -2208/49, and 2K<26;
the resulting upper bound is -297/49. The norm bound |v|<49 follows
from v_x<=4717/100 and |v_y|<13.

In (6.1), G'<0, G<=G(0)=3177/256<25/2, and

    G''=r K^2 B^2/(B^2+k^2)^(3/2)<13.

For the last comparison use k>23/2, sqrt(B^2+k^2)>35/2,
r<25/12, K<13, B<14. Since M''<=1 and M<101/100,

    (MG)''=M''G+2M'G'+MG''<25/2+(101/100)13<26.

Integration gives

    Phi(w)<=T+Kw+13w^2
           <=T+(1139/80)w <T+(29/2)w  (w>0).

#### A.7.2. The interval 1/10<=w<=3/10

Define the exact quadratic target after (6.4):

    H(w)=5977/480-(1639/320)w+(4209/320)w^2.

We need MG<=H. Concavity of the square root in k^2, using the
anchor k=K and r sqrt(B^2+K^2)=9Q, gives

    G<=3177/256-(1449/256)w+(4761/512)w^2.

Multiply this positive upper bound by M<=1+w^2/2. The difference
H-(1+w^2/2)G_upper is

    P(w)=161/3840+(689/1280)w-(3009/1280)w^2
           +(1449/512)w^3-(4761/1024)w^4.

It is concave on the whole real line: 1280 P'' equals
-6018+21735w-71415w^2, with negative discriminant. Moreover

    P(0)=161/3840>0,
    P(3/10)=939817/30720000>0.

This proves the required comparison on [1/10,3/10].

#### A.7.3. The interval 3/10<=w<=4/5

The inequality sqrt(s)<=C/2+s/(2C), with C=249/8 and
s=Q(B^2+k^2), gives a second quadratic upper bound. Its constant,
linear and quadratic coefficients are respectively

    54537201/4079616,
    K-2(47348145/4079616),
    47348145/4079616.

They are bounded above by 107/8, -41/4, 93/8, respectively.
The exact cross-product reserves are 27663, 100194 and 77391,
respectively. For the linear comparison the identity is
2*47348145-(371/16)*4079616=100194>0.
Therefore for w>=0,

    G< (107-82w+93w^2)/8.

The difference from H after multiplying by 1+w^2/2 is now

    P_2(w)=-443/480+(1641/320)w-(1651/320)w^2
             +(41/8)w^3-(93/16)w^4.

It is concave: 160 P_2'' equals -1651+4920w-11160w^2,
with negative discriminant. Its endpoint values are

    P_2(3/10)=58193/240000>0,
    P_2(4/5)=7247/60000>0.

This proves the final scalar interval.

## B. The fixed diagonal slope z=-1

Put Q=1105/256, r=sqrt(Q), A=46, B=27/2, T=211/4.
Let two original, interior-disjoint unit squares E,S lie in the Q-disk.
Write their centers (x,y),(X,Y), respectively. Assume

    89/60 <= x <= 91/60, |y| <= 1/8, h_E <= 8/15,
    0 <= X <= 13/12, Y >= 3/5.

For any unit square, h is its coordinate halfwidth and g=1/(4h)
its aligned-inset halfwidth. Let a>=b>=0 be the absolute components
of a side of S, with a²+b²=1. Then h_S=(a+b)/2 and
H_S((1,-1))=a. We prove

    A(x-h_E)+B(X-Y-a) < T-16 = 147/4.                 (D)

This is the z=-1 widened envelope, with a uniform positive margin.
It uses only the actual two-square domain, not a selected multiplier.

### B.1. Elementary bounds

Let alpha>=beta>=0 be the absolute side components of E. From
h_E <=8/15, alpha+beta<=16/15, so

    alpha >= (16+sqrt(194))/30 >399/400,
    beta  <= (16-sqrt(194))/30 <7/100,
    1/(alpha+beta)>=15/16, g_E>=15/32.

The first strict rational comparison follows from
194>(557/40)²=310249/1600; the second from sqrt(194)>139/10.
For p>=q>=0 its support satisfies

    H_E((p,-q)) >= ((p+q)alpha-(p-q)beta)/2.           (1)

This follows directly from the two possible chiralities and |v|>=v.
Containment gives p x-q y <=r sqrt(p²+q²)-H_E((p,-q)).

Throughout,

    a+h_S=(3a+b)/2 >=sqrt(2)>141/100,
    27/(4a)+27a/2 >=27/sqrt(2)>1909/100.             (2)

The first minimum is at an endpoint of a=cos(theta), b=sin(theta),
0<=theta<=pi/4, by concavity. The second is AM-GM; its strict
rational lower bound follows from 364.5>364.4281.
The disk constants obey

    r sqrt(46²+(27/2)²)<399/4,
    r sqrt((119/2)²+(27/2)²)<3169/25.                (3)

These follow by squaring positive quantities. The respective left
squares are 10158265/1024 and 8226725/512; the right squares are
159201/16 and 10042561/625.

### B.2. Coordinate separators from the inset of E

Put g=g_E, D=x-X>0, V=Y-y>0. Physical disjointness implies that
S and E's actual contained aligned square have disjoint interiors.

If D>=g+h_S, then X<=x-g-h_S. Consequently the left side of (D)
is at most

    46(61/60)+(27/2)(43/96-a-h_S)
      <47+(27/2)(9/20-141/100)=851/25<147/4.

If V>=g+h_S, it is at most

    [46(x-h_E)-(27/2)(y+g)]+(27/2)(13/12-h_S-a).

Using (1) with p=46,q=27/2, the total support penalty in square
brackets is at least

    (211/4)alpha+(27/4)beta+(27/4)/(alpha+beta)
      >=47157/800.

Hence (3) bounds square brackets by 32643/800. Since
(27/2)(13/12-141/100)=-441/100, this case is less than
29115/800=36.39375<147/4.

### B.3. The two physical S-owned separators

Suppose neither coordinate separator holds. Every remaining separator
belongs to S. Its directed normal points northwest. Indeed an upward
normal pointing right has inset-adjusted projection at most
q h_S-p(D+g). For (p,q)=(a,b) this is at most b h_S<=1/2;
for (p,q)=(b,a) it is at most 1/2+b(k-D-g)<1/2, where
k=(a-b)/2<=1/2 and D+g>=2/5+15/32>1/2. The southwest case
is the same, using V+g>=19/40+15/32>1/2. Southeast is impossible
by sign. Thus the only possibilities are (-a,b) and (-b,a).

Put t=b/a in [0,1].

#### B.3.1. Mostly horizontal: normal (-a,b)

The separator gives

    X-Y <=x-g-t(y+g)-1/(2a)-(3/5)(1-t).

The target expression is therefore bounded by

    (119/2)x-46h_E-(27/2)t y-(27/2)(1+t)g
      -(27/(4a)+27a/2)-(81/10)(1-t).               (4)

For 0<=t<=4/5, use the stated boxes and g>=15/32. This bounds
(4) by

    50701/960+(1107/320)t-(27/(4a)+27a/2)
      <175157/4800<147/4.

For 4/5<=t<=1, apply (1) and disk support with p=119/2,
q=(27/2)t. The subtracted total support penalty is at least

    (211/4+27t/4)alpha-(27/4)(1-t)beta
         +(27/4)(1+t)/(alpha+beta)
      >=46779/800+(10827/800)t.

Thus (4), using (2)--(3), is less than

    3169/25-53259/800-(4347/800)t-1909/100
      <=146997/4000=147/4-3/4000.

#### B.3.2. Mostly vertical: normal (-b,a)

The separator gives

    X-Y <=t(x-g)-(y+g)-1/(2a)+(13/12)(1-t).

Apply (1) with p=46+(27/2)t,q=27/2. The subtracted total
support penalty is at least

    (211/4+27t/4)alpha+(27/4)(1-t)beta
        +(27/4)(1+t)/(alpha+beta)
      >=47157/800+(10449/800)t.

Using (2), the target expression is strictly less than

    f(t)=r sqrt((46+(27/2)t)²+(27/2)²)
           -50729/800-(22149/800)t.

The function f is convex, so on [0,1] it is bounded above by the
larger endpoint value. Formula (3) gives

    f(0)<29071/800, f(1)<28530/800,

both below 147/4. This exhausts every actual physical separator and
proves (D), including weak contacts in the original domain.

## C. Negative slopes and the complete owner list

Put

Q=1105/256, r=sqrt(Q), rho=91/60,
    A=46, B=27/2, T=211/4,
    ell(z)=(29/2)z+(3/2)min(0,max(-1,z)).

Let original disjoint squares E,S satisfy the widened outer hypotheses:
E has center (x,y), 89/60<=x<=91/60, |y|<=1/8, h_E<=8/15;
S has center (X,Y), 0<=X<=13/12, Y>=3/5; both lie in the Q-disk.
Write g=1/(4h_E). We prove the stated cases of

    F(z):=A(x-h_E)+B[X+zY-H_S((1,z))] <=T+ell(z).

Parts A and B prove the positive envelope and the fixed diagonal z=-1.
At z=0 use the completed physical two-square cap.

### C.1. Reduction to the single negative shoulder-owned slope

For a fixed original S, H_S((1,z)) is piecewise affine. On (-infinity,0)
it has just one finite breakpoint, unless S is aligned. The other
breakpoint is positive. The target has its additional breakpoint -1.
Thus F(z)-T-ell(z) is affine between these points. Its limit at negative
infinity is minus infinity, because its coefficient of |z| is

    (29/2)-B(Y+h_S) <=29/2-B(11/10)=-7/20<0.

Consequently the full negative half-line follows from z=0,z=-1 and
the one negative S-owned side-axis slope. The aligned limiting case
requires only z=0 and z=-1.

Represent that owned direction by (p,-q), p,q>0, p²+q²=1;
then z=-q/p and H_S((1,z))=1/(2p), h_S=(p+q)/2.
The normalized target, multiplied by p, is

    Tp-(29/2)q-(3/2)min(p,q).                         (1)

We use the actual contained aligned inset of E. Put D=x-X>0,V=Y-y>0.
Its coordinate separators are D>=g+h_S and V>=g+h_S.
If neither holds, its separating axis must belong to S and point
northwest, by the same sign exclusions as in Part B:
D+g>1/2, V+g>1/2, and k_S<=1/2 rule out northeast and southwest
axes, while southeast has the wrong dot-product sign. Since (p,-q)
is an axis of S, the only northwest S-axis is (-p,q). Hence

    pX-qY <=px-qy-g(p+q)-1/2.                         (2)

This is separation from the actual INSET. Its support is g(p+q),
not H_E((p,-q)); no full-E separator is inferred from (2).

### C.2. Horizontal inset separation, both shallow and steep

Assume D>=g+h_S. Then X<=x-g-h_S. Since

    46h_E+(27/2)g >=119/4

(the expression increases for h_E>=1/2), and x<=91/60, the
target difference, multiplied by p, is at most

    (929/120)p+(32/5)q+(3/2)min(p,q)
                 -(27/4)(1+p²+pq).                   (3)

Here the lower shoulder height Y>=3/5 was used. Replace 929/120
by the larger 31/4.

If p>=q, then p²+pq>=p, p<=1, and q<5/7. Thus (3) is less than

    p+(79/10)q-27/4 <=1+79/14-27/4=-3/28<0.

If p<=q, then p<3/4, q<=1-p²/2, q>=1-p². Formula (3) is at most

    -7/20+(5/2)p-(199/20)p²+(27/4)p³
      <=-7/20+(5/2)p-(391/80)p²<0.

The final quadratic is strictly negative on the real line: its negative
has positive leading coefficient and discriminant -237/400.

### C.3. Northwest inset axis, shallow negative slope

Assume p>=q and (2); put t=q/p in [0,1]. Eliminating the shoulder
center through (2), the target difference is at most

    (119/2)x-(27/2)t y-46h_E-(27/2)(1+t)g
          -(27/2)sqrt(1+t²)-T+16t.                  (4)

The endpoint support calculation from Part B, with
coefficient vector (119/2,-(27/2)t), gives

    (119/2)x-(27/2)t y-46h_E-(27/2)(1+t)g
       <=r sqrt((119/2)²+(27t/2)²)
                     -46779/800-(10827/800)t.

The calculation is valid on the entire [0,1]; it uses only
alpha>=399/400, beta<=7/100, 1/(alpha+beta)>=15/16 and
the signed support lower bound, with all absolute-value cases retained.

Concavity of sqrt and r<25/12 give

    r sqrt((119/2)²+(27t/2)²) <989/8+(16/5)t².

The endpoint comparison follows from
15647905/1024<(989/8)²; the quadratic coefficient is bounded by
18225/5712<16/5. Also sqrt(1+t²)>=1+(2/5)t², since the chord
of sqrt on [1,2] has slope sqrt(2)-1>2/5.
Consequently (4) is strictly less than

    -879/800+(1973/800)t-(11/5)t²
       <=-1+(5/2)t-2t²<0.

The last quadratic has maximum -7/32. This proves the shallow
northwest-inset case without asserting any full-E separator.

### C.4. Northwest inset axis, steep negative slope

Assume p<=q and (2); put t=p/q in [0,1]. Multiply the target
difference by t. The resulting expression is at most

    (119/2)t x-(27/2)y-46t h_E-(27/2)(1+t)g
       -(27/2)sqrt(1+t²)-(205/4)t+29/2.              (5)

For t>=27/65 the expression
46t h+(27/2)(1+t)/(4h) increases for h>=1/2, so it is at least
23t+(27/4)(1+t). The endpoint boxes then bound (5) by

    151/16+(1109/120)t-(27/2)sqrt(1+t²)
       <19/2+(37/4)t-(27/2)sqrt(1+t²)<0.

The last step is Cauchy--Schwarz, since
(19/2)²+(37/4)²=2813/16<729/4=(27/2)².

For 0<=t<=27/65<5/12, use h_E>=1/2,g>=15/32 and the
endpoint boxes. Formula (5) is at most

    631/64+(9277/960)t-(27/2)sqrt(1+t²)
      <-18/5+(97/10)t-(27/5)t²<0.

The last displayed quadratic is increasing on [0,5/12] and equals
-119/240 at 5/12. This proves the whole steep northwest-inset case.

### C.5. Vertical inset separation, steep negative slope

Assume V>=g+h_S and that the negative owned slope is steep.
Write p=b,q=a with a>=b>=0, a²+b²=1. Put k_S=(a-b)/2.
Between z_*=-a/b and zero one has

    H_S((1,z))=h_S-k_S z.

The independently reviewed diagonal proof, in its vertical-inset case,
gives

    F(-1)-(T-16)<-285/800.                            (6)

On [z_*,-1], the derivative of F(z)-T-ell(z) is

    B(Y+k_S)-29/2.

If Y+k_S>=29/27, moving left cannot increase the difference, so (6)
already proves the claim. Otherwise the vertical inset condition gives

    Y+k_S>=y+g+a>=11/32+a,
    a<29/27-11/32=631/864<3/4.

Hence b>sqrt(7)/4>5/8 and a/b<6/5. Also
Y+k_S>11/32+2/3>1, so the displayed derivative is greater than -1.
The possible increase from -1 to z_* is less than 1/5, leaving

    F(z_*)-T-ell(z_*)<-285/800+1/5=-5/32<0.

Sections 2,4,5 and the inset SAT exhaust every steep negative
shoulder-owned slope. They require no new statement about actual
separator owners or discarded equality faces.

### C.6. Actual endpoint-owned left separator, shallow negative slope

For the remaining shallow owned slope put t=q/p<=1 and M=sqrt(1+t²).
The physical shoulder frame has side (1,-t)/M. Suppose the original
E-owned left separator is n=(-1,-e), |e|<=7/100.
Its supports satisfy

    H_E(n)>=1/2, H_S(n)>=(93/100)h_S.

The latter follows from |a-eb|+|b+ea|>=(1-|e|)(a+b).
Since V<=197/120, its physical inequality gives

    X<=13579/12000-(93/100)h_S.

Use this, Y>=3/5, x-h_E<=61/60, and h_S=(1+t)/(2M).
The difference from T-16t is at most

    223033/24000+(79/10)t-(27/4)M-(2511/400)(1+t)/M
      <f(t):=93/10+(79/10)t-(27/4)M-(25/4)(1+t)/M.

The function f increases on [0,1], because

    f'(t)>=79/10-(27/4)t-(25/4)(1-t)>=23/20>0.

Thus f(t)<=f(1)=86/5-13sqrt(2)<-1. This proves the whole
endpoint-owned left family, retaining its actual signed slope.

### C.7. Complete negative assembly

The negative shallow original-owner list consists of E-owned left,
E-owned up, S-owned northwest, and S-owned northeast. The left case
is Section 6. Here is the full exclusion of the other directions.
An E-owned right normal has center projection at most
-2/5+(7/100)(197/120)<0; an E-owned downward normal has projection
at most (7/100)(91/60)-19/40<0. The S-owned southeast axis has
negative projection. For the remaining S-owned southwest axis
(-q,-p), where p>=q, even the inset support gives

    qD-pV-g(p+q) <=(503/480)q-(453/480)p
                     <=5p/48<1/2=H_S((-q,-p)).

Thus this axis cannot separate the original pair. This proves the
four-case list, including zero components through the coordinate cases.
A physical S-owned northwest separator implies (2),
so Section 3 applies. E-owned up is proved in
Parts D and E. S-owned northeast is proved in
Part F. Together these, the complete steep
proof above, z=-1 and z=0 establish the entire negative outer envelope.

## D. Negative shallow slopes: endpoint-owned upward separators

Put

    A=46, B=27/2, K=207/16, Q=1105/256, r=sqrt(Q), T=211/4.

At the negative shallow shoulder-owned target direction, write

    a^2+b^2=1, a>=b>=0, t=b/a, M=1/a=sqrt(1+t^2),
    m=(1,-t), u_S=(a,-b), v_S=(b,a), k=K/a.

The original endpoint frame, reduced modulo a quarter turn, is

    u_E=(1,e)/N, v_E=(-e,1)/N,
    |e|<=7/100, N=sqrt(1+e^2).

The genuine E-owned upward separator is n=(-e,1). Its length need
not be one: the nonnegative multiplier k is applied to its homogeneous
physical separator inequality. No other frame is substituted for E.

### D.1. Exact scalar reduction, with both frame signs retained

Let E,S have centers (x,y),(X,Y), and put

    F=A(x-h_E)+B[X-tY-H_S(m)].

Containment in q_E=A e_x-kn and q_S=Bm+kn, together with the original
separator, gives F<=Phi(e,t), where

    Phi(e,t)=
      r sqrt(A^2+2Ake+k^2(1+e^2))
        -A(1+max(e,0))/N-kN
      +r sqrt((B-ke)^2+(k-Bt)^2)
        -BM-(k/M)[1-et+max(-e-t,0)].               (1)

Here k depends on t, and is held fixed in differentiation with respect
to e. The exact support formulas follow from the following coordinates:

    q_E in E's frame: A/N, -(Ae+kN^2)/N;
    q_S in S's frame: BM-k(e+t)/M, k(1-et)/M.

The first coordinate of q_S is positive: it is
B/a-K(e+t), bounded below by B sqrt(2)-K(107/100)>0;
its derivative with respect to t is B t/sqrt(1+t^2)-K<0.
The other displayed magnitudes are positive as well.
Thus (1) retains both changes at e=0 and e=-t.

We prove

    Phi(e,t)<=Phi(0,t)       (|e|<=7/100, 0<=t<=1).  (2)

### D.2. Negative endpoint slopes

Put delta=-e in [0,7/100], and set

    p=A/K=32/9, q=B/K=24/23,
    f_E=(pa-delta)/sqrt((pa-delta)^2+1),
    f_S=(qa+delta)/sqrt((qa+delta)^2+(1-qb)^2).

These are the horizontal-component-to-norm ratios of q_E and q_S.
Their components are positive; in particular 1-qb>0. Off the two
break lines, differentiation of (1) gives

    Phi_e >= k{r(f_E-f_S)+b}-161/50.               (3)

Indeed the two norm derivatives give rk(f_E-f_S). The final support
term has derivative at least kb, with an additional positive ka
when e<-t. The remaining two derivatives are
-A delta/N^3+k delta/N>=-A(7/100)=-161/50.

The bracket in (3) is greater than 1/4 on its entire interval. The
following four rows are exact sufficient bounds:

| b interval | lower f_E | upper f_S | lower r(f_E-f_S)+b |
|---|---:|---:|---:|
| [0,1/10] | 19/20 | 4/5 | 3/10 |
| [1/10,2/5] | 19/20 | 7/8 | 1/4 |
| [2/5,1/2] | 18/19 | 1 | 331/1140 |
| [1/2,1/sqrt(2)] | 12/13 | 1 | 53/156 |

All comparisons involving the ratios are strict. Here are full checks.

For b<=2/5, a>9/10, so pa-delta>313/100>31/10 and f_E>19/20,
using 39(31/10)^2>19^2. For b<=1/2, a>6/7 gives
pa-delta>6253/2100>89/30 and f_E>18/19, using
37(89/30)^2>18^2. On the whole interval a>7/10 gives
pa-delta>2177/900>12/5 and hence f_E>12/13.

For the upper bounds on f_S, its unsquared ratio is

    R(b,delta)=(q sqrt(1-b^2)+delta)/(1-qb).

It increases in delta and b; its b derivative has numerator
q[(q-b)/a+delta]>0. For b<=1/10,

    R <=(q+7/100)/(1-q/10)=2561/2060<4/3,

so f_S<4/5. At b=2/5 use a=sqrt(21)/5<11/12 to obtain

    R <=2361/1340<9/5<7/sqrt(15),

so f_S<7/8. The last comparison follows from 81/25<49/15.
For the first two rows use r>2 and the positive difference between
the displayed ratio bounds. For the last two rows use r<25/12:

    2/5-(25/12)(1/19)=331/1140>1/4,
    1/2-(25/12)(1/13)=53/156>1/4.

Consequently (3) is strictly positive, with the uniform estimate

    Phi_e > k/4-161/50 >= K/4-161/50=23/1600>0.     (4)

This proves that Phi increases throughout the negative e interval,
including across e=-t by continuity.

### D.3. Positive endpoint slopes

For e>0, e+t>0. The first norm derivative is at most rk.
The second norm derivative equals -rk f_S^+, where

    f_S^+=(qa-e)/sqrt((qa-e)^2+(1-qb)^2)>1/2.

For the last inequality, a>7/10 gives
qa-e>1519/2300>3/5, whereas 0<1-qb<=1. Thus
f_S^+>3/sqrt(34)>1/2.

Also

    (1-e)/N^3 >93/101>23/25,

using N^3<101/100. Hence the derivative of
-A(1+e)/N is less than -1058/25, the derivative of -kN is
nonpositive, and the final support derivative is kb. Therefore

    Phi_e <(r/2+b)k-1058/25
           <(25/24+3/4)(39/2)-1058/25
           =-2953/400<0.                         (5)

Here b<=1/sqrt(2)<3/4 and k=K/a<=K sqrt(2)<39/2.
Thus Phi decreases on the positive e interval. Together with (4)
and continuity at zero, this proves (2).

### D.4. The aligned caller is exactly the previously proved scalar

At e=0, formula (1) becomes

    Phi(0,t)=r sqrt(A^2+k^2)-A-k
              +r sqrt(B^2+(k-Bt)^2)-BM-k/M.

Since k/M=K, this is exactly the containment-plus-separation upper
bound in Part E. Multiplication by a
produces that note's F(b). Its two-interval convexity proof establishes

    Phi(0,t)<=T-16t,

strictly for t>0. Therefore the desired negative shallow envelope
holds for EVERY original E-owned upward separator, with its actual
frame retained. At t=0 the ordinary physical weighted pair cap applies.

## E. The aligned endpoint inequality

Put A=46, B=27/2, K=207/16, Q=1105/256, r=sqrt(Q), T=211/4.
Suppose E is aligned, S has side (a,-b), where a>=b>=0,
a²+b²=1, and E,S are physically separated upward by e_y.
Put t=b/a and use the nonnegative separator multiplier k=K/a.

At the shoulder-owned target direction m=(1,-t), its support is
H_S(m)=1/(2a). The two center coefficient vectors are

    q_E=(A,-k), q_S=(B,k-Bt).

The E support penalty is A+k. In the actual S frame,
q_S has positive components B/a-kb and ka (B-Kb>0), so its
total penalty is B/a+ka=B/a+K. Thus the desired target is bounded
by a scalar which, after multiplication by a, is at most Ta-16b
if and only if F(b)<=0, where

    F(b)=23Q sqrt(1-d b²)+9Q sqrt(1-c b)
         -M sqrt(1-b²)-N+16b,
    d=1024/1105, c=1104/1105,
    M=1787/16, N=423/16, 0<=b<=1/sqrt(2).

Here F(0)=0. The following two-interval convexity proof shows F(b)<0
for every b>0.

### E.1. Convexity

Let

    U(b)=92[(1-b²)/(1-d b²)]^(3/2),
    V(b)=(42849/4420)[(1-b²)/(1-c b)]^(3/2).

Direct differentiation gives

    (1-b²)^(3/2) F''(b)=M-U(b)-V(b).

U decreases. V increases on this interval: the numerator of the
derivative of its base ratio is c(1+b²)-2b, decreasing here and
bounded below by 3c/2-sqrt(2)>297/200-10/7>0.

For 0<=b<=1/2,

    U<=92,
    V<(97/10)(3/2)^(3/2)<(97/10)(15/8)=291/16.

Their sum is less than 1763/16<M=1787/16.

For 1/2<=b<=1/sqrt(2), put u=1105/1132. Then

    U<=92u^(3/2)<=46u(1+u)<89.

The final comparison is
92*2471885<89*2562848. Also c<1 gives
(1-b²)/(1-cb)<1+b<12/7, and sqrt(12/7)<4/3, hence

    V<(97/10)(16/7)=776/35.

The sum is less than 3891/35<1787/16. Thus F is strictly convex
throughout its full interval.

### E.2. Upper endpoint

At b=a=1/sqrt(2), the first radical contribution is

    r sqrt(A²/2+K²)<291/4.

Its square is 346635185/65536, less than 84681/16.
The second radical contribution obeys

    r sqrt(B²+K²-sqrt(2)BK)<211/10,

using sqrt(2)>24/17: its squared upper bound is
495589185/1114112<44521/100.
Therefore their sum is less than 1877/20=93.85.
The subtracted target is

    (M-16)/sqrt(2)+N
      >(1531/16)(707/1000)+423/16
       =1505417/16000=94.0885625.

Thus F(1/sqrt(2))<0. Convexity and F(0)=0 give F(b)<0 for b>0.
At b=0 the ordinary cap applies, with equality only in its stated
sharp aligned configuration.

This proves the negative shallow envelope T-16t for the aligned
upward endpoint-owned separator. Part D removes the endpoint's small frame deviation; Parts C and F cover
the other actual physical separator families.

## F. Negative shallow slopes: shoulder-owned northeast separators

Put

    Q=1105/256, r=sqrt(Q), A=46, B=27/2,
    K=207/16, T=211/4, L=A+K=943/16,
    G=3177/256.

Let E and S be two original, interior-disjoint unit squares in a disk
of radius R0<=r. The endpoint E has a frame represented, modulo a
quarter turn, by an angle eta with |tan(eta)|<=7/100. No center box
is needed for this particular owner case.

Suppose the shoulder S has side axes

    u=(a,-b), v=(b,a),
    a>=b>=0, a^2+b^2=1,

and the directed physical separator from E to S is the S-owned
northeast axis v. Put t=b/a in [0,1]. Thus

    m=(1,-t)=u/a, n=(t,1)=v/a,
    n.(c_S-c_E)>=H_E(n)+H_S(n).

We prove the negative shallow envelope

    A(x_E-h_E)+B(m.c_S-H_S(m)) <= T-16t.       (1)

It is strict for t>0, already at R0=r. It is strict also at t=0
when R0<r.

### F.1. Exact support reduction

Use the nonnegative multiplier K on the displayed unnormalized
separator n; this is the multiplier K/a on its unit normalization v.
The center coefficient vectors are

    q_E=A e_x-Kn=(A-Kt,-K),
    q_S=Bm+Kn=(B+Kt,K-Bt).

Containment gives q.c_V+H_V(q)<=r|q| for every original square V.
Adding this inequality for the two center coefficients to the
physical separating inequality bounds the left side of (1) by

    r|q_E|+r|q_S|
      -H_E(q_E)-A h_E-KH_E(n)
      -H_S(q_S)-BH_S(m)-KH_S(n).              (2)

In the actual shoulder frame, q_S=(B/a)u+(K/a)v. All coefficients
are positive. Consequently its complete support penalty is

    H_S(q_S)+BH_S(m)+KH_S(n)=(B+K)/a.

Since |q_S|=sqrt(B^2+K^2)/a and

    r sqrt(B^2+K^2)=9Q,
    9Q-B-K=3177/256=G,

the shoulder contribution to (2) is exactly G sqrt(1+t^2).

### F.2. The endpoint support penalty

Write c=cos(|eta|), s=sin(|eta|). Then

    c>99/100, 0<=s<7/100,
    12<K<13, L<59, 33<A-Kt<=46.

We show, uniformly over the complete endpoint frame interval, that

    P_E=H_E((A-Kt,-K))+A h_E+KH_E((t,1))
        >=L-3t.                               (3)

The elementary signs used below are uniform: with p=A-Kt,

    pc-Ks>33(99/100)-13(7/100)>0,
    ps-Kc<46(7/100)-12(99/100)<0,
    c-ts>99/100-7/100>0.

For eta>=0 the endpoint axes are (c,s),(-s,c). Direct substitution
in the square support formula gives

    P_E=Lc+ps.

This is at least L: indeed

    P_E-L=s[p-Ls/(1+c)]>=0,

because p>33 and Ls/(1+c)<413/199<3. The formula includes s=0.

For eta<=0 the endpoint axes are (c,-s),(s,c). There are exactly
two support sign cases.

If s<=tc, direct substitution gives

    P_E=Lc+Kt s.

Therefore

    L-P_E<=L(1-c)=Ls^2/(1+c)
       <= [L(7/100)/(1+c)]t
       < (413/199)t <3t.                       (4)

Here s<=tc<=t was used. At t=0 this branch has s=0 and (3) is
an equality, so the non-strict version of (4) suffices there.

If s>=tc, put alpha=|eta|. Direct substitution instead gives

    P_E=(L-Kt)cos(alpha)+K(1+t)sin(alpha).

This function is strictly increasing on the admitted interval
atan(t)<=alpha<=atan(7/100), because its derivative is at least

    -59(7/100)+12(99/100)>0.

Its minimum is consequently at alpha=atan(t), where s=tc and the
preceding branch applies. This proves (3) in every orientation.

### F.3. A single convex chord

By (2)--(3), the left side of (1) is at most Phi(t)+3t, where

    Phi(t)=r sqrt((A-Kt)^2+K^2)-L+G sqrt(1+t^2).

This function is convex on [0,1], as a positive sum of norms of
affine vectors. The exact identities

    r sqrt(A^2+K^2)=23Q,
    23Q-L+G=T

give Phi(0)=T.

At t=1, the first radical is less than 74: its square is

    356572450/65536 < 5476=74^2,

since 5476*65536-356572450=2302686>0. Also G<25/2 and sqrt(2)<10/7.
It follows that

    Phi(1)<74+125/7-943/16=3687/112
          <3780/112=T-19.

Convexity now gives Phi(t)<T-19t for every 0<t<=1. Adding the
3t loss allowed in (3) proves (1), strictly for every t>0.

At t=0 the same formulas give the non-strict bound T. If R0<r,
using R0 rather than r in (2) makes the result strict because
|q_E|+|q_S|>0. This proves the stated strictness throughout.

## G. Complete assembly and strictness

Part A proves the envelope for every positive slope by checking the
original shoulder's positive side-axis direction and zero. Part B proves
the fixed negative break of the target at z=-1. Part C reduces the
remaining negative half-line to the original shoulder's single negative
side-axis slope.

For a steep negative owned slope, Part C's horizontal-inset, vertical-inset
and northwest-inset cases are an exhaustive separating-axis cover.
For a shallow negative owned slope, the original physical owner list is
exhaustive: endpoint-left and shoulder-northwest are in Part C,
endpoint-up is in Parts D and E, and shoulder-northeast is in Part F.
The sign exclusions are printed with the list. Thus every real z is covered.

Each nonzero owned slope and the fixed slope -1 has a strict bound already
in the closed Q-disk. The intervening affine intervals inherit strictness
away from zero; the eventual slopes point toward minus infinity. At zero,
the weighted physical pair cap gives the asserted inequality and equality.
If R<r, that cap is strict at zero too. This proves the outer-envelope
theorem, including its entire boundary and strict-radius statements.

The proofs use no interval certificate, numerical search, unprinted
multiplier row, or assumption that the two original frames coincide.
Their role in the five-square theorem is the cancellation in
[FIVE_SQUARE_CAP.md](FIVE_SQUARE_CAP.md).
