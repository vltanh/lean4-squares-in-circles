# Whole-interval hand inequalities for an opposite-owned boundary star

Date: October 28, 2026 UTC. Author: root continuation.

**Status: complete proposed hand scalar theorem, frozen for separate
full independent review and root adoption.** Every proof is over a
whole real interval. The elementary polynomial calculations are printed
below and require no interval tree, sampled pose, or executable checker.
The returned port box is deliberately wider than the older certificate's
box; the separate original-star assembly uses the stronger geometric
exit appropriate to this box.

## 1. Complete scalar statement

Let real A,F,p,V satisfy

    -1/60<=A<=1/60, 37/50<=F<=1,
    13/40<=p<=1, 17/4<=V<=1105/256.

Define the same unchanged scalars as in the old original-star chart:

    L=sqrt(1+p^2), N=sqrt(A^2+F^2),
    H=(Ap+F)/L, z=(Fp-A)/L,
    S=H+1, W=sqrt(V-S^2),
    lambda=zS/W-H, eta=z+1-W.

Assume exactly the guards

    N<1, 1/2<H<33/35, z>0,
    0<=lambda<=1, 0<=eta<=1.                          (1)

Write

    B=1-F, D=1-B-(3/5)B^2,
    vbar=B(1-p)/(pD), kappa=sqrt(V-1)-1.

Then

    0<eta<1, 0<=lambda<eta,
    vbar<p/5, vbar<3/25,
    lambda/eta<7p/10,
    (p-v)/(1+pv)>7p/10 for every 0<=v<=vbar.          (2)

The entire far return satisfies

    h_far=[S(1-lambda)-(W-1)eta]
               /sqrt((1-lambda)^2+eta^2)>61/60.       (3)

For either of the two remaining returns put

    near: q_m=H;       side: q_m=zS/W;
    Q_1=(p q_m+1-W)/L,
    Q_2=(q_m+p(W-1))/L.

Impose only that return's literal boundary-contact guard

    q_m^2+(W-1)^2>=kappa^2.                          (4)

For every unchanged 0<=v<=vbar, the actual rotation

    Q_n=(Q_1-vQ_2)/sqrt(1+v^2),
    Q_f=(vQ_1+Q_2)/sqrt(1+v^2)

satisfies the complete bounds

    5/32<Q_n<1,       0<Q_f<1.                       (5)

This is an algebraic theorem about the displayed scalars and all their
closed input endpoints. No geometric realization is assumed for every
point of this larger scalar domain. The source of the identical chart
is identified only for provenance:

    S123_OPPOSITE_OWNED_BOUNDARY_PORT_SCALAR_CERTIFICATE.md.

No conclusion or computation from that certificate is used below.

## 2. Elementary bounds and the proper-length endpoints

The definitions give

    H^2+z^2=N^2<1, z=pH-AL,
    W^2>=17/4-(68/35)^2=2329/4900>(67/100)^2,
    W<23/16, S<2, L<=sqrt(2)<99/70,
    z<H+1/40.                                       (6)

For the last comparison, sqrt(2)/60<1/40. Also S>3/2 and
V<9/2 imply S>W. The identity

    lambda=1-S(1-eta)/W                              (7)

shows that eta=0 contradicts lambda>=0. If eta=1, then z=W
and N^2=V-2H-1>191/140>1, impossible. Thus 0<eta<1, and
(7) gives

    lambda-eta=-(S-W)(1-eta)/W<0,
    0<=lambda<eta<1.                                 (8)

In particular all denominators in (2),(3) are positive. The guard
lambda>=0 also gives z>=HW/S>1/6>1/40, using (6).

We will repeatedly use the following elementary curvature estimate.
If a twice differentiable real function f has f''>=m>0 throughout
an interval, then at any interior base point x0,

    f(x)>=f(x0)+f'(x0)(x-x0)+(m/2)(x-x0)^2
         >=f(x0)-f'(x0)^2/(2m).                      (9)

Both inequalities follow by integration and completing the square;
they hold on both sides of x0 and at both closed interval endpoints.

## 3. A whole-domain upper bound for B

The exact square-root comparison yields

    N<=F+A^2/(2F)<F+1/5000.

Since lambda>=0 gives zS>=HW, squaring and adding H^2S^2
to both sides yields sqrt(V)<=N+N/H. Consequently

    sqrt(V)<=N+LN/(F+Ap)
       <F+L+p/30+3/5000.                             (10)

Here F-p/60>=217/300, and the additional fraction is bounded by

    L(p/60+1/5000)/(F-p/60)
      <=99p/3038+297/759500<p/30+1/2500.

These comparisons hold without choosing A's sign. Finally
sqrt(V)>=sqrt(17)/2>103/50 and L<=1+p^2/2 imply

    B<K(p):=p^2/2+p/30-297/5000.                     (11)

This single bound will control all channel rotations.

## 4. The full rotation majorant is below both p/5 and 3/25

Since 0<=B<=13/50,

    D>=8743/12500>0,
    D>=1-(289/250)B.                                 (12)

First prove vbar<p/5, equivalently p^2D>5B(1-p).
For p>=3/4, the entire interval follows at once from

    p^2D-5B(1-p)>=13687/200000>0.                     (13)

For 13/40<=p<=3/4, (11),(12) reduce the claim to P(p)>0,
where the exact expanded polynomial is

    P(p)=p^2-K(p)[5(1-p)+(289/250)p^2]
        =-(289/500)p^4+(18461/7500)p^3
          -(4742501/3750000)p^2-(1391/3000)p+297/1000.

Its second derivative is a concave quadratic. At the two endpoints
its excess over 3/2 is respectively

    568667/15000000,       11796623/3750000.

Thus P''>3/2 on the whole interval. At p0=11/20,

    P(p0)=96344941/6000000000>1/100,
    P'(p0)=-26617/4687500,       |P'(p0)|<1/100.

Equation (9) proves P>1/100-1/30000>0. This proves the
first majorant bound everywhere.

For vbar<3/25, p<=3/5 is already covered by vbar<p/5.
For p>=4/5, (12) gives

    vbar<=3250(1-p)/(8743p)<=1625/17486<3/25.

On the entire intermediate interval 3/5<=p<=4/5, multiply
(3/25)pD-B(1-p) by 6250 and use (11),(12). It is strictly
greater than the polynomial

    T(p)=750p-K(p)(6250-5383p)
        =1485/4+(3328747/15000)p
          -(88367/30)p^2+(5383/2)p^3.                (14)

Its second derivative is increasing, with

    T''(3/5)=56974/15>3700.

At p0=2/3 one has

    T(p0)=127154/16875>7,
    T'(p0)=-5257759/45000,       |T'(p0)|<120.

Equation (9) now gives T>7-120^2/7400>0. Therefore both
majorant bounds in (2) hold throughout the original closed p range.

To obtain the stronger slope bound, first suppose p<=3/4. Then

    (p-v)/(1+pv)>(4p/5)/(1+p^2/5)
                  >=(64/89)p>(7/10)p.               (15)

For p>=3/4, use v<=vbar<=3250(1-p)/(8743p). The function
(1-p)(10+7p^2) is strictly decreasing and p^2 is increasing.
At p=3/4 the exact positive difference is

    26229p^2-3250(1-p)(10+7p^2)=219494/64>0.

Hence throughout this interval v<3p/(10+7p^2), which is
exactly the strict inequality (15) after rearrangement.

## 5. A whole-interval bound for lambda/eta

Put c=1/40. For fixed H,W consider the quadratic

    F_H,W(z)=7(z-c)(z+1-W)-10H(zS/W-H).              (16)

It is strictly decreasing for 0<z<=H+1/30. Indeed

    W*dF_H,W/dz
       <=7W(2H+25/24-W)-10H(H+1)
       <=(7/4)(2H+25/24)^2-10H(H+1)<0.             (17)

The negative of the last expression is increasing for H>=1/2
and at H=1/2 equals 473/2304>0. Thus it suffices to prove
F_H,W(Z)>0 at any upper bound Z for the actual z in this interval.

Use the following three entire H intervals and rational upper bounds:

| Whole H interval | Z |
| --- | --- |
| [1/2,7/10] | H+1/40 |
| [7/10,9/10] | (5-4H)/3 |
| [9/10,33/35] | (13-12H)/5 |

The first follows from (6). The other two follow from H^2+z^2<1
by taking dot products with the unit vectors (4/5,3/5) and
(12/13,5/13). Every displayed Z is positive, greater than c,
and at most H+1/30 on its whole interval. Thus (17) applies
up to each comparison point without a gap between intervals.

Here are full polynomial details proving the needed endpoint
comparisons. They also make every rational arithmetic check finite
and directly readable; no subdivision tree is a premise.

For any one displayed affine function Z(H), set

    A_Z(H)=7(Z-c)(Z+1)+10H^2,
    B_Z(H,V)=7(Z-c)(V-(H+1)^2)+10HZ(H+1),
    P_Z,V(H)=A_Z(H)^2(V-(H+1)^2)-B_Z(H,V)^2.         (18)

For fixed H, the expression

    W*F_H,W(Z)=A_Z(H)W-7(Z-c)W^2-10HZ(H+1)

is concave in W. It is therefore enough to check its two endpoints
W=sqrt(V_i-(H+1)^2), V_i=17/4 or 1105/256. At either endpoint
A_Z>0 and B_Z>0, so P_Z,V_i>0 proves the desired comparison
by squaring positive quantities. All square roots are real by (6).

### 5.1 First whole H interval

For Z=H+c divide P_Z,V by H^2 and call the result P_0,V.
This is a quartic. With x=5(H-1/2) in[0,1], its second
derivative with respect to H is exactly

    V=17/4:
      -2237389/800-(83727/50)x-(3576/25)x^2;
    V=1105/256:
      -8844581/3200-(83727/50)x-(3576/25)x^2.

Thus both quartics are strictly concave. Their endpoint pairs are

    V=17/4:       20633/1600, 141117/8000;
    V=1105/256:   14186939/1638400, 174299623/8192000.

All are positive, so both quartics are positive throughout the
whole first interval.

### 5.2 Middle whole H interval

For Z=(5-4H)/3 use P=P_Z,V without division. With
x=5(H-7/10), direct expansion of (18) gives

    P''(H)=a0+a1*x+a2*x^2+a3*x^3+a4*x^4.

For the two endpoints V the coefficient rows are exactly

    V=17/4:
      a0=154260697/108000, a1=-51418207/18000,
      a2=28939603/54000, a3=-140548/675, a4=-3368/135;
    V=1105/256:
      a0=6665650427/4608000, a1=-622449049/216000,
      a2=3709771/6750, a3=-140548/675, a4=-3368/135.

In both rows a1<-2800, 0<a2<550 and a3,a4<0. Therefore

    P'''(H)<5(-2800+1100)=-8500                     (19)

throughout this whole interval. The following exact evaluations
complete the argument:

| Quantity | V=17/4 | V=1105/256 |
| --- | --- | --- |
| P(3/4) | 191692471/33177600 | 24637846517/2831155200 |
| P'(3/4) | -55895983/2073600 | -535751243/132710400 |
| P''(4/5) | 1532869/14400 | 106441759/921600 |
| P(4/5) | 16290811/3200000 | 120267654691/13107200000 |
| P'(4/5) | -699857/120000 | 2165777947/122880000 |
| P(9/10) | 3024983/1012500 | 3346678414481/353894400000 |

On [7/10,4/5], (19) and the table give P''>100,
P(3/4)>5 and |P'(3/4)|<27. Equation (9) proves

    P>5-27^2/200=271/200>0.                          (20)

On [4/5,9/10], both endpoint values are greater than two.
If the minimum is at an interior point H*, then P''(H*)>=0.
Since P'' is strictly decreasing by (19), P''>=0 from 4/5
to H*. Thus P'(H)>=P'(4/5)>-6 on that interval, and

    P(H*)>=P(4/5)-6(9/10-4/5)>5-3/5>0.

This includes every possible interior minimum, including a zero
second derivative. Hence both endpoint polynomials are positive
on the entire middle interval.

### 5.3 Last whole H interval

For Z=(13-12H)/5 again use P=P_Z,V. Put
x=(70/3)(H-9/10), so x in[0,1]. The coefficients of P''
in powers of x are

    V=17/4:
      -2681433373/2500000, -26702000919/17500000,
       24378686721/245000000, -702339201/53593750,
      -98109063/375156250;
    V=1105/256:
      -355786654749/320000000, -108416484261/70000000,
       3149991477/30625000, -702339201/53593750,
      -98109063/375156250.

In each row the constant is less than -1000, the quadratic
coefficient is between zero and 103, and every other coefficient
is negative. Thus P''<-897<0 on the whole interval. Its exact
endpoint pairs are

    V=17/4:
      332689031/39062500,
      16778937059585951/1176490000000000;
    V=1105/256:
      609426294332031/40960000000000,
      103180290190749497871/4818903040000000000.

They are positive, so strict concavity proves P>0 throughout.

The three intervals therefore prove F_H,W(z)>0 for every
original scalar choice, with both V endpoints and all internal
H boundaries included. Since eta>0 and z-c<pH, (16) gives

    lambda/eta<7(z-c)/(10H)<7p/10.                   (21)

This proves the remaining ratio assertion in (2).


## 6. The entire far support by three elementary height bands

Set t=(1-lambda)/eta>0. Equations (7),(8) give

    t=S(W-z)/[W(1-W+z)],
    h_far=(St+1-W)/sqrt(1+t^2).                      (22)

For fixed S this t increases with W and decreases with z wherever
0<W-z<1. For example, writing u=W-z makes its W derivative
have positive numerator u^2+z; its z derivative has negative sign.
The comparisons below stay in that positive-denominator domain.

For fixed positive S and fixed W, the last function in (22), on
t>=t0, has its minimum at t0 or at its limit S: its derivative
has numerator S-(1-W)t and hence at most one zero, which when
present is a maximum. These facts justify each entire-band bound.

If H<=3/5, then S>3/2, W>=13/10, z<5/8 and W<23/16.
Thus t>405/169>2 and

    h_far>min(3/2,41/(16sqrt(5)))>61/60.              (23)

If 3/5<=H<=17/25, then S>=8/5, W>119/100,
z<141/200 and W<4/3. Therefore

    t>15520/12257>5/4,
    h_far>min(8/5,20/(3sqrt(41)))>61/60.              (24)

The last squared comparison has reserve 7439/147600>0.

For 17/25<=H<33/35, first prove t>1. Let

    W0=sqrt(17/4-S^2), J(W)=W(H+W)/(S+W).

J is strictly increasing for W>0. The inequality t>1 is
equivalent to J(W)>z. Since z<sqrt(1-H^2), it suffices to
compare J(W0) with that last root. The exact squared difference
after multiplying by (S+W0)^2 is

    W0^2(H+W0)^2-(S+W0)^2(1-H^2)=C(S)+D(S)W0,
    C(S)=2S^3-S^2-17S+357/16,
    D(S)=(-4S^2+17S-17)/2.                           (25)

On [42/25,68/35], D is positive: its numerator is concave,
and its endpoint values are 169/625 and 1139/1225. Also C''>18.
At S0=15/8, C=27/256 and C'=11/32. Equation (9) gives

    C>=27/256-(11/32)^2/36=3767/36864>0.

This proves t>1. Finally W<49/40 on this whole H interval,
since W^2<=239041/160000<240100/160000. Hence

    h_far>min(42/25,291/(200sqrt(2)))>61/60.           (26)

The last squared reserve is 17929/720000>0. The bands cover
every original H and include both join values, proving (3).

## 7. Basic bounds for both remaining return points

First, every side scalar q_m=zS/W satisfies q_m<13/12.
Using N<1, it is enough to prove

    169(17/4-(H+1)^2)-144(1-H^2)(H+1)^2>0.

The expanded polynomial is

    D0(H)=144H^4+288H^3-169H^2-626H+1621/4.

For H>=1/2 its second derivative is at least 958>900.
At H0=33/40,

    D0(H0)=351829/160000>2,
    D0'(H0)=6643/1000,       |D0'(H0)|<7.

Equation (9) gives D0>2-49/1800>0. The near scalar is
even smaller, q_m=H<33/35<13/12. In both cases q_m>1/2.

Put u=1-W<33/100 by (6). Holding q_m,u fixed, the function
(p q_m+u)/sqrt(1+p^2) increases for 0<=p<=1 because its
derivative has numerator q_m-pu>0. Consequently

    Q_1<(13/12+33/100)/sqrt(2)
         =106/(75sqrt(2))<1.                         (27)

The exact squared reserve is 2-(106/75)^2=14/5625>0.
Also Q_2=(q_m-pu)/L>0, since q_m>1/2 and u<33/100.

In the near return Q=P-eta*j, with P=(A,F) and
j=(-1,p)/L. In the side return Q=P+lambda*m-eta*j,
where m=(p,1)/L. Thus, after the unchanged rotation,

    near Q_f=[vA+F+eta(v-p)/L]/sqrt(1+v^2);
    side Q_f=[vA+F+
             (lambda(1+pv)+eta(v-p))/L]/sqrt(1+v^2).

By (2),(21), the extra term is strictly negative in either
case. Cauchy--Schwarz gives

    Q_f<(vA+F)/sqrt(1+v^2)<=N<1.                     (28)

In particular Q_2<1 follows by taking v=0. Below we prove
Q_1>0 and Q_n>5/32; then Q_f>0 follows as well, since
v>=0 and Q_2>0. Also Q_n<=Q_1<1.

## 8. The entire W<=1 return domain

If W<=1, then S^2=V-W^2>=V-1. Thus H>=kappa>4/5,
and u=1-W>=0. Since the side scalar q_m>=H by lambda>=0,
it is enough to bound the near Q_n. Using v<p/5,

    Q_n=[H(p-v)+u(1+pv)]/[Lsqrt(1+v^2)]
       >(16/25)*p/[sqrt(1+p^2)sqrt(1+p^2/25)].       (29)

Now p/sqrt(1+p^2)>=13/sqrt(1769), while
sqrt(1+p^2/25)<=sqrt(26)/5. Therefore

    Q_n>208/[5sqrt(45994)]>1/6.                     (30)

The last squared reserve is 1248^2-25*45994=407654>0.
Thus in this entire domain Q_1>0 and Q_n>1/6>5/32,
for both returns.

The actual near guard (4) always implies W<=1, so this already
covers every near return. To verify that implication exactly,

    |Q|^2=H^2+(W-1)^2=V-2(H+W),
    kappa^2=V-2sqrt(V-1).

Thus (4) gives H+W<=sqrt(V-1), whereas

    (H+W)^2-(V-1)=2H(W-1).

Since H>0, W<=1 follows, including equality.


## 9. Every side return with W>1 has H>23/40

Suppose H<=23/40. From z<H+1/40 the side squared norm is
strictly less than

    G(H)=(H+1/40)^2(H+1)^2/W^2+(W-1)^2.

Hold V fixed while H varies. With z0=H+1/40, its derivative
divided by 2S/W is exactly

    z0*S/W+z0^2*V/W^3-(W-1)>0.                      (31)

Indeed the first term is at least 63/115, whereas W-1<7/16.
Hence G increases on the whole interval [1/2,23/40]. At its
upper endpoint z0=3/5, S=63/40 and

    133/100<W<34/25.

It follows that

    |Q|^2<G(23/40)<(189/266)^2+(9/25)^2<16/25,

whose last reserve is 5011/902500. But kappa>4/5, contrary
to (4). Therefore every remaining side return has

    H>23/40,       1<W<34/25.                        (32)

## 10. One quartic controls the entire remaining side coordinate

Put K=sqrt(V-1), w=W-1 and

    q0=sqrt((K-1)^2-w^2).

By (4), q_m>=q0. The root is real and q0>7/10: use
K-1>4/5 and 0<w<9/25. Also

    9/5<K<73/40,       q0<=K-1<33/40.                (33)

For S=sqrt(K^2+1-W^2), H=S-1, define

    E(K,W)=W*q0^2/(SH)-(W-1)
           =1+W/S-2W(S+1)/(S(K+W)).                 (34)

The identity follows from (K-W)(K+W)=H(S+1).
We prove the whole-rectangle bound

    E(K,W)>13/30
      for 9/5<=K<=73/40, 1<=W<=34/25.               (35)

On this rectangle S>3/2. Differentiating (34) with respect to K
gives the sign of

    2S^2(S+1)-K(K+W)(K+W-2).

The first term is greater than 45/4. The subtracted term is less
than 65/8, using K<2, K+W<13/4 and K+W-2<5/4. Thus E
increases with K, and it suffices to take K=9/5.

For that value, (35) is equivalent, with positive sides, to

    S(43W-17K)<30W(K+W-2).

The positivity includes 43W-17K>0 throughout this rectangle.
After squaring and substituting S^2=K^2+1-W^2, the difference
right minus left is the explicit quartic

    J(W)=2749W^4-(14958/5)W^3-(34337/5)W^2
           +(1394748/125)W-2481354/625.              (36)

For W>=1, J'''=65976W-89748/5>0. Hence on [1,34/25],

    J''>=J''(1)=6518/5>1300.

At W0=11/10,

    J(W0)=370533/10000>37,
    J'(W0)=-21766/125,       |J'(W0)|<175.

Equation (9) yields J>37-175^2/2600>0. This proves (35)
on the whole rectangle, including its four edges.

Return now to the actual scalars. From z=pH-AL and q_m=zS/W,

    Q_1=[W*q_m^2/(SH)-(W-1)]/L+A*q_m/H.

The first bracket is positive by q_m>=q0 and (35). Therefore

    Q_1>=[W*q_m^2/(SH)-(W-1)]/sqrt(2)-q_m/(60H).

The right side is strictly increasing in q_m for q_m>=q0:
its derivative has sign 2W*q_m/(Ssqrt(2))-1/60>0, using
q0>7/10, W>=1 and S<2. It is thus at least its value at q0.
Equations (32)--(35) give

    Q_1>13/(30sqrt(2))-11/460
         >26/85-11/460>7/25.                         (37)

Here 1/sqrt(2)>12/17, and the last exact reserve is 77/39100.

We already know 0<Q_2<1. With v<3/25, (37) proves

    Q_n>(7/25-3/25)/sqrt(1+9/625)
         =4/sqrt(634)>5/32.                          (38)

The squared reserve for the last comparison is
128^2-25*634=534>0. In particular Q_1>0 and Q_f>0.
Together with (27),(28), this proves all of (5) for the remaining
side domain W>1.

## 11. Exact limits of the hand replacement

Sections 2--10 prove (2)--(5) for the complete stated scalar domain,
including every closed box endpoint, lambda=0, W=1, v=0,
v=vbar and both V endpoints. The far denominator never vanishes.
No physical mask, normal or mean is chosen by this theorem.

The old sharper coordinate conclusions 1/8<Q_n<3/4 and
1/10<Q_f<9/10 are not claimed here. They are unnecessary for
the new original-star assembly: the full upper-side loaded-M exit
only needs Q_f<1 and a downward slope at least 1/6, while the
strict-inner contact has a short chord already from (5).

The proof consists of monotonicity, concavity, positive curvature,
the displayed polynomial identities, and exact rational comparisons.
There is no generated finite cover or numerical interval certificate.
Symbolic expansion and rational arithmetic can check the printed
identities; their checker output is not a premise of the proof.
No Lean/Lake, CI, numerical geometric search, old certificate replay,
metadata/count edit, commit or remote operation was performed.
The complete original physical application and independent acceptance
are separate obligations; no original flag is closed by scalars alone.
