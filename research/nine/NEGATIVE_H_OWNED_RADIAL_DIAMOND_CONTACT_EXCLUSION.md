# Physical HK contact excludes a negative H-owned endpoint beside a radial diamond middle

**Status: complete whole-domain hand proof; root and separate independent full source, geometry and exact audits passed.**

Work in the common selected physical certificate, with 79/40 <= R <= sqrt(1105)/16. Let A have its true two positive pair neighbors H,K and a positive circle load at its unique physical corner z_A. Assume c_H dot z_A < 0, HA is an H-owned singleton, and K has two physical circle corners. Suppose additionally that H and K physically touch.

**Theorem.** These conditions are impossible. In particular this excludes the complete H-owned-HA / radial-K branch of the triangle-attached diamond KAB, retaining the true degrees H5,K3,A2, every force at K and H, either physical mask of B, the intact HXY petal, every original mean and all three completion squares.

The proof uses no force equation at K. In fact HK only needs to be a physical contact; no HK load, normal owner or application point is assumed.

NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md, Sections 1–5 and 7, with the higher-degree substitution expressly verified in its Section 9, already excludes R^2 >= 17/4 and all A-owned/shared AK alternatives. Its low-radius residue has exactly the following A/H chart. Section 6 of that source, which requires a degree-two middle body, is not used.

## 1. The unchanged low-radius chart

Put

    q = R^2,  d = sqrt(q−1/4)−1,  N = sqrt(q−9/4),
    (79/40)^2 <= q < 17/4,  91/100 < d < 1.

Reflect the source's radial frame (e,g) to (e,−g). Then

    K = [d,d+1] × [−1/2,1/2],
    A intersect K = Z = (t,1/2),
    H intersect A = Q = (t−s,1/2+c),
    z_A = (t+c,1/2+s),
    c,s > 0,  c^2+s^2=1,  d<t<N<sqrt(2)<10/7.

All displayed points and t are the original applications. In A's own frame its circle coordinates are

    a = 1+tc+s/2,  b = ts−c/2,
    a>b>3/5,  a>3/2,  a^2+b^2=q.

Set

    E(d) = (4d^2−1)/(4d^2+1),  F(d) = 4d/(4d^2+1).

The actual circle equation

    (t+c)^2+(s+1/2)^2 = (d+1)^2+1/4

and t>d imply s<2d(1−c), hence

    0<c<E(d)<3/5,  s>F(d)>4/5.

Write the actual H-to-A normal and H as

    n = (1,M)/sqrt(1+M^2),  j=Jn,
    M = b/[s(t+c)]−c/s,
    H = Q + [−1,0]n + [−1/2−eta,1/2−eta]j.

The original eta is retained. The singleton has |eta|<1/2; all estimates retain the closed interval |eta|<=1/2. Reflection only reverses the name of the old eta. Since b=ts−c/2, the useful exact identity is

    M = 1 − (c/s)[1+(s+1/2)/(t+c)].                         (1)

The inherited actual all-offset pressure bound is, with rho=u/v in A's frame,

    rho = 1/[1+(a/b−1)c/s],
    c_H dot z_A >= q−a−b
       − [(a+b)+(a−b)rho]/[2sqrt(1+rho^2)].                 (2)

Neither (1) nor (2) uses a K force or another loaded body.

## 2. The negative pressure bound c>1/20 transfers without a middle equation

Section 2 of NEGATIVE_H_OWNED_RADIAL_MIDDLE_UNIQUE_RETURN_OWNER_EXCLUSION.md uses precisely the A/H equations above to prove

    c>1/20.                                               (3)

For completeness, if c<=1/20, then a<11/7, b>119/100, a/b<4/3 and c/s<1/19. Thus rho>57/58>49/50. The support expression in (2) decreases with rho throughout this interval. Consequently the pressure is greater than

    Psi_0(q,a) = q−a−b−(99a+b)/(2sqrt(4901)),
    b=sqrt(q−a^2).

On q>=(79/40)^2 and 3/2<=a<=11/7, the whole-rectangle bounds are

    (Psi_0)_a < −1761/4970 < 0,
    (Psi_0)_q > 139/280 > 0.

At q=(79/40)^2, a=11/7, one has b<6/5 and sqrt(4901)>70, giving

    Psi_0 > 6241/1600−11/7−6/5
            −[99(11/7)+6/5]/140
          = 737/78400 > 0.

This contradicts the original negative pressure and proves (3). This reproduction makes explicit that no return force, degree-two K equation or middle-weight interval enters the transfer.

## 3. Actual HK contact gives a necessary reach inequality

Define

    T=t+c,  B=s+1/2,
    X=d−t+s=d−T+c+s.

First X>0. Indeed N<d+1/2 because N^2−(d+1/2)^2=d−5/4<0, and therefore

    X>d−N+s>−1/2+4/5=3/10.

If M<=0, the minimum n-support of K is at (d,1/2). Hence

    min_{x in K} n dot x − n dot Q
       = (X−Mc)/sqrt(1+M^2) > 0.

But every point of H has n-coordinate at most n dot Q. This is a strict separation of the actual H and K, contradicting their physical contact. Thus

    M>0.                                                  (4)

Let r=1/2+eta, retaining its actual value in [0,1]. Since n_x>0 and j_x<0, the maximum x-coordinate of H is at its lower-j endpoint of the HA face, and equals

    max_{x in H} x_x = Q_x + r M/sqrt(1+M^2).

Every point of K has x-coordinate at least d. Therefore actual HK contact implies

    X <= r M/sqrt(1+M^2) <= M/sqrt(1+M^2).

Equivalently, the scalar function

    L(d,c) = X − M/sqrt(1+M^2)                             (5)

must satisfy L(d,c)<=0. This only enlarges the necessary contact condition; it does not change r or choose any HK point or mean.

## 4. Whole-domain monotonicity of the reach obstruction

For scalar comparison use

    s=sqrt(1−c^2),  B=s+1/2,
    T=sqrt((d+1)^2−s^2−s),
    q=(d+1)^2+1/4=T^2+B^2.

Work on the entire enlarged domain 91/100<=d<=1, 0<c<E(d), where t=T−c>d, s>4/5 and c<3/5. At a closed upper radius endpoint d=1 these statements remain valid for c<E(1)=3/5.

Direct differentiation of (1) gives

    X_c=M,
    X_d=1−(d+1)/T<0,
    M_d=cB(d+1)/(sT^3)>0,
    M_c=−[T^2(T+B)−c^2 s q]/(s^3 T^3).                  (6)

The last derivative is strictly negative everywhere in this domain. Indeed T>d+c>9/10+c gives c/T<2/5. Also T+B>11/5 and q<=17/4. Consequently

    c^2 s q/T^2 < (4/25)(17/4)=17/25 < 11/5 < T+B.

Using (5)–(6), wherever M>=0 one has

    L_c=M−M_c/(1+M^2)^(3/2)>0,
    L_d=X_d−M_d/(1+M^2)^(3/2)<0.                         (7)

These comparisons cover the full continuous domain. Increasing d and decreasing c preserve c<E(d), since E increases strictly, and preserve M>0 by (6). Thus from any actual contact point (4), its L-value is bounded below by the value at any compared larger d and smaller c. This is an inequality between scalar necessary conditions, not a motion or re-selection of any actual square.

## 5. Two exact endpoint comparisons

### 5.1. The endpoint d=23/25, c=1/20

At this endpoint,

    s^2=399/400,  s>499/500,
    T^2=2304/625−399/400−s,  B=s+1/2.

The first strict comparison has squared reserve 187/125000. Also T<131/100: substituting s>499/500 into T^2 leaves squared reserve 63/2500. Therefore

    B/T > (749/500)/(131/100)=749/655>8/7,

where the last difference is 3/4585. Since s<1, equation (1) gives

    M<1−(1/20)(1+8/7)=25/28.                              (8)

For X, the exact square comparison is

    (s+91/300)^2−T^2
       =2s^2+(241/150)s+8281/90000−2304/625
       >1829/450000>0.

Every quantity compared is positive. Hence T<s+91/300 and

    X=23/25−T+1/20+s>2/3.

The function M/sqrt(1+M^2) is strictly increasing for all real M. Thus

    L(23/25,1/20)>2/3−25/sqrt(1409)>0.                    (9)

The final positive comparison follows by squaring; its squared reserve is

    4/9−625/1409=11/12681>0.

### 5.2. The endpoint d=1, c=3/40

Here

    s^2=1591/1600,  s>99/100,
    T^2=4−s^2−s,  B=s+1/2,
    T^2+B^2=17/4.

The first strict comparison has squared reserve 571/40000. Moreover B>149/100, so

    2B^2>2(149/100)^2>17/4=T^2+B^2;

the second difference is 951/5000. Thus B>T. With s<1, equation (1) yields

    M<1−2(3/40)=17/20.                                   (10)

The exact comparison for X is

    (s+17/40)^2−T^2=(37/20)s−2929/1600>7/8000>0.

It gives T<s+17/40 and X>13/20. Consequently

    L(1,3/40)>13/20−17/sqrt(689)>0,                       (11)

with squared reserve

    169/400−289/689=841/275600>0.

## 6. HK leaves only a rectangle with strictly positive root pressure

By (3), every actual negative-pressure configuration has c>1/20. If d<=23/25, the full monotonicity (7) and the first endpoint (9) give

    L(d,c)>=L(23/25,1/20)>0,

contradicting the necessary HK condition L<=0. Thus d>23/25.

Likewise if c>=3/40, increasing d to 1 and decreasing c to 3/40 in the scalar comparison gives

    L(d,c)>=L(1,3/40)>0

by (11), another contradiction. Therefore actual HK and negative pressure can remain only in

    23/25<d<1,  1/20<c<3/40.                              (12)

We now prove positive pressure on the entire enlarged closed rectangle d>=23/25, c<=3/40, still within the inherited low-radius A/H chart.

Because t<N<10/7 and s<=1,

    a=1+tc+s/2 < 3/2+(10/7)(3/40)=45/28.

Also

    q=(d+1)^2+1/4 >= 9841/2500,
    b^2=q−a^2 > 9841/2500−(45/28)^2 > (23/20)^2.

The last squared reserve is 7593/245000. Hence a/b<225/161<7/5. Since c<=3/40 gives s>99/100, one has c/s<5/66. The exact ratio in (2) therefore satisfies

    rho>1/[1+(2/5)(5/66)]=33/34>19/20.                    (13)

The support term in (2) decreases with rho in this whole range: its derivative has the sign of (a−b)−(a+b)rho, whereas (a−b)/(a+b)<1/6<19/20. Thus the actual root pressure is strictly greater than

    Psi(q,a)=q−a−b−(39a+b)/(2sqrt(761)),
    b=sqrt(q−a^2).                                       (14)

On the full enlarged rectangle q>=9841/2500, 3/2<=a<=45/28, one has b>23/20 and a/b<7/5. Using 27<sqrt(761)<28 gives the uniform derivatives

    Psi_a < −1−39/56+(55/54)(7/5)=−409/1512<0,
    Psi_q > 1−(55/54)/(23/10)=346/621>0.                 (15)

Therefore the minimum occurs at q_0=9841/2500, a_0=45/28. At that point b_0<7/6; its squared reserve is

    49/36−[9841/2500−(45/28)^2]=33601/4410000>0.

Finally 2sqrt(761)>55, with squared comparison 761−(55/2)^2=19/4>0. Substitution in (14) gives

    Psi(q_0,a_0)
      >9841/2500−45/28−7/6−[39(45/28)+7/6]/55
      =1021/577500>0.                                    (16)

Equations (14)–(16) contradict c_H dot z_A<0. This excludes every point of the whole residual rectangle (12), including every original H-side offset.

## 7. Complete scope and the diamond consequence

The physical HK contact first forces M>0 and the necessary horizontal reach inequality (5), without prescribing a normal owner, a feature, an HK point or an HK mean. The scalar monotonicity and two exact endpoint comparisons exhaust its full low-radius parameter domain. The remaining rectangle has uniformly positive actual root pressure by (16). Hence the entire low-radius radial-K / H-owned-HA domain is impossible.

Combining this with NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md, Sections 7 and 9, includes R^2=17/4 and every larger radius in the common window. Sections 1–5 and 9 of that source already exhaust the other AK owners before producing this chart. Thus no negative unique A with H-owned HA can occur beside a physical radial K that also touches H.

For the actual triangle-attached diamond KAB this is precisely the physical HK edge. H retains true degree five, K true degree three and A true degree two. K's HK,KA,KB forces are never replaced by a two-force equation, and no location or normal is inferred for KB. Neither individual K circle weight is assumed positive. The other endpoint B may have either physical circle mask and retains all its actual forces. H's intact petal, all three arbitrary completion squares and all zero-stress physical contacts remain.

All contact means and eta are original. The enlarged side interval and scalar endpoint bounds are inequalities only. No square is moved, no force deleted, no chord added, no selected normal changed, and no numerical pose or angle cover, Lean compilation or CI is used.
