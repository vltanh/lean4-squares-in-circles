# A true width-one loaded-intermediate path has endpoint distance below three

Date: October 26, 2026.

**Status: accepted complete hand theorem after full-source and original-domain
reviews in REVIEW_C6_SIDE_PATH_DIAMETER_ROOT_2026_10_26.md and
REVIEW_FOUR_C6_SIDE_PATH_DIAMETER_GLOBAL_2026_10_26.md.** No parent gate is
changed by this manuscript.

Put Q=1105/256. Keep the original compatible physical certificate in
79/40<=R<=sqrt(Q). Let the entire selected positive component be a simple
cycle with at least three positively circle-loaded bodies. Suppose four
consecutive actual bodies are A-B-U-C, where A,B,C have positive total
circle load and U is the original unloaded degree-two side-normal
transmitter. Its true reserve is one.

**Theorem.** The unchanged actual centers satisfy |c_A-c_C|<3.

All physical circle masks, individual zero or positive corner weights,
actual point normals and full side-mean intervals remain. The argument
uses the actual circle contacts at B,C, the actual A/B contact, and the
whole-channel center signs supplied by SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md,
Section 5. It does not change a force, mean, physical body or load. In
particular it does not require a new force equation at A or replace the
true degree-two equation at B.

The proof is geometric after the proper-channel conclusions are supplied.
A crucial exact fact is that the unchanged width-one channel applications
satisfy

    P_C=P_B+d,       |d|=1,
    d.(z-P_B)<=0 for every z in B.

Consequently P_B is the Euclidean nearest point of B to P_C, and

    dist(P_C,B)=1.                                          (1)

This applies equally to a singleton support and every original owned-side
mean, including its endpoints.

## 1. Radius ranges and the hypothetical distant endpoints

Every contained unit has center radius rho satisfying

    rho^2+rho+1/2<=R^2.

If R<sqrt(17)/2, every center radius is below 3/2, proving the theorem.
Assume henceforth R^2>=17/4 and |c_A-c_C|>=3.

Use one of the following three closed radius ranges. Their overlap at an
endpoint is harmless; either corresponding row may be used.

| Range for R^2 | M | lower radius q_* | k_* | j_* | L |
| --- | --- | --- | --- | --- | --- |
| [17/4,429/100] | 151/100 | 17/4 | 43/50 | 18/25 | 6 |
| [429/100,431/100] | 303/200 | 429/100 | 5/6 | 23/30 | 20/3 |
| [431/100,Q] | 91/60 | 431/100 | 33/40 | 39/50 | 55/8 |

In every row R^2<M^2+M+1/2. Hence all actual center radii are strictly
below M, and both hypothetical distant endpoints have radii greater than
3-M>=89/60. Write m=89/60 and M_*=91/60 for the common weak bounds.

Rotate C's own frame so

    c_C=(x,y),       x>=|y|,       x>0.

Its actual circle contact gives

    R^2=(x+1/2)^2+(|y|+1/2)^2.

The endpoint radius bound therefore yields

    x+|y|<Q-1/2-m^2=93089/57600<97/60.                      (2)

In fact

    |y|<7/50,       x>59/40.                               (3)

For the first assertion, if b=|y|>=7/50, then x>=b and (2) put
b in [7/50,97/120]. The convex function (97/60-b)^2+b^2 is strictly below
m^2 at both interval endpoints. At the left endpoint its reserve is
1/7500; at the right it is 6433/7200. This contradicts x^2+b^2>m^2.
The second assertion follows from m^2-(7/50)^2>(59/40)^2.

Let gamma be C's signed radial frame angle, so x=r cos(gamma),
y=r sin(gamma), r=|c_C|. From (3),

    |sin gamma|<42/445<19/200,
    cos gamma>199/200,
    cos|gamma|-sin|gamma|>9/10,
    cos|gamma|+sin|gamma|<11/10,
    |gamma|<1/10.                                          (4)

The last claim follows, for example, from sin(1/10)>19/200 and the
monotonicity of sine on the relevant own-frame interval.

## 2. The actual C application must be its inner upper or lower vertex

Direct d from B to C along the original channel. The exact center
projection gap is

    d.(c_C-c_B)=1+H_C(d)+H_B(d)>=2.

As |c_B|<M, this gives d.c_C>2-M>=29/60. If d_x<=0, (3) instead gives
d.c_C<=|y|<7/50, a contradiction. Thus d_x>0.

If d_y=0, the actual C application is some unchanged mean

    P_C=(x-1/2,y+t),       -1/2<=t<=1/2.

Then P_B=(x-3/2,y+t). Equations (3), x<M_* and |y|<7/50 give

    |P_B|^2<(1/40)^2+(16/25)^2<(129/200)^2.

But every point of the physical boundary square B is within sqrt(2) of
one of its actual circle corners, so

    |P_B|>=R-sqrt(2)>103/50-283/200=129/200.

Here sqrt(17)/2>103/50 and sqrt(2)<283/200 follow by squaring. This
contradiction excludes the entire side-owned mean interval, without
selecting a new mean.

Reflect across C's primary own axis if necessary. We may now write

    d=(cos delta,-sin delta),       0<delta<pi/2,
    P_C=(x-1/2,y+1/2).                                    (5)

This is the original singleton C application. It may coexist with a
physical two-corner circle mask at C. The proof does not change that mask.
The other actual endpoint is P_B=P_C-d.

The actual outward channel normal is Jd=(sin delta,cos delta): its
projection on (5) is positive. The accepted proper-channel center
conclusions therefore give

    d.c_B<0,       (Jd).c_B>=0,
    d.c_C>0,       (Jd).c_C>=0.                            (6)

## 3. A wall containing every possible distant A

Keep the M from the chosen radius row, and define theta by

    cos theta=(9-M^2-r^2)/(2Mr),       0<theta<=theta_0,
    cos theta_0=9/(2M^2)-1.                               (7)

The strict inequality r>3-M makes theta positive. The numerator in (7)
is positive throughout the present range. Since r<M, theta<theta_0 is
also possible, but no strict endpoint estimate is needed below.

Use the orthonormal wall frame

    e=c_C/r,
    f=cos(theta)e-sin(theta)Je,
    n=sin(theta)e+cos(theta)Je.

Its f-axis points approximately right and its n-axis approximately up.
The following bounds hold uniformly for all three rows:

    theta<3/10,       sin theta<3/10,       cos theta>19/20,
    M tan theta<7/15.                                    (8)

They follow by monotonicity in M from M=M_*. At that endpoint
cos(theta_0)=7919/8281. The bound theta_0<3/10 follows from
cos(3/10)<=76427/80000<7919/8281. In particular

    (7/15)^2-(M_* tan(theta_0))^2
      =37623964/14109876225>0.

### 3.1. Complete far-square support estimate

We claim that the whole unchanged A satisfies

    A subset {p:n.p<1/2}.                                 (9)

Write its center, in C's radial frame, as

    c_A=(-rho cos eta,rho sin eta).

The assumed endpoint distance and rho<M imply

    -c_A.e > (9-M^2-r^2)/(2r)=M cos theta.

Thus |eta|<theta. Put

    alpha=theta-eta,       beta=theta-|eta|,
    0<alpha<2theta,        0<beta<=theta.

The radius deficit obeys

    M-rho < M tan(theta) beta.                            (10)

Indeed rho cos(eta)>M cos(theta), and
cos(|eta|)-cos(theta)<=sin(theta)(theta-|eta|).

Let psi in [0,pi/4] be the actual own-frame tilt of A from its radial
axis. Whole-square containment gives

    rho^2+rho(cos psi+sin psi)+1/2<Rbar,
    Rbar=M^2+M+1/2.

Since rho>3-M, its radial factor is less than

    (7M-9)/(3-M)<=97/89.

But cos(1/10)+sin(1/10)>6569/6000>97/89. Hence psi<1/10, and

    cos psi+sin psi-1 >=(9/10)psi.

The latter follows directly from
cos psi>=1-psi^2/2 and sin psi>=psi-psi^3/6. Combining this with
(10) gives

    psi < (10/9) M tan(theta) ((M+rho+1)/rho) beta
         <=(3388/2403) beta <(3/2)beta.                    (11)

The support halfwidth of A in direction n is at most

    H_A(n)<=1/2+(alpha+psi)/2,

using |cos t|+|sin t|<=1+|t| at the actual frame angle. Also
n.c_A=-rho sin(alpha).

If eta>=0, then alpha=beta<=theta. Equations (8),(11) give
H_A(n)<1/2+(5/4)alpha, while

    rho sin(alpha)>=rho cos(theta)alpha>(5/4)alpha.

For the last inequality use rho>m and m(19/20)>5/4.
If eta<0, then theta<alpha<2theta and beta=2theta-alpha. Therefore
alpha+psi<(5/2)theta, whereas
rho sin(alpha)>=rho sin(theta)> (5/4)theta.
Here 2theta<pi/2, so sine is increasing on the needed interval.
Both alternatives prove (9), with all orientations of A retained.

## 4. Exact application bounds in the wall frame

Write P_C=(k,j) in the f,n frame. We prove the k_*,j_* bounds in the
radius table, as well as two useful common bounds:

    k>k_*,       j<j_*,
    0<k<6/5,     j>9/20.                                 (12)

Put zeta=|gamma| and epsilon=sign(gamma), allowing either sign at zero.
In C's radial frame the same application has coordinates

    q=r-(cos zeta)/2+epsilon(sin zeta)/2,
    t=((cos zeta)+epsilon sin zeta)/2.

Thus

    k=q cos theta-t sin theta,
    j=q sin theta+t cos theta.                            (13)

By (4), q>9/10, 9/20<t<11/20, and q>t. Consequently j>9/20 and
k> (9/10)(19/20)-(11/20)(3/10)>2/3. Moreover the actual physical
circle identity and (3) give

    |P_C|^2=R^2-2x+y-|y|<Q-59/20<(6/5)^2.

This proves the common bounds in (12).

### 4.1. Increasing the radial coordinate is the adverse direction

Fix zeta and the actual sign epsilon. Temporarily increase r to the
unique positive solution of

    rbar^2+rbar(cos zeta+sin zeta)+1/2=Rbar.

This is an inequality comparison, not a physical motion or replacement.
The whole interpolation satisfies 3-M<r<=rbar<=M. Define theta from
(7) at each comparison value. If

    K=(9-M^2+r^2)/(2Mr^2),

then

    theta_r=K/sin(theta),       K>=9/(2M^3)>5/4.

In particular theta_r>25/6. Also, from (8),(13),

    j theta_r=K(q+t cot theta)>(5/4)(9/10+27/20)=45/16.

Differentiating the unchanged formulas (13) with zeta fixed gives

    k_r=cos(theta)-j theta_r<0,
    j_r=sin(theta)+k theta_r>0.

Therefore this radial comparison only decreases k and increases j.

### 4.2. At the enlarged radius, zero own-frame tilt is the adverse endpoint

Now keep the enlarged circle equation and vary zeta between zero and
its actual value. Write

    T=cos zeta+sin zeta,       D=cos zeta-sin zeta,
    r_zeta=-rho_1,       rho_1=rD/(2r+T)>3/10.

The last bound uses r>m, D>9/10, T<11/10 and M<=M_*.
Along this comparison theta_zeta=-rho_1 theta_r.

For epsilon=+1,

    q_zeta=-rho_1+T/2>0,       t_zeta=D/2<=1/2.

The bounds above give

    k_zeta>-(3/10)(1/2)+(3/10)(45/16)>0,
    j_zeta<(3/10)(11/20)+1/2-(3/10)(2/3)(25/6)<0.

For epsilon=-1,

    q_zeta=-rho_1-D/2,       t_zeta=-T/2,

and hence

    k_zeta>rho_1(45/16-1)-1/2>7/160>0,
    j_zeta<0.

All intermediate values retain the inequalities used in Section 4.1.
Thus zero tilt minimizes k and maximizes j, for either original sign.
At that endpoint r=M, and

    k> (M-1/2)C-S/2,
    j< (M-1/2)S+C/2,
    C=9/(2M^2)-1,       S=sqrt(1-C^2).                   (14)

For transparency, the entire fixed arithmetic check of the table uses
these upper bounds on S:

| M | exact C | rational upper S | resulting k lower | resulting j upper |
| --- | --- | --- | --- | --- |
| 151/100 | 22199/22801 | 23/100 | 43/50 | 18/25 |
| 303/200 | 9799/10201 | 7/25 | 5/6 | 23/30 |
| 91/60 | 7919/8281 | 293/1000 | 33/40 | 39/50 |

All S upper bounds are strict by squaring. The positive lower-k reserves
in the three rows are respectively

    38003/4560200,       10207/6120600,       35951/49686000.

The positive upper-j reserves are respectively

    205477/228010000,    332137/153015000,    1974487/496860000.

This proves (12) over each entire radius interval. In particular all
rows have k>33/40 and j<39/50.

## 5. The actual intermediate B must be in the upper-left wall quadrant

Because A meets B and (9) holds, the minimum n-coordinate of B is
strictly less than 1/2. We may use the weak bound

    min_B n.p<=1/2.                                      (15)

Every physical boundary square has center radius at least R-1/sqrt(2).
Here

    |c_B|>103/50-17/24=811/600>27/20.                    (16)

Write d=(cos beta,sin beta) in the wall frame. Equations (5)--(7) give

    beta=theta-gamma-delta,
    -pi/2<beta<2/5.

For the lower bound use d.c_C>0, which implies delta+gamma<pi/2.
For the upper bound use theta<3/10 and |gamma|<1/10.
The actual sign conclusions (6) place c_B in the quadrant having
negative d-coordinate and nonnegative Jd-coordinate.

If beta>=0, this already makes its f-coordinate negative. Suppose its
n-coordinate were negative. Its absolute n-coordinate would then be
less than M_* sin(beta)<2/3. Equation (16) forces its f-coordinate to be
less than -7/6. But

    (P_B)_f=k-cos beta>33/40-1=-7/40.

Thus the f-distance from P_B to c_B exceeds 119/120, impossible for a
point of a unit square, whose center-to-point distance is at most
1/sqrt(2)<17/24. Hence its n-coordinate is nonnegative too.

If beta<0, (6) already makes the n-coordinate positive. Suppose the
f-coordinate were nonnegative. Equation (15) gives

    (c_B)_n<=1/2+1/sqrt(2)<29/24.                          (17)

Put b=-beta in (0,pi/2), and w=P_B-c_B. An actual support point of a
unit square in direction (cos b,-sin b) satisfies

    w_f>=(cos b-sin b)/2,
    w_n<=(cos b-sin b)/2.                                (18)

To see this for every owner and mean, each supporting vertex has radius
1/sqrt(2) about the center and differs in angle by at most pi/4 from the
support normal. The two component extrema on that entire angle interval
are exactly the bounds (18). A side mean is a convex combination of its
two actual supporting vertices, so retains both inequalities.

Since (P_B)_n=j+sin b, equations (12),(18) imply

    (c_B)_n>9/20+(3/2)sin b-(1/2)cos b.

If b>=arctan(9/8), the right side is at least
9/20+19/(2sqrt(145))>29/24, contradicting (17).
The last fixed comparison follows, for example, from sqrt(145)<49/4.
Thus b<arctan(9/8), and consequently

    cos b>33/50,       cos b-sin b>-1/12.

Using k<6/5 and (18),

    (c_B)_f<6/5-33/50+1/24=349/600<7/12.

Together with (17) this gives
|c_B|^2<(7/12)^2+(29/24)^2=1037/576<(27/20)^2,
contrary to (16). Hence the f-coordinate is negative.

We have proved, from the original physical premises and (15),

    (c_B)_f<0,       (c_B)_n>=0.                          (19)

## 6. A complete boundary-square screen

We now prove that (12),(15),(19) imply dist(P_C,B)>1, contrary to (1).
The screen retains every orientation and physical circle mask of B.

Choose actual own axes of B in the wall frame as

    u=(c,s),       v=(-s,c),       c,s>=0,       c^2+s^2=1.

Let P be its minimum-n vertex and write P=(p,l), with l<=1/2. A face
limit c=0 or s=0 is included by choosing the indicated endpoint vertex.
Its four vertices are P,P+u,P+v,P+u+v. Its maximum f-coordinate is at
Q_B=P+u. From (19), its own v-center coordinate is nonnegative. Therefore
one of the following two displayed corners is an actual farthest circle
corner, with equality/ties retained:

    (I)  P+v,       or       (II)  P+u+v.

The proper physical circle equality is used in that original feature;
no mask or load is changed.

### 6.1. Circle corner P+v

This corner has negative f-coordinate, so write

    P+v=(-a,l+c),       a=sqrt(R^2-(l+c)^2)>0.

The rightmost f-coordinate of B is c+s-a.
Since (c_B)_n>=0, l>=-(c+s)/2. If l<=0, then |l+c|<=1, so

    a>=sqrt(17/4-1)>9/5,
    max_B f.p<=sqrt(2)-a<-3/10.

This already separates B from k>33/40 by more than one.
If 0<=l<=1/2, it suffices to prove

    sqrt(17/4-(1/2+c)^2)>c+s+7/40.                        (20)

Here is one fixed quadratic completion proving (20) over the entire
quarter circle. Put

    A0=[[1,1],[1,0]],       b0=(27/20,7/20),
    lambda=23/10,          T0=lambda I-A0.

The matrix T0 is positive definite: its first diagonal is 13/10 and
its determinant is 199/100. For z=(c,s), |z|=1, completing the square
with w=(1/2)T0^{-1}b0 gives

    z^T A0 z+b0.z
      =lambda+(1/4)b0^T T0^{-1}b0-(z-w)^T T0(z-w)
      <=5901/1990.

On the other hand the difference of the two squares in (20) is exactly

    4751/1600-[c^2+2cs+(27/20)c+(7/20)s]
       >=4751/1600-5901/1990=1289/318400>0.

Both square-root sides are positive, proving (20). Consequently
max_B f.p<-7/40, whereas k>33/40. Thus dist(P_C,B)>1 in the whole first
circle-corner alternative.

### 6.2. Circle corner P+u+v: exact position and low-height case

Put T=c+s. This corner's n-coordinate l+T is positive, because
l>=-T/2. Its f-coordinate is negative as well. Indeed if it were
nonnegative, (c_B)_f<0 would bound it by 1/2, and its n-coordinate is
at most 1/2+sqrt(2). Its squared norm would then be at most
5/2+sqrt(2)<17/4, contradicting R^2>=17/4.

Thus write

    P+u+v=(-a,l+T),
    a=sqrt(R^2-(l+T)^2),
    P=(-a-c+s,l),       Q_B=(s-a,l+s).                   (21)

If l<=0, then a>=sqrt(17/4-T^2)>=3/2. Hence max_B f.p=s-a<=-1/2,
which again separates by more than one. Assume 0<=l<=1/2 below.
Throughout this interval

    l+T>=1,       a<sqrt(Q-1)<15/8,
    (l+T)/a>8/15.                                       (22)

### 6.3. The fixed separator when 15c-8s>=0

Use the unit normal (15,-8)/17. Its support on B is attained at Q_B,
because its scalar products with u,v have signs nonnegative, negative.
The unnormalized gap from P_C is

    15k-8j+8l+15a-7s.

Its derivative with respect to l in the comparison (21) is
8-15(l+T)/a<0 by (22). Its least value therefore occurs at l=1/2.
It remains to use the following fixed radical bound for the radius row:

    15sqrt(q_*-(1/2+c+s)^2)-7s>L.                         (23)

The complete proof of (23) is one quadratic estimate. Put
D=s-c, T=s+c=sqrt(2-D^2), and a_L=225+7L, b_L=7L. Expanding gives

    225(1/2+T)^2+(L+7s)^2
      =2123/4+L^2+a_L T+(b_L+(49/2)T)D-225D^2.

Replacing D by |D| can only increase the right side. On 0<=D<=1,

    T<=sqrt(2)-D^2/(2sqrt(2)),       TD<=sqrt(2)D.

Complete the resulting scalar quadratic and use sqrt(2)<99/70 and
1/(2sqrt(2))>7/20. The expression is strictly less than or equal to

    E(L)=2123/4+L^2+(99/70)a_L
          +(b_L+(49/2)(99/70))^2/[4(225+(7/20)a_L)].       (24)

Every bound is in the adverse direction. The exact positive reserves
225q_*-E(L) for the three original radius rows are

    8647147/1188880,
    65497739/96793200,
    13168999/114900800,

respectively. Therefore (23) follows by squaring positive quantities.
This is a fixed continuous quadratic estimate, not a sampled angle or
coefficient-cover premise.

Using (23), the gap at l=1/2 is strictly greater than

    15k_*-8(j_*-1/2)+L.

Its excess over 17 is respectively 7/50, 1/30 and 1/100 in the three
radius rows. The unit-normal gap is thus greater than one, proving
dist(P_C,B)>1 for every orientation with 15c-8s>=0.

### 6.4. The actual own-side separator when 15c-8s<=0

The remaining orientations satisfy c<=8/17 and s>=15/17. Use B's own
unit normal (s,-c), whose support face is P+[0,1]u. Its gap from P_C is

    D(l)=s(k+a+c-s)-c(j-l).

Its derivative is c-s(l+T)/a<0 by (22) and c/s<=8/15. Again its least
value is at l=1/2. Put

    a0=sqrt(R^2-(1/2+c+s)^2),       d0=a0+c-s.

The following fixed lower bounds cover the whole interval 0<=c<=8/17:

    d0>2/5                     for every c;
    d0>9/20                    if 2/5<=c<=1/2;
    d0>19/40                   if 9/20<=c<=1/2.            (25)

For any positive t0, the exact squared difference is

    a0^2-(s-c+t0)^2
      >=2-t0^2-[(1-2t0)c+(1+2t0)s].                    (26)

For t0=2/5, Cauchy-Schwarz bounds the bracket by sqrt(82)/5<46/25.
For t0=9/20 in its stated interval, use c<=1/2 and s<11/12; the
positive reserve in (26) is at least 7/1200. For t0=19/40, use c<=1/2
and s<179/200; the reserve is at least 33/8000. These comparisons prove
(25) even if s-c+t0 is nonpositive.

Finally D(1/2)=s(k+d0)-c(j-1/2), with k>33/40 and j-1/2<7/25.
The full orientation interval has these three elementary estimates:

| c interval | bounds used | strict lower bound for D(1/2) |
| --- | --- | --- |
| [0,2/5] | s>91/100, d0>2/5 | 4011/4000 |
| [2/5,9/20] | s>89/100, d0>9/20 | 807/800 |
| [9/20,8/17] | s>=15/17>22/25, d0>19/40, c<12/25 | 631/625 |

All three bounds exceed one. The full original side-support alternative
therefore also has dist(P_C,B)>1.

Sections 6.1--6.4 exhaust every own orientation, farthest circle corner,
face join and physical circle tie of B. Together they contradict the
unchanged exact channel equation (1).

## 7. Original-domain conclusion and four-load central consequence

The contradiction proves |c_A-c_C|<3 for the entire stated original
width-one path. The proof kept A's actual whole square and A/B contact,
B's actual circle contact and channel support, C's actual circle mask
and support, and the original mean whenever a side was owned. It used
no numerical pose, certificate packet, force deletion, Lean compilation
or CI step.

After independent acceptance, this theorem supplies precisely the side
analogue of LOADED_INTERMEDIATE_DIAGONAL_PATH_DIAMETER.md. Together with
that diagonal theorem, the complete pair covers in
SIX_CYCLE_FOUR_LOAD_DIAGONAL_CENTRAL_CAPACITY_ONE.md extend to both widths
at every actual transmitter:

* In U-A-V-B-D-C-U, the sole remaining loaded opposite pair A,D uses
  D-B-V-A or D-C-U-A. The pairs U,B and V,C retain their two-middle-
  boundary paths.
* In U-A-B-V-C-D-U, the loaded opposite pairs A,C and B,D use the
  corresponding actual paths across either U or V. The U,V pair retains
  its two-middle-boundary path.

Thus every actual core-center pair is below three in either four-load
orbit. The unchanged physical central routing and
SHORT_DIAMETER_CONTACT_RING_CENTRAL_CAPACITY_ONE.md then give central
capacity one, for every original width pattern and physical mask.

The accepted complete side and diagonal cap bounds give capacity one in
each actual exterior channel pocket. The three extras therefore have the
single remaining allocation (n_in,n_U,n_V)=(1,1,1). Excluding that coupled
allocation remains a separate original obligation. This source does not
claim either whole four-load parent, its cap gate, C6.ALL or the coarse
cell closed, and it does not modify a shared ledger.
