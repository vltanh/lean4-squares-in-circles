# The entire nonpositive-tangent unique-C far return

Date: October 25, 2026.

**Status: complete hand proof; root analytic/arithmetic audit and separate
independent full saved-source/feature-assembly review passed on October 25,
2026. See REVIEW_ABC_COMPLETE_FAR_RETURN_2026_10_25.md. No roadmap checkbox,
gate ID, accepted count, force or selected normal changes from this feature
exclusion alone.**

Keep the original H--A--B--C--H cycle, the intact HXY petal, genuine
H4/A2/B2/C2 equations, every original positive force and application mean,
all nine squares, and all three completion squares. Use the unchanged
physically unique A,B,C upper-left far chart of
ABC_UPPER_LEFT_FAR_RETURN_SUPPORT_WORKING_2026_10_25.md throughout

    q0=6241/1600 <= q=R^2 <= Q=1105/256.

The original A pressure is negative, HA is H-owned, AB is the B-owned
upper-left contact, and BC is the strict far vertex with k_y<0. This
manuscript concerns the actual epsilon_B=1 circle-corner alternative.
It keeps the entire original HC feature and mean cover.

**Theorem.** Every actual maximum-Jk C side return with k_j<=0, including
the genuinely shared k_j=0 case and every original mean endpoint, is
impossible. Every strict right C endpoint return is also impossible,
for both physical choices U=w+1>0 and U=w<0 of C's circle corner.

The scalar input is deliberately weaker than the unproved proposed
comparison N>=1/2: the original prefix with k_j<=0 forces b>9/10, and
then N>1/4. Actual negative A pressure supplies the rest of the radius
obstruction.

## 1. Unchanged original chart and accepted geometric inputs

Write

    a>b>3/5, a^2+b^2=q, x=a-1,
    P=(x,b-1), T=(x,b),
    f=(s,c), g=(-c,s), c,s>0, c^2+s^2=1,
    rho=c/[c+s(a/b-1)],
    v=1/sqrt(1+rho^2), u=rho*v,
    n=(u,v), j=(-v,u), 0<u<v,
    H=P+[-1,0]n+[r-1,r]j, 0<r<1.

The displayed rho is exactly the original true A2 concurrence identity.
Set

    E=n dot f=su+cv>0, d=n dot g=sv-cu,
    L=T dot f=xs+bc, h=T dot g=-xc+bs,
    H_B=h+1>1/2, beta=sqrt(q-H_B^2)>0,
    tau=beta-L in (0,1), delta=1-tau in (0,1),
    sigma=tau*H_B/beta>0,
    D_k=sqrt(delta^2+sigma^2),
    k=(-delta*f+sigma*g)/D_k.

In particular k_x,k_y<0 and k_n=k dot n<0. Since
j=-d*f+E*g, its tangential component is

    k_j=k dot j=(delta*d+sigma*E)/D_k.          (1)

Thus k_j<=0 implies d<0. No H/B separation inequality or sampled
condition is used in the scalar argument below.

The accepted reflected endpoint-pressure source
ABC_RETURN_OWNER_NONNEGATIVE_ENDPOINT_PRESSURE.md gives the original
C pressure nonnegative. The accepted full far theorem
ABC_FAR_UNIQUE_NONNEGATIVE_ROOT_PROJECTION_EXCLUSION.md and the full
prefix theorem
ABC_UPPER_LEFT_NONNEGATIVE_RETURN_POSITIVE_CONTACT_PROJECTION.md give

    N=P dot n in (0,1/2), m=-P dot j>0.          (2)

The actual negative A pressure is therefore the strict inequality

    Phi(r)=(N-1/2)(N+u+v)
             -(r-1/2-m)(m+v-u)<0.              (3)

Indeed the genuine unique A circle corner is
z_A=P+(1,1)=(N+u+v)n-(m+v-u)j, and its original circle load is positive.

## 2. A whole-prefix bound: k_j<=0 forces b>9/10

Suppose for contradiction that b<=9/10. The original radius window gives

    a^2>=q0-81/100=989/320>49/16,
    a^2<Q-9/25<4.

Hence 7/4<a<2, so 3/4<x<1 and a/b>35/18.

### 2.1. The complete remaining angle interval

The physical B corner gives h>-1/2. If s<=1/4, then

    h=-xc+bs < -3sqrt(15)/16+9/40 < -1/2,

because sqrt(15)>58/15. Thus s>1/4.

On the other hand d<0 implies s/c<rho<1, so s<1/sqrt(2). Its exact
form in the original A2 chart is

    (a/b)*s^2+s*c<1.                            (4)

Both s^2 and s*sqrt(1-s^2) increase on [0,1/sqrt(2)]. At s=27/50,
the latter square root exceeds 21/25, and

    (35/18)*(27/50)^2+(27/50)*(21/25)
      =1+103/5000>1.

Consequently the whole actual interval is

    1/4<s<27/50, c>21/25.                       (5)

There is no retained angle box outside (5) under the contradiction
assumption b<=9/10.

### 2.2. Uniform bounds for the actual beta and tau

Since 1-c=s^2/(1+c), (5) gives

    c>1-(11/20)s^2,
    c<=1-s^2/2.

Put

    H_+(s)=1/4+(9/10)s+(33/80)s^2,
    B_-(s)=19/10-s/4,
    T_-(s)=1-(5/4)s+(9/20)s^2.

The actual original data obey

    H_B=1-xc+bs < H_+(s).

The polynomial F(s)=q0-H_+(s)^2-B_-(s)^2 is strictly concave on (5):

    F''=-2[(H_+')^2+H_+*H_+'']-1/8<0.

Both endpoint values are strictly positive:

    F(1/4)=447999/1638400,
    F(27/50)=2087039951/40000000000.

Therefore F>0 throughout the closed comparison interval. All square
roots and B_- are positive there, so

    beta^2=q-H_B^2>q0-H_+^2>B_-^2,
    beta>B_-.

Also L=xs+bc<s+(9/10)c<=s+(9/10)(1-s^2/2). Thus

    tau=beta-L>T_-(s),                          (6)
    0<T_-(s)<1.

The last bounds hold on the entire interval; T_- decreases there and
its endpoint values are 229/320 and 22811/50000. Finally

    H_B/beta > (1/2)/(25/12)=6/25,              (7)

because beta<R<25/12.

### 2.3. One exact positive quartic gives the contradiction

By the unchanged A2 identity,

    z=-d/E
      =[1-(a/b)s^2-s*c]/[c^2+(a/b)s*c]>0.

Using a/b>35/18 and c>21/25 in the numerator and denominator separately
gives

    z<Z(s):=[1-(35/18)s^2-(21/25)s]
                 /[1-s^2+(49/30)s].            (8)

Both comparison numerator and denominator are positive: the numerator
is strictly larger than the positive actual numerator in (4), and the
denominator is manifestly positive on (5).

Write D(s)=1-s^2+(49/30)s and A(s)=1-(35/18)s^2-(21/25)s. The polynomial

    G(s)=(6/25)*T_-(s)*D(s)-(1-T_-(s))*A(s)
      =6/25-(579/500)s+(439/500)s^2
         +(113803/45000)s^3-(983/1000)s^4        (9)

is strictly positive on the single whole interval [1/4,27/50]. Here
is its complete exact degree-four Bernstein identity: set
s=1/4+(29/100)t, 0<=t<=1, and write

    G(s)=sum_{i=0}^4 b_i*binom(4,i)*t^i*(1-t)^(4-i),

with

    b_0=472897/11520000,
    b_1=5427751/288000000,
    b_2=2277601/75000000,
    b_3=425205657/5000000000,
    b_4=1158370107/6250000000.

Every displayed coefficient is strictly positive, and the Bernstein
basis sums to one. The accompanying standard-library checker rebuilds
(9), all five coefficients, and every coefficient of the inverse
identity exactly with Fraction arithmetic. No grid or external
computer algebra is a premise.

Equations (6)--(9), with z>0 and 0<T_-<tau<1, now give

    delta*d/E+sigma
      =-(1-tau)*z+tau*H_B/beta
      >-(1-T_-)*Z+(6/25)*T_-
      =G(s)/D(s)>0.

This contradicts (1) and k_j<=0. Thus

    b>9/10.                                    (10)

This lemma uses the whole original epsilon_B=1 prefix and its actual
selected far normal. It neither assumes negative A pressure nor
replaces any physical B or C circle corner.

## 3. The coarse contact-coordinate consequences

We prove from d<0 and (10) that

    N>7/(4sqrt(34))>1/4,
    N^2+m^2=|P|^2<793/800<1.                    (11)

### 3.1. A short monotonicity proof for N

For a>b>0, let rho_d be the unique root in (0,1) of

    (a/b-1)*rho_d^2+rho_d-1=0.

The actual A2 identity and d<0 give
1-rho=(a/b-1)*rho*(s/c)<(a/b-1)*rho^2, hence rho>rho_d. The function

    N(a,b,rho)=[(a-1)rho+b-1]/sqrt(1+rho^2)

increases in rho throughout the present a>b, a>1 domain, because its
rho derivative has positive numerator a-1-(b-1)rho. Consequently
N>N_d(a,b):=N(a,b,rho_d).

At fixed b, the root rho_d decreases as a increases. Substituting its
root identity into N_d gives

    N_d=[b(rho_d+1/rho_d)-rho_d-1]/sqrt(1+rho_d^2).

The derivative of this expression with respect to rho_d is

    -[b(1+1/rho_d^2)+1-rho_d]/(1+rho_d^2)^(3/2)<0.

Thus N_d increases with a, and hence with q at fixed b. At fixed q,
a=sqrt(q-b^2) decreases with b, a/b decreases, and rho_d increases.
The direct b derivative of N at fixed rho is

    [1-(b/a)rho]/sqrt(1+rho^2)>0.

Its rho derivative is also positive as just checked, so N_d increases
with b at fixed q. First decrease b to 9/10 at fixed actual q, then
decrease q to q0. These comparisons stay inside a>b>0. Therefore

    N>N_d(sqrt(q0-81/100),9/10).

At that comparison endpoint 7/4<a<9/5, so a/b-1<1 and rho_d>3/5.
Using the positive rho derivative once more yields

    N>[(3/4)(3/5)-1/10]/sqrt(1+9/25)
      =7/(4sqrt(34))>1/4.

### 3.2. A uniform upper bound for the distance of P

From (10), a>b and the upper radius endpoint,

    a^2<Q-81/100<225/64,
    b^2<Q/2<(59/40)^2.

The two exact reserves are 59/6400 and 223/12800, respectively.
Thus 0<a-1<7/8 and |b-1|<19/40. It follows that

    |P|^2=(a-1)^2+(b-1)^2
      <49/64+361/1600=793/800<1,

which completes (11). In particular m<1.

## 4. Actual negative A pressure puts every top-j return inside 13/16

Because P belongs to the circle-touching square A, its distance from
the origin is at least R-sqrt(2). The exact radius reserve gives

    R-sqrt(2)>157/280,
    (157/280)^2-5/16=149/78400>0.

Together with (2) and (11), this implies

    1/4<N<1/2,
    b0:=sqrt(5/16-N^2) in (1/4,1/2),
    b0<m<1.                                    (12)

We first show that the actual negative pressure (3) forces

    r>2m-1.                                    (13)

The function Phi is strictly decreasing in r. At r0=2m-1 its exact
value is

    Phi(r0)=N^2-N/2+m(3/2-m)
               +(1+N-m)v-(2-N-m)u.

Both 1+N-m and 2-N-m are positive by (12). For 0<u<=v and
u^2+v^2=1, the last two terms are bounded below by (2N-1)/sqrt(2):
as a function of u, A*sqrt(1-u^2)-B*u decreases when A,B>0, and its
endpoint at u=1/sqrt(2) is (A-B)/sqrt(2).

The concave function f(t)=t(3/2-t) on [b0,1] has its minimum at an
endpoint. Since f(1)=1/2>=f(b0), we have f(m)>=f(b0). Moreover

    b0^2-(3/4-N)^2=2(N-1/4)(1/2-N)>=0.

Both b0 and 3/4-N lie in [1/4,1/2], where f increases. Hence

    f(m)>=f(b0)>=f(3/4-N)=9/16-N^2.

It follows that

    Phi(r0)>=9/16-N/2+(2N-1)/sqrt(2)
      >7/16-sqrt(2)/4>1/16>0.

The middle affine function increases with N, and N>1/4; the final
comparison uses sqrt(2)<3/2. Since the actual Phi(r)<0 and Phi
decreases, (13) follows.

Write T_j=r-m. Equations (12)--(13) and r<1 give

    -(1-m)<T_j<1-m,
    |T_j|<1-m.                                 (14)

Every actual point Q on H's top-j support face, including any original
mean on that entire face, has

    Q dot j=T_j, Q dot n in [N-1,N].

Since 0<N<1/2, (12)--(14) therefore give

    |Q|^2< (1-N)^2+(1-m)^2
          < (1-N)^2+(1-b0)^2
          = 2+5/16-2(N+b0)
          <=13/16,                              (15)

where N+b0>=3/4 follows from the displayed square identity. Thus every
actual top-j return point has squared norm strictly below 13/16. No
circle weight, HC application, side mean, or H coordinate was changed.

## 5. The full actual HC feature and corner cover

The original physically unique C chart and true concurrence are

    C=[w,w+1]k+[-V,1-V]Jk,
    U=w+1>1/2 or U=w<-1/2,
    U^2+V^2=q, V>1/2,
    M=det(W,k)>0, delta_C=V-M in (0,1),
    kappa=M/V in (0,1), z_C=U*k-V*Jk,
    q_C=kappa*z_C.

The fan in ABC_UPPER_LEFT_FAR_RETURN_SUPPORT_WORKING_2026_10_25.md,
Section 2, retains the original HC applications and all means. At a
strict C endpoint the two applications W and Q are distinct; the
compatible fixed-tip selection excludes a free HC, and the genuine
H4/petal parallel-root theorem excludes H normals parallel to n.
The remaining actual H-to-C normal is +j. These are the original
owner and degree inputs, not a new normal selection.

### 5.1. The entire C-owned or shared side with k_j<=0

The true positive C moment forces U>0, so U=w+1. The actual unchanged
side mean and its H-to-C normal are

    Q0=kappa*U*k+(1-V)*Jk,
    ell=-Jk, ell dot j=-k_n>0.

Thus Q0 is on H's actual top-j support face. For k_j<0 it is H's
back-top vertex; for k_j=0 it is the full original shared side mean,
with its actual n coordinate anywhere in [N-1,N]. Both cases are
included in (15).

Section 3 of the accepted source
ABC_FAR_UNIQUE_SAME_SIDE_RADIUS_OBSTRUCTION.md proves the independent
whole-circle inequality

    |Q0|^2=q+1-2V-2U^2(beta-U)/V^2>13/16       (16)

for every U,V>1/2 with U^2+V^2=q, beta<sqrt(q-1/4), and the actual
epsilon_B=1 identity W=z_B-f. That section uses no sign of k_j and
does not require a front-side return. Hence it applies here without
any changed force or mean. Equations (15)--(16) contradict each other.

### 5.2. The strict right endpoint with the positive C circle corner

The complete actual strict right feature has k_j<0 and H-to-C normal
j, so its fixed C vertex QR lies on H's top-j face. If U=w+1>0, then

    QR=U*k+(1-V)*Jk,
    |QR|^2=q+1-2V >= (R-1)^2
      >=(39/40)^2>13/16.

The last exact reserve is 221/1600. This again contradicts (15).

### 5.3. The strict right endpoint with the negative C circle corner

This alternative is not dropped. Here U=w<0, and the actual positive
outgoing C moment requires U+V>0, so V>|U|. Its proper ray is exactly

    QR-q_C=A_C*k+B_C*Jk,
    A_C=1+delta_C*U/V,
    B_C=1-delta_C>0.

Consequently

    A_C-B_C=delta_C*(1+U/V)>=0,
    A_C/B_C>=1.                                 (17)

The non-strict comparison includes delta_C=0 as an enlarged endpoint,
even though the original strict far chart has delta_C>0.

The actual H-to-C normal is +j, so the positive proper C-to-H ray is
a positive multiple of -j. Its two C-coordinate coefficients give

    A_C/B_C=(-k_j)/(-k_n).                       (18)

Write k=(-p,-t) in the original A frame, with p,t>0. Since k_j<0,

    (-k_j)/(-k_n)=(u*t-v*p)/(u*p+v*t)
      <u/v<1.                                  (19)

Cross-multiplication in the first strict inequality leaves
-v^2*p<u^2*p, with all denominators positive. Equations (17)--(19)
contradict each other. This closes the entire negative-U right
alternative independently of (15), retaining its actual positive
moment condition and original HC normal.

## 6. Exact join and scope

The present theorem excludes the entire epsilon_B=1 side/shared
return with k_j<=0 and both strict-right C corner alternatives.
Together with the already reviewed complete sources, the full
unique-C far k_y<0 cover is now:

* The epsilon_B=0 alternative is excluded by
  ABC_FAR_UNIQUE_LOWER_B_CORNER_EXCLUSION.md.
* The epsilon_B=1 C side with k_j>0 is excluded by
  ABC_FAR_UNIQUE_SAME_SIDE_RADIUS_OBSTRUCTION.md.
* The entire strict-left C endpoint requires U>V>0 and is excluded
  by ABC_FAR_UNIQUE_POSITIVE_C_COORDINATE_COMPARISON.md.
* The epsilon_B=1 side/shared return with k_j<=0 and both strict-right
  endpoints are the complete theorem proved here.

The radial-C far alternative was already excluded, with both original
circle-weight endpoints, by
ABC_UPPER_LEFT_FAR_RADIAL_BLOCK_PRESSURE_EXCLUSION.md. These joins
retain both physical C masks. They do not assert an exit for the
separate strict B-owned singleton minimum-f BC feature, whose adjacent
C-circle residue remains assigned in
ABC_UNIQUE_SINGLETON_SIDE_ADJACENT_RETURN_FAN.md.

The only exact coefficient packet in the new proof is the single
whole-interval quartic (9), with all five coefficients printed above.
Its checker also reconstructs all rational reserves used here. No
sampled sign, extra H/B contact, force reassignment, degree reduction,
Lean compilation, or CI run is a premise.
