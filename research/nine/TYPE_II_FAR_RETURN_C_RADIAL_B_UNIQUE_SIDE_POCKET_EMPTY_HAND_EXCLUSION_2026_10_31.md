# The entire C-radial, B-unique far-return side pocket is empty

Date: October 31, 2026 UTC.

**Status: complete hand geometric exclusion of every additional unit
in the original outer N pocket, throughout the C-radial/B-unique
far-return side mask.** The actual A side forces dist(O,N)>1/40.
The complete occupied-side-pocket proximity theorem gives the opposite
strict inequality if that outer pocket contains an additional unit.

The only finite comparison below is an eight-row table of printed
rational inequalities. Each row covers a complete interval, following
the explicit derivative signs. Its entries and reserves are ordinary
exact arithmetic; no generated pose cover, numerical solver or external
mathematical proof script is an input.

## 1. Exact original entry and notation

Retain the entire original same-nine D02.L135 unique-V, Type II
D-owned roof-direction, strict far-A-vertex SIDE return. Keep the
positive AD chord, full A3,D3,V2,B2,C2,N2 stars, all actual contact
applications, common selected normals, physical circle masks and
individual circle coefficients. Assume C is physically radial along
-n and B has its actual unique physical circle corner.

The exact chart, angle and full-hub bounds are the hand conclusions of

    TYPE_II_FAR_RETURN_RADIAL_UNIQUE_ANGLE_AND_ROOF_SLOPE_HAND_REDUCTION_2026_10_31.md,
    TYPE_II_FAR_RETURN_WHOLE_FORCE_RATIO_ONE_FIFTH_LOWER_BOUND_2026_10_31.md,
    TYPE_II_FAR_RETURN_C_RADIAL_B_UNIQUE_CENTRAL_STRIP_EMPTY_HAND_EXCLUSION_2026_10_31.md.

In the original oriented frame (d0,n), d0=-tD, put

    1/5<q<1/3, 0<e<1/2,
    P=sqrt(1+q^2), a=1/P, b=q/P,
    f=(-a,b), w=Jrot(f),
    H=(1+e)/sqrt((1+e)^2+(1+q)^2),
    k=(1+q)/sqrt((1+e)^2+(1+q)^2),
    H=sin(xi), k=cos(xi), h_A=(H,-k),
    D=sqrt(R^2-1/4)-1, D>117/125,
    u=(-sin(theta),cos(theta)),
    0<theta<atan(1/q)-pi/4<pi/4,
    x=cos(theta), y=sin(theta), j=Jrot(u)=(-x,-y),
    delta=atan(1/q)-theta in (pi/4,pi/2).

The actual C/N and B/N applications, original A/B port K and original
A/D port W satisfy

    U=(-1/2,-D), T=U+u,
    h0=T.j=U.j=D*y+x/2,
    K=T-beta*w, 0<beta<1,
    W=K+h_A,
    W.n=1-D, K.n=1-D+k,
    a*beta=1+k-x.                                  (1)

The whole actual side-channel N is

    N=[U.u,T.u]*u+[rho,rho+1]*j,
    T.u-U.u=1, rho<=h0<=rho+1.                    (2)

The transverse scalar rho is the original one. All its extreme
application choices are retained.

Write c0=(1+q)/P and d0s=(1-q)/P; the latter is a scalar, distinct
from the original vector d0. The unchanged unique B circle corner
and actual radial C give the exact circle equation

    D=F_q(theta)
      =[2+d0s+2*c0*x+(1+2*d0s)*y]
                       /[2*(1+c0+x)].             (3)

The cited angle reduction proves that F_q strictly increases on
`0<=theta<=atan(1/q)-pi/4`. The radius lower bound used here is the
same-nine printed analytic hand measure theorem R>2, with its complete
hand dependencies recorded in those cited sources.

## 2. The actual A side crosses N's upper endpoint line

Put eta=xi-theta. Its tangent comparison is

    tan(xi)=(1+e)/(1+q)>(1-q)/(1+q)>tan(theta),

so 0<eta<pi/2. In the (u,j) frame the vector from W to K has
components `(cos(eta),sin(eta))`, both positive. Also

    K.u=T.u+beta*sin(delta)>T.u.

The point W is strictly inside the horizontal u-strip of N. Indeed

    T.u-W.u
      =cos(eta)-beta*sin(delta)
      =y*[H+q*(1+k-x)]-x*(1-x)>0.                (4)

For the last inequality, divide by y>0 and use

    x*(1-x)/y=x*y/(1+x)<tan(theta/2)<1/2,
    H>3/5,
    1+k-x>0.

Here H>3/5 follows from e>0,q<1/3. The same difference in (4) is
less than one because cos(eta)<=1 and beta*sin(delta)>0. Therefore

    U.u<W.u<T.u<K.u.

There is a unique point E in the relative interior of the actual A
side WK such that E.u=T.u. Its exact height, obtained by moving back
from K along that unchanged side, is

    E.j=h0-beta*[cos(delta)+sin(delta)*tan(eta)]
       =h0-(1+k-x)*(H+q*k)/(H*y+k*x).             (5)

For the second equality use
`cos(delta-eta)=a*H+b*k`, `cos(eta)=H*y+k*x`, and (1).
Every factor in the subtracted expression is positive, so E.j<h0.
We next prove uniformly over the whole original circle domain that

    E.j>1/40.                                     (6)

## 3. A concave tangent reduces (6) to two scalar endpoint inequalities

Set

    epsilon=1/40, D0=117/125,
    t=H/k=(1+e)/(1+q),
    1/(1+q)<t<3/[2*(1+q)], 3/4<t<5/4.

By (5), the desired inequality is equivalent to

    [(h0-epsilon)*y-(1-x)]*t
       +(h0-epsilon)*x-q*(1-x)
            >(t+q)/sqrt(1+t^2).                  (7)

For each fixed q in [1/5,1/3], the function on the right is concave
on [3/4,5/4]. Its second derivative has the sign of

    2*q*t^2-3*t-q < (2/3)*(25/16)-9/4<0.

Its tangent at t=1 therefore gives

    (t+q)/sqrt(1+t^2)
      <=[(1-q)*t+1+3*q]/(2*sqrt(2))
       <tau*[(1-q)*t+1+3*q],
    tau=99/280.                                  (8)

The last strict bound uses sqrt(2)>140/99, whose squared integer
reserve is 2. All brackets in (8) are positive.

After applying (8), the difference in (7) is affine in t. It is enough
to check the two actual interval endpoints

    t=m/(1+q), m=1 and m=3/2.

Multiplying by 1+q shows that the sufficient endpoint inequalities are

    L_m(D,q,theta)>R_m(q),                        (9)

where

    L_m=[m*y+(1+q)*x]*(D*y+x/2-epsilon)
                        -(m+q+q^2)*(1-x),
    R_m=tau*[m*(1-q)+(1+q)*(1+3*q)].              (10)

Both endpoints imply (7) over the complete t interval. Thus no angle
or force-ratio interval in the original e variable needs subdivision.

## 4. Whole-interval monotonicities used by the hand table

The circle comparisons in Section 5 imply, in particular,

    y>13/40.

The original angle bound also gives

    y/x<(1-q)/(1+q)<=2/3,
    x>3/sqrt(13)>4/5,
    y<2/sqrt(13)<5/9.                             (11)

Throughout this domain h0=D*y+x/2 increases with theta. More precisely,

    partial_theta h0=D*x-y/2
       >[3/sqrt(13)]*(117/125-1/3)
       =226/[125*sqrt(13)]>1/2.                 (12)

The last comparison has positive squared reserve
`452^2-125^2*13=1179`. The first row's elementary cosine lower bound
is cos(arcsin(13/40))>9457/10000. Consequently

    h0-epsilon
      >(117/125)*(13/40)+(9457/10000)/2-1/40
       =0.75205>3/4.                             (13)

All finite decimals in this proof denote exact rational numbers.

For fixed D,theta, the q derivative of L_m is independent of m:

    partial_q L_m=x*(h0-epsilon)-(1+2*q)*(1-x)
       >(4/5)*(3/4)-(5/3)*(1/5)=4/15>0.          (14)

The D derivative is positive as well:

    partial_D L_m=[m*y+(1+q)*x]*y>0.             (15)

We verify the theta derivative on the whole original angle domain.
Put A_m=m*y+(1+q)*x and B_m=m+q+q^2. Then

    partial_theta L_m
      =[m*x-(1+q)*y]*(h0-epsilon)
                       +A_m*(D*x-y/2)-B_m*y.    (16)

For m=1, the first coefficient is greater than q*x>4/25.
Also A_1 increases with theta throughout the original angle range,
and increases with q for fixed theta. Thus

    A_1>(13/40)+(6/5)*(9457/10000)>29/20,
    B_1<=13/9.

Equations (11)--(13),(16) give the strict uniform reserve

    partial_theta L_1
       >(4/25)*(3/4)+(29/20)/2-(13/9)*(5/9)
        =689/16200>0.                            (17)

For m=3/2, the first coefficient is greater than
`(q+1/2)*x>(7/10)*(3/sqrt(13))>1/2`. Furthermore

    A_(3/2)>29/20+13/80=129/80,
    B_(3/2)<=35/18.

The corresponding reserve is

    partial_theta L_(3/2)
       >(1/2)*(3/4)+(129/80)/2-(35/18)*(5/9)
        =2618/25920>0.                           (18)

Finally both right sides in (10) increase with q:

    R_m'(q)=tau*(4-m+6*q)>0.                    (19)

Accordingly, on a row q in [q_l,q_h], a verified theta lower bound
theta_l permits the sufficient comparison

    L_m(D,q,theta)>L_m(D0,q_l,theta_l)>R_m(q_h).

To justify the comparison path, first decrease q to q_l at fixed
D,theta; this preserves the original angular upper bound. Next
decrease D to D0 and then theta to theta_l. The derivative bounds
above hold throughout. In particular no partial monotonicity is
mistaken for monotonicity along the circle equation.

## 5. Eight exact lower-angle comparisons from the actual circle equation

For a proposed lower sine y_l, put x_l^*=sqrt(1-y_l^2) and
theta_l=arcsin(y_l). The inequality F_q(theta_l)<D0 is equivalent to

    J(q,x_l^*,y_l)>0,

where

    J(q,x,y)=sqrt(1+q^2)*[D0*(1+x)-1-y/2]
                   +(1+q)*(D0-x)-(1-q)*(1/2+y). (20)

All proposed y_l below are at most 427/1000<1/sqrt(5). Thus each
theta_l is less than atan(1/2), and lies in the increasing-theta
interval of F_q for every q<=1/3.

For the values of x,y in the table, the bracket multiplying the square
root in (20) is positive. The q derivative of J is therefore positive:

    partial_q J
      =[q/sqrt(1+q^2)]*[D0*(1+x)-1-y/2]
                      +D0-x+1/2+y>0.            (21)

The last two terms already exceed D0-1/2>0. It suffices to check
q=q_l. Its coefficient of x is negative because
`D0*sqrt(1+q_l^2)<1+q_l`. Consequently a lower square-root bound
p_l and an upper cosine bound x_+ give the rational lower comparison

    J(q_l,x_l^*,y_l)>=J_l,
    J_l=p_l*[D0*(1+x_+)-1-y_l/2]
             +(1+q_l)*(D0-x_+)-(1-q_l)*(1/2+y_l). (22)

The full table is as follows. Each decimal is a terminating rational,
not a measured or sampled value.

| q_l | q_h | y_l | p_l | x_- | x_+ | Printed lower bound for J_l |
| --- | --- | --- | --- | --- | --- | --- |
| 1/5 | 13/60 | .325 | 1.0198 | .9457 | .9458 | >1/20000 |
| 13/60 | 7/30 | .335 | 1.0232 | .9422 | .9423 | >3/1000 |
| 7/30 | 1/4 | .350 | 1.0268 | .9367 | .9368 | >1/500 |
| 1/4 | 4/15 | .363 | 1.0307 | .9317 | .9318 | >3/1000 |
| 4/15 | 17/60 | .378 | 1.0349 | .9258 | .9259 | >3/1000 |
| 17/60 | 3/10 | .394 | 1.0393 | .9191 | .9192 | >3/1000 |
| 3/10 | 19/60 | .410 | 1.0440 | .9120 | .9121 | >1/250 |
| 19/60 | 1/3 | .427 | 1.0489 | .9042 | .9043 | >1/200 |

Every radical enclosure in this table is the direct positive-square
comparison

    p_l^2<1+q_l^2,
    x_-^2+y_l^2<1<x_+^2+y_l^2.                  (23)

For example, the closest first-row comparisons are

    1.0198^2=1.03999204<1.04,
    .9457^2+.325^2=.99997349<1,
    .9458^2+.325^2=1.00016264>1,
    J_l=.00005242224>1/20000.

Equations (22)--(23) and the displayed rational table prove J>0 on
each whole row. Since D=F_q(theta)>D0 and F_q increases on the full
original angle interval, the actual theta is strictly greater than
theta_l. The first row's comparison, with (21), also proves the global
bound y>13/40 used in Section 4, before any row-dependent comparison.
There is no circular use of its derivative estimates.

## 6. The two endpoint inequalities on every row

At D0,q_l,theta_l, the expression L_m is increasing in x when y_l
is fixed: its x derivative is

    (1+q_l)*(D0*y_l+x/2-epsilon)
                   +[m*y_l+(1+q_l)*x]/2+m+q_l+q_l^2>0.

Thus replacing the exact cosine x_l^* by x_- gives a rational lower
bound for L_m. Put

    H_l=D0*y_l+x_-/2-epsilon,
    A_l=y_l+(1+q_l)*x_-,
    B_l=1+q_l+q_l^2,
    S_1=A_l*H_l-B_l*(1-x_-)
                    -tau*(2+3*q_h+3*q_h^2),
    S_(3/2)=S_1+[y_l*H_l-(1-x_-)]/2
                              -tau*(1-q_h)/2.    (24)

These are exactly the two sufficient endpoint differences, with the
left side decreased and the right side increased. Direct rational
multiplication gives the following complete reserves, in the same
row order as Section 5:

| q interval | S_1 | S_(3/2) |
| --- | --- | --- |
| [1/5,13/60] | >43/1000 | >3/10000 |
| [13/60,7/30] | >39/1000 | >13/5000 |
| [7/30,1/4] | >40/1000 | >11/1000 |
| [1/4,4/15] | >37/1000 | >15/1000 |
| [4/15,17/60] | >35/1000 | >21/1000 |
| [17/60,3/10] | >32/1000 | >26/1000 |
| [3/10,19/60] | >28/1000 | >30/1000 |
| [19/60,1/3] | >23/1000 | >33/1000 |

For clarity, the smallest comparison, the first-row m=3/2 value,
has the exact displayed operands

    L_(3/2)(D0,q_l,x_-,y_l)=1.125598797,
    R_(3/2)(q_h)=378081/336000.

Their difference exceeds 3/10000: after multiplying by
`336000*10^9`, the remaining numerator is 19395792000>0.
This also illustrates the arithmetic convention for every other row;
all their inputs, operations and rational lower reserves are printed
in (22)--(24) and the two tables.

Equations (14)--(19) make these comparisons valid over the whole
corresponding intervals of q,D,theta. The intervals cover [1/5,1/3]
without gaps, and the actual q range is strict inside it. Both endpoint
inequalities (9) are proved. The concave-tangent argument consequently
proves (7), and hence the whole-domain crossing estimate

    E.j>1/40.                                     (25)

## 7. Physical disjointness and the whole outer-pocket conclusion

The actual E lies on the original closed A side WK, and E.j<h0 by
(5). If rho<E.j, then points of the same side immediately toward W
have their u coordinate strictly between U.u and T.u by Section 2,
and their j coordinate strictly between rho and rho+1 by (2),(25).
Such points would lie in int(N). A closed A side point inside an open
N neighborhood forces int(A) and int(N) to overlap, contradicting
the actual packing. Therefore

    rho>=E.j>1/40.

Every point of N has j coordinate at least rho, so

    dist(O,N)>=rho>1/40.                          (26)

No assumption that zero lies in N's u interval is needed. Every
original transverse mean, including an extreme value of (2), remains.

The original outer chain is C--N--B and its actual channel height is
h0>0. The complete hand theorem
`FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md`, with
its physical outer-side routing, says that a whole additional unit in
this actual outer pocket requires dist(O,N)<1/40. Equation (26)
contradicts it. Thus the whole original outer N pocket is empty of
additional units throughout this complete physical endpoint mask.

The original B unique corner, both actual C circle corners and their
individual coefficients, possible zero-load physical circle contacts
of N, and every weak subdivision are retained. The overlap argument
uses an actual occupied side and so remains valid at all such limits.
The cited whole-pocket proximity theorem routes compact completion
interiors on the same original bounded side; extra contacts can only
subdivide its free space.

Combined with the complete central-strip theorem cited in Section 1,
all three original completion units would have to occupy the two
exterior hub pockets. Their literal whole-mask capacities must still
be supplied before the entire original endpoint mask is declared
closed. This source itself changes no original fine or coarse flag.

All eight rows are exact hand rational comparisons over complete
intervals. No external computational certificate or mathematical proof
script, sampled packing, changed original mean, Lean/Lake invocation
or CI was used.
