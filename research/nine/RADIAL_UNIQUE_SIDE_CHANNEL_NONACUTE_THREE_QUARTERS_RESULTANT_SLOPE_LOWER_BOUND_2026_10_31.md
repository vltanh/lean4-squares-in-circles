# The three-quarters resultant-slope bound for every nonacute radial/unique side channel

Date: October 31, 2026 UTC.

**Status: complete hand theorem on the entire stated nonacute physical chart.**
Together with
`RADIAL_UNIQUE_SIDE_CHANNEL_THREE_QUARTERS_RESULTANT_SLOPE_LOWER_BOUND_2026_10_31.md`,
this proves the same strict lower slope for every exterior aperture in
(0,pi) having the literal physical side signs and full stars below. The
present proof handles the perpendicular aperture and all obtuse apertures.
One circle comparison and two rational endpoint comparisons cover continuous
intervals. No generated cover or sampled configuration is a premise.

## 1. Literal original chart and theorem

Keep the original origin, every actual square and circle vertex, every
individual nonnegative circle coefficient, positive pair magnitude,
genuine exterior side application, full mean and complete endpoint star.
Let

    2<R<=sqrt(1105)/16,
    D=sqrt(R^2-1/4)-1,
    Dlo=117/125<D<Dhi=61/60.                       (1)

For an all-nine caller, the hand measure route to R>2 is given by
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md` Sections 1--3,
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md` Sections 2--6, and
`ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md` Section 3. Its printed
mass is 8997/1000<9. The rational comparisons in (1) are the same positive
squarings used in the companion acute source.

In an oriented orthonormal coordinate frame `(d0,n)`, suppose the actual
radial endpoint C is

    C=[-1/2,1/2]*d0+[-D-1,-D]*n,
    Q_C=(chi,-D), -1/2<chi<1/2,
    U=(-1/2,-D).

Its exterior force is `-P_C*n`, with P_C>0. Its other original force is
the side-channel force `-ell*u` at U, ell>0. Both physical circle corners
and their original coefficients are retained.

The other actual endpoint B is loaded true2 with one physical circle
corner. It owns the actual exterior axis

    f=(-a,b), w=Jrot(f)=(-b,-a),
    q=b/a<=0, P=sqrt(1+q^2), a=1/P, b=q/P.

Thus the exterior aperture is

    Theta=pi/2-atan(q) in [pi/2,pi).

At its genuine original exterior side-interior point Q, the actual unit is

    B=Q+[0,1]*f+[-(1-beta),beta]*w,
    0<beta<1,
    T=Q+beta*w, T-U=u, |u|=1.

The literal original channel signs are strict:

    u.n>0, u.f>0,
    u=(-sin(theta),cos(theta)),
    max(0,Theta-pi/2)<theta<pi/2,
    delta=Theta-theta in (0,pi/2).

These signs fix the actual applications T,U and the actual circle corner
`Z_B=T+f-w`. A caller must establish this physical entry; the statement
does not assign a replacement corner or mean at a support tie.

Normalize every original force by the same positive factor so that the
complete B2 force is

    P*f+ell*u=kappa*Z_B, kappa>0,
    P*f=(-1,q).

The unchanged opposite exterior resultant is then

    F=(1,z), z=P_C-q.                            (2)

**Theorem 1.1.** Every actual configuration in this whole nonacute chart
satisfies `z>3/4`.

This is a theorem about the full original true2 endpoint stars and their
literal actual side channel. It makes no degree or equation assumption
at the other exterior neighbors. Additional forces at either endpoint
cannot be dropped to manufacture this chart.

## 2. Exact moments and circle identity

The complete torque about the unique physical B corner gives

    P*(1-beta)=ell*(sin(delta)-cos(delta))>0.

Consequently delta>pi/4. Put v=-q>=0. For 0<=v<1 the entire actual
angular interval is therefore

    atan(v)<theta<pi/4+atan(v).                  (3)

The lower endpoint in (3) is the strict condition delta<pi/2, not merely
theta>0. This lower endpoint is essential below.

Write x=cos(theta), y=sin(theta), and define the positive scalars

    c=(1-v)/sqrt(1+v^2),
    d=(1+v)/sqrt(1+v^2),
    c^2+d^2=2.

For v<1, the original physical corner and its two-circle identity are

    Z_B=(-1/2-y-d,-D+x+c),
    D=F_v(theta)
      =[2+d+2*c*x+(1+2*d)*y]/[2*(1+c+x)].        (4)

The same direct full force and origin-moment calculations as in the acute
source give

    h=D*y+x/2,
    K=d*x-c*y,
    E=h+K=(1/2+d)*x+(D-c)*y,
    G=P-D+v/2+x+v*y,
    ell=G/E,
    P_C*chi=M=G*h/E.

On the actual interval, h,K,G,E are positive. Thus chi>0, and its unchanged
genuine upper port bound chi<1/2 gives

    z=P_C+v>2*M+v.                              (5)

Each original circle force has zero origin moment individually. These
identities do not average, equate or omit either radial-circle coefficient.

## 3. The entire interval v>=4/15 is already excluded or immediate

If v>=3/4, (2) directly gives z=P_C+v>3/4, without further geometry.
It remains to consider 0<=v<3/4, where c,d in Section 2 are positive.

For this entire interval F_v is strictly increasing on
`[0,pi/4+atan(v)]`. Apart from a positive denominator, its derivative is

    (1+2*d)*[1+(1+c)*cos(theta)]
      +(2+d-2*c-2*c^2)*sin(theta).

If the second coefficient is nonnegative, positivity is immediate.
Otherwise the closed comparison bounds
`cos(theta)>=c/sqrt(2)` and `sin(theta)<=d/sqrt(2)` give the positive
lower bound

    (1+2*d)+(c+c^2+2*d+d^2)/sqrt(2)
      =(1+2*d)+(c+2+2*d)/sqrt(2)>0.

Using the strict lower endpoint in (3), we obtain

    D>F_v(atan(v))
      =Fmin(v)=[4*sqrt(1+v^2)+1+2*v]
                 /[2*(sqrt(1+v^2)+2-v)].        (6)

The right side strictly increases for 0<=v<3/4. With P=sqrt(1+v^2),
the derivative has the sign of

    6*P+5+(7*v-6*v^2)/P>0.

At v=4/15,

    Fmin(4/15)=(4*sqrt(241)+23)/[2*(sqrt(241)+26)]
                 >61/60.

The last comparison is equivalent to `sqrt(241)>896/59`, whose exact
positive squared reserve is `36105/3481`. Therefore (1),(6) exclude
the whole interval 4/15<=v<3/4. Every case still requiring proof has

    0<=v<4/15.                                  (7)

## 4. Two derivative comparisons on the full enlarged rectangle

For this section enlarge to

    Dlo<=D<=Dhi, 0<=v<=4/15,
    0<theta<=pi/4+atan(v).

These comparison angles need not satisfy the original lower endpoint
theta>atan(v). Their use does not alter any original application.

The following uniform bounds follow by positive squaring and elementary
monotonicity:

    P<26/25,
    d<5/4, c>7/10,
    d/c=(1+v)/(1-v)<=19/11,
    y/x<=19/11.

For instance the two nontrivial endpoint comparisons are
`d<=19/sqrt(241)<5/4` and `c>=11/sqrt(241)>7/10`, with squared
cross-product reserves 249 and 291, respectively. Also

    A=x+v*y>=P/sqrt(2),
    G>=P*(1+1/sqrt(2))-D+v/2>41/60>0.

Indeed A increases up to theta=atan(v) and then decreases; its endpoint
values on the displayed comparison interval are 1 and P/sqrt(2), and
P/sqrt(2)<1. Moreover K>=0, h>0 and E>0.

### 4.1. M strictly decreases with D

Direct differentiation gives

    E^2*M_D=-h^2+K*(G*y-h),
    G*y-h=y*(P-2*D+v/2+A)-x/2.

Since A<=P,

    G*y-h<(128/375)*y-x/2
             <=(739/8250)*x.

Here `2*(26/25)-2*(117/125)+(4/15)/2=128/375`, and
`(128/375)*(19/11)-1/2=739/8250`.
If G*y-h<=0, the desired sign is immediate. Otherwise use
`K<=d*x<=(19/15)*x` and `h>x/2` to obtain

    E^2*M_D
      <[14041/123750-1/4]*x^2<0.

The positive reserve in the last comparison is
`1/4-14041/123750=33793/247500`. Thus

    M_D<0.                                      (8)

### 4.2. M strictly increases with theta

Put

    J=y-v*x, A=x+v*y,
    K0=D*d+c/2>0.

The original elementary identities give

    h_theta=D*x-y/2
         >=[117/125-19/22]*x=(199/2750)*x>0,
    h_theta*E-h*E_theta=K0,
    E^2*M_theta=N=G*K0-J*h*E,
    N_theta=-2*J*h_theta*E-A*h*E.

If J<0, then N>0 directly. On the remaining interval J>=0, N strictly
decreases, so it suffices to check its upper angular endpoint. There

    x=c/sqrt(2), y=d/sqrt(2),
    h=E=K0/sqrt(2), J=P/sqrt(2),
    Gend=P*(1+1/sqrt(2))-D+v/2,
    P*K0=D*(1+v)+(1-v)/2,
    Nend=K0*[Gend-P*K0/(2*sqrt(2))].

Use P>=1 and D<=61/60 in the bracket. Its resulting lower bound is

    -1/60+29/(120*sqrt(2))
      +v*[1/2-31/(120*sqrt(2))]>61/400>0.

The v coefficient is positive, and the constant comparison uses
`1/sqrt(2)>7/10`. Hence N>0 everywhere in the comparison rectangle,
including angles below atan(v), and

    M_theta>0.                                  (9)

## 5. One uniform lower angle

Every actual configuration in (7) satisfies

    sin(theta)>7/50.                            (10)

If v>=1/7, this follows immediately from (3):
`sin(theta)>v/sqrt(1+v^2)>=1/sqrt(50)>7/50`.
The last squared reserve is `1/2500`.

For 0<=v<=1/7, put `theta_l=asin(7/50)`, y_l=7/50 and
`x_l=sqrt(1-y_l^2)>99/100`. The positive squared reserve for this last
bound is `3/10000`. Rewrite `F_v(theta_l)<Dlo` as

    Jcirc(q)=P*[Dlo*(1+x_l)-1-y_l/2]
       +(1+q)*(Dlo-x_l)-(1-q)*(1/2+y_l)>0,
    q=-v in [-1/7,0].

The bracket is positive and at most 401/500. Therefore

    Jcirc'(q)
      =(q/P)*[Dlo*(1+x_l)-1-y_l/2]
          +Dlo-x_l+1/2+y_l
      >=-401/3500+72/125=323/700>0.

It suffices to compare at q=-1/7. Replace P by its lower bound 1;
the bracket is positive. The resulting expression is affine in x_l,
with positive coefficient `Dlo-6/7=69/875`, so x_l>99/100 gives

    Jcirc(-1/7)
      >[Dlo*(1+99/100)-1-7/100]
           +(6/7)*(Dlo-99/100)-(8/7)*(1/2+7/50)
       =653/43750>0.

Thus `F_v(theta_l)<Dlo<D=F_v(theta)` throughout this complete interval.
The strict increase of F_v proves theta>theta_l, giving (10).

## 6. Two rational endpoint comparisons prove the slope bound

By (8)--(10), for each remaining v,

    M(D,v,theta)>M(Dhi,v,theta_l),
    y_l=7/50, x_l>99/100.

At this one comparison angle, throughout 0<=v<=4/15,

    G=P-Dhi+v/2+x_l+v*y_l>=73/75,
    h=Dhi*y_l+x_l/2>=239/375,
    G*h>=17447/28125.                            (11)

For 0<=v<=1/8, one has

    d<=(1+v)<=9/8,
    c>6/7.

For the second bound, c decreases in v and its endpoint is
`7/sqrt(65)>6/7`, with positive squared cross-product reserve 61.
Using x_l<=1, we obtain

    E=h+d*x_l-c*y_l
       <1927/3000+9/8-3/25=2471/1500.

The complete rational comparison is

    8*(17447/28125)-3*(2471/1500)
       =2329/112500>0.

Consequently `M>3/8` throughout this whole v interval, and (5) gives
`z>3/4`.

For 1/8<=v<=4/15, use instead the uniform bounds d<5/4,c>7/10:

    E<1927/3000+5/4-49/500=5383/3000,
    3*(17447/28125)-5383/3000=5001/75000>0.

Thus `M>1/3`, and the original moment inequality (5) gives

    z>2/3+1/8=19/24>3/4.

This proves the theorem on every interval left by Section 3. The joins
v=0,1/8,1/7 and4/15 were included in their closed comparison domains;
no original side coordinate or circle coefficient was reset at a join.

## 7. Scope and whole-aperture join

This theorem covers every actual nonacute aperture with the stated full
radial/unique stars, genuine exterior side applications, strict channel
projections and original circle normalization. The companion acute
three-quarters source covers the remaining acute apertures. Their common
perpendicular boundary is retained. Hence a literal caller with these
physical premises may use `z>3/4` without restricting the exterior aperture
to an acute angle.

A parallel-channel endpoint or another support tie that does not have the
actual U,T,Z_B printed in Section 1 must receive its own original physical
entry argument. Neither source silently chooses a different original mean.
The theorem keeps the radial unit's two physical circle vertices, including
any individual zero coefficient, and imposes no equation on the exterior
neighbors. It does not change an original fine-row flag by itself.

All comparisons above are explicit hand derivatives, positive square-root
comparisons and rational arithmetic. No external calculation, generated
cover, Lean or CI is a proof premise.
