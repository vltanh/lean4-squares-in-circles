# The whole opposite-return radial/radial central face lies in a strip narrower than one

Date: October 31, 2026 UTC.

**Status: complete hand exclusion of every additional unit in the original
central face.** In the West/strict opposite return with both genuine
exterior endpoints physically radial and N the original side transmitter,
the entire actual contact pentagon lies in a strip of width strictly less
than one. This keeps all original endpoint means and the original full
stars. It makes no assumption on the transverse position of N and uses
neither a pose certificate nor a replacement force equilibrium.

## 1. Full original entry and complete hand angular bounds

Retain the same nine squares, disk, original positive graph

    A--V--D--C--N--B--A, with chord AD,

and every original degree, force, application, mean, physical circle
corner and individual nonnegative circle coefficient. The original
unloaded true3 hubs are A,D, the loaded true2 units are V,B,C, and
N is the original unloaded true2 side transmitter.

Use the full chart in
`WEST_STRICT_OPPOSITE_RETURN_HAND_APERTURE_MASK_COVER_AND_UNIQUE_CENTRAL_EXCLUSION_2026_10_31.md`:

    h=(c,-s), e=Jrot(h), c^2+s^2=1,
    a^2+b^2=1, a,b>0,
    alpha=atan(s/c), psi=atan(b/a),
    theta_D=alpha+psi,
    u=a*c-b*s, v=a*s+b*c,
    q=(u-v)/b,
    H in (1/2,1],
    x=1-a+H*s, y=1-H*c+b, m=x/y,
    K-W=-x*h+e,
    W-L=b*h+a*e,
    Delta=K-L=(b-x)*h+(1+a)*e.                 (1)

The original external axes will be denoted B_axis,C_axis to avoid
confusing them with the scalar b in (1):

    B_axis=(-m*h+e)/sqrt(1+m^2), w=Jrot(B_axis),
    C_axis=(c*h+(s+q)*e)/sqrt(c^2+(s+q)^2),
    z=Jrot(C_axis).

Their clockwise aperture is

    Theta=pi/2+atan(m)-alpha-chi,
    chi=arg(C_axis)>0.                         (2)

The complete hand radial-C aperture theorem

`WEST_STRICT_OPPOSITE_RETURN_C_RADIAL_ACUTE_APERTURE_AND_UNIQUE_B_COMPLETE_HAND_EXCLUSION_2026_10_31.md`

gives q>1, `Theta<atan(3)<pi/2` and
`pi/4<theta_D+chi<pi/2`. The additional complete RR reduction

`WEST_STRICT_OPPOSITE_RETURN_C_RADIAL_RR_SMALL_ROOF_ANGLE_HAND_REDUCTION_2026_10_31.md`

gives

    0<s<1/6, q>1.                              (3)

That source retains the original whole side means, excludes both
parallel cone endpoints, and supplies the exact strict radial bridge
used next. Its hand same-nine radius entry is R>2, with

    117/125<d<61/60,
    R^2=(d+1)^2+1/4.

For clarity, the full hand R>2 dependency is
`NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md`, Sections 1--3,
`NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md`, Sections 2--6,
and the adopted `ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md`,
Section 3. No historical checking program is used.

## 2. The actual RR direction, original means, and exact depths

Let n be the unchanged N side direction, with T-U=n. The complete
strict RR geometry puts n on the bisector of the two original axes.
Write

    delta=Theta/2 in (0,pi/4),
    kappa=cos(delta), sigma=sin(delta), j=Jrot(n),
    B_axis=kappa*n+sigma*j,
    C_axis=kappa*n-sigma*j.

The actual inner radial vertices are

    T=d*B_axis+(1/2)*w,
    U=-d*C_axis+(1/2)*z.

Their unchanged unit separation is exactly

    2*d*kappa-sigma=1.                          (4)

It follows that `kappa=2*d*(1-sigma)`, hence

    T=(1/2)*n+d*j,
    U=-(1/2)*n+d*j.                            (5)

Keep the actual original exterior port coordinates

    K=d*B_axis-chi_B*w,
    L=-d*C_axis-chi_C*z.

Both are genuine side-interior ports. The full original loaded
endpoint torques, with the same positive side force ell, give

    p_B*chi_B=p_C*chi_C=ell*d>0,
    0<chi_B,chi_C<1/2.                          (6)

No equal-weight physical radial resultant is assumed. These are
the original full-star moments, including both physical circle
corners and all original coefficient endpoints. Thus

    beta_B=1/2+chi_B, beta_C=1/2+chi_C in (1/2,1),
    K.j=d-beta_B*kappa,
    L.j=d-beta_C*kappa,
    Delta.n=1+(1+chi_B+chi_C)*sigma,
    Delta.j=(chi_C-chi_B)*kappa.                 (7)

Define the reciprocal tangent

    k=cot(delta)=kappa/sigma.

The exact bridge (4) gives
`tan(delta)=d-1/(4*d)`. From d>117/125,

    12*d^2-8*d-3>393/15625>0,

so `tan(delta)>2/3`. Together with delta<pi/4,

    1<k<3/2.                                   (8)

The polynomial is increasing on the complete d interval; the
displayed value is its exact value at 117/125.

Put

    zeta=atan(m)-delta,
    h_W=d-W.j.

In A's actual frame, n has argument pi/2+zeta. Consequently

    Delta.n=(x-b)*sin(zeta)+(1+a)*cos(zeta),
    Delta.j=(x-b)*cos(zeta)-(1+a)*sin(zeta),
    h_W=beta_C*kappa+sin(psi+zeta).              (9)

Eliminating the unchanged means from (7),(9) gives exactly

    h_W=(A*cos(zeta)+B*sin(zeta)-k)/2,
    A=(1+a)*k+x+b,
    B=(x-b)*k+a-1.                              (10)

For example, substitute
`kappa*(1+chi_B+chi_C)=k*(Delta.n-1)` and
`kappa*(chi_C-chi_B)=Delta.j` into (9). This proves (10) with
the original means, rather than assigning new ones.

We shall prove

    A^2+B^2<(k+2)^2.                            (11)

Cauchy's inequality in (10) will then give h_W<1.

## 3. Two monotonicities remove H and the entire q interval

For fixed a,b,k, the derivative of `(A^2+B^2)/2` with respect to x
is

    A+k*B=2*k*a+(1+k^2)*x-(k^2-1)*b>0.

Indeed x>0, a>b, and `2*k-(k^2-1)>0` for 1<=k<=3/2.
Since H<=1, it is enough to prove (11) after the scalar replacement

    x<=x1=1-a+s.                               (12)

After (12),

    A=k+1+s+(k-1)*a+b,
    B=k-1+k*s-(k-1)*a-k*b.                     (13)

For fixed alpha, increasing q decreases psi. To see this directly,
the original return identity gives

    W0=sqrt(q^2+2*q*(c+s)+2),
    a=(c+s+q)/W0, b=(c-s)/W0,
    partial psi/partial q=(s-c)/W0^2<0.

For q>=1 and 0<=s<=1/6, one has

    0<b<=1/sqrt(5)<9/20,
    a>4/5,
    a>b.

We show that the squared norm in (13) strictly increases in psi
over this whole range. Its half derivative expands exactly as

    A*A_psi+B*B_psi
      =a*[-k^2+2*k+1-(k^2-1)*s]
        +(k^2-1)*(a^2-b^2)
        +(-k^2+4*k-1)*a*b
        +(k-1)^2*b*s-2*(k-1)*b.                (14)

All terms except the final one are nonnegative, and the first
coefficient is at least

    7/4-(5/4)*(1/6)=37/24.

Thus the right side of (14) is greater than
`(4/5)*(37/24)-9/20=47/60>0`. The squared norm is therefore
largest at the closed scalar comparison q=1. This comparison is
legitimate although the original theorem gives q>1: it only enlarges
the scalar bound and does not replace an original force or mean.

It remains to prove (11) for

    q=1, x=1-a+s, 0<=s<=1/6, 1<=k<=3/2.        (15)

## 4. Convexity in k reduces the bound to two endpoints

For each fixed a,b,x, the expression

    Q(k)=A^2+B^2-(k+2)^2

is a strictly convex quadratic: its leading coefficient is
`(1+a)^2+(x-b)^2-1>0`. It suffices to show that Q is negative
at k=1 and k=3/2 throughout the remaining interval (15).

At k=1, the identity a+x=1+s gives

    Q(1)=2*((1+s)^2+(1+b)^2)-9
       <2*((7/6)^2+(29/20)^2)-9
        =-3731/1800<0.                         (16)

At k=3/2, direct expansion with x=1-a+s gives

    4*Q(3/2)=F(alpha)
      =-21+11*b^2+8*a+14*b+26*s+13*s^2
                  -2*a*s+10*a*b-10*s*b.        (17)

Here a,b are still the exact q=1 functions of alpha. We next prove
that the whole expression (17) increases with alpha, so that only
the endpoint s=1/6 must be checked.

## 5. One derivative proves the entire alpha comparison

At q=1 and 0<=s<=1/6, the elementary bounds are

    c>59/60,
    7/20<b<9/20,
    a<15/16,
    a*b<=2/5.                                  (18)

For the lower b bound, use
`W0^2=3+2*(c+s)<16/3<(7/3)^2` and
`c-s>59/60-1/6=49/60`, hence b>7/20. The upper b bound was
already proved in Section 3. It implies a*b<=2/5 because
`b*sqrt(1-b^2)` increases for b<1/sqrt(2), and its value at
b=1/sqrt(5) is 2/5. The lower b bound gives a<15/16 by squaring.

The exact original q=1 angle derivative is

    psi'=-(2+c+s)/(3+2*(c+s)),
    -3/5<=psi'<0.

Differentiating (17) along the same actual a=cos(psi), b=sin(psi)
gives

    F'=(26+26*s-2*a-10*b)*c+psi'*G,
    G=22*a*b+14*a+10*(a^2-b^2)-8*b-10*a*s+2*b*s.

All following are whole-interval bounds from (18):

    (26+26*s-2*a-10*b)*c>(157/8)*(59/60)=9263/480,
    G<44/5+105/8+151/20-14/5+3/20=1073/40.

If G<=0, its contribution psi'*G is nonnegative. If G>0,
it is bounded below by `-(3/5)*(1073/40)`. In both cases,

    F'>9263/480-3219/200=7687/2400>0.            (19)

Thus (17) is largest at s=1/6.

## 6. The final rational endpoint has a strict reserve

At s=1/6, put c0=sqrt(35)/6. The q=1 formulas simplify to

    b^2=(3-c0)/(10+6*c0),
    a^2=1-b^2.

Since c0>493/500,

    b^2<1007/7958<(89/250)^2.

The last cross-multiplied reserve is
`7958*7921-1007*62500=97818>0`. Also c0<1 gives b^2>1/8,
so a^2<7/8 and

    a<117/125,

because `8*117^2-7*125^2=137>0`.

At this endpoint (17) is

    F=11*b^2+(23/3)*a+(37/3)*b+10*a*b-587/36.

Every displayed a,b coefficient is positive. The preceding bounds
give the exact rational comparison

    F<11*(89/250)^2+(23/3)*(117/125)
           +(37/3)*(89/250)+10*(117/125)*(89/250)-587/36
      =-3553/281250<0.                          (20)

For a direct integer check, multiplication by 562500 gives positive
terms totaling 9164769, against 9171875 from the final constant.
This is precisely the reserve 7106.

Equations (19),(20) prove Q(3/2)<0 on the whole alpha interval.
Together with (16), convexity proves Q(k)<0 for every k in (15).
The monotonicities in Section 3 return this strict inequality to
every unchanged original H,q in (1),(3). This proves (11), and
(10) gives

    h_W<1.                                      (21)

## 7. The actual W depth is positive, so the entire face lies in one strip

No unproved global half-plane assignment is needed for W. From
(2) and the original angle definitions,

    psi+zeta=theta_D+chi+delta-pi/2.

The whole radial-C angle fact quoted in Section 1 therefore gives

    delta-pi/4<psi+zeta<delta.

All these angles lie in (-pi/4,pi/4), where sine is increasing.
Using (6),(8),(9),

    h_W>kappa/2-sin(pi/4-delta)
        =kappa/2-(kappa-sigma)/sqrt(2)
        >kappa*(1/2-1/(3*sqrt(2)))>0.           (22)

Here sigma>2*kappa/3 is exactly k<3/2. Combining (21),(22)
with (5),(7), the five actual contact-pentagon vertices satisfy

    0<d-W.j<1,
    0<d-K.j<1,
    0<d-L.j<1,
    d-T.j=d-U.j=0.

The finite maximum of their three positive depths is strictly less
than one. Consequently the entire contact pentagon

    W -- L -- U -- T -- K -- W

and its bounded region lie in a common closed strip of width
strictly less than one.

The inherited physical contact-cycle localization is the same one
used in `CONTACT_RING_HOLE_AREA.md`, Section 1, and in Sections 5--6
of the opposite-return aperture source. All consecutive segments
join actual applications inside the relevant closed convex unit.
Every original central extra is in the bounded free side of that
same actual weak contact polygon. This is independent of the
transverse mean or side offset of N. In a weak physical junction,
the usual compatible physical routing localizes each compact
subset of an extra interior to the same bounded side; its label
cannot cross any occupied segment. Additional physical contacts
can subdivide this region but cannot enlarge it beyond the strip.

Every unit square has projection width at least one in every
direction: in a unit orthonormal side frame that width is
`|cos(t)|+|sin(t)|>=1`. An actual whole unit cannot therefore lie
in this strictly narrower strip. The entire original central face
contains no additional unit, as asserted.

This proof retained all nine physical units, original degrees,
full stars, means and circle weights. Its finite comparisons are
the exact continuous inequalities printed above. No Lean, CI,
computational exclusion certificate or external proof script was
used.
