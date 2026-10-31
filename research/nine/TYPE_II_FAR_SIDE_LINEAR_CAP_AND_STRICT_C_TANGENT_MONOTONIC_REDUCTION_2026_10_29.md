# A whole-domain linear cap and strict tangent monotonicity for the far side

Date: October 29, 2026 UTC.
Authors: far-vertex continuation and root continuation.

The root continuation supplied the strong linear-cap comparison and
its concavity proof in Section 3. The far-vertex continuation supplied
the slope variables, tangent derivative bound and positive q comparison.
Both independently supplied the connecting-interval argument. These
contributions are disclosed for a separate independent review.

**Status: complete proposed necessary scalar reduction of the entire
original far-side domain, frozen for independent review.** One continuous
linear cap and one strict monotonicity argument reduce the original
C tangent to a single explicit comparison function on 0<ell<1/2.
The final inequality bounding that function by 1/2 is not proved.
No new physical mask or whole family is declared closed here.

## 1. Entire original chart and exact scalar names

Retain the full original unique-circle Type II far-A-vertex side row of
D02.L135, with all nine actual squares, every original force, torque,
selected normal, actual point or full shared mean, physical circle mask
and individual zero coefficient. A,D remain unloaded true3; V,B,C
remain loaded true2; N remains the original unloaded true2. The full
V/A/D equations and all unused B/C/N equations remain. The prior
conditional common selection is unchanged.

Use the two complete operative sources pinned in Section 8. In the
actual oriented frame (d0,n), introduce only scalar abbreviations

    e=ell, J=sqrt(1+e^2), A=1+e, B=1-e,
    0<e<1/sqrt(3)<3/5,
    d=B/J, L=A/J,
    H,k>0, H^2+k^2=1,
    q=A*k/H-1>0,
    v=k+e*H<1,
    a=1/sqrt(1+q^2), k<a,
    z=Z.n/Z.d0=(L-H*J^2)/d>0.

Here d is a scalar and d0 is an actual unit vector; z is a radial
slope, not an original contact mean. The complete V equation gives

    Z=R*(1,z)/sqrt(1+z^2),
    P=Z-(d,L),
    79/40<=R<=sqrt(1105)/16<25/12.

The actual physical C cap is

    P.n=R*z/sqrt(1+z^2)-L>-1/60.                 (1)

Put u=z-e and T=q+e, used only as scalar abbreviations below. The
full original force ratio and D mean are exactly

    p=rho/nu=T/u,
    delta_D=T*v/(T+u).

Indeed u=J^2*(1-J*H)/B and substitution in the original
p=S^3*(1-e)*(q+e)/(S-H), S=1/J, gives that identity. Thus the
unchanged actual tangent is

    Q_C.d0=R/sqrt(1+z^2)-B/J-delta_D.             (2)

Every mean in (2) is still the original full D-torque mean. It is
not independently chosen to fit the comparison below.

## 2. The entire original side domain has e<1/2 and z<1

Positive squaring of v=k+eH<1 gives H*J^2>2e. Since
L-d=2e/J<2e, this yields

    0<z<1,
    z<z_v(e)=(A-2e*J)/B.

Direct differentiation on 0<e<1 gives

    z_v'(e)=2*(1-J-e^2*B/J)/B^2<0.

If e>=1/2, then

    z<z_v(1/2)=3-sqrt(5)<4/5,
    L>=3/sqrt(5)>4/3.

The strict comparisons follow by positive squaring. Consequently

    Z.n<(25/12)*4/sqrt(41)<125/96,
    P.n<125/96-4/3=-1/32<-1/60,

contrary to (1). The middle inequality uses sqrt(41)>32/5.
Therefore the whole original side domain satisfies

    0<e<1/2.                                      (3)

## 3. One strict linear cap on the whole interval

Define the comparison line and scalar function on [0,1/2] by

    w(e)=8/15+(4/7)*e,
    Phi(e)=L-1/60-(25/12)*w(e)/sqrt(1+w(e)^2).

We prove Phi>0 on the entire closed interval by strict concavity.
The exact second derivative of L is

    L''=-(1+3e-2e^2)/(1+e^2)^(5/2)<=-1.

To check the last comparison without a numerical estimate, the numerator
is at least 1+2e. Also

    (1+e^2)^(5/2)<=(1+e^2)^3<=1+2e,

because for 0<=e<=1/2,

    3e+3e^3+e^5<=61/32<2.

The equality e=0 causes no problem. The other second-derivative term is

    (100/49)*w/(1+w^2)^(5/2).

For w>=0 the function w/(1+w^2)^(5/2) has its global maximum
at w=1/2, as its derivative has the sign of 1-4w^2. Its maximum
is 16/(25*sqrt(5)). Hence

    Phi''<=-1+64/(49*sqrt(5))<-1+32/49<0.

Both comparison endpoints are strictly positive. At e=0 the
8-15-17 identity gives exactly

    Phi(0)=59/60-(25/12)*(8/17)=1/340>0.

At e=1/2, w=86/105. Using

    3/sqrt(5)>67/50,
    sqrt(18421)>271/2,

whose positive squared reserves are 11/2500 and 243/4 respectively,
gives

    Phi(1/2)>397/300-1075/813=29/27100>0.

Strict concavity places every value above the positive chord between
these endpoints, proving Phi>0 throughout [0,1/2]. Because the
function z/sqrt(1+z^2) is strictly increasing, (1) and R<25/12
now imply the uniform original cap

    z>w(e)=8/15+(4/7)e.                            (4)

In particular every original scalar slope reserve satisfies

    u=z-e>w(e)-e>=67/210>3/10.                    (5)

No angular subinterval or original force ratio was selected to obtain
(4). It follows from the full original cap and one closed-interval
concavity proof.

## 4. The entire linear comparison has q>0

The next calculation verifies the positive branch even at z=w(e),
where no hypothetical C square or physical cap is asserted.

At the scalar locus q=0, positive H,k with H^2+k^2=1 give

    H0=A/sqrt(1+A^2),
    u0=J^2*(1-J*H0)/B.

For every e in [0,1/2], we claim u0<3/10. Since B,J,A and
J^2-(3/10)B are positive, this is equivalent by positive squaring to

    A^2*J^6-(A^2+1)*(J^2-(3/10)B)^2>0.

The exact expansion is

    1/50+(9/50)e-(31/100)e^2+(7/5)e^3
      +(131/100)e^4+(17/5)e^5+3e^6+2e^7+e^8.

It is strictly positive on the whole interval: the only negative
coefficient combines as

    (9/50)e-(31/100)e^2=e*(18-31e)/100>=e/40>=0,

and every other coefficient is positive, including the constant 1/50.
This is one exact continuous polynomial comparison, without a table.

Since w(e)-e>=67/210>3/10>u0, and u decreases strictly as H
increases, the positive H at z=w(e) is strictly below H0.
Consequently k/H is larger than at q=0, proving

    q(w(e))>0                                     (6)

for the whole comparison interval. Positivity of H at this comparison
also follows directly from

    H(w(e))=(49+101e+60e^2)/(105*J^3)>0.

Moreover u>0 implies H<S=1/J<=1, so k=sqrt(1-H^2)>0 and
all positive square-root branches used here are valid.

## 5. Complete connecting-interval verification

Fix one original actual e,R and vary only the comparison slope along

    w(e)<=z<=z_actual.

No varied scalar value is asserted to be a physical packing. The
purpose is to compare the exact function in (2), while the original
packing and every original equation remain unchanged.

As z decreases, H=(L-dz)/J^2 increases, k decreases and
q=A*k/H-1 decreases. By (6) it remains strictly positive. Thus
u=z-e remains positive and every original-ratio denominator is positive.
Since k decreases while a(q)=1/sqrt(1+q^2) increases, the original
side inequality k<a is preserved throughout the comparison interval.

At the actual point H-e*k>0. Indeed v<1 implies H>2e/J^2>e/J,
and positive squaring gives H>e*k. This sign remains true toward w,
because H increases and k decreases. With H=cos(eta), k=sin(eta),
the identities

    z_eta=J^3*k/B>0,
    v_eta=H-e*k>0

show v_z>0 throughout. Therefore moving toward w decreases v and
retains 0<v<1. The fixed e,R, all exact scalar identities, H,k>0,
z<1, z>=w>1/2 and u>3/10 remain throughout. This verifies every
premise used in the derivative proof below; no cap at the comparison
point is needed.

## 6. A strict derivative bound on the entire connecting interval

Differentiate T=q+e at fixed e. The exact identity is

    T_z=(1-e^2)/(J^3*k*H^2).

The function k*(1-k^2) has maximum 2/(3*sqrt(3))<2/5. By
e<1/2 and sqrt(5)<9/4,

    1-e^2>3/4,
    J^3<5*sqrt(5)/8<45/32,
    T_z>4/3.                                       (7)

The already verified v_z>0 and delta_D=T*v/(T+u) give

    (delta_D)_z
       =v*(u*T_z-T)/(T+u)^2+T*v_z/(T+u).

If u*T_z-T>=0 this derivative is positive. Otherwise 0<v<1
and (7) yield

    (delta_D)_z>((4/3)*u-T)/(T+u)^2
                >=-3/(28u)>-5/14.              (8)

The middle inequality holds for every T,u>0: the exact minimum
as a function of T is at T=(11/3)u. Equivalently, multiplying by
the positive 84u(T+u)^2 reduces it to the square

    (3T-11u)^2>=0.

No original T or mean is moved to that comparison minimum.

For z in [1/2,1], differentiation of z/(1+z^2)^(3/2) shows
its minimum is at an endpoint. Its endpoint values satisfy

    4/(5*sqrt(5))>1/(2*sqrt(2)).

Positive squaring has reserve 128-125=3. Since R>sqrt(2),
differentiating (2) and using (8) therefore gives the whole-interval
strict bound

    (Q_C.d0)_z
       =-R*z/(1+z^2)^(3/2)-(delta_D)_z
       <-1/2+5/14=-1/7<0.                       (9)

Every support mean and force ratio in (9) is still its original formula.
The derivative concerns only the explicitly defined comparison function.

## 7. One explicit endpoint function remains

Equations (4),(9) and the verified connecting interval prove

    Q_C.d0 < R/sqrt(1+w(e)^2)-B/J-delta_D(e,w(e))
            < (25/12)/sqrt(1+w(e)^2)-B/J-delta_D(e,w(e)).

The final comparison radius 25/12 is only an arithmetic upper bound;
no physical circle or square is moved to that radius.

For exact subsequent work, put

    P0=49+101e+60e^2,
    K=sqrt(11025*J^6-P0^2),
    w=(56+60e)/105,
    H=P0/(105*J^3), k=K/(105*J^3).

The whole interval in Section 4 verifies K>0 and q=A*K/P0-1>0.
The exact original mean at this comparison is

    delta_D(e,w)
      =(A*K-B*P0)*(K+e*P0)
        /[J^3*(105*A*K+(60e-49)*P0)].            (10)

Its denominator is positive because it is the positive original
T+u denominator after the substitutions above. Thus the remaining
single-variable target is precisely

    (25/12)/sqrt(1+w(e)^2)-B/J-delta_D(e,w(e))<=1/2
    for the actual allowed 0<e<1/2.             (11)

**Inequality (11) is not proved in this source.** Therefore this source
does not conclude Q_C.d0<=1/2, does not exclude either remaining
physical radial endpoint mask, and closes no original far-side family.
It supplies one complete hand reduction of the whole original scalar
domain, with every sign and comparison interval verified.

## 8. Complete inputs and verification boundary

Both direct sources were read in full:

| Source | SHA256 | Exact use |
| --- | --- | --- |
| TYPE_II_FAR_RETURN_SIDE_CHANNEL_EXCLUDES_BOTH_PARALLEL_LOADED_ENDPOINTS_2026_10_29.md | e573ec4e567bb3e255ddbc9348b24dd4780651beebd1f3ea713e949930929b68 | Entire original side entry, original degrees and means, k<a and every retained physical/load boundary |
| UNIVERSAL_UNIT_SQUARE_CAP_AND_COMPLETE_TYPE_II_FAR_RETURN_DIAGONAL_EXCLUSION_2026_10_29.md | f4f2f293e038ea9f42dc8572cb8f216c9b9718a8fb14c4ac215232efcaf34e3c | Original positive force-ratio identities, exact V radial direction, genuine v<1, original physical cap and all original means |

The constant, derivative and concavity comparisons are complete above.
The one expanded polynomial was recomputed with exact rational
arithmetic; its positivity is the printed positive-term argument.
The final remaining target (11) is not treated as an adopted fact.
This manuscript needs separate full independent review because both
listed authors contributed to the proof.

No pose search, angle mesh, packing certificate, sampled exclusion,
changed normal, replacement mean, shortened star, altered physical
mask, omitted unit, Lean/Lake invocation, CI, shared-metadata mutation
or remote write was used.
