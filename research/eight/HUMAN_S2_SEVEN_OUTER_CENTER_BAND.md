# A centered-band necessity for seven outer centers in the S2 pattern

## Theorem

Assume eight unit squares with independent arbitrary
orientations fit in D_R, with R^2<=9789/2500.
Let C be their unique origin-containing square
and suppose the seven exterior squares all have
single-side central separator statuses with
opposite-side counts

    S2=(3+0,2+2).

Let t denote the signed central-center coordinate
on the **2+2** axis in the central square's own
frame. If all seven exterior square centers have
norm at least one (the macro-branch k=7), then

    **|t|<1/8.**                                      (1)

Equivalently, the S2/k=7 branch with
1/8<=|t|<5/24 is **completely impossible**,
with no assumptions about contacts or frames.

The proof is an exact angular arc comparison,
using the known whole-orientation outer-center
pair gap delta0=pi/4-1/500. The only difficult
endpoint comparison is one positive rational
square difference displayed below. This does
not exclude S2/k=7 when |t|<1/8, nor prove
the unrestricted eight-square optimality.

## 1. An outer-center radial ceiling and a sector saturation fact

Every packed square center p obeys

    |p|<r0:=283/200.                                (2)

Indeed the exact farthest-vertex formula gives
R^2>=|p|^2+|p|+1/2, and at r0 the right side
is 156689/40000>9789/2500=156624/40000.

The hand theorem HUMAN_STABLE_OUTER_ANGLE.md
says that two distinct squares with center
norm at least one have smaller angular
center-ray separation strictly greater than

    delta0=pi/4-1/500.                              (3)

In particular if k>=2 such center rays all
fit in a single ordinary angle interval of
width W (with no wrap-around), then sorting
the k directions gives

    W>(k-1)*delta0.                                 (4)

Every consecutive **linear** angle difference
is >delta0: if it is <=pi, apply the
smaller-angle separation (3); if >pi,
it already exceeds delta0. Adding proves (4).

Thus seven outer centers can never fit in
an arc of width <=6*delta0.

## 2. The two perpendicular side populations confine all seven rays

Rotate/refelect C's own frame so its S2
populations are R=3,L=0,U=2,D=2.
Write p_C=(a,t), so the U and D
outward side line offsets are

    h_U=1/2+t,        h_D=1/2-t.

The respective square centers have

    y_U>=1+t>0,      y_D<=-(1-t)<0,               (5)

because a unit square has projected
half-width at least 1/2 on every
unit direction.

Put

    A(t)=asin((1+t)/r0),
    B(t)=asin((1-t)/r0).

The prior two-cap theorem gives |t|<5/24,
so both inverse-sine arguments lie
strictly between zero and one.

Equation (2) and the side signs imply
every U center ray has angle

    0<theta_U<pi-A(t),

and every D center ray has angle

    -pi+B(t)<theta_D<0.                             (6)

Each R center has positive x coordinate
(x_R>h_R+1/2>0) and therefore angle
in (-pi/2,pi/2). Since B,A in (0,pi/2),
all seven rays consequently lie in the
single unwrapped angular interval

    I=(-pi+B(t),pi-A(t)),

whose width is

    W=2*pi-[A(t)+B(t)].                             (7)

Hence the outer-center k=7 branch will be
excluded if

    A(t)+B(t)>pi/2+6/500
            =pi/2+3/250.                            (8)

## 3. The inverse-sine sum increases with |t|

The function f(t)=A(t)+B(t) is even.
For 0<t<=5/24, differentiating gives

    f'(t)=1/sqrt(r0^2-(1+t)^2)
          -1/sqrt(r0^2-(1-t)^2)>0,                 (9)

since r0>1+t>1-t>0. Thus for |t|>=1/8,

    f(t)>=f(1/8).                                  (10)

Set u=9/8,d=7/8 and r2=r0^2=80089/40000.
Let

    P=(r2-u^2)*(r2-d^2)
       =22771989/25000000.

The cosine addition identity gives

    cos(f(1/8))
       =[sqrt(P)-u*d]/r2.                           (11)

The relevant purely rational inequality is

    (u*d-r2*(3/250))^2-P
      =1138929731289/100000000000000>0.          (12)

Also u*d-r2*(3/250)=9603483/10000000>0.
Taking positive square roots in (12) shows

    sqrt(P)<u*d-r2*(3/250),

and substitution into (11) yields

    cos(f(1/8))< -3/250.                           (13)

For x=3/250>0 we have sin x<x,
so

    cos(pi/2+x)=-sin x> -3/250.

Cosine is strictly decreasing on [0,pi],
and f(1/8) lies in (0,pi).
Equation (13) therefore proves

    f(1/8)>pi/2+3/250.                             (14)

Combining (10) and (14) proves (8)
for all |t|>=1/8.

## 4. Contradiction and remaining branches

If k=7 and |t|>=1/8, equation (7) and (8)
force all seven outer center rays into
an interval of width

    W<2*pi-(pi/2+3/250)
      =3*pi/2-6/500=6*delta0,

contradicting the general angular saturation
inequality (4). This proves (1). QED.

The new exact pruning joins the previously
proved S2 conditions:

* S2/k=3 requires the triple-side offset
  <7/50 and |t|>1/10.
* S2/k=4 is excluded when the triple
  offset >=7/50 and |t|<=1/10.
* **S2/k=7 requires |t|<1/8.**

These leave real continuous intervals rather
than asserting one forced candidate frame.
The sharp family equality candidate has
status S4, not S2, and is unaffected.
The global lower bound R8>=Rhat remains OPEN.
