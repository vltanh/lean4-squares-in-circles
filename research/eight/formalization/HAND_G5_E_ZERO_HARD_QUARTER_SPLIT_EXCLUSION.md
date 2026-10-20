# The whole E-zero hard-quarter split is excluded

## 1. Complete conditional branch theorem

Put `Q=9789/2500`. Consider the original seven shared centers with

\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,0),\qquad b_i\ge0,
\]

and the original primary and corner constraints

\[
 a_i\ge b_i,\qquad
 (a_i+1/2)^2+(b_i+1/2)^2\le Q.
\tag{1}
\]

After a common frame shift suppose

\[
 \theta_H=\theta_G=t,\quad\theta_A=\theta_B=0,
 \quad\theta_T=\theta_D=-u,\quad\theta_E=-u+\delta,
\tag{2}
\]

where

\[
 t,u,\delta\ge0,\qquad
 \epsilon:=t+u-\delta\ge0,\qquad
 t+u=\delta+\epsilon\le7/10.
\tag{3}
\]

Retain original transverse witnesses on HG, AB, TD; an original GA
axis 0; an original BT axis 2; an original DE axis 3; and an original
EH axis 1. In the owner notation, T owns TB and D owns ED. All ties
are allowed. These are explicit branch hypotheses, not owner
conclusions imported from a later mismatch scale.

**Theorem.** No such cycle exists. The actual shared A and B corner
coordinates would simultaneously satisfy

\[
 Z_A+Z_B\ge2
 \quad\text{and}\quad
 Z_A+Z_B<2-\frac{149}{625000},
 \qquad Z_i=b_i+\frac12.
\tag{4}
\]

This extends the aligned-GA branch in
`HAND_G4_ALIGNED_ZERO_E_ZERO_BRANCH_EXCLUSION.md` to every split
of the same total frame span between the GA tilt t and the negative
BT error `-u`. It keeps the same E-zero condition, all three aligned
zero edges, and the indicated original quarter/mixed witnesses.
It is a complete continuous branch exclusion, not a proof that all
candidate cycles reduce to this branch, and not a G4 or G5 contraction.

No contact equality, outer-boundary equality, tangent cut, or core
slider value is assumed. Core avoidance and physical-gap bounds may
be retained but are unnecessary for the proof.

## 2. The same E state bounds both endpoint transverse coordinates

Use the functions proved in the cited branch note:

\[
 v=\sqrt{Q-1/4}-1,\qquad
 C_0=\sqrt{Q/2}-1/2,
\]
\[
 h(z)=\sqrt{Q-[1+\tfrac12\cos z-v\sin z]^2}-\frac12,
 \qquad B(z)=\min\{C_0,h(z)\}.
\tag{5}
\]

They are well-defined for `0<=z<=7/10`, h increases there, and

\[
                 \frac{79}{100}<h(0)\le B(z)<\frac9{10}.
\tag{6}
\]

For completeness, the lower bound follows from
`(129/100)^2<Q-9/4`; the upper bound follows from
`Q/2<(7/5)^2`. The positivity and monotonicity of h follow from
positivity and strict decrease of `1+cos(z)/2-v*sin(z)`.

Because the original E transverse coordinate is zero, its primary
coordinate satisfies `a_E<=v+1/2`. The actual DE3 and EH1 witnesses
are

\[
 a_D+a_E\sin\delta\ge W(\delta),\qquad
 a_H+a_E\sin\epsilon\ge W(\epsilon),
\]

with `W(z)=(1+cos z+sin z)/2` on this nonnegative interval.
Their original circles and primary cones therefore give

\[
                     b_D\le B(\delta),\qquad
                     b_H\le B(\epsilon).
\tag{7}
\]

Both bounds use the same unchanged E state. They hold with arbitrary
original radial slack.

## 3. Collect the two forces on each of A and B

For `0<=z<=7/10` and `79/100<=b<=9/10`, define

\[
 \begin{aligned}
 D&=\frac32-b,\qquad c=\cos z,\qquad s=\sin z,\\
 C&=D+c,\qquad w=\sqrt{Q-C^2},\\
 \mathcal L(z,b)&=cw-sC.
 \end{aligned}
\tag{8}
\]

This is the upper transverse corner coordinate allowed by the circle
and the projection `X*c-Z*s>=C`. The derivation is the elementary
circular-cap formula (7) in
`HAND_G5_SHARED_CENTER_FORWARD_REDUCTION_AT_ONE_TENTH.md`.
It can also be obtained by rotating the vector `(C,w)`.

The original GA0 witness and the HG zero witness give

\[
 a_A\cos t-b_A\sin t\ge1+W(t)-b_H.
\]

Writing `X_A=a_A+1/2`, `Z_A=b_A+1/2`, and using (7), this becomes

\[
 X_A\cos t-Z_A\sin t\ge\frac32+\cos t-B(\epsilon).
\]

Consequently

\[
                         Z_A\le\mathcal L(t,B(\epsilon)).
\tag{9}
\]

The original BT2 witness has error `-u` and gives

\[
 a_B\cos u-b_B\sin u-b_T\ge W(u).
\]

Add the original TD inequality `b_T+b_D>=1` and use (7).
The same corner conversion gives

\[
                         Z_B\le\mathcal L(u,B(\delta)).
\tag{10}
\]

Finally AB gives `Z_A+Z_B>=2`. Hence the actual seven vertices
imply the single necessary split inequality

\[
 \mathcal L(t,B(\epsilon))+\mathcal L(u,B(\delta))\ge2,
 \qquad t+u=\delta+\epsilon.
\tag{11}
\]

The shared G and T coordinates canceled before applying any circle.
The common A and B coordinates are then joined by their actual AB
constraint. Thus (11) is not a sum of independent pair minima.

## 4. One exact convexity factorization on the whole angle interval

Fix b in the domain (8), so `3/5<=D<=71/100`. On the entire
interval `0<=z<=7/10`, one has `c>=3/4`, `s>=0`, and `w>0`.
In fact `C<=171/100<sqrt(Q)`.

First, `L:=mathcal L(z,b)>0`. Because c, C, w are positive,

\[
 cw>sC
 \quad\Longleftrightarrow\quad
 \sqrt Q\,c>C
 \quad\Longleftrightarrow\quad
 (\sqrt Q-1)c>D.
\]

The last comparison follows from

\[
 (\sqrt Q-1)c>\left(\frac{39}{20}-1\right)\frac34
                 =\frac{57}{80}>\frac{71}{100}.
\tag{12}
\]

Put

\[
                    X=Cc+ws,\qquad k=w-s.
\]

The following identity proves `k>0` and a stronger estimate:

\[
 w^2-\left(\frac{s(C+1)}{1+c}\right)^2
 =\frac{Q-2D(D+1)-1+c(Q-2D-1)}{1+c}>0.
\tag{13}
\]

Indeed, for `D<=71/100` the two numerator coefficients are at
least `2437/5000` and `3739/2500`, respectively. Both are positive.
Taking positive square roots in (13) gives

\[
                  w-s-\frac{Ds}{1+c}>0.
\]

An exact expansion now gives

\[
 \begin{aligned}
 X-k^2
 &=D^2+3D+2-Q
       +3s\left(w-s-\frac{Ds}{1+c}\right)\\
 &\ge\frac{611}{2500}>0.
 \end{aligned}
\tag{14}
\]

Here the polynomial `D^2+3D+2-Q` increases for `D>=3/5`,
and its value at `3/5` is `611/2500`.

Differentiating the definitions gives the short identities

\[
 w'=Cs/w,\quad k'=-L/w,\quad X'=Lk/w,\quad L'=-Xk/w.
\]

Thus the second derivative factors as

\[
 \boxed{
 L''=\frac{Lw(X-k^2)+XkCs}{w^3}>0.}
\tag{15}
\]

All factors in the first term are positive by (12)--(14); the second
term is nonnegative. This proves strict convexity of
`z -> mathcal L(z,b)` on the entire interval, with no angle split
or numerical derivative bound.

## 5. The already-proved endpoint scalar excludes both split endpoints

Let `a=delta+epsilon<=7/10`. The cited aligned-GA branch proves,
for all such nonnegative delta and epsilon, that

\[
 \begin{gathered}
 w_\epsilon=\sqrt{Q-(5/2-B(\epsilon))^2},\quad
 Y_\epsilon=2-w_\epsilon,\quad
 r_\epsilon=\sqrt{Q-Y_\epsilon^2},\\
 F(\epsilon,\delta):=
 B(\delta)+(r_\epsilon-1)\cos a
                    -Y_\epsilon\sin a
 <\frac{1499702}{10^6}.
 \end{gathered}
\tag{16}
\]

This is the explicit scalar result of Sections 3--6 of
`HAND_G4_ALIGNED_ZERO_E_ZERO_BRANCH_EXCLUSION.md`. It was proved
there by one cap reduction, a uniform Hessian reserve, and one rational
comparison point. No existence of a comparison packing is required
to use that scalar inequality.

We translate (16) to the cap sum. Put

\[
 L_a=\mathcal L(a,B(\delta)),\qquad
 C_a=\frac32+\cos a-B(\delta),
\]

and define the decreasing function

\[
                    g(z)=\cos a\sqrt{Q-z^2}-z\sin a.
\]

Rotating `(C_a,sqrt(Q-C_a^2))` shows `g(L_a)=C_a`.
Also (16) says

\[
 g(Y_\epsilon)-g(L_a)
      =F(\epsilon,\delta)-\frac32
      <-\frac{149}{500000}.
\tag{17}
\]

Consequently `Y_epsilon>L_a>0`. The elementary bounds in the cited
note give `Y_epsilon<101/100` and
`sqrt(Q-Y_epsilon^2)>17/10`. On `[L_a,Y_epsilon]`, therefore,

\[
 0<-g'(z)
 =\frac{z\cos a}{\sqrt{Q-z^2}}+\sin a
 <\frac{101}{170}+\frac{13}{20}<\frac54.
\]

Integration of (17) yields

\[
 Y_\epsilon-L_a>\frac{149}{625000},
\]

or, equivalently,

\[
 \mathcal L(0,B(\epsilon))+\mathcal L(a,B(\delta))
                   <2-\frac{149}{625000}.
\tag{18}
\]

Interchanging delta and epsilon in the same proved scalar result also
gives

\[
 \mathcal L(a,B(\epsilon))+\mathcal L(0,B(\delta))
                   <2-\frac{149}{625000}.
\tag{19}
\]

## 6. Every split lies below those two endpoints

For `0<=z<=a`, consider

\[
 \Psi(z)=\mathcal L(z,B(\epsilon))
                      +\mathcal L(a-z,B(\delta)).
\]

Equation (15) makes this function convex. Its maximum on the interval
is therefore at an endpoint. Equations (18)--(19) give

\[
                       \Psi(z)<2-\frac{149}{625000}
                         \qquad(0\le z\le a).
\tag{20}
\]

When `a=0`, the same assertion is just (18). Evaluate (20) at the
actual split `z=t`, `a-z=u`. Together with (9)--(10), it contradicts
the original AB lower bound in (11) and proves (4).

This is a scalar convexity comparison after deriving inequalities
from the actual common centers. It does not rotate an original square,
move a center to contact, replace a feasible owner, or assume that an
endpoint comparison configuration exists.

The remaining reduction must still address `y_E<0`, nonzero errors
on HG/AB/TD, the other original owner alternatives, and the other
signs of the mixed and quarter errors. The theorem resolves exactly
the branch stated in (1)--(3), throughout its full continuous frame
span. No generated angle/state cover, numerical minimum, certificate
table, Lean compilation, or CI run is a premise.
