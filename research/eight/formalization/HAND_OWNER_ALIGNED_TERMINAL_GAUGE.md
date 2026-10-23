# An owner-aligned gauge removes the singular terminal force remainder

## Status and exact scope

This note proves an exact replacement for the five force-norm estimates in
Section 7.1 of `HAND_TERMINAL_RESERVES_AND_SQUARE_COMPLETION_WITHOUT_TABLES.md`.
It covers every one of the 32 intended original owner choices, including
weak contacts and ties. The geometric E-force is made constant by the choice
of comparison frame. Consequently its former coefficient
`delta * w / sin(t)` is absent, rather than estimated more tightly.

The complete sharp terminal is **not** asserted on an enlarged mismatch
interval here. The support/offset terms, slider terms, family defect, and
first angular derivatives must be assembled in this new gauge before
claiming such an extension. The global G3--G5 capture hypotheses and the
mixed-owner restrictions are not supplied by this lemma.

All decimals below denote exact rationals. The argument is an identity
and a whole-domain Taylor estimate, not a state or angle subdivision.

## 1. Choose actual owner frames, not two prescribed vertex frames

Use the actual intended signed normals in the conditional terminal:
AB is owned by A or B; TB by T or B; DT by D or T; ED by E or D;
GA by G; HG by H or G; and HE by H. Here TB, DT, ED and HE have the
geometric directions specified in the existing terminal theorem.

Let the physical frames of A, B, T, D, E be denoted by
`theta_A, theta_B, theta_T, theta_D, theta_E`, and those of G and H
by `theta_G, theta_H`. Choose the ED owner once. Rotate the whole
configuration so that this owner's physical frame is zero. Put

\[
 x_1=\theta_B-\theta_A,\quad
 x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad
 x_4=\theta_E-\theta_D,\quad
 h=\theta_H-\theta_G,
\]
\[
 S=|x_1|+|x_2|+|x_3|+|x_4|+|h|,\qquad \tau=\theta_H.
\tag{1}
\]
These differences are unchanged by the rigid rotation. Let
`o` be 0 when D owns ED and 1 when E owns ED. Then the exact frames are

\[
\begin{aligned}
 a_A&=-x_1-x_2-x_3-o x_4,& a_B&=a_A+x_1,\\
 a_T&=a_B+x_2,&a_D&=a_T+x_3,&a_E&=a_D+x_4,\\
 \theta_H&=\tau,&\theta_G&=\tau-h.
\end{aligned}
\tag{2}
\]
In particular the actual ED normal is precisely `f_0`, and the actual
HE normal is precisely `f_tau`. No assertion about centers or radial
kinds was used to make this choice.

If the old gauge has A-frame zero, G-frame `t`, H-error `h`, and ED-owner
error `d_0`, then

\[
                    \tau=t+h-d_0,\qquad |\tau-t|\le S.
\tag{3}
\]
Thus a terminal window imposed on `t` must not silently be imposed on
`tau`. The quantitative application below explicitly assumes that the
comparison family is defined in its stated `tau` window.

## 2. All seven actual forces

Write `e_z=(cos z,sin z)` and `f_z=(-sin z,cos z)`. Take the positive
stationary family weights at `(q,u(q,tau),tau)` from the existing terminal
note. Denote its edge weights by

\[
 \alpha=\lambda_{AB},\quad
 \beta=\lambda_{TB}=\lambda_{DT},\quad
 \delta=\lambda_{ED},\quad
 \epsilon=\lambda_{HE},\quad
 \omega=\lambda_{GA}=\lambda_{HG}.
\]
Let `b_0` be the actual AB-owner frame, `u_0` the TB-owner frame,
and `v_0` the DT-owner frame. Thus

\[
 b_0\in\{a_A,a_B\},\quad
 u_0\in\{a_B,a_T\},\quad
 v_0\in\{a_T,a_D\}.
\]
Let `zeta` be 0 when H owns HG and 1 when G owns HG, so the HG normal is
`n=e_(tau-zeta*h)`. Subtracting the positively weighted actual signed
separating gaps gives exactly these center forces:

\[
\begin{aligned}
 F_A&=\alpha f_{b_0}-\omega e_{\tau-h},&
 F_B&=-\alpha f_{b_0}-\beta e_{u_0},\\
 F_D&=\beta e_{v_0}-\delta f_0,&
 F_E&=\delta f_0-\epsilon f_\tau,\\
 F_H&=\omega n+\epsilon f_\tau,&
 F_T&=\beta(e_{u_0}-e_{v_0}),\\
 F_G&=\omega(e_{\tau-h}-n).
\end{aligned}
\tag{4}
\]
These are the same actual gaps as in the previous proof. In particular
no originally selected witness has been replaced by a preferred axis.

For the chosen stationary comparison data and fixed `tau`, **F_E does
not depend on any of the five errors**. Hence

\[
 -\frac{|F_E|^2}{4\mu_E}
 =-\frac{\delta^2+\epsilon^2-2\delta\epsilon\cos\tau}
          {4\mu_E}
\tag{5}
\]
is constant. This is the cancellation of the former large E remainder.
It holds even though `mu_E` is small, and does not use a lower bound on it.

## 3. The exact force-norm identity for every owner assignment

Retain the stationary notation `r,U,V,u,c=cos(tau),s=sin(tau),k_1`
and the positive circle weights of the terminal note. Define

\[
 K_A=\frac{\alpha\omega}{2\mu_A}=\frac{\alpha r}{c},\quad
 K_B=\frac{\alpha\beta}{2\mu_B}=\beta(2-u),
\]
\[
 K_D=\frac{\beta\delta}{2\mu_D}=\delta V,\qquad
 K_H=\frac{\omega\epsilon}{2\mu_H}=\epsilon k_1.
\tag{6}
\]
The right-hand identities follow directly from the definitions of the
stationary weights, with the same normalization on all weights.

For the five weighted centers let

\[
 \mathcal N(x)=-\sum_{i=A,B,D,E,H}\frac{|F_i(x)|^2}{4\mu_i}.
\]
Set

\[
 z_A=-h-b_0,\qquad z_B=u_0-b_0,\qquad z_D=v_0.
\]
The elementary dot products `f_b dot e_u=sin(u-b)` and
`e_(tau-h) dot f_tau=-sin(h)` give the exact identity

\[
\begin{aligned}
 \mathcal N(x)-\mathcal N(0)
 ={}&K_A\{\sin(\tau+z_A)-\sin\tau\}
       -K_B\sin z_B+K_D\sin z_D
       +\zeta K_H\sin h.
\end{aligned}
\tag{7}
\]
There are four varying terms, not five. Formula (5) accounts for the
missing term. The HG term is absent when H owns HG in this gauge.

Every angle in (7) satisfies

\[
                 |z_A|,|z_B|,|z_D|,|h|\le S.
\tag{8}
\]
For example, the coefficients of `b_0` in the four variables `x_i`
are all either 0 or -1, by (2). Thus `-h-b_0` has coefficients of
absolute value at most one in the five variables in (1). Also
`u_0-b_0` is one of `0,x_1,x_2,x_1+x_2`, so it has the same bound.
The four choices of `v_0` arising from (2) have coefficients 0 or -1.
This verifies (8) for all owners without enumerating a numerical table.

The complete first differential of (7) is

\[
 \mathcal L_N=K_A\cos\tau\,z_A-K_Bz_B+K_Dz_D
                                  +\zeta K_Hh.
\tag{9}
\]

## 4. A uniform remainder with no inverse sine

Assume `0<=tau<=pi/2`. For every real `z`,

\[
 0\le1-\cos z\le z^2/2,\qquad
 |\sin z-z|\le |z|^3/6.
\]
Expanding `sin(tau+z)` proves

\[
 \sin(\tau+z)-\sin\tau-\cos\tau\,z
 \ge-\frac{\sin\tau}{2}z^2-\frac{|z|^3}{6}.
\]
Consequently (7)--(9) imply the full-domain bound

\[
\boxed{
 \mathcal N(x)-\mathcal N(0)-\mathcal L_N
 \ge-\frac{K_A\sin\tau}{2}S^2
       -\frac{K_A+K_B+K_D+K_H}{6}S^3.}
\tag{10}
\]
This estimate applies to any size of `S` for which the comparison
weights in (6) are defined and positive. It is not inferred from
samples or from an assumed small-angle stationary point.

For a comparison family in the original proved rectangle

\[
 3.9154\le q\le3.9156,\quad
 .895\le u\le.94,\quad .1\le\tan\tau\le.164,
\]
the terminal's already proved whole-domain bounds give

\[
 r<1.765,\quad c>.9868,\quad V<1.359,\quad
 k_1<1.422,\quad 2-u<1.105,
\]
and every edge weight is less than `.87`. Hence

\[
 \frac{K_A\sin\tau}{2}
 <\frac{.87(1.765)(.164)}2
 =\frac{1259151}{10000000}<.126,
\]
\[
 \frac{K_A+K_B+K_D+K_H}{6}
 <\frac{.87}{6}
       \left(\frac{1.765}{.9868}+1.105+1.359+1.422\right)
 =\frac{202989299}{246700000}<.823.
\tag{11}
\]
These are individual rational comparisons on the whole comparison
rectangle. In particular, the force-norm loss is at most

\[
                         .126S^2+.823S^3.
\tag{12}
\]
At `S=0` all remainders are zero. No term proportional to
`delta*w/sin(tau)` occurs in (10)--(12).

## 5. What the full assembly must still do

The identities above leave the original center-square completion valid,
with its actual selected corner offsets. They change the convenient
reference gauge, not the underlying packing or original gaps.
However, GA is no longer error-independent: its actual relative angle
is `tau-h-a_A`. Its support/offset contribution must be recomputed, as
must the slider projections relative to the new frames. The stationary
family defect must also be retained; changing the comparison tilt without
accounting for its first derivative is not legitimate.

Thus (12) is a proved replacement of the **force-norm part**, not a claimed
bound for the complete terminal remainder. It identifies a way to avoid
the previous dominant quadratic loss in the remaining capture work.
The full unrestricted proof continues to require the open global gates.
No Lean source or historical table has been changed; no compilation or CI
is used by this hand argument.
