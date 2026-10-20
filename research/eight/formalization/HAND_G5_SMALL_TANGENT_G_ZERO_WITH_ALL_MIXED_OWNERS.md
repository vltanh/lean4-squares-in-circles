# The small-tangent G-zero endpoint is impossible for every mixed owner and E frame

## 1. Endpoint scope

Put
\[
 Q=\frac{9789}{2500},\qquad p=\frac{50}{49},\qquad
 S_0=2\sqrt{Q-1}-3,\qquad k=\sqrt{Q-1/4}-1.
\tag{1}
\]
Retain normal signs at H,G,A,B,T,D, either E sign, sorted
own-frame magnitudes, true core avoidance, and circles at
most \(q\le Q\). The relevant actual witnesses are
\[
 HG=0,\qquad GA=0,\qquad BT=2,\qquad TD\in\{0,2\},
 \qquad DE\in\{2,3\},\qquad EH\in\{0,1\}.
\tag{2}
\]
Assume
\[
 \theta_A=\theta_B=\rho,\qquad b_A+b_B=1,\qquad
 \frac{67}{200}\le b_A\le\frac12,\qquad
 \theta_T\le\rho\le\theta_H<\theta_G,\qquad b_G=0.
\tag{3}
\]
Write
\[
 \Theta=\theta_H-\rho\ge0,\quad
 h=\theta_G-\theta_H>0,\quad
 z=\Theta+h,\quad v=\rho-\theta_T\ge0.
\]
The H,D,E frames and the TD frame difference lie in the
original interval of length at most \(7/10\). It suffices
that \(z,v\le7/10\); no total spread involving a newly
constructed G frame is required.

**Endpoint exclusion.** No system (2)--(3) exists.
There is no hypothesis on E's position relative to H,D,
its radial boundary kind, either outer-error sign on the
opposite path, or the original mixed-owner choice.

In particular, the transverse-zero alternative of the
positive noncanceling small-tangent boundary theorem is
excluded in this full mixed-owner scope. Reflection gives
the same statement for a T-zero endpoint. Its E sign need
not be preserved by that reflection.

## 2. One previously proved middle envelope

Set \(b=b_A\), and use only the enlarged ceiling Q in
this scalar comparison:
\[
\begin{gathered}
 Y=b+\frac12,\quad Y_B=2-Y,\quad
 R=\sqrt{Q-Y^2},\quad R_B=\sqrt{Q-Y_B^2},\\
 P=R-1,\qquad P_B=R_B-1.
\end{gathered}
\]
Let \(z_A,z_B\) be the nonnegative hard-contact roots
\[
 P\cos z_A-Y\sin z_A=\frac12,\qquad
 P_B\cos z_B-Y_B\sin z_B=\frac12,
\]
and put
\[
 M(b)=\max_{0\le w\le z_B}
             \{P_B\cos w-Y_B\sin w+pw\},\qquad
 J(b)=pz_A+M(b)-\frac12.
\tag{4}
\]
Sections 2--4 of
[the small-tangent crossed HG0 theorem](HAND_G5_CROSSED_SMALL_TANGENT_NONCANCELING_GA_ALIGNMENT.md)
prove the scalar bounds
\[
                  z_A<.312<.4,\qquad J(b)<.419
                    \quad(.335\le b\le.5).
\tag{5}
\]
Their proof of \(J\) is independent of the crossed-frame
hypothesis: it uses the two intrinsic optimizer branches
at \(b=47/98\), inverse-angle derivatives on the whole
interval, and the balanced endpoint. Thus (5) is available
here as a scalar inequality without asserting a crossed
geometric state.

The actual GA0 and BT2 inequalities, after enlarging only
their circle bounds to Q, imply
\[
 z\le z_A,\qquad v\le z_B,\qquad
              b_T+\frac12+pv\le M(b).
\tag{6}
\]
In particular \(0<h<.4\).

## 3. The actual H circle gives a positive one-variable reserve

Since \(b_G=0\), its actual primary is at most
\(\sqrt{Q-1/4}-1/2\). The actual HG0 inequality therefore
gives
\[
                       b_H\ge\frac12+\frac12\cos h-k\sin h.
\tag{7}
\]
Sorting gives \(b_H<.9\), while \(k<.915\).
If \(h\le.1\), the quadratic cosine lower bound and
\(\sin h\le h\) would imply
\[
 b_H\ge1-\frac{h^2}{4}-.915h
 \ge1-\frac{.1^2}{4}-.915(.1)
 =.9+\frac3{500},
\]
a contradiction. Thus
\[
                                .1<h<.4.
\tag{8}
\]

Define
\[
                         f(h)=ph-k\sin h-\frac12(1-\cos h).
\]
On \([.1,.4]\),
\[
 f''(h)=k\sin h-\tfrac12\cos h
 <.915(.4)-\frac12(1-.4^2/2)=-\frac{47}{500}<0.
\tag{9}
\]
It is enough to check the two endpoints of this one
concave function. With
\[
 S_5(x)=x-x^3/6+x^5/120,\qquad C_2(x)=1-x^2/2,
\]
the lower bounds \(px-.915S_5(x)-\tfrac12(1-C_2(x))\)
at \(x=.1,.4\) exceed .007 respectively by
\[
                    \frac{46775011}{39200000000},
                    \qquad
                    \frac{741919}{153125000}.
\tag{10}
\]
Consequently
\[
                              f(h)>.007
                               \quad(.1\le h\le.4).
\tag{11}
\]

## 4. Join the unchanged endpoint budget and the TD charge

The all-mixed H,D,E endpoint theorem gives
\[
 b_H+b_D-p(\theta_H-\theta_D)+S_0<2.
\]
Its extension to either E sign is the exact endpoint
reflection in Section 2 of
[the crossed canceling theorem](HAND_G5_CROSSED_CANCELING_OUTER_TO_GA_ALIGNED_NONCANCELING.md).
The unchanged TD transverse witness and the all-sign
zero charge give
\[
                         b_D+b_T+p(\theta_D-\theta_T)\ge1.
\]
Their sum requires
\[
                         b_H-b_T-p(\Theta+v)<1-S_0.
\tag{12}
\]
Only the unchanged H,D,E and T states enter these two
inequalities. Thus an enlarged G frame in a boundary
comparison does not affect their hypotheses.

On the other hand, (6)--(7), with \(\Theta=z-h\), give
\[
\begin{aligned}
 b_H-b_T-p(\Theta+v)
 &\ge\frac32-pz-M(b)
          +ph-k\sin h-\frac12(1-\cos h)\\
 &\ge1-J(b)+f(h)\\
 &>1-.419+.007=.588.
\end{aligned}
\tag{13}
\]
But \(\sqrt{Q-1}>1.7075\), so \(S_0>.415\) and
\(1-S_0<.585\). Equations (12)--(13) contradict each
other with reserve greater than \(3/1000\).

The argument retains the actual endpoint and TD circles,
uses one Q-envelope for A/B, and does not assume that the
opposite outer path has already been aligned. It therefore
excludes the transverse-zero endpoint whether the opposite
side is aligned or retains a negative error, without a
separate E-order or negative-error endpoint analysis.

No numerical sample, state or angle mesh, Lean compilation,
or CI result is used.
