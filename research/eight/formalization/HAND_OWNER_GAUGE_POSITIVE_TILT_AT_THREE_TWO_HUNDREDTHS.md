# Positive tilt capture in the actual owner frame at S <= 3/200

## 1. The captured angle is an actual owner-frame difference

Assume the candidate hypotheses of
`HAND_MIXED_OWNER_CLOSURE_AT_THREE_TWO_HUNDREDTHS.md`, now with
`q <= Q1 = 1957767069/500000000`, and `S <= 3/200`. Retain any originally
feasible intended owner on each aligned edge. Let d0 be the physical
frame of the retained ED owner and define

\[
                    \tau=\theta_H-d_0.
\]

**Theorem.** Every such cycle satisfies

\[
                         1/10<\tau<4/25.             \tag{1}
\]

This is an owner-frame tilt theorem. It does NOT assert that the old
A-to-G tilt t lies in this interval. The distinction matters because
`|tau-t| <= S`. The owner-frame sharp terminal must use the same tau;
substituting t for tau would not be a valid application.

The theorem does not require `S <= 1/1000`. All actual aligned owners,
all original centers and their possible separating ties are included.
The earlier tangent cuts and mismatch bound remain prerequisites.
All terminating decimals in this note are exact rationals.

The preceding theorem `HAND_NEGATIVE_TILT_AT_THREE_TWO_HUNDREDTHS.md`
gives `t>S`, with A's physical frame zero and G's frame t. The actual
HG+G0 chain and the bounds `a_A<1.303,b_A>.316,b_H<.9` give
`-.203+.816 sin(t) <= (251/250)S`, hence `sin(t)<.27` and `t<.274`.
Since `|tau-t|<=S`,

\[
           0<\tau<.289,\qquad 0<s=\sin\tau<3/10.
\tag{2}
\]

The actual GA and HE relative tilt angles are both positive: they are
t and `t+theta_H-t-theta_E`, respectively, and the latter is at least
`t-S`. This will justify their smooth width branches below.

## 2. Exact scalar identity for every retained owner

The identity in this section is valid for arbitrary positive edge
weights alpha,beta,delta,epsilon,omega, with equal weights beta on TB/DT
and omega on GA/HG. Use positive circle masses on A,B,D,E,H.
The later application specifies these quantities explicitly.

Write

\[
 x_1=\theta_B-\theta_A,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h=\theta_H-\theta_G,
\]
\[
 S=|x_1|+|x_2|+|x_3|+|x_4|+|h|.
\]

Let `a,b,d,j,g` be zero or one, with one meaning respectively that B
owns AB, T owns TB, D owns DT, E owns ED, and G owns HG. Rotate the entire
configuration by minus the actual ED-owner frame. Its frames are exactly

\[
\begin{aligned}
 a_A&=-x_1-x_2-x_3-jx_4,& a_B&=a_A+x_1,\\
 a_T&=a_B+x_2,&a_D&=-jx_4,&a_E&=(1-j)x_4,\\
 \theta_H&=\tau,&\theta_G&=\tau-h.
\end{aligned}                                                    \tag{3}
\]

Set `b0=a_A+a x1`, `u0=a_B+b x2`, `v0=a_T+d x3` and
`n=e_(tau-g h)`, where `e_z=(cos z,sin z)`, `f_z=(-sin z,cos z)`.
The actual global center forces are

\[
\begin{aligned}
 F_A&=\alpha f_{b0}-\omega e_{\tau-h},&
 F_B&=-\alpha f_{b0}-\beta e_{u0},\\
 F_D&=\beta e_{v0}-\delta f_0,&
 F_E&=\delta f_0-\epsilon f_\tau,\\
 F_H&=\omega n+\epsilon f_\tau,&
 F_T&=\beta(e_{u0}-e_{v0}),\\
 F_G&=\omega(e_{\tau-h}-n).
\end{aligned}                                                    \tag{4}
\]

The actual selected corner offsets are `(e_aA-f_aA)/2`,
`(e_aB+f_aB)/2`, `(-e_aD+f_aD)/2`, `(-e_aE-f_aE)/2`, and
`-(e_tau+f_tau)/2` on A,B,D,E,H. Completing their five circles gives
the necessary scalar inequality

\[
 \Phi:=\sum_e\lambda_e W_e-\sum_{i=A,B,D,E,H}
       \left(F_i\cdot o_i+\frac{|F_i|^2}{4m_i}+qm_i\right)
       +F_T\cdot p_T+F_G\cdot p_G\le0.
\tag{5}
\]

This follows directly from the nonnegative original signed separation
gaps and the five containing disks. The discarded terms are the
nonnegative completed center squares and disk slacks.

In particular, `F_E=(epsilon s,delta-epsilon c)` is **constant in all
five errors** at fixed tau. No estimate of its small-mass norm term is
needed. This is an exact cancellation, not a better bound on `1/s`.

Keep the actual own-frame coordinates of the free squares fixed:

\[
 p_T=b_Te_{a_T}+a_T^{\rm prim}f_{a_T},\qquad
 p_G=b_Ge_{\tau-h}-a_G^{\rm prim}f_{\tau-h}.
\]

In formulas below abbreviate their primary coordinates by aT,aG;
these are not the frame errors in (3). They satisfy
`7/12<=aT,aG<1.396` and `0<=bT,bG<.8`.
An auxiliary straight error segment is only an evaluation of (5) after
the anchor centers have been eliminated; no packing along that segment
is assumed.

Put

\[
 K_A=\frac{\alpha\omega}{2m_A},\quad
 K_B=\frac{\alpha\beta}{2m_B},\quad
 K_D=\frac{\beta\delta}{2m_D},\quad
 K_H=\frac{\omega\epsilon}{2m_H},
\]
\[
 z_A=(1-a)x_1+x_2+x_3+jx_4-h,\quad
 z_B=(1-a)x_1+bx_2,\quad z_D=-(1-d)x_3-jx_4,
\]
\[
 v=x_1+x_2+x_3+jx_4-h.
\]

Subtract the zero-error scalar `g(q,s)=Phi(0)`. Direct dot products in
(4) give the following complete identity:

\[
\begin{aligned}
\Phi-\Phi(0)={}&K_A[\sin(\tau+z_A)-s]-K_B\sin z_B
                    +K_D\sin z_D+gK_H\sin h\\
&+\alpha[\cos x_1-1+\tfrac12\sin x_1
                                      +\tfrac12|\sin x_1|]\\
&+\beta[\tfrac{1+b}{2}(\cos x_2-1)+\tfrac b2\sin x_2
                                      +\tfrac12|\sin x_2|]\\
&+\beta[\tfrac{2-d}{2}(\cos x_3-1)+\tfrac{1-d}{2}\sin x_3
                                      +\tfrac12|\sin x_3|]\\
&+\delta[\cos x_4-1+\tfrac12\sin x_4
                                      +\tfrac12|\sin x_4|]\\
&+\omega[\tfrac{1+g}{2}(\cos h-1)-\tfrac g2\sin h
                                      +\tfrac12|\sin h|]\\
&+\omega[\cos(\tau+v)-c]
       +\epsilon[\sin(\tau-(1-j)x_4)-s]\\
&+\beta\{b_T[\cos((1-b)x_2)-\cos(dx_3)]
                  -a_T[(1-b)\sin x_2+d\sin x_3]\}\\
&+\omega(1-g)\{b_G(1-\cos h)+a_G\sin h\}.
\end{aligned}                                                    \tag{6}
\]

The letter g multiplying the H terms is the HG-owner indicator, not
the zero-error scalar function. Formula (6) retains all 32 intrinsic
owner assignments symbolically. The mixed support/offset combinations
are exactly `omega(1/2+cos(tau+v))` and
`epsilon(1+sin(tau-(1-j)x4))`. Both actual mixed angles and tau are
positive, so these branches remain valid on the entire error segment.
Every displayed linear angle has absolute error at most S.

## 3. A single continuous choice of weights

Use precisely the explicit family from
`HAND_POSITIVE_TILT_NOMINAL_GAP.md`:

\[
\begin{aligned}
 \omega&=1,\quad\alpha=24/41+(49/100)s-s^2/20,\\
 \beta&=1-s/20-s^2/6,\\
 \delta&=36/31-(7/10)s-s^2/16,\\
 \epsilon&=36/31-s+(11/20)s^2,
\end{aligned}
\]
\[
\begin{aligned}
 m_A&=(12/41)/(1+13s/60),&m_B&=(12/41)/(1-9s/50),\\
 m_D&=(12/31)/(1+9s/25),&m_H&=(12/31)/(1+49s/100),\\
 m_E&=(3s/10)/(1+4s/5).
\end{aligned}                                                    \tag{7}
\]

They are positive for the actual s>0. Their common nominal scalar is
exactly the one already proved in that note, so on the full interval
`0<s<=3/10`,

\[
 g(q,s)\ge p(s):=B_0-\frac{79}{1250}s+\frac{51}{200}s^2
                   -\frac{s^3}{100}-\frac{27}{100}s^4-\frac3{10}s^5,
 \quad B_0=\frac{38726637}{9929687500}.
\tag{8}
\]

The cited nominal proof establishes this inequality by its single
polynomial identity on the whole interval. In particular

\[
 g(q,s)>9/100000\ (s\le1/10),\qquad
 g(q,s)>1/25000\ (s\ge79/500).
\tag{9}
\]

No nominal inequality is assumed for an actual nonzero-error packing;
(6) supplies the missing error comparison.

## 4. All first-order owner reserves on one interval

Put `C=K_A c-s`. Removing the five linear cusps from (6), the smooth
first coefficients are

\[
\begin{aligned}
 c_{AB}&=(1-a)(K_Ac-K_B)+\alpha/2-s,\\
 c_{TB}&=C-bK_B+b\beta/2-(1-b)\beta a_T,\\
 c_{DT}&=C-(1-d)K_D+(1-d)\beta/2-d\beta a_T,\\
 c_{ED}&=j(C-K_D)+\delta/2-(1-j)\epsilon c,\\
 c_{HG}&=-C+g(K_H-1/2)+(1-g)a_G.
\end{aligned}                                                    \tag{10}
\]

The corresponding reserve is `lambda/2-|c_edge|`. We prove that all
are nonnegative on `[0,.3]`, and quantify the relevant small ones.

### Scalar bounds, proved without subdivision

The weight formulas immediately give

\[
 24/41\le\alpha<.73,\quad .97\le\beta\le1,
 \quad .94<\delta<1.162,\quad .9<\epsilon<1.162.
\]

The four norm coefficients obey

\[
 0<K_A<4/3,\quad0<K_B<6/5,\quad0<K_D\le3/2,
                         \quad0<K_H\le3/2.
\tag{11}
\]

For explicit reproduction,

\[
\begin{aligned}
 K_A&=1+843s/800+13817s^2/144000-533s^3/28800,\\
 K_B&=1+1457s/2400-34849s^2/80000-592807s^3/7200000
                         +11111s^4/288000-41s^5/16000,\\
 K_D&=3/2-527s/1200-245s^2/384+149597s^3/2880000
                         +7967s^4/115200+31s^5/6400,\\
 K_H&=3/2-167s/300+31s^2/400+16709s^3/48000.
\end{aligned}
\]

KA increases and `4/3-KA(.3)=17419/1920000>0`. Dropping the negative
terms of KB proves its upper bound. In KD and KH, replacing s by .3 in
the positive terms after factoring s shows that their change from 3/2
is nonpositive. All positivity follows directly from (7).

Use `1-4s^2/7 <= c <= 1-s^2/2`, and define
`C_L=K_A(1-4s^2/7)-s`, `C_U=K_A(1-s^2/2)-s`.
Then

\[
                         .95<C<1.01.                 \tag{12}
\]

Indeed `C_U <= 1+.054s-.4s^2<1.01`, by completing a square.
For the lower bound,

\[
 C_L''=(106600s^3-331608s^2-1876845s-479281)/504000<0.
\]

Thus its minimum is at an endpoint; `C_L(0)=1` and
`C_L(.3)=53544741/56000000>.95`.

Furthermore,

\[
 K_B-C\ge s/2,\qquad \alpha+C-K_B>1/2,
                         \qquad\alpha>2s.           \tag{13}
\]

For the first inequality, the exact difference `KB-CU-s/2` is

\[
 s\left(4/75-11363s/360000+3333943s^2/7200000
                     +779s^3/9000-3403s^4/288000\right)\ge0.
\]

Its bracket stays positive after discarding the positive middle terms
and using s<=.3 in the two negative terms. For the second, expansion
of `alpha+CL-KB` gives the lower bound

\[
 24/41-(19/300)s-.09s^2-.54s^3-.094s^4>.54.
\]

The last inequality in (13) is the decreasing quadratic
`24/41-1.51s-.05s^2>0` at s=.3.

### Apply these bounds to every receiver

The AB reserves for a=0 are `KB-C` and `alpha+C-KB`, so their minimum
is at least s/2. For a=1 their minimum is exactly s.
The T-owned TB alternative has the same small reserve `KB-C`; its
other reserve is `beta+C-KB`, larger than `alpha+C-KB`.

The free T reserves are
`C-beta(aT-1/2)` and `beta(aT+1/2)-C`. By (12), both exceed 1/25:
the two sufficient lower comparisons are `.95-.896>.04` and
`13(.97)/12-1.01=49/1200>.04`.
The free G comparisons are even larger.

The anchored DT and E-owned ED alternatives have lower reserve
`KD-C`, and other reserves `beta+C-KD` or `delta+C-KD`.
Equations (11),(12) give lower bounds exceeding 1/25; for example
`KD >= (.94)(.97)(31/24)>1.17`, whereas `C<1.01`.
For anchored HG use `KH-C` and `1+C-KH`; again both exceed 1/25,
since `KH >= (.9)(31/24)`.

Finally, D-owned ED has reserves `epsilon c` and `delta-epsilon c`.
They are nonnegative because

\[
 \delta-\epsilon c\ge\delta-\epsilon
                         =s(3/10-49s/80)\ge0.
\tag{14}
\]

On `3/50<=s<=3/10` both exceed `3/200`: the quadratic in (14) is
concave and its endpoint values are `.015795` and `.034875`;
`epsilon c>.9(.95)` is larger.

This covers every one of the two owners in (10), with the actual full
G/T coordinate intervals and no sign alternatives omitted.

## 5. A simultaneous owner-sensitive remainder

On the error segment `S<=.015`, all arguments of (6) have magnitude
at most `.32`. The four norm terms in its first line have every Hessian
entry bounded by

\[
 (4/3)(.32)+(3/2)(.015)<.45.
\]

Apart from KA, the KB, KD and KH terms occupy disjoint coordinate
blocks, so they are not all added into this bound.
The smooth aligned terms have diagonal curvature at most
`1.162(1+.015/2)<1.18`. The mixed GA cosine has entries at most one.
The free T and G terms have diagonal entries below
`.8+1.396(.015)<.821`, on disjoint coordinates. Therefore each ordinary
smooth Hessian row has entries below

\[
                         .45+1.18+1+.821<7/2.        \tag{15}
\]

When D owns ED (j=0), x4 appears in none of these norm, GA or slider
terms. Its only smooth terms are its own ED support and the mixed HE
sine. Thus that entire row has entries below

\[
                      1.18+1.162(.32)<8/5.           \tag{16}
\]

For a symmetric Hessian with row bounds B_i,
`|sum H_ij x_i x_j| <= S sum B_i |x_i|`. Integrating Taylor's theorem
therefore loses at most `(7/4)S` per unit of ordinary error, and
`(4/5)S` per unit of D-owned ED error. This is one shared five-variable
bound. Restoring the sine cusps loses less than `S^2/10` per unit error.

## 6. Exclude both complete positive tails

For `0<s<=3/50`, all first-order reserves are nonnegative. The nominal
polynomial decreases on this interval and

\[
 p(3/50)=63313779/62060546875>1/1000.
\]

Thus even at the largest S,

\[
 \Phi\ge p(3/50)-(7/4)(3/200)^2-(3/200)^3/10
        =\frac{39789049071}{63550000000000}>0.
\tag{17}
\]

For `3/50<=s<=3/10`, every ordinary reserve is at least `.03`, and
the D-owned ED reserve is at least `.015`. At `S<=.015`,

\[
 .03-(7/4)S-S^2/10>1/500,
 \qquad .015-(4/5)S-S^2/10>1/500.
\]

Consequently (6) gives the full necessary bound

\[
                         \Phi\ge g(q,s)+S/500.      \tag{18}
\]

If `s<=1/10` or `s>=79/500`, (9) makes its right side strictly positive,
including S=0. This contradicts (5). Equations (17),(18) therefore force

\[
                         1/10<\sin\tau<79/500.
\]

Since `sin(tau)<=tau` and
`sin(.16)>=.16-.16^3/6>.158`, this implies (1).

The captured tilt belongs to the actual ED-owner/H frame, and the same
owner remains selected throughout. The small E mass was never divided
into an error remainder. No frame mesh, state partition, owner table,
external acceptance statement, Lean compilation or CI run is a premise.
The earlier unrestricted tangent and mismatch gates remain separate.
