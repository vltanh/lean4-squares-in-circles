# A negative core DE3 error and positive A/TD2 errors: whole-angle concentration

## 1. Scope and conclusion

Put
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad
 h=\frac7{10},\qquad L=\frac16,\qquad K=\frac{13}{12}.
\tag{1}
\]
Retain a necessary G0--G2 boundary cycle whose sorted outer states
H, G, B and D have signed tangents respectively positive,
negative, negative and negative. E is a nonpositive true-core
boundary representative. A and T may have either sign and either
radial kind. The original owners include
\[
 HG\in\{0,2\},\qquad BT=2,\qquad TD=2,\qquad DE=3,\qquad EH=0,
\tag{2}
\]
with
\[
 d_{TD}=z\ge0,\qquad d_{DE}=-s\le0.
\]
At A allow any of the following:

* GA2 and AB0 with arbitrary errors, putting \(a=0\);
* one selected primary GA3 or AB2 with nonnegative error \(a\),
  and the other A edge secondary with arbitrary error;
* both GA3 and AB2 with arbitrary individual signs and
  nonnegative signed total \(a=d_{GA}+d_{AB}\).

Assume the actual errors have signed sum zero and positive and
negative variations each at most h. Set
\[
                         \theta=a+z\le h.
\tag{3}
\]
No frame order is assumed. The proof uses only the stated
neighboring inequalities, boundary circles, true-core condition,
and variation bounds. It therefore also applies after a prior
transport that preserved these necessary conditions.

**There is no such necessary cycle.** The scalar reduction below
leaves exactly five low-interval functions and four high-interval
functions at each of the two formal split endpoints
\[
                       (a,z)=(0,\theta),\quad(\theta,0).
\tag{4}
\]
Every one is strictly positive by
[the companion scalar theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md).

Use the two continuous coefficient families \(k,l,c\) in that
companion. Their parameter is \(\theta\), and they are held fixed
when s or the split a varies. All family ranges invoked below
are independently established there. All decimals in this note
denote exact rational numbers.

## 2. The actual E flat side and the secant force

Write
\[
\begin{gathered}
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,\qquad
 c_0=\sqrt{Q/2}-\tfrac12,\qquad d_0=c_0-\tfrac12,\\
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 \phi(t)=\cos t+\sin t,\\
 \eta=\frac{293}{1000},\qquad
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 m=c(\cos z+\eta\sin z).
\end{gathered}
\tag{5}
\]
EH0 gives, at its actual error r,
\[
                 a_H\cos r+b_H\sin r-b_E\ge W(r)\ge1.
\]
The sorted outer H circle has center norm at most \(a_0<1.415\).
Consequently
\[
                         b_E<.415<\frac12.
\tag{6}
\]
The true-core boundary on this range is its flat side, so
\(a_E=7/12\). This is the unchanged actual E, as proved also
in Section 2 of
[the secant D-support lemma](HAND_G3_CORE_E_NEGATIVE_DE3_SECANT_D_SUPPORT.md).

Give the original inequalities, in cyclic order, weights
\[
                     (k,l,l,m,c,w,1),\qquad w=\sec s.
\tag{7}
\]
The weighted DE3 projection is
\[
 w\{a_D-a_E\sin s+b_E\cos s\}
                     =w a_D-\frac7{12}\tan s+b_E.
\tag{8}
\]
Its E tangent cancels with EH0. TD2 gives the T force
\[
 c\sin z\,a_T+(c\cos z-m)y_T
                     =c\sin z(a_T-\eta y_T)
                     \le c\sigma\sin z.
\tag{9}
\]
The last estimate uses the actual corner
\((a_T+1/2,|y_T|+1/2)\) and is valid for either T sign or radial kind.

For the selected A primaries the
[signed A-combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md)
gives charge at least \(l j(a)\), where
\[
\begin{split}
 S(f,g)&=\max_{0\le b\le c_0}
  \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},\\
 \overline S(f,g)&=R\sqrt{f^2+g^2}-\frac{f+g}{2},\\
 j(t)&=W(t)-1-S(\sin t,1-\cos t)\qquad(0\le t\le h).
\end{split}
\tag{10}
\]
With no selected A primary use \(j(0)=0\). Every unselected
secondary angular argument remains in the force expression.

The exact scalar baseline is
\[
\begin{split}
 {\cal B}(s;\theta,a)={}&k+2l+m+cW(z)+w+1-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(l,k)-\overline S(m,l)
       -{\cal S}(w,c)\\
 &+l j(a)+K\tan s-\frac12(w-1),\qquad z=\theta-a.
\end{split}
\tag{11}
\]
Here \({\cal S}=S\) for \(0\le\theta\le L\), and
\({\cal S}=\overline S\) for \(L\le\theta\le h\). The latter is
a valid lower bound for demand minus actual support throughout
the high interval, including at \(s=0\).

There is no D angular block left: its actual force after (8)--(9)
is \((w,c)\). Put \(x=\tan s\), so \(w=\sqrt{1+x^2}\).
On a full-circle D branch all the s-dependent terms of (11) are,
up to a constant independent of s,
\[
                  F_0(x)=w+Kx-R\sqrt{w^2+c^2}.
\tag{12}
\]
On a diagonal branch they are \(Kx-d_0w\), up to another constant.
The first derivatives agree at \(w=c\). In the low family no
axis support can occur, since \(c\ge1.0389\) and \(w<1.308\).
Thus these are precisely its actual support branches.

For later use,
\[
\begin{split}
 F_{0,s}
 &=\sec^2s\left[K+\sin s
        \left(1-\frac R{\sqrt{1+c^2\cos^2s}}\right)\right],\\
 F_{0,xxx}
 &=3x\left\{\frac{R(1+c^2)}{(1+c^2+x^2)^{5/2}}
                           -\frac1{(1+x^2)^{5/2}}\right\}.
\end{split}
\tag{13}
\]

## 3. Concentration of the remaining ordinary angles

The three ordered pairs are
\[
 (p_G,q_G)=(k,l),\quad (p_H,q_H)=(k,1),\quad
 (p_B,q_B)=(\min(l,m),\max(l,m)).
\tag{14}
\]
They all have \(p_i/q_i\ge1/2\). Define
\[
\begin{split}
 N_{p,q}(t)&=\sqrt{p^2+q^2+2pq\sin t},\\
 U_{p,q}(t)&=p\{\phi(t)-1\}-R\{N_{p,q}(t)-N_{p,q}(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)-R\{N_{p,q}(-t)-N_{p,q}(0)\},\\
 \Psi_{p,q}(P,N)&=p\{\phi(P)-1\}+q(\cos N-1)\\
 &\hspace{28mm}-R\{N_{p,q}(P-N)-N_{p,q}(0)\}.
\end{split}
\tag{15}
\]
The whole-interval concavity results in the
[TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md)
apply: U and V are concave, and \(\Psi\) is separately concave.

Delete the designated A arguments and the two arguments \(z,-s\)
only from the algebraic angular vector. The remaining positive
and negative variations satisfy
\[
 P\le h-\theta,\qquad N\le h-s,\qquad N-P=\theta-s.
\tag{16}
\]
For two A primaries their deleted positive parts are at least a;
any deleted negative parts only enlarge the permitted domain.
If there is no A primary, both actual secondary A arguments
remain. The enlarged full-circle blocks allow them. A missing
argument may instead be inserted as a virtual zero, exactly as
in the cited concentration theorem.

The two simplex concentrations and the final common-variation
concentration therefore leave the following intrinsic alternatives,
added to (11):
\[
\begin{array}{ll}
 V_i(\theta-s),&s\le\theta,\\
 U_i(s-\theta),&s\ge\theta,\\
 \Psi_i(h-\theta,h-s),&\text{either case},\\
 U_i(h-\theta)+V_j(h-s),&i\ne j.
\end{array}
\tag{17}
\]
There is no D alternative. For a feasible original system the
minimum of (17), added to \({\cal B}\), is nonpositive.
This is a scalar relaxation of the same positive weighted sum;
it neither aligns an original angle nor asserts a new witness.

## 4. Derivative facts used below

For \(N=N_{p,q}\), put
\[
 C(t)=-RN''(t),\quad
 C_0=\frac{Rp^2q^2}{(p^2+q^2)^{3/2}},\quad
 C_1=\frac{Rpq\{(p^2+q^2)^2-3p^2q^2\}}
             {(p^2+q^2)^{5/2}},\quad
 D_0=\frac{Rpq}{\sqrt{p^2+q^2}}.
\tag{18}
\]
Section 4 of the
[negative-A concentration theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_ANGLE_CONCENTRATION.md)
proves on the entire signed interval that C is increasing and
concave, and
\[
 C(t)\le C_0+C_1t,\qquad
 C_0<.7q,\quad C_1>\frac q3,\quad D_0<1.4q.
\tag{19}
\]
Integrating the first inequality towards a negative argument gives
the useful stronger tangent
\[
 RN'(-d)\le D_0+C_0d-\frac12C_1d^2\qquad(0\le d\le h).
\tag{20}
\]
In particular,
\[
 V'(d)\le D_0-(q-C_0)d-\frac q6d^2+\frac q6d^3.
\tag{21}
\]
We used \(\sin d\ge d-d^3/6\).

We also need
\[
 U'(t)>-.72q\quad(0\le t\le h),\qquad
 U'(t)>-.64q\quad(0\le t\le h-L).
\tag{22}
\]
Concavity reduces these to their right endpoints. At either
endpoint the normalized derivative
\[
 r\phi'(t)-\frac{Rr\cos t}{\sqrt{1+r^2+2r\sin t}},
 \qquad r=p/q\in[1/2,1],
\]
decreases with r. Indeed the derivative of
\((1+r\sin t)/(1+r^2+2r\sin t)^{3/2}\) is negative, and the
resulting derivative at \(r=1\) is already negative.
At \(t=h\), \(\phi'(t)>.12\) and
\(R\cos t/\sqrt{2+2\sin t}<.84\). At \(t=h-L\), the respective
bounds are \(.35\) and \(.99\). These prove (22).

For \(p/q\ge2/3\), the balanced scalar-envelope bounds give
\[
 V'(t)>\frac23q\quad(0\le t\le h),\qquad
 V'(t)>.78q\quad(0\le t\le h-L).
\tag{23}
\]
For the second inequality it suffices to substitute
\(r=2/3,t=8/15\) in the exact formula for \(V'\).
All endpoint estimates in this note follow by positive squaring
with \(S_{11}<\sin<S_9\), \(C_{10}<\cos<C_{12}\), and
\(1.978787<R<1.978788\).

Finally, two direct subtractions give the same-block comparisons
\[
\begin{split}
 \frac{\Psi(P,N)-V(N-P)}p
 &=(1-r\cos N)(\cos P-1)+(1-r\sin N)\sin P,\quad P\le N,\\
 \frac{\Psi(P,N)-U(P-N)}p
 &=\phi(P)-\phi(P-N)-r(1-\cos N),\quad N\le P,
\end{split}
\tag{24}
\]
where \(r=q/p\). The first is nonnegative if \(r\sin N\le1\).
The second is nonnegative for \(r\le1.7\), since its minimum at
fixed N is at \(P=h\), and
\[
 \phi'(h)>.12,\quad \phi(h)>1.409,\quad
 \tan(h/2)<.366,\quad .12-.291(.366)>0.
\tag{25}
\]
These are also proved in Section 6 of the cited negative-A note.

## 5. Low interval: the D slope and pure positive terms

For \(0\le\theta\le L\), the companion gives
\[
\begin{gathered}
 \frac23<k<.757,\quad 1.0073\le l<1.352,\quad
 c\ge l,\quad m\ge c,\quad m/l<1.38,\\
 c=1.0389+3.45u+9u^2,\quad
 k=.6708-.15u+4u^2,\quad
 l=1.0073+1.7u+2.2u^2,\quad u=L-\theta.
\end{gathered}
\tag{26}
\]
In addition \(m<1.864\). To see the latter directly,
\(m\le c(\cos\theta+\eta\sin\theta)\); this upper function
decreases with \(\theta\), since \(c'\le-3.45\), the trigonometric
factor is at least one, and its derivative is at most \(\eta\).
Its value at zero is \(1.8639\).

Let \(D(s)\) denote the derivative with respect to s of the
s-dependent part of (11). On both actual D-support branches,
\[
                              D(s)>1.045.
\tag{27}
\]
For the diagonal branch use
\[
 D(s)=\frac{K-d_0\sin s}{1-\sin^2s},\qquad d_0<.4.
\]
The quadratic for (27) has positive minimum because
\[
             4(1.045)(K-1.045)-.4^2=\frac7{30000}>0.
\tag{28}
\]
For the interior branch, with \(y=\sin s\le.645\),
\[
 \frac R{\sqrt{1+c^2(1-y^2)}}<1.375+.44y^2.
\tag{29}
\]
It suffices to use \(c=1.038\). After squaring, the difference
is a concave cubic in \(y^2\) with positive values at zero and
\(.645^2\). The numerator of (27) is then bounded below by
\[
 P(y)=K-1.045-.375y+1.045y^2-.44y^3.
\]
At \(y=.2+v\), \(-.2\le v\le.445\), its quadratic coefficient
after absorbing the cubic is at least .5852, and its
completed-square lower bound exceeds .0015.

Every pure U alternative in (17) increases for \(s\ge\theta\).
Here are bounds that also retain the diagonal branch at large c.
The derivative \(U'_{p,q}(t)\) decreases with q. After increasing q
to 1.864, its derivative with respect to p is negative for
\(p\le1.352\). One way to check the latter is to put \(r=p/q<.73\).
The function
\[
 \frac{(1-\tan t)(1+r^2+2r\sin t)^{3/2}}{1+r\sin t}
\]
decreases with t: its logarithmic derivative is negative by
\[
 (1+r^2+2ry)(1+ry)-r(2-r^2+ry)>0,\qquad y=\sin t,
\]
where replacing the discarded factor \(\cos^2t(\cos t-\sin t)\)
by one only enlarges the left comparison. At zero its value is
\((1+r^2)^{3/2}<R\), because \(Q>(1+.73^2)^3\).
Thus
\[
                U'_{p,q}(t)\ge U'_{1.352,1.864}(t).
\tag{30}
\]
For \(s\le1/2\), concavity and one endpoint substitution give
\(U'(s-\theta)>-1.038\), paid by (27).
For \(s\ge1/2\) on the diagonal branch, \(D(s)\) increases,
\(D(1/2)>1.157\), and \(U'(h)>-1.142\).
On an interior branch \(c<\sec s<1.308\), so every larger
coefficient is below \(1.365\). Equations (22) and (27)
give reserve \(1.045-.72(1.365)>.06\).
This proves the asserted increase on each branch and across
its matching derivative.

## 6. Low interval: pure negative and same-block terms

For \(0\le s\le\theta\le L\), the least pure V term is \(V_H\).
For B, the universal endpoint inequality \(V_{p,q}(h)>.87p\)
and concavity give
\[
             V_B(t)\ge\frac{.87}{h}l\,t
                          \ge1.195t\ge V_H(t).
\tag{31}
\]
The middle inequality is strict for \(t>0\); all terms are zero at
\(t=0\). The last inequality uses \(V_H'(0)<1.195\).
For G, increasing its larger coefficient from one to l increases
\(V_{k,q}(t)\) for \(0\le t\le L\), by the coordinate comparison
in Section 7 of the negative-A concentration theorem.
Its hypotheses \(q/k\le2\), \(k>2/3\), and \(t\le.2\) hold.

Throughout \(s\le\theta\), D is diagonal because
\(c\ge1.0389>\sec L\). Its x-dependent part is strictly concave.
The other term is also concave in x:
\[
 \frac{d^2}{dx^2}V_H(\theta-\arctan x)
 =\frac{V_H''+2xV_H'}{(1+x^2)^2}
 <\frac{-71/72+.576+2(.169)(1.195)}{(1+x^2)^2}<0.
\tag{32}
\]
Here \(C_0(k,1)<.576\), \(\tan L<.169\), and the V derivatives
are evaluated at \(\theta-s\). Therefore its minimum is at
\(s=0\) or \(s=\theta\).

The H and B same-block alternatives dominate their pure
counterparts by (24), since their larger-to-smaller ratios are
below 1.5. Only the G same-block term remains.
Its derivative with respect to s is
\[
                  D(s)+l\sin(h-s)-RN'_{k,l}(s-\theta).
\tag{33}
\]
The companion proves \(C_0(k,l)>.5\); also \(D_0(k,l)<1.31\).
For \(s\ge\theta\), (19), (27), and
\(\sin(h-s)\ge.92(h-s)\) give
\[
 (33)>1.045+.92(h-s)-1.31+.5(s-\theta)
                               \ge\frac1{600}>0.
\tag{34}
\]
For \(s\le\theta\), use \(\sin(h-s)>.508\) and
\(RN'(s-\theta)\le1.31+.7(1.352)/6\); the margin remains positive.
Thus the G same-block function increases on the entire s interval,
and reduces to \(s=0\).

## 7. Low interval: the two separated negative blocks

A separated term with negative B is bounded below by the
corresponding term with negative H, by (31). It remains to prove
\[
                   D(s)-V'_H(h-s)>0,\qquad
                   D(s)-V'_G(h-s)>0.
\tag{35}
\]
The positive-block U term is constant in s. We give the full
uniform estimates for (35).

### 7.1 Diagonal D

On a diagonal branch \(D(s)=(K-d_0\sin s)/\cos^2s\).
The derivative \(V'_{p,q}(d)\) increases with p, so it suffices
to take
\[
                           p=.757,\qquad 1\le q\le1.352.
\]
For fixed p, \(D_0(q)\) has second derivative below \(-.389\),
and \(C_0(q)\) is concave. The latter follows from the numerator
\[
                         2p^4-11p^2q^2+2q^4<0.
\]
The following rational tangents, centered at \(q_*=1.25\), hold:
\[
\begin{split}
 D_0(q)&<1.28132+.27506(q-q_*)-.1945(q-q_*)^2,\\
 C_0(q)&<.56775-.08856(q-q_*).
\end{split}
\tag{36}
\]
For explicit rounding checks,
\[
\begin{gathered}
 D_0(q_*)<1.28130,\quad .27505<D_0'(q_*)<.27507,\\
 C_0(q_*)<.56774,\quad -.08857<C_0'(q_*)<-.08855.
\end{gathered}
\]
The intercept buffers in (36) exceed the derivative-rounding
error times \(|q-q_*|\le1/4\), so they apply on both sides
of the center.

Combining (21) and (36), put
\[
\begin{split}
 A(d)&=.27506-1.08856d-\frac{d^2}{6}+\frac{d^3}{6},\\
 B(d)&=1.28132-.68225d-\frac5{24}d^2+\frac5{24}d^3.
\end{split}
\tag{37}
\]
Then
\[
 V'(d)\le B(d)+A(d)(q-q_*)-.1945(q-q_*)^2
                         \le B(d)+\frac{A(d)^2}{.778}.
\tag{38}
\]
For \(0\le d\le.36\), use \(s=h-d\) and define the explicit polynomial
\[
 P_*(d)=K-.4S_5(h-d)
       -C_4(h-d)^2\left\{B(d)+\frac{A(d)^2}{.778}\right\}.
\tag{39}
\]
Write \(P_*(d)=\sum_{j=0}^{14}a_j(d-.12)^j\). Direct rational
expansion gives
\[
\begin{gathered}
 a_0>.0084268,\qquad |a_1|<.0077231,\qquad a_2>.62170,\\
 a_2-\sum_{j=3}^{14}|a_j|(.24)^{j-2}>.21535,\\
                         P_*(d)>.00835.
\end{gathered}
\tag{40}
\]
The last line is one completed square on the entire interval:
\(|d-.12|\le.24\). Equation (39) gives
\(D(s)-V'(d)>0\), since its Taylor numerator is a lower bound
after multiplication by the positive \(C_4(h-d)^2\).

For \(.36\le d\le h\), A decreases and
\(A(.36)<-.09725\). The first quadratic in (38) therefore
decreases for \(q\ge1\), so its maximum is at \(q=1\).
The resulting cubic is
\[
       1.20039875-.41011d-\frac{d^2}{6}+\frac{d^3}{6}.
\tag{41}
\]
It decreases on this interval and is below \(1.039\) at .36.
Equation (27) completes (35) on this branch.

### 7.2 Interior D

If \(c<\sec s<1.308\), (26) implies
\[
             u<.067,\quad k<.68,\quad l<1.132,\quad \sin s>.27.
\tag{42}
\]
Indeed \(c(.067)>1.308\), and
\(1.0389^2(1-.27^2)>1\).
A slightly stronger consequence of (29) is
\[
                       D(s)>1.045+.6(s-.25)^2.
\tag{43}
\]
To verify it, put \(y=\sin s\), use \(s\le y/.92\), and clear
\(1-y^2\). The required polynomial is
\[
 \frac1{1200}-\frac9{184}y+\frac{79057}{211600}y^2
              -\frac{881}{1150}y^3+\frac{375}{529}y^4.
\tag{44}
\]
At \(y=.27+v\), \(0\le v\le.375\), its coefficients satisfy
\[
 a_0>.00355,\quad a_1>.04110,\quad a_2>.06315,\quad
 a_3>-.000492,\quad a_4>0.
\]
Combining \(a_2v^2+a_3v^3\) proves positivity directly.

For either pair in (35), (42) gives
\[
                  D_0<1.154,\quad C_0<.518,\quad q\le1.132.
\]
The C0 bound is largest at \(p=.68,q=1\); it decreases with q
there because \(2(.68)^2<1\). Omitting the favorable quadratic
term from (21) yields
\[
                  V'(N)<1.154-.482N+.189N^3.
\tag{45}
\]
Subtract (45) from (43), with \(N=h-s\). The difference exceeds
\[
 .0125-.058N+.6N^2-.189N^3
 \ge .0125-.058N+(.6-.189h)N^2>.010.
\tag{46}
\]
This is again a single completed square. Equations (35) follow
on both support branches and through their continuous join.

Consequently every low separated term reduces to \(s=0\).
At that endpoint its positive part may be bounded by
\[
                  U_i(h-\theta)\ge-.545m(h-\theta),
\tag{47}
\]
since \(m\) is the largest coefficient. Together with Sections
5--6 this leaves exactly the four s=0 envelopes
\[
 V_H(\theta),\quad \Psi_G(h-\theta,h),\quad
 -.545m(h-\theta)+V_H(h),\quad
 -.545m(h-\theta)+V_G(h),
\tag{48}
\]
and the zero-angle baseline at \(s=\theta\).

## 8. High interval: saturation and the positive remainder

For \(L\le\theta\le h\), the companion establishes
\[
\begin{gathered}
 p_i/q_i\ge2/3,\quad q_{\max}/q_{\min}<1.16,\quad
 q_{\max}<1.066,\quad q_{\min}>.862,\\
 .862<c<1.022,\qquad
                       c\le1.073-.3\theta.
\end{gathered}
\tag{49}
\]
Every same-block term dominates its pure counterpart by (24).

For \(s\le\theta\), put \(P=h-\theta\), \(N=h-s\), so \(N\ge P\).
Using (23) and \(U_i(P)\ge-.545q_iP\), every separated term is
at least
\[
 V_j(N-P)+\left(\frac23q_j-.545q_i\right)P
                             \ge V_j(\theta-s).
\tag{50}
\]
For \(s\ge\theta\), \(0\le N\le P\le h-L\). Equations (22)--(23)
instead give
\[
 U_i(P)+V_j(N)\ge U_i(P-N)+(.78q_j-.64q_i)N
                             \ge U_i(s-\theta).
\tag{51}
\]
The last reserve in (51) is at least
\((.78-.64(1.16))q_{\min}N\).

In the high family the full D derivative satisfies
\[
                              F_{0,s}>.96.
\tag{52}
\]
Indeed
\[
 \frac R{\sqrt{1+c^2\cos^2s}}<1.66,
\]
by \(c>.86\) and \(\cos h>.7648\); the quadratic
\(.96y^2-.66y+K-.96\) has negative discriminant.
Equations (22), (49), and (52) show that every pure U function
increases for \(s\ge\theta\), with derivative reserve
\[
                           .96-.72(1.066)>.19.
\tag{53}
\]
Thus only the pure V functions on \(0\le s\le\theta\) remain.

## 9. High interval: convexity of the first derivative

Fix a pair from (14), put \(d=\theta-s\), and consider
\[
                         f(x)=F_0(x)+V(d),\qquad s=\arctan x.
\]
We prove \(f'''(x)>0\) throughout this interval. From (13),
\[
 f'''=F_{0,xxx}
   +\frac{-V'''(d)-6xV''(d)+2(1-3x^2)V'(d)}{(1+x^2)^3}.
\tag{54}
\]
This shape statement will be combined with the right-endpoint
derivative, not with an assumption that f itself is concave.

### 9.1 The range \(s\le.55\)

First,
\[
                              F_{0,xxx}>-.2.
\tag{55}
\]
Its expression in (13) decreases with c on this range, so use
\(c=1.022\). Put \(y=\sin s<.523\), \(A=1+1.022^2\).
Then
\[
 \frac R{A^{3/2}}>.676,\qquad \frac{1.022^2}{A}>.51.
\]
The first three positive binomial coefficients of
\((1-v)^{-5/2}\) give the lower polynomial
\[
 3y(1-y^2)^2
 \left\{-.324+\frac52(.676)(.51)y^2
                  +\frac{35}{8}(.676)(.51)^2y^4\right\}.
\tag{56}
\]
After adding .2, (56) is exactly
\[
 \frac15-\frac{243}{250}y+\frac{45297}{10000}y^3
 -\frac{15342651}{4000000}y^5
 -\frac{4059549}{2000000}y^7
 +\frac{9230949}{4000000}y^9.
\tag{57}
\]
Expand at \(y=.3\). The constant exceeds .0209827,
the absolute linear coefficient is below .08668, and the
quadratic coefficient after subtracting
\(\sum_{j\ge3}|a_j|(.3)^{j-2}\) exceeds 1.966.
Its completed-square lower bound exceeds .020.
This proves (55) on the whole range.

From (19),
\[
 V''(d)<-.288q,\qquad V'''(d)<.312q.
\tag{58}
\]
If \(x\le1/\sqrt3\), (23), (54), and (58) bound the second
numerator in (54) below by
\[
              q\{4/3-.312+1.728x-4x^2\}>.685q.
\]
The quadratic is concave; its two endpoint comparisons suffice.
Since \((1+x^2)^3\le64/27\), this pays (55) with reserve.

For \(1/\sqrt3\le x\le\tan(.55)<.614\), one has \(d<.177\).
Now \(V''<-.3q\), \(-V'''>q(1/3-.177)\), and \(V'<1.4q\).
The numerator is greater than
\[
       q\{1/3-.177+1.8x+2.8(1-3x^2)\}>.894q.
\]
Division by \((1+.614^2)^3\), using \(q>.862\), again exceeds .2.
Thus \(f'''>0\) throughout this first range.

### 9.2 The range \(s\ge.55\)

Here \(x>.613\), \(d\le.15\), and \(q\le1\). For the last claim,
write the companion's high parameter as
\(t=(\theta-L)/(8/15)\ge23/32\).
Its cubic gives
\(l\le1.005069-.141335t<1\), while
\(c\le.908\) and \(m\le.908\sqrt{1+\eta^2}<1\).

The sharper versions of (58) are
\[
\begin{split}
 V''(d)&\le q(-.3-d/3+d^2/2),\\
 -V'''(d)&\ge q(1/3-d),\qquad
 V'(d)\le q(1.4-.3d).
\end{split}
\]
They bound the numerator in (54) below by
\[
 q\{A_3(x)+d(-1.6+2x+1.8x^2)-3xd^2\}\ge qA_3(x),
 \quad
 A_3(x)=\frac{47}{15}+1.8x-8.4x^2.
\tag{59}
\]
The last step follows from
\(-1.6+1.55(.613)+1.8(.613)^2>0\).

The value \(F_{0,xxx}\) is positive here: its minimum comparison
uses \(x=.613,c=.908\) and positive squaring.
If \(A_3(x)\ge0\), (54) is therefore positive immediately.
When \(A_3(x)<0\), use \(q\le1\) and the correlated c bound
in (49). Set
\[
\begin{gathered}
 c_*(x)=1.073-.3\arctan x,\quad w=\sqrt{1+x^2},\\
 T(x)=\frac{R(1+c_*^2)w^6}{(w^2+c_*^2)^{5/2}},\\
 H(x)=3x\{T(x)-w\}+A_3(x).
\end{gathered}
\tag{60}
\]
Since \(F_{0,xxx}\) decreases with c, the right side of
(54), multiplied by \(w^6\), is at least \(H(x)\).

On the actual late range \(\tan(.55)\le x\le\tan h\), hence
\(.613<x<.843\),
\[
 .863\le c_*\le.908,\qquad T<1.83,\qquad T'<3.
\tag{61}
\]
For clarity, the logarithmic derivative used for the last bound is
\[
 \frac{T'}T
 =x\left(\frac6{w^2}-\frac5{w^2+c_*^2}\right)
 +c_*c_*'\left(\frac2{1+c_*^2}-\frac5{w^2+c_*^2}\right).
\tag{62}
\]
The first term is below 1.35. Clearing its positive denominators
reduces this to positivity of
\[
 1.35(1+x^2)(1+x^2+.825)-x(1+x^2+6(.825));
\]
the centered coefficient bound at .728 with radius .115 is
positive. The second term in (62) is below .252, and
\(1.83(1.35+.252)<3\). Positive squaring at
\(x=.843,c_*=.863\) gives the bound for T in (61).

Consequently
\[
\begin{split}
 H'
 &<3(1.83-1.17)+3(.843)(3-.52)+1.8-16.8(.613)\\
 &<-.24.
\end{split}
\tag{63}
\]
At the right endpoint the exact enclosures
\[
 .842288<\tan h<.842289,\qquad
 \sec h<1.30746,\qquad T(\tan h)>1.82777
\]
give
\[
\begin{split}
 H(\tan h)&>
 3(.842288)(1.82777-1.30746)+\frac{47}{15}\\
 &\hspace{17mm}+1.8(.842288)-8.4(.842289)^2>.0047.
\end{split}
\tag{64}
\]
Thus \(H>0\), proving \(f'''>0\) also on the late range.

### 9.3 The two s endpoints

The companion's two whole-interval derivative certificates give
\[
 F_{0,s}(\theta)<\frac{Rk}{\sqrt{1+k^2}},\qquad
 F_{0,s}(\theta)<\frac{Rkl}{\sqrt{k^2+l^2}}.
\tag{65}
\]
These are \(V_H'(0)\) and \(V_G'(0)\).
For B, \(m\ge k\) implies \(D_0(l,m)\ge D_0(k,l)\).
Thus every pure-V function has strictly negative derivative
at \(s=\theta\), equivalently at \(x=\tan\theta\).

By (54)--(64), its first derivative is convex. Once a convex
first derivative with negative right endpoint becomes
nonpositive, it stays nonpositive up to that endpoint.
The function therefore increases and then decreases, or
decreases throughout. Its minimum is at \(s=0\) or \(s=\theta\).
This leaves the three s=0 pure-V functions and the single
equal-angle baseline in the high interval.

## 10. The A/TD split and the strict contradiction

Perform the s reductions first, with the actual split fixed.
At \(s=0\), the low functions before the optional coarse bound
(47) have the same B-dependent forms as the low alternatives of
[the two-positive split theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
Its concavity proof applies because \(c/l,m/l<1.38<1.5\).
Thus each exact endpoint function is concave in
\(a\in[0,\theta]\). After taking the two split endpoints, apply
(47) to obtain the four scalar envelopes (48).
If replacing a negative B term by H in (31) puts both signs
in the H block, its B-dependent form is simply \(H_0\), so
the same concavity comparison still applies.

At \(s=\theta\), only the zero-angle baseline remains.
Its B-dependent part is
\[
                       H_0(m)=\frac32m-R\sqrt{l^2+m^2}.
\]
The same low split proof applies. The D term depends on the
fixed \(\theta\), not on the split.

In the high interval, the B-dependent part is \(H_0\) for
the H/G alternatives, and for a B negative remainder d it is
\[
 H_d(m)=\frac32m+\max(l,m)(\cos d-1)
              -R\sqrt{l^2+m^2-2lm\sin d}.
\]
Both are concave and increasing on \(m/l\le23/20\), uniformly
for \(0\le d\le h\), by Section 6 of the split theorem.
Its remaining second-derivative estimate uses only
\(.9\le c/l\le1.1\) and \(a+z\le h\), so it applies to the
present high family as well. The exact j support transition
has matching first derivatives; the coefficient crossing
at \(m=l\) has a downward derivative jump.
Every retained high endpoint function is therefore concave
on the full split interval.

We have reduced (17) to the eighteen scalar obligations stated
at the start: ten low and eight high, counting both split
endpoints. The companion proves all of them strictly positive.
That contradicts the necessary nonpositive weighted
demand-minus-support inequality. Every reduction used an exact
support, a pointwise lower bound, or a whole-domain derivative
argument. No concentration of the original geometric angles
was assumed.
