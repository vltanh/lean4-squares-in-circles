# Stationary existence from one circle stress and two trial radii

## Theorem and scope

Put

\[
q_b=\left(\frac{79}{40}\right)^2,
\quad q_L=\frac{19577}{5000},
\quad q_U=\frac{1957767069}{500000000},
\quad \alpha=\arctan\frac15.
\tag{1}
\]

Thus \(q_L=3.9154\), \(q_U=3.915534138\), and
\(q_b<q_L<q_U<9789/2500\).

For the actual five-circle radicals

\[
\begin{aligned}
r&=\sqrt{q-u^2},& U&=\sqrt{q-(2-u)^2},& V&=3-U,\\
Y&=\sqrt{q-V^2},&v&=2-Y,& w&=\sqrt{q-v^2},\\
c&=\cos t,&s&=\sin t,\\
k_1&=2-c(r-1)+su,& k_2&=1+cv-s(w-1),\\
F(q,u,t)&=k_1^2+k_2^2-q,
\end{aligned}
\tag{2}
\]

there is an interior triple satisfying

\[
q_L<q_*<q_U,\qquad
\frac{87}{100}<u_*<\frac{11}{10},\qquad
0<t_*<\alpha,
\qquad F=F_u=F_t=0.
\tag{3}
\]

It is obtained as a zero minimum of the actual continuous circle
defect, using the intermediate value theorem. All radicals are
strictly positive. The already proved actual-envelope critical-point
theorem identifies this triple uniquely, and in fact puts \(u_*<1\).

The construction of (3) below does not use that uniqueness theorem,
a local inverse bound, a numerical stationary root, the five support
intervals in `../HUMAN_FAMILY_ENCLOSURE.md`, or any formula checker.
Its only non-elementary analytic operations are compact minimization,
the intermediate value theorem, and differentiation of positive square
roots. The single varying circle stress used below was proved on its
whole domain in `HAND_POSITIVE_TILT_NOMINAL_GAP.md`.

This closes stationary **existence and the displayed radius bracket**
without local-box certificates. It does not assert the much narrower
coordinate brackets used by some historical equality and adaptive
appendices. Those are separate estimates. The theorem is about the
conditional five-corner family; the unrestricted capture of an arbitrary
packing remains a separate global task.

## 1. One fixed smooth position window

Work first on

\[
q_b\le q\le Q_0:=\frac{9789}{2500},\qquad
\frac{87}{100}\le u\le\frac{11}{10},\qquad
0\le t\le\alpha.
\tag{4}
\]

The four radical branches in (2) are positive throughout this product
of intervals. Indeed, successive square comparisons give

\[
r>\frac{41}{25},\qquad
\frac{1619}{1000}<U<\frac{1763}{1000},\qquad
\frac{1237}{1000}<V<\frac{1381}{1000},
\]

\[
\frac{1411}{1000}<Y<2,\qquad
0<v<\frac{589}{1000},\qquad w>\frac{1885}{1000}.
\tag{5}
\]

Here are the direct inequalities behind these bounds. On (4),
\(9/10\le2-u\le113/100\), so

\[
r^2\ge q_b-(11/10)^2>(41/25)^2,
\]

\[
(1619/1000)^2<q_b-(113/100)^2
 \le U^2\le Q_0-(9/10)^2<(1763/1000)^2.
\]

Subtract from three for the two bounds on \(V\). Then

\[
Y^2\ge q_b-(1381/1000)^2>(1411/1000)^2,
\qquad Y^2<q<4.
\]

Finally
\(w^2>q_b-(589/1000)^2>(1885/1000)^2\).
Every squaring here compares positive quantities, so no sign branch is
lost. The same observations give \(r,w<2\). Thus
\(k_1>1\) and \(k_2>4/5\) on (4), since
\(0\le s<1/5\) and \(0<c\le1\).

Define

\[
p=\frac{(2-u)V}{UY}>0,
\qquad
Z=\frac{q}{(2-u)U^2}+\frac{pq}{YV^2}>0.
\tag{6}
\]

Actual differentiation of the four circles gives

\[
r'=-u/r,\quad U'=(2-u)/U,\quad Y'=p,\quad
v'=-p,\quad w'=vp/w,\quad p'=-pZ.
\tag{7}
\]

For the last identity, differentiate
\(\log p=\log(2-u)+\log V-\log U-\log Y\), and use
\(U^2+(2-u)^2=q\), \(V^2+Y^2=q\).

Put

\[
a=s+cu/r,\qquad b=p(c+sv/w).
\]

Then \(k_{1u}=a\), \(k_{2u}=-b\), and

\[
\begin{aligned}
F_{uu}=2\bigg(&a^2+b^2+k_1\frac{cq}{r^3}\\
 &+k_2\left[pZ(c+sv/w)+\frac{sp^2q}{w^3}\right]\bigg)>0.
\end{aligned}
\tag{8}
\]

This proves strict position convexity on the entire fixed window
directly from the positive circle curvatures.

## 2. The minimizing position never reaches either endpoint

We give the endpoint derivative signs over all radii and tilts in (4).
They follow from circle bounds and a quadratic in \(h=\tan t\), with
no subdivision of either radius or tilt.

### 2.1. The left endpoint

At \(u=87/100\), the circle equations give successively

\[
1.773<r<1.778,\quad 1.619<U<1.625,\quad
1.375<V<1.381,
\]

\[
1.411<Y<1.424,\quad .576<v<.589,\quad
1.885<w<1.894.
\tag{9}
\]

For example the two radicands for \(r,U\) are respectively
\(q-.7569\), \(q-1.2769\); the two displayed intervals follow by
squaring their positive endpoints at \(q_b,Q_0\). Next

\[
q_b-1.381^2=1.993464>1.411^2,
\qquad Q_0-1.375^2=2.024975<1.424^2,
\]

which gives the bound on \(Y\). The bounds on \(v,w\) follow in
the same way by subtracting from two, and using
\(q_b-.589^2>1.885^2\), \(Q_0-.576^2<1.894^2\).
Thus all inequalities in (9) have been reduced to their printed
positive-square comparisons.

Writing \(x=u/r\), \(y=v/w\), (6), (9) give

\[
.671<p<.684,\qquad .489<x<.491,\qquad
\frac3{10}<y<\frac5{16}.
\tag{10}
\]

For the first comparison use directly

\[
\frac{1.13(1.375)}{1.625(1.424)}>.671,
\qquad
\frac{1.13(1.381)}{1.619(1.411)}<.684.
\]

The other two are divisions of the positive bounds in (9).

The five coefficients

\[
\begin{aligned}
L_c&=2x-p,&L_s&=2-py,\\
Q_c&=(r-1)x+pv,&Q_s&=u+p(w-1)y,\\
J&=ux-(r-1)-pvy+p(w-1)
\end{aligned}
\]

satisfy

\[
L_c\le\frac5{16},\quad L_s\le\frac95,\quad
Q_c\ge\frac{61}{80},\quad
J\le\frac3{20},\quad Q_s\le\frac{17}{16}.
\tag{11}
\]

To verify these uniformly, substitute respectively the bounds

\[
\begin{aligned}
L_c&<2(.491)-.671,\\
L_s&<2-(.671)(.3),\\
Q_c&>(.773)(.489)+(.671)(.576),\\
J&<(.87)(.491)-.773-(.671)(.576)(.3)+(.684)(.894),\\
Q_s&<.87+(.684)(.894)(5/16).
\end{aligned}
\]

All five right sides compare in the asserted directions with (11).
These are five bounds for one derivative polynomial, not a family of
local verification boxes.

Since \(0\le h\le1/5\) and \(1/c=\sqrt{1+h^2}<51/50\),
expansion of the actual derivative gives

\[
\begin{aligned}
\frac{F_u}{2c^2}
 &=\frac{L_c}{c}-Q_c
      +h\left(\frac{L_s}{c}+J\right)+h^2Q_s\\
 &\le\frac{51}{50}\frac5{16}-\frac{61}{80}
   +\frac15\left(\frac{51}{50}\frac95+\frac3{20}\right)
   +\frac1{25}\frac{17}{16}
 =-\frac{81}{20000}<0.
\end{aligned}
\tag{12}
\]

This proves \(F_u<0\) at the left endpoint throughout (4).

### 2.2. The right endpoint

At \(u=11/10\), the same successive-square argument gives

\[
r<\frac{33}{20},\qquad
U>1.758,\qquad V<1.242,\qquad
Y>1.53,\qquad v<.47,\qquad w>1.91.
\tag{13}
\]

Indeed \(U^2=q-.81>1.758^2\); then
\(Y^2>q_b-1.242^2>1.53^2\), and
\(w^2>q_b-.47^2>1.91^2\). Therefore

\[
0<p<\frac{(.9)(1.242)}{(1.758)(1.53)}<\frac{21}{50},
\quad \frac ur>\frac23,
\quad 0<\frac vw<\frac14.
\]

It follows that

\[
k_1\ge\frac{27}{20},\qquad
a>\frac23c,\qquad
k_2\le\frac{147}{100},\qquad
b\le\frac{441}{1000}c.
\]

Here the last bound uses
\(c+s(v/w)\le c(1+(1/5)(1/4))=(21/20)c\).
Consequently

\[
\frac{F_u}{2}=k_1a-k_2b
 >c\left(\frac{27}{20}\frac23
          -\frac{147}{100}\frac{441}{1000}\right)
 =\frac{25173}{100000}c>\frac14c>0.
\tag{14}
\]

By compactness, continuity, (8), (12), and (14), at every fixed \(q,t\)
in (4) there is a unique minimizing position inside the window. The
derivative is zero there. Define

\[
M(q,t)=\min_{87/100\le u\le11/10}F(q,u,t),
\qquad
H(q)=\min_{0\le t\le\alpha}M(q,t).
\tag{15}
\]

These are minima over fixed compact sets. Joint continuity of the actual
radicals therefore makes \(M,H\) continuous. This argument does not
postulate continuity or differentiability of a selected minimizer.

## 3. The single stress excludes the lower radius and both tilt endpoints

Write \(g(q,s)\) for the explicit varying five-circle gap proved in
`HAND_POSITIVE_TILT_NOMINAL_GAP.md`. Its mass sum is

\[
\begin{aligned}
\mathcal M(s)={}&\frac{12/41}{1+13s/60}
 +\frac{12/41}{1-9s/50}
 +\frac{12/31}{1+9s/25}\\
 &+\frac{12/31}{1+49s/100}
 +\frac{3s/10}{1+4s/5}.
\end{aligned}
\tag{16}
\]

That note proves, by one explicit polynomial inequality on the whole
arc, that

\[
g(q_U,s)\ge p(s)\qquad(0\le s\le3/10),
\tag{17}
\]

where

\[
p(s)=B_0-\frac{79}{1250}s+\frac{51}{200}s^2
       -\frac{s^3}{100}-\frac{27}{100}s^4-\frac3{10}s^5,
\quad B_0=\frac{38726637}{9929687500}.
\tag{18}
\]

Its exact radius dependence is

\[
g(q,s)=g(q_U,s)+(q_U-q)\mathcal M(s).
\tag{19}
\]

The stress implication needed here concerns the exact family, with no
perturbation or owner assumption:

\[
F(q,u,t)\le0\quad\Longrightarrow\quad g(q,\sin t)\le0.
\tag{20}
\]

For an explicit adapter to the stress's coordinates, take

\[
\begin{array}{lll}
(a_A,b_A)=(r-1/2,u-1/2),&
(a_B,b_B)=(U-1/2,3/2-u),\\
(a_D,b_D)=(3/2-v,5/2-U),&
(a_E,b_E)=(w-1/2,v-1/2),\\
(a_H,b_H)=(k_2-1/2,k_1-1/2),&
b_T=U-3/2,\quad b_G=3/2-k_1.
\end{array}
\tag{21}
\]

The five quantities
\((a_i+1/2)^2+(b_i+1/2)^2\) equal \(q,q,q,q,q+F\).
The seven nominal chain projections are exactly

\[
1,W,1,1,1,1,W,\qquad W=\frac{1+c+s}{2}.
\]

For example,
\(ca_A-sb_A-b_G=W\) and
\(a_H+sa_E-cb_E=W\) follow by substituting (2).
The other identities are immediate adjacent-coordinate differences.
The free variables \(b_T,b_G\) cancel in the positive stress. Its
completed-square disk inequality is valid for all real \(a_i,b_i\),
so (21) requires no hidden radial chart or sign hypothesis. This proves
(20) directly from the same circle stress used in (17).

### 3.1. A lower bound for the stress on the whole small-tilt arc

For \(0\le s\le1/5\), each of the first four masses in (16) is
strictly greater than \(1/4\). For example the first is at least
\(3600/12833>1/4\), and the last of those four is at least
\((12/31)/(549/500)>1/4\). Hence

\[
\mathcal M(s)>1.
\tag{22}
\]

The polynomial (18) has

\[
p''(s)=\frac{51}{100}-\frac3{50}s
        -\frac{81}{25}s^2-6s^3
\ge\frac{801}{2500}>\frac8{25}
\quad(0\le s\le1/5).
\tag{23}
\]

At the single expansion point \(s_0=13/100\),

\[
p(s_0)=-\frac{14824601979}{127100000000000}
       >-\frac{117}{1000000},
\qquad
p'(s_0)=-\frac{8327}{40000000},
\quad |p'(s_0)|<\frac1{4000}.
\]

Integrating (23), then completing a square, proves

\[
\begin{aligned}
p(s)&\ge p(s_0)-\frac{25}{16}p'(s_0)^2\\
 &>-\frac{117}{1000000}-\frac{25}{16}\left(\frac1{4000}\right)^2
 =-\frac{29977}{256000000}>-\frac1{8000}
\end{aligned}
\tag{24}
\]

throughout the entire interval \([0,1/5]\).

Now \(q_U-q_L=67069/500000000\). Equations (17), (19), (22),
(24) give

\[
g(q_L,s)>-\frac1{8000}+(q_U-q_L)
 =\frac{4569}{500000000}>0.
\tag{25}
\]

Since \(\sin t\le1/\sqrt{26}<1/5\) on the full tilt interval,
(20), (25) show that \(F(q_L,u,t)>0\) for every allowed \(u,t\).
Compactness therefore gives

\[
H(q_L)>0.
\tag{26}
\]

### 3.2. The tilt endpoints are infeasible at every intervening radius

At \(t=0\), the gap in (17) equals \(B_0>0\). Its E force and
mass both vanish and E is omitted from the stress, exactly as in the
nominal proof. Equations (19), (22) retain positivity for every
\(q\le q_U\).

At \(t=\alpha\), \(s=1/\sqrt{26}>19/100\). The polynomial
\(p\) is strictly increasing on \([3/20,1/5]\): its second
derivative is positive by (23), and
\(p'(3/20)=13153/1600000>0\). Direct substitution gives

\[
p(19/100)=\frac{76621791543}{127100000000000}>\frac1{2500}>0.
\]

Thus (17)--(20) show, uniformly for \(q_L\le q\le q_U\),

\[
M(q,0)>0,\qquad M(q,\alpha)>0.
\tag{27}
\]

This excludes the two actual geometric tilt boundaries using the same
continuous stress as (25). There is no cover of the intervening angles.

## 4. An explicit negative trial at the sharp rational upper ceiling

The following fixed rational chain is useful because it proves the
upper bound \(q_*<q_U\) directly. None of its coordinates is defined
by a stationary root. Put \(N=10^{12}\) and take

\[
\bar u=\frac{920656678000}{N},\quad
\bar r=\frac{1751549433859}{N},\quad
\bar U=\frac{1658478860659}{N},
\]

\[
\bar Y=\frac{1454597941254}{N},\quad
\bar v=2-\bar Y=\frac{545402058746}{N},\quad
\bar w=\frac{1902122691183}{N}.
\tag{28}
\]

Choose the rational half-angle parameter

\[
\bar z=\frac{61897411}{10^9},\quad
\bar c=\frac{1-\bar z^2}{1+\bar z^2},\quad
\bar s=\frac{2\bar z}{1+\bar z^2},\quad
\bar t=2\arctan\bar z.
\tag{29}
\]

The identities in (29) give a unit frame. Also
\(0<\bar z<1/16\), so
\(0<\tan\bar t<32/255<1/5\). Thus the trial tilt is inside
the required interval, and \(\bar u\) is inside the position window.

The first four fixed circle comparisons are exactly

\[
\begin{aligned}
N^2(q_U-\bar r^2-\bar u^2)&=2220900368119>0,\\
N^2(q_U-\bar U^2-(2-\bar u)^2)&=1229578085719>0,\\
N^2(q_U-(3-\bar U)^2-\bar Y^2)&=850026993203>0,\\
N^2(q_U-\bar w^2-\bar v^2)&=2366378967995>0.
\end{aligned}
\tag{30}
\]

Define the fifth corner by the exact chain demands,

\[
\bar k_1=2-\bar c(\bar r-1)+\bar s\bar u,
\quad
\bar k_2=1+\bar c\bar v-\bar s(\bar w-1).
\]

With \(D=1003831289488502921\), the common denominator of
\(\bar c,\bar s\), the last circle comparison is

\[
\begin{aligned}
D^2N^2(q_U-\bar k_1^2-\bar k_2^2)
={}&1792883094085810154277440730806605808809643271216323\\
>{}&0.
\end{aligned}
\tag{31}
\]

For direct reproduction of this one integer identity, the numerators
of \(\bar k_1,\bar k_2\) over \(DN\) are respectively

\[
1372965078140161465967017802139,
\qquad 1435465637082661064163165402934.
\]

Thus (30), (31) are five inequalities for five explicitly written
points. They do not assert a sign throughout any variable box.

Apply the actual radical definitions (2) at
\((q,u,t)=(q_U,\bar u,\bar t)\). From (30), in sequence,

\[
r>\bar r,\quad U>\bar U,\quad
V<3-\bar U,\quad Y>\bar Y,\quad
0<v<\bar v,\quad w>\bar w.
\]

The positivity required to square or compare these quantities follows
from (5) and the positive constants (28). Since both components in (2)
are positive and \(\bar c,\bar s>0\), we obtain

\[
0<k_1<\bar k_1,\qquad 0<k_2<\bar k_2.
\]

Equation (31) therefore proves

\[
F(q_U,\bar u,\bar t)<0,
\qquad H(q_U)<0.
\tag{32}
\]

## 5. Intermediate value, stationarity, and radius uniqueness

Continuity of \(H\), (26), and (32) give some
\(q_*\in(q_L,q_U)\) with \(H(q_*)=0\). Choose a minimizing
pair \((u_*,t_*)\) from (15).

The signs (12), (14) exclude either position endpoint. The positive
values (27) exclude either tilt endpoint. Hence the pair is interior
in the fixed product of intervals. The actual function (2) is smooth
there by (5). Fermat's rule gives

\[
F(q_*,u_*,t_*)=F_u(q_*,u_*,t_*)=F_t(q_*,u_*,t_*)=0.
\]

This proves existence (3) without a local stationary equation checker.

There is also only one zero of \(H\), even on the full broad strip
\([q_b,Q_0]\). If \(q_0<q_1\) belong to that strip, keep any fixed
position and tilt. Increasing \(q\)
increases \(r,U,Y,w\) and decreases \(V,v\), by the same sequence
of circle comparisons used in Section 4. Both positive components
\(k_1,k_2\) strictly decrease, since \(c>0\). Consequently

\[
F(q_1,u,t)<F(q_0,u,t)-(q_1-q_0).
\]

Evaluate at a minimizing pair for \(q_0\) and take the minimum at
\(q_1\). Then

\[
H(q_1)<H(q_0)-(q_1-q_0).
\tag{33}
\]

Thus the zero-minimum radius is unique, without differentiating a
minimizer with respect to radius.

## 6. Connection with the existing geometric stationary uniqueness theorem

The uniqueness step can now be used in its proper order: **after**
existence has been supplied without a local formula certificate.
Full-domain strict position convexity, including comparison with radical
endpoints, is proved in Section 1 of `STATIONARY_GEOMETRY.md`. Therefore
any admissible position-stationary point is the unique global position
minimum and agrees with the minimizer on our window. Sections 5--10
of that note, and the corresponding
hand estimates in Section 4 of `../HUMAN_FAMILY_CLOSURE.md`, prove
the following statement on the entire broad strip
\(q_b\le q\le Q_0\), \(0<t<\alpha\):

* Every simultaneous position/tilt critical point of the actual
  minimized envelope has \(87/100<u<1\).
* At every such point the actual Hessian satisfies
  \(F_{uu}>0\) and
  \(\det(\operatorname{Hess}F)>(237/5000)k_1^2>0\),
  **without assuming a nonpositive defect**.
* The implicit differentiation formula is
  \(M_{tt}=F_{tt}-F_{ut}^2/F_{uu}\).

The strict determinant estimate uses the actual positive-defect normal
term \(2k_1+k_2-|k|^2\); it does not replace \(|k|^2\) by \(q\).
Its estimates use whole-domain circle supports and the one fixed
comparison position from Section 2, not the historical root boxes.

It follows that every critical point of \(M(q,\cdot)\) is a strict
local minimum. Two such minima would give a maximum between them,
which would be another critical point and could not be a strict
minimum. Thus there is at most one critical tilt. An interior critical
tilt is the global minimum on the closed tilt interval: the derivative
has negative sign immediately before and positive sign immediately
after it, and cannot change sign again without another critical point.
The endpoint comparisons follow by integration and continuity.

Apply this to the witness from Section 5. At its radius the tilt is
unique, strict position convexity makes the position unique, and the
positive radicals determine every remaining coordinate. Its remaining
admissibility signs follow as well. Since \(v'=-p<0\) and \(u_*<1\),
\[
v_*>v(q_*,1)=2-\sqrt{6\sqrt{q_*-1}-8}>\frac12.
\]
The last inequality follows from
\(q_*<Q_0<2257/576\), which gives
\(\sqrt{q_*-1}<41/24\). Together with (5), this proves
\(1/2<v_*<.589<.87<u_*<1\). Therefore
\(y_*=-u_*\), \(y_{4,*}=-v_*\) have exactly the required branches
\(-1<y_*<y_{4,*}<-1/2\). With
\(z_* = \tan(t_*/2)>0\), the half-angle formula also gives
\(2z_* /(1-z_*^2)=\tan t_*<1/5\) and \(z_*<1\).
The witness consequently satisfies all the original broad stationary
admissibility conditions, in addition to its three stationary equations.

Conversely
every broad admissible stationary zero is an interior global envelope
minimum by the same argument. Its radius must therefore be the unique
zero of \(H\), by (33), and its position and tilt agree with the
constructed witness. This is the existing geometric uniqueness theorem
with its existence premise supplied by (3).

No use of `HUMAN_FAMILY_ENCLOSURE.md`'s five tilt intervals is needed
for this selection argument. The old local existence and numerical
coordinate-bracket checks are also unnecessary for the theorem (3).

## 7. The same rational trial gives an unconditional eight-square upper bound

For completeness, (28)--(31) describe an actual packing at \(q_U\),
not merely five unconstrained circle points. Use six standard-frame
squares with centers

\[
\begin{aligned}
A&=(\bar r-\tfrac12,\tfrac12-\bar u),&
B&=(\bar U-\tfrac12,\tfrac32-\bar u),\\
C&=(\bar U-\tfrac32,\tfrac7{20}),&
T&=(\bar U-\tfrac32,\tfrac{27}{20}),\\
D_0&=(\bar U-\tfrac52,\tfrac32-\bar v),&
E&=(\tfrac12-\bar w,\tfrac12-\bar v).
\end{aligned}
\tag{34}
\]

Let \(e=(\bar c,\bar s)\), \(f=(-\bar s,\bar c)\), and use
the tilted squares

\[
P_H=-\bar k_1e-\bar k_2f,\qquad
H=P_H+\frac{e+f}{2},\qquad G=H+e.
\tag{35}
\]

Equations (30), (31) contain the five farthest vertices of
\(A,B,D_0,E,H\). The farthest squared norm of \(G\) is smaller
than that of \(H\), because
\(|P_H+2e|^2-|P_H|^2=4(1-\bar k_1)<0\).
For \(C,T\), the farthest vertices are
\((\bar U-1,17/20)\), \((\bar U-1,37/20)\). Since
\(0<\bar U-1<.66\), their squared norms are below respectively
\(.66^2+.85^2\) and \(.66^2+1.85^2\), both below \(q_U\).

The six standard squares occupy three horizontally separated columns.
The required inequalities are \(\bar r>\bar U\) and
\(\bar w+\bar U>3\), which are direct from (28). Within each
column, the two squares have the exact horizontal contact heights
\(1-\bar u\), \(17/20\), \(1-\bar v\), respectively. This
covers their fifteen pairs.

The pair \(H,G\) is separated along \(e\), with center gap one.
Writing \(W=(1+\bar c+\bar s)/2\), the definitions give

\[
e\cdot(A-G)=W,\quad e\cdot(A-H)=W+1,
\quad f\cdot(E-H)=f\cdot(E-G)=W.
\]

These are separating axes for the four pairs with \(A,E\). Finally
the elementary rational bounds from (28)--(31) include

\[
1.36<\bar k_1<1.38,\quad1.42<\bar k_2<1.44,
\quad .99<\bar c<1,\quad .12<\bar s<.13.
\]

The top of \(G\), which is higher than that of \(H\), is

\[
\bar s(2-\bar k_1)+\bar c(1-\bar k_2)
 <(.13)(.64)-(.99)(.42)<-\frac3{20}.
\]

The bottoms of \(B,C,D_0,T\) are all at least \(-3/20\).
Thus these four squares are vertically separated from each of
\(H,G\), covering the last eight pairs. All 28 pairs have disjoint
open interiors, and all eight squares lie strictly inside the disk of
squared radius \(q_U\).

This fixed construction justifies the sharp rational ceiling used by
the nominal tilt stress without calling a stationary root bracket. It
does not prove the unrestricted lower bound; that still requires the
global geometric capture gates.
