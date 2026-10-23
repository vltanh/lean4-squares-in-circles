# The three zero edges for the augmented primary charge

## 1. Statement and common potential

Work on the actual G0--G2 boundary cycle at
\(Q=9789/2500\). Retain the notation and the single outer
potential of
[`HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md`](HAND_G3_HIGH_QUARTER_AUGMENTED_PRIMARY_CHARGE.md):
\[
\begin{gathered}
R=\sqrt Q,\qquad a_0=\sqrt{Q-1/4}-1/2,
\qquad c_0=\sqrt{Q/2}-1/2,\\
\kappa=103/100,\qquad \rho=11/10,\\
F_H^*(A,B)=\pi/4-.569472(A-c_0)+.390886(B-c_0),\\
J(A,B)=F_H^*(A,B)-F(A,B),\qquad
\Pi(A,B)=\kappa A+\rho J(A,B).
\end{gathered}                                                   \tag{1}
\]
Here F is the unchanged original L, M, or H outer marker. Both
adjacent original markers are allowed at a chart junction.
All terminating decimals below are exact rational numbers.

Consider any original zero-quarter edge whose source has
primary coordinate a and signed tangent y, and whose outer
target has primary coordinate A and signed tangent \(-B<0\).
Its actual witness is one of
\[
\begin{split}
P_0&=y+A\sin d+B\cos d\ge W(d),\\
P_2&=a\sin d+y\cos d+B\ge W(d),\\
W(d)&=(1+\cos d+|\sin d|)/2,\qquad |d|\le7/10.
\end{split}                                                     \tag{2}
\]
Put
\[
C_z=d+\kappa y-\Pi(A,B),\qquad
\gamma_0=\kappa(1-2c_0).                              \tag{3}
\]

**Theorem.** If the source is positive, or the target uses its
L or M marker, or \(d\le7/20\), then
\[
                         C_z\ge\gamma_0.             \tag{4}
\]
In every remaining case,
\[
                         C_z>\gamma_0-7/1000.        \tag{5}
\]
In particular, if all three zero targets are negative outer
states, their charges satisfy
\[
\boxed{\qquad
\sum_{\text{three zero edges}}C_z>
               3\kappa(1-2c_0)-7/1000.\qquad}       \tag{6}
\]

The source may be any original radial state. When y is
nonpositive it is outer by
[`HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md`](HAND_G3_NONPOSITIVE_ZERO_SOURCE_IS_OUTER.md).
The global original-owner theorem then gives owner 2 and d>0.
For positive sources the proof below needs only the original
corner bounds. No assumption on the other source signs, a
frame order, a G1 upper charge cap, or a preferred zero owner
is made.

The final summation uses the global total positive variation
less than 7/10. Hence at most one of the three zero edges can
have d>7/20. This is the only coupling required for (6).
The note supplies the zero component for (1); an outer-to-outer
bridge bound is still needed before the components exclude a
cycle.

## 2. An outer-target gap

The defining square identities give
\[
.89921<c_0<.89922,\quad
1.41457<a_0<1.41458,\quad
\cos z>.76,\quad \sin z<.65\qquad(0\le z\le.7).
                                                               \tag{7}
\]
The trigonometric estimates are the alternating Taylor bounds
in `HAND_G3_GLOBAL_D_IS_OUTER.md`, Section 2. The original
whole-chart marker estimate in
`HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md`, Section 2,
is
\[
                         F(A,B)\ge .86B.             \tag{8}
\]
Set
\[
\begin{split}
C_H&=\pi/4+.178586c_0,\\
u&=\kappa-\rho(.569472)=126119/312500,\\
v&=\rho(.86-.390886)=2580127/5000000.
\end{split}                                                     \tag{9}
\]
Equation (8) implies
\[
                         \Pi(A,B)\le uA-vB+\rho C_H. \tag{10}
\]

For every outer target,
\[
                   \Pi(A,B)+\kappa B\le2\kappa c_0. \tag{11}
\]
On the H chart this is just A+B<=2c0, since J=0.
On L and M, B<13/25. Indeed the M/H junction has A=7B/3,
and substitution of B=13/25 into its circle equation exceeds
Q by 1357/22500. Moreover
\[
1.19<a(13/25)<1.2,\qquad
a(B)=\sqrt{Q-(B+1/2)^2}-1/2.                         \tag{12}
\]
The two exact square reserves in (12) are respectively
191/10000 and 37/2500.

The derivative of uA+(kappa-v)B along the sorted outer arc
is at least kappa-v-u=551969/5000000>0. Therefore (10), (12),
\(\pi<355/113\), and (7) give the stronger gap
\[
\begin{split}
2\kappa c_0-\Pi-\kappa B
&>\Delta_0,\\
\Delta_0
&=(2\kappa-\rho(.178586))(.89921)
       -\rho\frac{355}{452}-\frac65u-\frac{13}{25}(\kappa-v)\\
&=\frac{3402760306721}{56500000000000}>0.
\end{split}                                                     \tag{13}
\]
This proves (11) for all three charts, with a uniform strict
reserve on L and M.

## 3. Nonpositive errors

At d=0 either projection in (2) is y+B. Feasibility gives
y+B>=1 and therefore y>0, because B<9/10. Thus
\[
C_z-\gamma_0=\kappa(y+B-1)
                +(2\kappa c_0-\Pi-\kappa B)\ge0.     \tag{14}
\]

Suppose d<0. A nonpositive source is impossible by the global
zero-owner/sign theorem; equivalently, its only possible
projection P2 would be at most B<1. Hence y>0. Apply
`HAND_G4_ALL_SIGN_ZERO_LINEAR_CHARGE.md` to the actual edge.
For D=y+B-1 and \(h(x)=(\sin x+\cos x-1)/2\), it gives
\[
                    d-.02h(|d|)+.98D>0.              \tag{15}
\]
In particular D>0. Since h(|d|)>0 and kappa>.98,
d+kappa D>0. Equations (11) and (14), with the additional d,
then prove C_z>gamma0. This deals with every nonpositive error
without a radial substitution.

## 4. Positive source and nonnegative error

Write s=sin d and c=cos d. Here y>=0; allowing y=0 only
enlarges the scalar comparisons in this section.

### 4.1 Target in L or M

For owner 2, add kappa(W-P2)<=0 to the charge and retain
a<=a0, y>=0. By (13),
\[
C_z-\gamma_0\ge\Delta_0+F_0(d),\qquad
F_0(d)=d-\kappa\{(a_0-1/2)\sin d+(1-\cos d)/2\}.     \tag{16}
\]
For owner 0, the corresponding lower expression is
\[
                d+\kappa W-\kappa(A\sin d+B\cos d)-\Pi.
                                                               \tag{17}
\]
At zero this is at least gamma0+Delta0. Its derivative is
\[
1+\kappa\{(1/2-A)\cos d+(B-1/2)\sin d\}.
\]
Both this derivative and F0' are bounded below by
\[
1-\kappa\sqrt{(.915)^2+(1/2)^2}
             >1-\kappa(1.043)=-.07429,               \tag{18}
\]
because \((1.043)^2-(.915)^2-1/4=39/62500>0\).
Consequently both original owners have
\[
C_z-\gamma_0>
\Delta_0-.07429\frac7{10}
       =\frac{464590806721}{56500000000000}>0.         \tag{19}
\]

### 4.2 H target, original owner 0

Here Pi=kappa A. Add kappa(W-P0) and use the target's actual
circle, enlarged to its whole disk. This gives
\[
C_z\ge F_1(d):=
d+\kappa\{1+\sin d+\cos d-R\sqrt{2+2\sin d}\}.        \tag{20}
\]
We have F1(0)=gamma0. Put
\[
j(s)=\sqrt{1-s^2}-s-(c_0+1/2)\sqrt{1-s}.
\]
Then F1'=1+kappa j(s). On 0<=s<=.65,
\[
j''(s)=(1-s)^{-3/2}
 \{(c_0+1/2)/4-(1+s)^{-3/2}\}<0,
\qquad j'(0)<-.3.                                  \tag{21}
\]
For the strict sign in (21), use c0+1/2<1.4,
1+s<2, and \(8(.35)^2<1\). Thus j decreases. At s=.65,
\(\sqrt{.5775}>.759\) and \(\sqrt{.35}<.592\), so
\[
j(s)> .759-.65-1.4(.592)=-.7198,
\qquad F_1'(d)>\frac{129303}{500000}>0.               \tag{22}
\]
This proves (4) for this owner.

### 4.3 H target, original owner 2

For any 0<=lambda<=kappa, add lambda(W-P2), retain y>=0
and a<=a0, and use the target disk. Since kappa-lambda cos d
is nonnegative,
\[
C_z\ge d+\kappa/2+\lambda X(d)
                      -R\sqrt{\kappa^2+\lambda^2},\qquad
X(d)=1+\tfrac12\cos d-(a_0-\tfrac12)\sin d.          \tag{23}
\]
With lambda=kappa, the right side minus gamma0 is F0(d).
On [0,1/5],
\[
F_0''(d)=\kappa\{(a_0-1/2)\sin d-\tfrac12\cos d\}<0,
\]
because the expression in braces is at most
.915(.2)-.5(.98)=-307/1000. Alternating Taylor bounds give
\[
F_0(1/5)>
\frac15-\kappa\{.915 S_5(1/5)+1/100\}
             =\frac{6160217}{2500000000}>0,          \tag{24}
\]
where \(S_5(x)=x-x^3/6+x^5/120\). Concavity and F0(0)=0
therefore prove the result throughout this first interval.

For d>=1/5, X is positive and decreasing. The elementary
Taylor estimates give
\[
0<X(d)<1.309,\qquad
V(d):=\sqrt{Q-X(d)^2}>1.483.                         \tag{25}
\]
For clarity, X>=1+.5(.76)-.915(.65)=3141/4000>0;
at d=1/5 its upper bound
\(1+C_4(1/5)/2-.91457S_3(1/5)\) is less than 1.309
by 16531/25000000; and
\(Q-(1.309)^2-(1.483)^2=283/100000>0\).
Choose the admissible multiplier lambda=kappa X/V in (23).
It gives
\[
C_z-\gamma_0\ge
F_2(d):=d+\kappa\{2c_0-1/2-V(d)\}.                 \tag{26}
\]
This multiplier maximizes the concave expression in (23), so
F2(1/5)>=F0(1/5)>0. Also
\[
F_2'(d)\ge
1-\frac{\kappa(1.309)(1.043)}{1.483}
            =\frac{7675439}{148300000}>0.            \tag{27}
\]
The norm estimate in (18) bounds |X'| here. This proves
(4) for the last positive-source case.

## 5. Nonpositive source: retain both circle supports

The source is now outer, with y=-b<=0. Its original owner is
2, and d=z>0. Put
\[
\mu=1-z/5,\qquad \lambda=\kappa\mu,\qquad
N_1=\sqrt{1+\mu^2-2\mu\cos z},\qquad
N_2=\sqrt{1+\mu^2}.                                 \tag{28}
\]
Throughout [0,.7], .86<=mu<=1. In particular all coefficients
of the source support below have the indicated nonnegative
signs. Add lambda(W-P2) to C_z. The source force is
\((\lambda\sin z,\kappa-\lambda\cos z)\), whose norm is
kappa N1.

### 5.1 Target in H

The target force is (kappa,lambda). Applying the two actual
circle supports and collecting their half-coordinate shifts
gives exactly
\[
C_z\ge z+\kappa+\lambda(1+\sin z)
                       -R\kappa(N_1+N_2).           \tag{29}
\]
Using \(R\sqrt2=2c_0+1\), this becomes
\[
C_z-\gamma_0\ge
z+\kappa\{\mu(1+\sin z)-1-RN_1-R(N_2-\sqrt2)\}.
                                                               \tag{30}
\]
Section 6 supplies a single polynomial H on the whole angle
interval which is no larger than the right side. It proves
\[
H(z)\ge0\quad(0\le z\le7/20),\qquad
H(z)>-7/1000\quad(0\le z\le7/10).                    \tag{31}
\]

### 5.2 Target in L or M

Use (10). The target force to maximize is
uA+(lambda-v)B. It increases along 0<=B<=.52, since (12)
and lambda>=.86kappa give
\[
\lambda-v-u\frac{B+1/2}{A+1/2}
\ge .86\kappa-v-u\frac{102}{169}
                 =\frac{106633329}{845000000}>0.     \tag{32}
\]
Thus its maximum is less than 1.2u+.52(lambda-v).
Collect the source circle support as in (29), and then use
the definition of Delta0 in (13). The result is
\[
C_z-\gamma_0\ge\Delta_0+z+
\kappa\{\mu\sin z+.02(1-\mu)-RN_1\}.                \tag{33}
\]
Section 6 bounds the right side below by one polynomial L
which is positive on all of [0,.7]. This proves (4) for both
lower target charts, including every adjacent marker choice.

## 6. Two explicit norm envelopes and whole-interval bounds

Set
\[
\begin{split}
p_1(z)={}&1-\frac5{52}z-\frac{725}{16224}z^2
       +\frac{1045}{281216}z^3+\frac{365515}{526436352}z^4,\\
p_2(z)={}&1-\frac z{10}+\frac{z^2}{200}
       +\frac{z^3}{2000}+\frac{z^4}{20000},\\
S_7(z)={}&z-z^3/6+z^5/120-z^7/5040.
\end{split}                                                     \tag{34}
\]
For every 0<=z<=.7,
\[
N_1\le\frac{\sqrt{26}}5z p_1(z),\qquad
N_2\le\sqrt2 p_2(z),\qquad p_2(z)\le1.               \tag{35}
\]
Here is an exact whole-interval verification. The lower
cosine polynomial C6 gives
\[
N_1^2\le z^2 X_1(z),\qquad
X_1(z)=\frac{26}{25}-\frac z5-\frac{z^2}{12}
               +\frac{z^3}{60}+\frac{z^4}{360}-\frac{z^5}{1800}.
\]
Write \((26/25)p_1^2-X_1=\sum_{j=5}^8r_jz^j\).
Direct expansion of (34) gives the single remainder estimate
\[
r_5-\sum_{j=6}^8|r_j|(7/10)^{j-5}
          =\frac{355688580400073}{10659047411810304000}>0.
                                                               \tag{36}
\]
Also p1>.9 by dropping its positive cubic and quartic terms.
This proves the first inequality of (35).

For the second,
\[
\begin{split}
p_2^2-(1-z/5+z^2/50)
=z^4\left\{\frac1{40000}-\frac z{200000}
       +\frac{3z^2}{4000000}+\frac{z^3}{20000000}
       +\frac{z^4}{400000000}\right\}.
\end{split}
\]
The constant coefficient minus the sum of the absolute
remaining terms at z=.7 is
84458999/4000000000000>0. Since p2>=.93, squaring is valid.
Finally p2-1<=0 follows after factoring z and substituting
.7 in the three positive terms. These prove (35).

The circle constants satisfy
\[
\frac{R\sqrt{26}}5<\frac{1009}{500},\qquad
R\sqrt2>\frac{139921}{50000}.                        \tag{37}
\]
Their squared reserves are 1/10000 and
113759/2500000000. Because p2-1<=0, the second comparison
has the correct direction in (30). Define the following
two fixed degree-eight polynomials:
\[
\begin{split}
H(z)={}&z+\kappa\left\{
\mu(1+S_7(z))-1-\frac{1009}{500}z p_1(z)
             -\frac{139921}{50000}(p_2(z)-1)\right\},\\
L(z)={}&\Delta_0+z+\kappa\left\{
\mu S_7(z)+\frac z{250}-\frac{1009}{500}z p_1(z)\right\}.
\end{split}                                                     \tag{38}
\]
Equations (35)--(37) and S7<=sin show that these bound
(30) and (33), respectively, from below.

For completeness, the next calculations give explicit
whole-interval control of (38). For a polynomial
\(P(z)=\sum_i p_i z^i\), set h=7/20 and define
\[
[P]_j=\sum_{i\ge j}p_i\binom ij h^{i-j};
\qquad P(h+w)=\sum_j[P]_j w^j.                       \tag{39}
\]
This is an ordinary change of origin, not a subdivision of
the angle domain. Expanding the factored polynomial H in
(38) gives
\[
2[H]_2+\sum_{j=3}^8j(j-1)|[H]_j|h^{j-2}
       =-\frac{1487392591742497}{43869696000000000}<0. \tag{40}
\]
Hence H''<0 on the entire interval. Its exact endpoint
values are
\[
\begin{split}
H(0)&=0,\\
H(7/20)&=\frac{1649888279468003300257}
                     {263218176000000000000000}>0,\\
H(7/10)&=-\frac{54794962276481408359}
                      {8225568000000000000000}>-\frac7{1000}.
\end{split}                                                     \tag{41}
\]
Concavity proves both assertions in (31).

For L, the corresponding first-derivative bound is
\[
[L]_1+\sum_{j=2}^8j|[L]_j|h^{j-1}
       =-\frac{182385530325000823}{26321817600000000000}<0.
                                                               \tag{42}
\]
Thus L decreases throughout [0,.7], and
\[
L(7/10)=\frac{48132410094491689181}
                   {7435913472000000000000}>0.       \tag{43}
\]
This proves the claim after (33). All comparisons in this
section follow from the two displayed fixed polynomials,
their explicit coefficient formula (39), and one aggregate
remainder bound for each required derivative. There is no
angle mesh or generated family of interval rows.

## 7. Sum the three original zeros

Sections 3 and 4 give (4) for nonpositive errors and for
all positive sources. Section 5.2 gives it for every L or M
target. The only possible loss is therefore the H-target,
nonpositive-source case of Section 5.1, where d>0. By (31),
there is no loss for d<=7/20, and the loss is strictly less
than 7/1000 for every d<=7/10.

The global variation theorem, as used in
`HAND_G3_ALL_NONPOSITIVE_ZERO_SOURCES_ARE_OUTER.md`, Section 3,
gives total positive variation less than 7/10. Two zero edges
cannot both have d>7/20. Summing the three charges therefore
proves (6). This conclusion applies in particular when all
four quarter owners are high: all three zero targets are
then negative outer anchors by the global sign and radial
theorems.

The proof retains every original zero witness and the same
outer potential at every occurrence of a state. It uses no
numerical feasibility premise, state mesh, Lean computation,
or CI result.
