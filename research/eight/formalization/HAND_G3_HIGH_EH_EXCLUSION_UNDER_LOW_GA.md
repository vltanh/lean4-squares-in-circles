# A low GA owner excludes every high EH owner globally

## 1. Statement and the original path

Assume the actual G0--G2 seven-cycle at
\[
q\le Q=\frac{9789}{2500},
\]
with its common real frame interval of length less than \(7/10\).
Then
\[
\boxed{
\text{an original GA axis in }\{0,1\}\text{ feasible}
\quad\Longrightarrow\quad
\text{every original EH axis belongs to }\{0,1\}.
}
\tag{1}
\]
This excludes an EH axis 2 or 3 even if it is tied with another
feasible original axis. There is no mismatch bound, tangent cut,
middle-frame order, or hypothesis on the other quarter owners.
The theorem is conditional on a low GA witness; the case of GA
axis 2 or 3 is a separate branch.

Work first on the fixed-witness G0 boundary cycle at Q. Suppose
GA has a retained axis 0 or 1 and EH a retained axis 2 or 3.
The generic quarter signs in Section 11 of
[the global DE theorem](HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md)
and the two-edge propagation in Section 9 of
[the global A-sign theorem](HAND_G3_GLOBAL_A_SIGN_UNDER_FORBIDDEN_B_OWNER.md)
give
\[
y_E=-b_E<0,\qquad y_H=b_H>0,\qquad
y_G=-b_G<0,\qquad y_A=b_A>0.
\tag{2}
\]
Thus even the E sign is supplied by the putative original owner.
The global zero-primary exclusion leaves HG only axes 0 and 2.

Put
\[
r=\theta_H-\theta_E,\qquad
v=\theta_G-\theta_H,\qquad
t=\theta_A-\theta_G,\qquad
\delta=r+v+t=\theta_A-\theta_E.
\tag{3}
\]
Every pair of these four original frames is separated by less
than \(7/10\). In particular,
\[
|r|,|v|,|t|,|r+v|,|v+t|,|\delta|<7/10.
\tag{4}
\]
With
\[
W(x)=\frac{1+\cos x+|\sin x|}{2},
\]
the relevant original projections are
\[
\begin{array}{c|l}
\text{owner}&\text{projection}\\ \hline
EH2&a_E\cos r+b_E\sin r-b_H\\
EH3&a_E+a_H\sin r-b_H\cos r\\
HG0&b_H+a_G\sin v+b_G\cos v\\
HG2&a_H\sin v+b_H\cos v+b_G\\
GA0&a_A\cos t+b_A\sin t-b_G\\
GA1&a_A+a_G\sin t-b_G\cos t.
\end{array}
\tag{5}
\]
Each retained projection is at least its corresponding W.
These are exactly the original quarter projections and the two
surviving zero projections; no favorable owner is assumed.

Choose the common unsigned G1 marker F once per vertex, with the
same choice on both incident edges at a chart junction. The
charged three-edge path is
\[
C_3=\pi+\delta-F_E-F_A.
\tag{6}
\]
Its two internal markers have canceled. We will prove
\[
\boxed{C_3+\frac9{50}h(|\delta|)>\frac{11}{4}},
\qquad h(x)=\frac{\sin x+\cos x-1}{2}.
\tag{7}
\]
Section 10 joins this to the four original return edges.

## 2. A common stress and the endpoint supports

Use throughout
\[
\lambda=\frac{13}{10},\quad \eta=\frac25,\quad
m=\frac{111}{100},\quad L=\frac{447}{800},\quad
R=\sqrt Q,\quad a_0=\sqrt{Q-\frac14}-\frac12.
\tag{8}
\]
The boundary geometry gives \(a>L\), \(0\le b<9/10\),
\(b\le a\), and the actual shifted-circle inequality
\[
(a+1/2)^2+(b+1/2)^2\le Q.
\tag{9}
\]
An outer state has equality in (9); a core state has
\(a\le7/12\), and \(b\le1/2\) on the core implies
\(a=7/12\). These are the unchanged bounds from Section 2 of
the global DE theorem and
[the center-norm note](HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md).

On every outer chart, including both choices at a junction,
\[
F_O\le\eta(a-a_0)+mb.
\tag{10}
\]
For completeness, the whole-chart bound
\(F_O\le(3/8)(a-a_0)+1.091b\) in
[the BT marker note](HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md)
also implies (10) directly.
The outer circle gives
\[
a_0-a=\frac{b(b+1)}{a+a_0+1}\le\frac35b,
\]
using \(a\ge b\), \(b<9/10\), and \(a_0>7/5\).
The new upper expression minus the old one is therefore at
least \((.019-.025\cdot.6)b=.004b\ge0\).
Circle support therefore gives
\[
F_O+\lambda a
\le T:=-\eta a_0+
R\sqrt{(\lambda+\eta)^2+m^2}
-\frac{\lambda+\eta+m}{2}
<T_*:=\frac{20467}{10000}.
\tag{11}
\]
Here \(a_0>141457/100000\). The two positive-squaring reserves
establishing (11) are
\[
\begin{aligned}
Q-\frac14-
 \left(\frac{141457}{100000}+\frac12\right)^2
 &=\frac{217151}{10^{10}},\\
\left(T_*+\frac{\lambda+\eta+m}{2}
              +\eta\frac{141457}{100000}\right)^2
 -Q\{(\lambda+\eta)^2+m^2\}
 &=\frac{8904}{244140625}.
\end{aligned}
\tag{12}
\]
For a core endpoint, the actual marker is
\[
F_C=7.506931(7/12-a)+1.077372b.
\]
Since \(a>L\), \(b\le a\le7/12\),
\[
F_C+\lambda a
<8(7/12-L)+(11/10+\lambda)\frac7{12}
=\frac{479}{300}<T_*.
\tag{13}
\]
Thus (11), with its strict upper bound \(T_*\), is available
at both endpoints regardless of radial kind.

Weight the three original inequalities (5) by the same
\(\lambda\). At zero errors their projections sum to
\(a_E+a_A\). If \(\Delta P_j(x)=P_j(x)-P_j(0)\), define
\[
I_j(x)=x+\lambda\{W(x)-1-\Delta P_j(x)\}.
\tag{14}
\]
The resulting exact dual lower bound is
\[
\begin{split}
C_3\ge{}&\pi+3\lambda
 -(F_E+\lambda a_E)-(F_A+\lambda a_A)\\
&+I_{EH}(r)+I_{HG}(v)+I_{GA}(t).
\end{split}
\tag{15}
\]
Without the error terms its common base exceeds
\[
B_*:=\frac{294819}{100000}=2.94819,
\tag{16}
\]
because \(\pi>3.14159\) and
\(3.14159+3\lambda-2T_*=B_*\).
The stated lower bound for pi follows, for example, from the
Machin estimate recorded in
[the BT marker note](HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md).
All subsequent reductions compare (15) as a scalar lower bound;
they do not assert the existence of a moved feasible packing.

## 3. Every rotated-quarter error can be removed

The owners EH2 and GA0 have the common rotated-primary form
\[
P(x)=a\cos x+b\sin x-b_0,
\tag{17}
\]
where \((a,b)\) is the endpoint E or A. Its retained feasibility
forces this endpoint to be outer. Indeed, on the core,
\[
P(x)\le\sqrt{a^2+b^2}\le\frac{7\sqrt2}{12}<1\le W(x).
\]
The internal coefficient \(-b_0\) is independent of x.

### 3.1 Nonnegative error

For \(x\ge0\), its exact error cost is
\[
I(x)=x+\lambda\{(a-1/2)(1-\cos x)
                            +(1/2-b)\sin x\}.
\]
Using \(a>L>1/2\), \(b<9/10\), \(\sin x\le x\),
\[
I(x)\ge\left(1-\frac25\lambda\right)x
=\frac{12}{25}x\ge\frac9{100}x.
\tag{18}
\]
The endpoint can then be supported by (11).

### 3.2 Negative error: retain the outer endpoint in its support

Write \(x=-z\), \(0\le z\le7/10\), and put
\[
\begin{aligned}
N(z)&=\sqrt{(\eta+\lambda\cos z)^2
                          +(m-\lambda\sin z)^2},\\
J(z)&=-z+\lambda(1/2+\cos z)
       +\frac{\eta+m}{2}+\eta a_0-RN(z).
\end{aligned}
\tag{19}
\]
The outer marker bound and its shifted-circle support give
\[
-(F+\lambda a)+I(-z)\ge J(z)-\lambda.
\tag{20}
\]
At zero, \(J(0)=\lambda-T\). We claim
\[
J'(z)>\frac9{100}\qquad(0\le z\le7/10).
\tag{21}
\]

Here is one whole-interval rational proof. Set
\[
\begin{aligned}
S(z)&=z-z^3/6+z^5/120-z^7/5040,&
U(z)&=z-z^3/6+z^5/120,\\
C(z)&=1-z^2/2+z^4/24-z^6/720,&
V(z)&=1-z^2/2+z^4/24.
\end{aligned}
\tag{22}
\]
Alternating Taylor inequalities on this interval give
\(S\le\sin z\le U\), \(C\le\cos z\le V\).
Define the explicit rational polynomials
\[
\begin{aligned}
K(z)&=\eta S(z)+mC(z),\\
N_+(z)&=\eta^2+m^2+\lambda^2
                         +2\lambda\{\eta V(z)-mS(z)\},\\
T_+(z)&=109/100+\lambda U(z),\\
H(z)&=Q\lambda^2K(z)^2-T_+(z)^2N_+(z).
\end{aligned}
\tag{23}
\]
The polynomial H has degree 17. Write its single centered
expansion as
\[
H(7/20+x)=\sum_{j=0}^{17}A_jx^j.
\]
Direct rational expansion of (23) gives the signs, in increasing
order of j,
\[
+,-,-,+,-,-,+,+,-,-,+,+,-,-,+,+,-,-,
\]
and the exact coefficient sum
\[
A_0-\sum_{j=1}^{17}|A_j|(7/20)^j
=\frac{26011751632517632558973980287499}
       {141557760000000000000000000000000}
>\frac{18}{100}>0.
\tag{24}
\]
This is a single bound on the entire interval, not evaluations
at a list of angles. In (23), \(K>0\),
\(N_+\ge N^2>0\), and \(T_+\ge109/100+\lambda\sin z>0\).
Positive squaring and (24) imply
\[
\frac{R\lambda(\eta\sin z+m\cos z)}{N(z)}
>\frac{109}{100}+\lambda\sin z.
\]
But differentiation of (19) gives
\[
J'(z)=-1-\lambda\sin z
       +\frac{R\lambda(\eta\sin z+m\cos z)}{N(z)}.
\]
This proves (21), and (20) yields
\[
-(F+\lambda a)+I(-z)>-T_*+\frac9{100}z.
\tag{25}
\]
Together with (18), every rotated-quarter error can therefore be
deleted from (15) after supporting its endpoint, with a gain at
least \(9|x|/100\).

## 4. A negative primary error has the same deletion bound

Consider GA1 with \(t=-z<0\). The EH3 case is the identical
calculation after local reflected reversal. If the original GA0
projection is also feasible, select that actual weak witness
and apply Section 3. Suppose therefore that GA1 is feasible
but GA0 is not.

For the actual intermediate G and endpoint A write
\[
K_G=a_G+\frac12,\qquad D_G=b_G+\frac12,\qquad
X=a_A+\frac12,\qquad Y=b_A+\frac12.
\]
The GA1 inequality gives
\[
X\ge X_*:=1+D_G\cos z+K_G\sin z.
\tag{26}
\]
The strict inequality \(P_1-P_0>0\) gives
\[
Y>Y_*-\tan(z/2)(X-X_*),\qquad
Y_*:=K_G\cos z-D_G\sin z>0.
\tag{27}
\]
The positivity follows from \(K_G\ge D_G\) and
\(\cos z>\sin z\) for \(z\le7/10\). Furthermore,
\[
X_*-\tan(z/2)Y_*=1+D_G+K_G\tan(z/2)>0.
\]
Thus the dot product of \((X_*,Y_*)\) with
\((X-X_*,Y-Y_*)\) is positive. Completing the squared
distance proves
\[
\begin{split}
Q\ge X^2+Y^2
&>X_*^2+Y_*^2\\
&=1+K_G^2+D_G^2
                  +2(D_G\cos z+K_G\sin z)\\
&\ge K_G^2+(D_G+1)^2.
\end{split}
\tag{28}
\]
In the last line, \(K_G\ge D_G\) and
\(\sin z+\cos z\ge1\) were used. This is the same
comparison-vector identity as Section 5 of the global A-sign
theorem, now without its extra lower bound on \(b_G\).

If G were outer, the middle line of (28), together with
\(K_G^2+D_G^2=Q\), would already be impossible. Thus G is
core. Equation (28) also implies \(D_G<1\), since otherwise
\(K_G\ge D_G\ge1\) would give its last expression at least 5.
Consequently \(b_G<1/2\), so the actual core condition gives
\[
a_G=\frac7{12},\qquad K_G=\frac{13}{12}.
\]
Equation (28) now sharpens this to
\[
D_G<\frac{82}{125},\qquad b_G<\frac{39}{250}.
\tag{29}
\]
The exact reserve for the first inequality is
\[
\left(\frac{13}{12}\right)^2+
\left(1+\frac{82}{125}\right)^2-Q
=\frac{781}{2250000}>0.
\]

There is also an actual angle bound. Since \(Y\ge1/2\),
\[
1+\frac12\cos z+\frac{13}{12}\sin z
\le X_*\le X\le\sqrt{Q-\frac14}<\frac{383}{200}.
\tag{30}
\]
The left side increases on \([0,7/10]\). At \(z=9/20\),
the lower Taylor polynomials (22) give
\[
1+\frac12C(9/20)+\frac{13}{12}S(9/20)-\frac{383}{200}
=\frac{18453844169}{2867200000000}>0.
\]
The last upper bound in (30) has squared reserve \(13/8000\).
Hence
\[
0<z<9/20.
\tag{31}
\]

For the retained GA1 projection the exact error cost is
\[
\begin{split}
I_{GA1}(-z)
&=-z+\lambda\{(a_G+1/2)\sin z
                         -(b_G+1/2)(1-\cos z)\}\\
&>-z+\lambda\left\{\frac{13}{12}\sin z
                     -\frac{82}{125}(1-\cos z)\right\}.
\end{split}
\tag{32}
\]
Subtract \(9z/100\) from the last expression and call it
\(k(z)\). It is concave, \(k(0)=0\), and its Taylor lower
bound at \(9/20\) is
\[
k(9/20)>
\frac{26648983251717}{716800000000000}
>\frac{3717}{100000}>0.
\tag{33}
\]
Concavity on \([0,9/20]\) proves
\[
I_{GA1}(-z)>\frac9{100}z.
\tag{34}
\]
For EH3 exchange the unsigned endpoint and intermediate roles
by reflected reversal; (26)--(34) then concern H in place of G.
Either the actual EH2 witness is feasible, or H is the forced
core state and the same strict deletion bound holds.

## 5. Deletions preserve the augmented charge

Apply Sections 3--4 to every rotated-quarter error and to every
negative primary-quarter error. The only remaining quarter
errors are
\[
r\ge0\text{ on EH3},\qquad t\ge0\text{ on GA1},
\tag{35}
\]
with a deleted quarter error represented by zero in the dual.
Each deletion has supplied at least \(9|x|/100\). The endpoint
support used for a rotated quarter in (25) replaces exactly its
own term \(-(F+\lambda a)+I\) in (15); it does not spend the
same endpoint support a second time.

On \([0,7/10]\), h is increasing, concave, and has Lipschitz
constant \(1/2\). Thus \((9/50)h(|x|)\) has Lipschitz
constant \(9/100\) on \([-7/10,7/10]\). Let \(\delta'\)
be the sum after deleting the quarter errors. Its possible
values are the original frame differences
\[
\theta_A-\theta_E,\quad\theta_A-\theta_H,\quad
\theta_G-\theta_E,\quad\theta_G-\theta_H,
\]
according to which endpoint errors were deleted. Therefore
\(|\delta'|<7/10\), as well as \(|\delta|<7/10\), and
\[
\frac9{50}\{h(|\delta'|)-h(|\delta|)\}
\le\frac9{100}\sum_{\text{deleted }x}|x|.
\tag{36}
\]
The deletion gains cover this entire change of the augmented
charge. We may henceforth estimate (15) with (35), both
endpoints supported by \(T_*\), and augmentation
\((9/50)h(|r+v+t|)\), where r and t are the remaining errors.
All sums of consecutive surviving errors used below are original
pairwise frame differences listed in (4).

## 6. Two continuous error costs

For \(0\le x\le7/10\), define
\[
\begin{aligned}
f(x)&=x+\lambda\sin x-2\lambda R\sin(x/2),\\
d(x)&=-x+\lambda\{(L+1/2)\sin x
                               -\tfrac12(1-\cos x)\}.
\end{aligned}
\tag{37}
\]
A positive primary-quarter error changes its projection by
\(a\sin x+b(1-\cos x)\). One actual shifted circle gives
\[
a\sin x+b(1-\cos x)
\le2R\sin(x/2)-\frac{\sin x+1-\cos x}{2}.
\tag{38}
\]
Substitution in (14) gives \(I\ge f(x)\).
A positive HG error changes its projection by
\(a\sin x-b(1-\cos x)\), which is at most the left side
of (38), so it has the same bound. A negative HG error
\(v=-x\) changes its projection by
\(-a\sin x-b(1-\cos x)\); using \(a>L\), \(b\ge0\)
gives \(I_{HG}(-x)\ge d(x)\).

Both functions are concave and vanish at zero. Indeed,
\[
\begin{aligned}
f''(x)&=\lambda\sin(x/2)\{R/2-2\cos(x/2)\}<0
                                      &&(x>0),\\
d''(x)&=-\lambda\{(L+1/2)\sin x+\tfrac12\cos x\}<0.
\end{aligned}
\tag{39}
\]
The first sign follows already from \(R<1979/1000\) and
\(\cos(x/2)>9/10\). Concavity and \(f(0)=0\) imply
\[
f(x_1)+\cdots+f(x_k)\ge f(x_1+\cdots+x_k)
\quad(x_i\ge0,\ \sum_i x_i\le7/10).
\tag{40}
\]

We record all endpoint arithmetic needed below. With (22) and
\(R<1979/1000\),
\[
\begin{aligned}
f(7/10)&>f_-:=-\frac{1306737704027}{5760000000000},\\
d(7/10)&>d_-:=\frac{1948692345061}{57600000000000}>0,\\
\frac9{50}h(7/10)&>h_-:=\frac{2945220061}{80000000000}.
\end{aligned}
\tag{41}
\]
For the first line use S at \(7/10\) and U at \(7/20\);
for the second and third use S and C at \(7/10\).
The exact reserves are
\[
\begin{aligned}
B_*+f_-+h_--\frac{11}{4}
 &=\frac{9378508073}{1152000000000}>.00814,\\
B_*+f_-+d_--\frac{11}{4}
 &=\frac{297059304791}{57600000000000}>.00515.
\end{aligned}
\tag{42}
\]
Every decimal here is an exact rational. Concavity and the
positive endpoint in (41) also prove \(d(x)\ge0\) throughout.

Two consequences will finish the proof. First,
\(f(x)+(9/50)h(x)\) is concave, so (16), (41)--(42) give
\[
B_*+f(x)+\frac9{50}h(x)>\frac{11}{4}
\quad(0\le x\le7/10).
\tag{43}
\]
Second, on the square \(0\le x,z\le7/10\), the function
\[
f(x)+d(z)+\frac9{50}h(|x-z|)
\tag{44}
\]
is jointly concave on each of the two intrinsic triangles
\(x\ge z\) and \(x\le z\). Its minimum is therefore at
one of the four square corners. Their values are
\[
0,\quad f(7/10)+\frac9{50}h(7/10),\quad
d(7/10)+\frac9{50}h(7/10),\quad f(7/10)+d(7/10).
\]
The two possibly negative corners are covered by (42), and
the other two are nonnegative. Hence
\[
B_*+f(x)+d(z)+\frac9{50}h(|x-z|)>\frac{11}{4}
\quad(0\le x,z\le7/10).
\tag{45}
\]
This is a whole-domain concavity argument; the diagonal split
is the exact sign split of the absolute value in (44).

## 7. A shared intermediate circle cancels two opposed errors

The only case not handled by independent uses of (37) is
\(r,t>0\) with \(v<0\). For HG0, retain HG0 and GA1
together. Write \(v=-z\), \(z,t\ge0\), and set
\(s=t-z\). The exact combined force on the same actual G,
without its common factor \(\lambda\), is
\[
F_G=(\sin t-\sin z,\ \cos z-\cos t).
\tag{46}
\]
At zero errors its force is zero, because the two nominal
\(b_G\) terms cancel. Therefore the exact combined cost is
\[
I_{HG0}(-z)+I_{GA1}(t)
=s+\lambda\{W(z)+W(t)-2-F_G\mathbin{\cdot}(a_G,b_G)\}.
\tag{47}
\]

### 7.1 Nonnegative combined error

If \(s\ge0\), put \(t=z+s\). Both components in (46)
are nonnegative, and
\[
|F_G|=2\sin(s/2).
\]
Use one shifted G circle in (47). It gives
\[
I_{HG0}(-z)+I_{GA1}(t)
\ge s+\lambda\{\cos z+\sin t-1\}
                          -2\lambda R\sin(s/2).
\tag{48}
\]
For fixed s, \(\cos z+\sin(z+s)\) increases on its
domain \(0\le z\le z+s\le7/10\): its derivative is
\(-\sin z+\cos(z+s)>0\), since \(\cos(7/10)>\sin(7/10)\).
Thus \(\cos z+\sin t\ge1+\sin s\), and
\[
I_{HG0}(-z)+I_{GA1}(t)\ge f(s).
\tag{49}
\]

### 7.2 Negative combined error

If \(s<0\), put \(w=z-t>0\). Both components in (46)
are negative. Consequently \(a_G>L\), \(b_G\ge0\) give
\[
F_G\mathbin{\cdot}(a_G,b_G)
\le L(\sin t-\sin z).
\]
With \(F(x)=\sin x+\cos x-1\), (47) is at least
\[
-w+\lambda\left\{\frac{F(t+w)+F(t)}2
                          +L(\sin(t+w)-\sin t)\right\}.
\tag{50}
\]
At \(t=0\), this expression equals \(d(w)\). For fixed
w its derivative with respect to t, after removal of the
positive factor \(\lambda\), is
\[
\frac{(1+2L)\cos(t+w)+(1-2L)\cos t
                    -\sin(t+w)-\sin t}{2}.
\]
Since \(t,t+w\le7/10\), \(1-2L<0\), and
\(\cos x>191/250\), \(\sin x<13/20\), this is bounded
below by the exact positive constant
\[
\frac{(1+2L)(191/250)+(1-2L)-13/10}{2}
=\frac{20027}{200000}>0.
\tag{51}
\]
Thus
\[
I_{HG0}(-z)+I_{GA1}(t)\ge d(w).
\tag{52}
\]

For HG2, the same paired estimate applies to EH3 and HG2.
To see every sign and error explicitly, reverse this local
four-vertex path and negate the signed tangents, exchanging
\(E\leftrightarrow A\), \(H\leftrightarrow G\).
The unsigned states are exchanged; EH3 and GA1 exchange;
HG2 becomes HG0; the errors become \((t,v,r)\).
Their total, the endpoint marker sum, and the charged path
are unchanged. This is the local reflected-reversal identity
for the original projections, not a new seven-cycle.
It justifies (49)--(52) for either retained zero owner.

## 8. Exhaustion of the remaining error signs

After Section 5, r and t satisfy (35).

If \(v\ge0\), all remaining errors are nonnegative and
\(r+v+t\le7/10\) by (4). Apply (37)--(40) to obtain
total error cost at least \(f(r+v+t)\). Equation (43)
proves the augmented bound (7).

Suppose \(v<0\) and at most one of r,t is positive. Let x
be that positive error, or zero if neither is positive,
and put \(z=-v\). Their cost is at least \(f(x)+d(z)\),
and their total is \(x-z\). Equation (45) proves (7).

Finally suppose \(v<0\), \(r,t>0\). Use the local
reflection in Section 7 if necessary to write the zero owner
as HG0, and put \(z=-v\), \(s=t-z\).
If \(s\ge0\), (49) and the remaining EH3 cost give
\[
I_{EH3}(r)+I_{HG0}(-z)+I_{GA1}(t)
\ge f(r)+f(s)\ge f(r+s).
\]
Here \(r+s=r+v+t\ge0\) and is at most \(7/10\).
Equation (43) applies. If \(s<0\), put \(w=-s\).
Equation (52) gives total cost at least \(f(r)+d(w)\),
with total error \(r-w\). Both \(r\) and w are at most
\(7/10\); in particular
\(w=|v+t|=|\theta_A-\theta_H|\) is an original frame
difference. Equation (45) applies.

This exhausts both original HG owners, both original high EH
owners, both original low GA owners, every sign of their
errors, and both radial kinds at all four states. Section 5
then restores the deleted errors and the original augmentation,
proving (7) for the retained original path.

## 9. Scope of the analytic estimates

The endpoint estimate (13) includes the core side/corner
junction. All outer marker bounds hold for either containing
chart at a junction. A negative primary witness was changed
to a rotated witness only after proving that actual original
rotated projection feasible; otherwise its actual intermediate
was retained and forced onto the core by (28).

The three common weights remain \(13/10\) throughout.
Section 7 combines two forces on the same actual center
before taking its circle support. Section 5 compares scalar
dual bounds and explicitly pays for the change in the return
augmentation. It neither assumes that a partial frame change
preserves packing nor applies a hypothetical circle in place
of the actual one.

## 10. Close the four-edge return and transfer to original centers

On each of the complementary original edges AB, BT, TD, DE,
the unchanged G1 inequality is
\[
\phi_j+\ell_j-\ell_{j+1}
>\Gamma+\frac9{50}h(|d_j|),\qquad
\Gamma=\frac{8833}{10000}.
\tag{53}
\]
The common frame interval has length less than \(7/10\).
The increasing concave function h, with \(h(0)=0\), gives
a metric \(h(|\theta_i-\theta_j|)\) on this interval.
Its triangle inequality along the actual four-edge return
from A to E gives
\[
\sum_{j\in\{AB,BT,TD,DE\}}h(|d_j|)\ge h(|\delta|).
\tag{54}
\]
This is the same original-frame return argument as Section 9
of the global DE theorem, now using four edges.

The common vertex markers cancel. Summing (7) and (53), then
using (54), would give
\[
2\pi>\frac{11}{4}+4\Gamma.
\]
This is impossible because
\[
\frac{11}{4}+4\frac{8833}{10000}-\frac{710}{113}
=\frac1{70625}>0,\qquad 2\pi<\frac{710}{113}.
\tag{55}
\]
The contradiction proves (1) on the boundary cycle.

For an original candidate at \(q\le Q\), retain the putative
high EH witness and the low GA witness before applying G0's
fixed-witness boundary reduction and radius expansion to Q.
Choose any feasible original witness on each other edge.
The reduction preserves all chosen weak SAT inequalities,
the real frames, and the signed center rays. Apply the global
sign implications to that boundary cycle, choose its common
G1 markers, and use Sections 1--8 and the original return path.
This contradicts the retained pair of owners. Thus the theorem
holds for original centers and for every original tie.

All bounds are analytic on complete intervals or intrinsic
concavity domains. The rational calculation (24), the Taylor
endpoint reserves, and the positive-squaring identities are
explicit finite arithmetic. A sampled minimum, state or angle
mesh, numerical decision oracle, Lean compilation, or CI result
is not a premise.
