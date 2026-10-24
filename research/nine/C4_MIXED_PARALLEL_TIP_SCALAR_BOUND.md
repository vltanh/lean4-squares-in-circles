# The full parallel-unique/radial bypass inequality has positive pressure

**Status: complete uniform analytic hand lemma; root and separate independent
full hand audits passed.** All variables below range over their entire
stated continuous domains. There is no parameter subdivision certificate
or sampled-angle premise.

Let
\[
 \begin{gathered}
 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\\
 c^2+d^2=1,\qquad c\ge d>0,\\
 p=Dc-\frac d2,\qquad Z=Dd+\frac c2,\\
 W=2-p,\qquad V=\sqrt{R^2-W^2}>0,\qquad
 \ell=1+Z-V.
 \end{gathered}
\tag{1}
\]
Assume
\[
 W>V,\qquad 0<\ell\le1,\qquad
 \rho=\frac{W-(W-V)/\ell}{V}\in(0,1],
 \quad a=\frac1{\sqrt{1+\rho^2}},\quad b=\rho a,
\tag{2}
\]
and the actual bypass inequality
\[
                         g:=a+b\ell-(bc-ad)-1\le0.
\tag{3}
\]

**Theorem.** Throughout this complete domain,
\[
 \boxed{\quad
 F:=R^2-V-W-\frac12\{a(V+W)+b(W-V)\}>0.
 \quad}
\tag{4}
\]
The proof also gives W-V<9/40 and rho>8/9. These are intermediate
inequalities inside the full pressure proof, not separate angle gates.

## 1. Two circle equations and their full parameter interval

Write
\[
 \Delta=W-V>0,\quad S=V+W=\sqrt{2R^2-\Delta^2},\quad
 r^2=D^2+\frac14.
\]
Then
\[
 \begin{gathered}
 V=\frac{S-\Delta}{2},\quad W=\frac{S+\Delta}{2},\quad
 Z=\sqrt{r^2-(2-W)^2},\qquad
 \ell=1+Z-V,\\
 V^2-Z^2=2D+5-4W,\qquad
 c=\frac{Dp+Z/2}{r^2},\quad
 d=\frac{DZ-p/2}{r^2}.
 \end{gathered}
\tag{5}
\]
The radius bounds give
\[
                  \frac{91}{100}<D<\frac{61}{60},\qquad
                  1<r^2<\left(\frac{23}{20}\right)^2.
\tag{6}
\]
At fixed R, the interval V>=Z is precisely the interval from
Delta=0 to the endpoint
\[
 W_* =\frac D2+\frac54,\qquad
 V_*=Z_*=
       \sqrt{\frac34D(D+1)-\frac5{16}}.
\tag{7}
\]
All square roots remain positive there, and p=2-W>0. In particular
\[
 V_*^2>\left(\frac{99}{100}\right)^2+\frac{439}{40000},
 \quad V>\frac{99}{100},\quad W<\frac{211}{120},
 \quad \Delta<1,\quad S>\frac52.
\tag{8}
\]
The first strict estimate follows by substituting D>91/100 in (7).
The last follows from S^2=2R^2-Delta^2 and (1).

At Delta=0, both V=R/sqrt(2) and Z increase with R. At R=R_0,
\[
 \frac{279}{200}<\frac{R_0}{\sqrt2}<\frac{559}{400},\qquad
 Z^2>\left(\frac{91}{100}\right)^2+\frac14
                         -\left(\frac{121}{200}\right)^2
       =\frac{28483}{40000}
       =\left(\frac{27}{32}\right)^2+\frac{103}{640000}.
\tag{9}
\]
Thus Z>27/32 there. The first two comparisons are direct squares.

The derivative identities used below are
\[
 \begin{gathered}
 V_\Delta=-W/S,\quad W_\Delta=V/S,\quad
 V_{\Delta\Delta}=W_{\Delta\Delta}=-R^2/S^3,\\
 Z_\Delta=pV/(SZ),\qquad
 Z_{\Delta\Delta}=-r^2V^2/(S^2Z^3)-pR^2/(S^3Z)<0.
 \end{gathered}
\tag{10}
\]
Consequently V+3Z is concave in Delta. Its minimum on the full
interval (7) is at an endpoint. At Delta=0, (9) gives
V+3Z>3141/800>19/5. At the other endpoint it equals 4V_*>396/100>19/5.
We have proved the useful uniform inequality
\[
                              V+3Z>\frac{19}{5}.
\tag{11}
\]

## 2. A strict derivative reserve on the entire domain

Set h=V-Z=1-ell. Thus 0<=h<1 in the domain (2). Equation (11) gives
\[
                             V>\frac{19}{20}+\frac34h.
\tag{12}
\]
Using (5), an exact rearrangement gives
\[
 \begin{split}
 4(V\ell^2-\Delta)
   &=V(8-6h+4h^2)-(2D+5+h^2)\\
   &>\frac{17}{30}+\frac3{10}h-\frac{17}{10}h^2+3h^3>0.
 \end{split}
\tag{13}
\]
The first strict estimate uses (6),(12); its quadratic coefficient
8-6h+4h^2 is positive. For the last sign, if h<=17/30, omit the
positive linear and cubic terms and bound the remaining expression
below by
\[
              \frac{17}{30}-\frac{17}{10}
                       \left(\frac{17}{30}\right)^2
                       =\frac{187}{9000}>0.
\]
If h>=17/30, the quadratic and cubic terms have nonnegative sum.
Thus
\[
                              \Delta<V\ell^2.
\tag{14}
\]

For later comparison, the remaining derivatives at fixed Delta are
\[
 \begin{gathered}
 V_R=W_R=R/S,\qquad D_R=R/(D+1),\\
 \ell_R=\frac{R}{SZ}
       \left(\frac{SD}{D+1}+p-Z\right)>0,\\
 d_R=\frac{cR}{Z}\left(\frac{c}{D+1}+\frac1S\right)>0,\qquad
 d_\Delta=\frac{cV}{SZ}>0.
 \end{gathered}
\tag{15}
\]
Indeed SD/(D+1)>45/38>23/20>Z by (6),(8). The last two identities
follow either from (5), or from p=D cos(theta)-sin(theta)/2,
Z=D sin(theta)+cos(theta)/2 with c=cos(theta), d=sin(theta).
On c>=d, c>2/3 and V>=Z, so
\[
 \frac{d_R}{V_R/V}
   =\frac{cV}{Z}\left(\frac{Sc}{D+1}+1\right)
   >\frac23\left(\frac{100}{121}+1\right)
   =\frac{442}{363}>1.
\tag{16}
\]

## 3. Geometry forces Delta below9/40

Let T(rho)=(sqrt(1+rho^2)-1)/rho. Its derivative is
1/[sqrt(1+rho^2)(sqrt(1+rho^2)+1)], which strictly decreases for
rho>0. Hence T is concave, and its tangent at rho=1 gives
\[
 T(\rho)\le\sqrt2-1-
                      \left(1-\frac1{\sqrt2}\right)(1-\rho).
\tag{17}
\]
Equation (3), divided by b, and 1/rho>=2-rho now imply
\[
 \ell\le c-d+\sqrt2-1
              -\left(d+1-\frac1{\sqrt2}\right)(1-\rho).
\tag{18}
\]
Moreover (2) gives exactly
\[
                    1-\rho=\frac{\Delta(1-\ell)}{V\ell}=:z.
\tag{19}
\]
Because sqrt(2)-1<5/12 and 1-1/sqrt(2)>7/24, (18) yields
\[
       G:=\ell-c+d-\frac5{12}+
                        \left(d+\frac7{24}\right)z<0.
\tag{20}
\]

We show that G strictly increases with each of R and Delta throughout
the comparison domain. For either parameter i, differentiation gives
\[
 \begin{split}
 G_i={}&\ell_i\left[1-
             \frac{(d+7/24)\Delta}{V\ell^2}\right]
       +d_i(1+d/c+z)\\
       &+(d+7/24)z
             \left(\frac{\Delta_i}{\Delta}-\frac{V_i}{V}\right).
 \end{split}
\tag{21}
\]
Here d+7/24<1 since d<=1/sqrt(2)<17/24. The first coefficient is
positive by (14). For i=Delta, every term is positive, by (10),(15)
and V_Delta<0. For i=R, the only negative term is dominated by
z d_R using (16). The remaining terms are strictly positive. Thus
\[
                               G_R>0,\qquad G_\Delta>0.
\tag{22}
\]

These comparisons do not leave the actual domain. In reducing R at
fixed Delta, V^2-Z^2 increases, since its R derivative is
2R/(D+1)-4R/S<0. The positive Z remains real, and ell stays positive
because ell_Delta>0 and ell(R_0,0)>4/9 as shown explicitly in
Section 4. The angle theta decreases by (15), so d<=c is preserved.
The parameter d remains positive: it is smallest at (R_0,0), where
the bounds in (9) give DZ>p/2. After reaching R_0, decreasing Delta
has the same properties. Hence
any hypothetical Delta>=9/40 can be compared to the single point
(R_0,9/40).

At that point S=sqrt(12401)/40 and
D=(sqrt(5841)-40)/40. The following strict rational bounds follow by
squaring these two radicals and then substituting into Z^2=r^2-p^2:
\[
 \begin{gathered}
 \frac{91066}{100000}<D<\frac{91067}{100000},\qquad
 \frac{127949}{100000}<V<\frac{127950}{100000},\\
 \frac{49550}{100000}<p<\frac{49551}{100000},\qquad
 \frac{91310}{100000}<Z<\frac{91313}{100000}.
 \end{gathered}
\tag{23}
\]
For explicit verification, the lower and upper D square margins are
8411/2500000000 and 348489/10000000000. The bounds
278399/100000<S<348/125 have square margins
246799/10000000000 and 31/1000000. After these substitutions the
lower and upper Z square margins are 39731/2000000000 and
3399/500000000. These are single exact endpoint comparisons, not
a cover of parameter boxes.

The formulas (5),(19),(23), by direct rational multiplication, give
\[
 \ell>\frac{63360}{100000},\quad
 c<\frac{84112}{100000},\quad
 d>\frac{54086}{100000},\quad
 z>\frac{10166}{100000}.
\tag{24}
\]
For the last bound one uses
ell<15841/25000, V<2559/2000 in (19). Therefore
\[
 \begin{split}
 G(R_0,9/40)>{}&
 \frac{63360-84112+54086}{100000}-\frac5{12}\\
 &+\left(\frac{54086}{100000}+\frac7{24}\right)
                    \frac{10166}{100000}
   =\frac{9809957}{7500000000}>0.
 \end{split}
\tag{25}
\]
Equations (20),(22),(25) exclude every Delta>=9/40. Thus
\[
                              0<\Delta<\frac9{40}.
\tag{26}
\]

## 4. The entire remaining interval forces rho>8/9

At R=R_0 and Delta=0, (9) gives
\[
        \ell=1+Z-V>
           1+\frac{27}{32}-\frac{559}{400}
           =\frac{357}{800}>\frac49.
\tag{27}
\]
For 0<=Delta<=9/40 at R_0, we have V>51/40 (use12401>111^2
at the right endpoint), S>5/2, r^2>1 and Z<1. From (10),
\[
 S^3Z^3\ell_{\Delta\Delta}
                   =R_0^2Z^2(Z-p)-r^2V^2S<0.
\tag{28}
\]
If Z-p<0 the sign is immediate. Otherwise the first term is <4,
whereas the second exceeds (51/40)^2(5/2)=13005/3200>4.
Thus ell is concave on this entire interval. Its right endpoint
from (24) satisfies ell>396/625>223/360. The chord joining the
weaker endpoint lower bounds in (27) and223/360 gives
\[
                 \ell(R_0,\Delta)>\frac{4+7\Delta}{9}.
\]
Equation (15) then gives the same strict lower bound for every R in
the domain. Combining it with V>51/40 yields
\[
 \begin{split}
 9\Delta(1-\ell)-V\ell
   &<5\Delta-7\Delta^2-\frac{17}{30}
                                     -\frac{119}{120}\Delta\\
   &=\frac{481}{120}\Delta-7\Delta^2-\frac{17}{30}
    \le-\frac{23}{1200}<0.
 \end{split}
\tag{29}
\]
The quadratic is increasing up to9/40, and the displayed last value
is its exact value there. By (19), equation (29) proves
\[
                                  \rho>\frac89.
\tag{30}
\]

## 5. The full pressure bound

The function (S+rho Delta)/sqrt(1+rho^2) decreases with rho here:
its derivative has numerator Delta-rho S<0, using (8),(26),(30).
Consequently
\[
                  aS+b\Delta<\frac{9S+8\Delta}{\sqrt{145}}.
\]
It follows that
\[
 F>\Phi(R,\Delta):=
 R^2-\left(1+\frac9{2\sqrt{145}}\right)
                \sqrt{2R^2-\Delta^2}
       -\frac4{\sqrt{145}}\Delta.
\tag{31}
\]
This lower bound increases with R and decreases with Delta on the
whole interval (26). Indeed its R derivative is
2R[1-(1+9/(2sqrt(145)))/S]>0. For its Delta derivative, use
1+9/(2sqrt(145))<11/8, S>5/2, Delta<9/40 and
4/sqrt(145)>8/25; the derivative is less than99/800-8/25<0.

Therefore its minimum is at (R_0,9/40). Using the direct square
comparisons S<348/125 and sqrt(145)>301/25 there gives
\[
 \begin{split}
 F&>\frac{6241}{1600}-\frac{348}{125}
       -\frac{9(348/125)+9/5}{2(301/25)}\\
  &=\frac{3233}{2408000}>0.
 \end{split}
\tag{32}
\]
This proves the entire analytic implication (4). Every parameter and
closed mean endpoint in (1)--(3) has been included. No numerical
optimizer, generated coefficient table, angle sampling, Lean compilation
or CI is a premise of the proof.
