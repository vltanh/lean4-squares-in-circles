# A whole-axis threshold excludes the smaller tilted side returns

**Status: complete whole-domain hand implication; root author and separate independent full saved-source, direct-prerequisite, exact-polynomial and original-offset audits passed. This closes a geometric subfeature, not a whole roadmap gate.**

Work in the original negative large-left ABC frame of NEGATIVE_H_OWNED_LEFT_SINGLETON_SIDE_RADIAL_EXIT.md, with all nine physical units, true H4/A2/B2/C2, intact petal, every original force, mean and physical mask retained. Write

\[
P_A=(a-1,b-1),\quad T=(a-1,\beta),\quad
t=\beta-b+1\in(0,1],
\]
\[
n=(u,v),\quad j=Jn,\quad u^2+v^2=1,\quad
5/6<\rho=u/v\le1,
\]
\[
e=(-c,s),\quad f=(-s,-c),\quad 0<c<1/2,\quad
s=\sqrt{1-c^2},\quad B=T+[0,1]e+[0,1]f.
\]

Set
\[
E=su+cv,\quad F=sv-cu,\quad
n=Fe-Ef,\quad j=Ee+Ff.
\tag{1}
\]
The letter E without a subscript is a scalar; e is B's side vector. The whole-left normal-ratio theorem supplies the displayed \(\rho\), without changing the original normal.

**Algebraic theorem.** Throughout the entire enlarged rectangle
\(5/6\le\rho\le1,\ 0\le c\le1/2\), one has
\[
3E(F+c^2)>2(E^2+v-E).
\tag{2}
\]

**Physical consequence.** Suppose the remaining actual tilted unique C has its BC contact W opposite its circle corner, with sides
\[
p=d e+l f,\qquad q_{\rm edge}=-l e+d f,
\qquad d\ge l>0,\quad d^2+l^2=1.
\]
An actual C-owned HC return with C-to-H normal \(-p\), negative \(p\cdot n\), and \(l/d\le2/3\) is impossible. Every original C-side mean and endpoint is retained. The larger-ratio return remains a separate open obligation.

## 1. A single polynomial bound on the full rectangle

Put \(r=\rho\) in this section only, and \(N=\sqrt{1+r^2}\). Thus
\[
u=r/N,\quad v=1/N,\quad
E=(sr+c)/N,\quad F=(s-cr)/N.
\]

Let J denote the left side of (2) minus its right side. After using \(s^2=1-c^2\), its exact numerator is
\[
\begin{aligned}
N^2J={}&3r-2r^2+c^2(2r^2-6r-2)\\
 &+sc(3-4r-3r^2)
 +N\{(2+3c^2)(sr+c)-2\}.
\end{aligned}
\tag{3}
\]

The coefficient of s in (3) is strictly positive. Indeed
\(3-4r-3r^2\ge-4\), while
\(rN\ge5\sqrt{61}/36>1\). Hence this coefficient exceeds
\[
-4c+2+3c^2\ge3/4.
\]

Use the full-interval lower bound
\[
s\ge L(c):=1-\frac{c^2}{2}-\frac{c^4}{6}.
\tag{4}
\]
The exact identity
\(1-s-c^2/2=c^4/[2(1+s)^2]\), with \(s\ge\sqrt3/2>6/7\), proves (4); at c=0 it is an equality. Replacing s by L therefore lowers (3).

Put
\[
C=(2+3c^2)(rL+c)-2.
\]
On the whole rectangle \(C\ge-1/3\). To see this, \(L>0\),
\(L'=-c-(2/3)c^3\ge-7/12\), so
\[
C_c=6c(rL+c)+(2+3c^2)(1+rL')>0.
\]
At c=0, \(C=2r-2\ge-1/3\).

Write \(\sigma=1/\sqrt2\). The exact comparison
\[
N=\sigma(r+1)+\epsilon,\qquad
0\le\epsilon=\frac{(r-1)^2}{2\{N+\sigma(r+1)\}}
\le\frac{(r-1)^2}{5}
\tag{5}
\]
holds, and its upper comparison is strict unless r=1. Both terms in braces exceed 5/4. Also
\[
707/1000<\sigma<708/1000.
\]
Since \(C(r+1)\ge-2/3\), equations (5) and \(C\ge-1/3\) give the complete sign-independent estimate
\[
NC\ge\frac{707}{1000}(r+1)C
       -\frac{(r-1)^2}{15}-\frac1{1500}.
\tag{6}
\]

Consequently \(N^2J\ge P(r,c)\), where the single global polynomial is
\[
\begin{aligned}
P(r,c)={}&3r-2r^2+c^2(2r^2-6r-2)\\
 &+Lc(3-4r-3r^2)
 +\frac{707}{1000}(r+1)\{(2+3c^2)(rL+c)-2\}\\
 &-\frac{(r-1)^2}{15}-\frac1{1500}.
\end{aligned}
\tag{7}
\]

Here is an exact coefficient certificate over the entire rectangle. Set
\(x=6r-5,\ y=2c\), so \(0\le x,y\le1\), and define
\(B_{i,n}(z)=\binom ni z^i(1-z)^{n-i}\).
The polynomial identity is
\[
P((x+5)/6,y/2)=
 \sum_{i=0}^2\sum_{j=0}^6 b_{ij}B_{i,2}(x)B_{j,6}(y),
\tag{8}
\]
with all 21 exact coefficients below.

| i | j=0 | j=1 | j=2 | j=3 | j=4 | j=5 | j=6 |
|---|---|---|---|---|---|---|---|
| 0 | 36533/54000 | 74647/108000 | 140033/216000 | 5009189/8640000 | 26395841/51840000 | 4706939/10368000 | 5794309/13824000 |
| 1 | 847/1000 | 3883/4800 | 257377/360000 | 230491/384000 | 2826509/5760000 | 1401461/3456000 | 1613599/4608000 |
| 2 | 1499/1500 | 541/600 | 11267/15000 | 140819/240000 | 62887/144000 | 46357/144000 | 47683/192000 |

Every basis product in (8) is nonnegative, and their sum is one. Thus
\[
P(r,c)\ge47683/192000>0.
\tag{9}
\]
The identity (8) is an ordinary finite rational polynomial identity. It is not a sampled angle test, a pose mesh or a collection of additional gate domains. Equations (3)--(9) prove (2), including every endpoint of the enlarged comparison rectangle.

## 2. Physical non-overlap bounds the unchanged H offset

Return to the original H side coordinate \(r_H\in(0,1)\):
\[
H=P_A+[-1,0]n+[-(1-r_H),r_H]j.
\]
Define
\[
r_g=st/E.
\tag{10}
\]
The actual packing necessarily satisfies \(r_H\le r_g\).

For if \(r_H>r_g\), the actual front/top vertex \(U=P_A+r_Hj\) of H has B coordinates relative to T
\[
U-T=(-st+r_HE)e+(ct+r_HF)f.
\]
Its e-coordinate lies strictly between zero and one. Its f-coordinate is positive and strictly less than
\[
c+F=sv+c(1-u)
 \le\sqrt{v^2+(1-u)^2}=\sqrt{2-2u}<1,
\]
because the global normal bound gives \(u>5/\sqrt{61}>1/2\).
Thus U would be strictly inside the actual B. A vertex of one full-dimensional square inside the other square's interior forces overlapping interiors, contrary to physical non-overlap. This proves (10) for the original pose. No comparison square is installed in the packing.

## 3. The actual back/top side return violates that bound

The unchanged B-side application is
\[
W=T+f+\theta e,\qquad
\theta=\mathsf Bc/Y,\quad
\mathsf B=sX+cY,\quad X=a-1-c>0,\quad Y=\beta+s>0.
\]
Hence
\[
\theta>c^2.
\tag{11}
\]
These are the actual B2 mean and circle coordinates from the side-radial source, not a chosen point on the side.

Put \(N_0=tv-E\). The exact H-axis displacements are
\[
\begin{aligned}
(W-P_A)\cdot n&=N_0+\theta F,\\
(W-P_A)\cdot j&=tu+F+\theta E
              =r_g-FN_0/E+\theta E.
\end{aligned}
\tag{12}
\]
The second equality uses \(uE+vF=s\).

For the actual C-owned \(-p\) return, retain its original application
\[
Q=W+\lambda q_{\rm edge},\qquad0\le\lambda\le1.
\]
Let
\[
N_p=dF-lE<0,\qquad J_p=dE+lF>0.
\]
The H-to-C normal p has negative n-component and positive j-component. Therefore its unchanged H application is the back/top vertex:
\[
(Q-P_A)\cdot n=-1,\qquad
(Q-P_A)\cdot j=r_H.
\tag{13}
\]
The first equation, together with (12), says
\[
\lambda J_p=1+N_0+\theta F.
\]
Substituting this into the second equation gives the exact identity
\[
EJ_p(r_H-r_g)
 =dE(F+\theta)-l(E^2+N_0).
\tag{14}
\]

By t<=1, (2) and (11),
\[
E(F+\theta)>\frac23(E^2+N_0).
\tag{15}
\]
If \(E^2+N_0\le0\), the right side of (14) is immediately positive. If \(E^2+N_0>0\), the hypothesis \(l/d\le2/3\) and (15) again make it strictly positive. Since E and \(J_p\) are positive, (14) forces \(r_H>r_g\), contradicting Section 2.

This exhausts every original mean of the stated return family, including endpoints. No extracted normal, physical circle mask, positive force or offset is changed. The proof assumes no degree-two equation at H or any larger junction. It does not exclude the remaining larger-ratio return or any whole upper-left, diamond or alternating-C6 family. No roadmap gate is closed by this source alone. No Lean compilation or CI is used.

