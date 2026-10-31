# Whole-domain exclusion of the constant-corner two-share alternating C6

Date: October 26, 2026.

**Status: complete hand proof, accepted after root and separate
independent saved-source and original-scope review.** See
`REVIEW_C6_CONTACT_TYPE_CLOSURES_ROOT_2026_10_25.md` and
`REVIEW_SIX_CYCLE_CONSTANT_CHI_TWO_SHARE_2026_10_26.md`.
The proof covers the entire constant-corner
two-share orbit in Section 2 of
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md`. Its only finite
positivity calculation consists of six explicitly displayed rational
three-by-three matrices. There is no angular subdivision, force-ratio
subdivision, numerical premise, external coefficient packet, or sign
checker in the proof dependency. These six matrix checks are stated
openly; this source does not call the proof table-free.

Retain all nine actual squares, the selected positive certificate, the
original application means and their endpoints, the actual physical
circle masks, and the complete radius interval

\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]

**Theorem.** An all-unique, all-side-transmitter alternating C6 cannot
have constant corner bits and exactly two genuine shared interfaces.
The proof gives a contradiction already for its six actual component
squares. Consequently its three extra squares and every original
transmitter position remain arbitrary throughout.

This excludes one of the three full contact orbits in the cited domain
source. It does not by itself exclude either mixed-corner two-share
orbit, the one-share family, or the one-radial family. No shared ledger
or roadmap gate is changed by this manuscript. No Lean compilation or
CI was run.

## 1. The original constant-corner equations

The complete mean-preserving symmetry cover in
`SIX_CYCLE_TWO_SHARE_FULL_DOMAIN_AND_CORNER_BOUNDS.md` reduces this
orbit to

\[
       (\chi_0,\chi_1,\chi_2)=(1,1,1),
       \qquad S_0W_0\text{ and }S_1W_1\text{ genuinely shared}.
\tag{2}
\]

Cyclic relabeling puts the two shared loaded units at 0 and 1.
Reflection followed by reversal carries the all-zero constant pattern
to (2), including the actual means and all physical units.

Use the proper counterclockwise force triangle and the accepted strict
turn theorem. With cyclic indices,

\[
 f_i=\mu_i n_i,\quad \mu_i>0,\quad |n_i|=1,
 \quad F_i=f_{i-1}-f_i,\quad D_i=|F_i|,
\]
\[
 \pi/2<\theta_i\le3\pi/4,\qquad \sum_i\theta_i=2\pi.
\tag{3}
\]

The actual inner-side direction and actual port chord of loaded unit
\(i\) are \(u_i\) and \(\ell_i\), respectively. At the two
shares the original torque equations give

\[
 u_0=-Jn_0,\qquad
 \ell_0=1-\frac{\mu_2}{\mu_0}
                    (\sin\theta_0+\cos\theta_0),
\]
\[
 u_1=-Jn_1,\qquad
 \ell_1=1-\frac{\mu_0}{\mu_1}
                    (\sin\theta_1+\cos\theta_1),
 \qquad 0<\ell_0,\ell_1\le1.
\tag{4}
\]

The nonshared loaded unit has its actual two side vertices as ports,
so \(\ell_2=1\). Its actual support vector is

\[
                 g_2=f_1+JF_2,\qquad u_2=g_2/|g_2|.
\tag{5}
\]

Write \(h_i=\sin\theta_i-\cos\theta_i\). The mean-preserving
support and virial identities in the cited domain source are exactly

\[
 E_0=\mu_0+\mu_2h_0,\qquad
 E_1=\mu_1+\mu_0h_1,\qquad
 E_2=\sqrt{2\mu_1^2+\mu_2^2+2h_2\mu_1\mu_2},
\]
\[
 \sum_i(n_i+\ell_i u_i)=0,
 \qquad R\sum_iD_i=N:=\sum_i\mu_i+E_0+E_1+E_2.
\tag{6}
\]

In particular a genuine share with endpoint mean has not been changed
to a singleton. Equation (4), rather than a replacement chord of
length one, will be used in the closure calculation.

## 2. One projection of actual closure removes a whole angular region

Put \(\beta_i=\theta_i-\pi/2\). Thus

\[
 0<\beta_i\le\pi/4,\qquad \sum_i\beta_i=\pi/2.
\tag{7}
\]

For this calculation only, divide the force magnitudes by \(\mu_0\)
and write \((\mu_0,\mu_1,\mu_2)=(1,p,q)\), where \(p,q>0\).
Choose the coordinate axes so that

\[
 n_0=(1,0),\quad n_1=(-c,d),\quad n_2=(-a,-b),
\]
\[
 a=\sin\beta_0,\quad b=\cos\beta_0,\quad
 c=\sin\beta_1,\quad d=\cos\beta_1,
 \quad A=d-c\ge0.
\tag{8}
\]

Expansion of (5) gives

\[
       g_2=p\bigl(-(c+d),d-c\bigr)+q(-b,a).
\tag{9}
\]

Let \(\gamma=\pi/4-\beta_1\). The two vectors on the right
of (9) have directions \(\pi-\gamma\) and
\(\pi-\beta_0\). Since \(\beta_2\le\pi/4\), equation (7)
gives \(\gamma\le\beta_0\). A positive sum of these two
vectors has direction \(\pi-t\), with

\[
              \gamma\le t\le\beta_0.
\]

Write \(u_2=(-m,n)\). It follows that

\[
                         m=\cos t\ge\cos\beta_0=b.
\tag{10}
\]

The first coordinate of the actual closure equation in (6), using
\(u_0=(0,-1)\), \(u_1=(d,c)\), and the actual \(\ell_1\)
from (4), is

\[
 m=1-a-c+d\ell_1
   =1-a+A-\frac{Ad}{p}.
\tag{11}
\]

Combining (10)--(11) proves the whole-domain necessary inequality

\[
 A-(a+b-1)\ge\frac{Ad}{p}\ge0.
\tag{12}
\]

Only its weaker angular consequence will be needed for the radius
bound:

\[
 \boxed{\quad
 \cos\beta_1-\sin\beta_1
       \ge\sin\beta_0+\cos\beta_0-1.
 \quad}
\tag{13}
\]

Thus the proof retains the true means long enough to obtain an
angular restriction that the virial identity alone does not supply.

There is also a useful force-ratio consequence, although it is not
needed below:

\[
                         p\ge1+1/\sqrt2.
\tag{14}
\]

Indeed \(A=0\) would give \(\beta_1=\pi/4\); because
\(\beta_0>0\), this contradicts (12). Hence \(A>0\), and
the denominator \(H=1-a-b+A\) is positive. Put
\(r=1/\sqrt2\). Since
\(\beta_0\ge\pi/4-\beta_1\) and sine plus cosine is
increasing on \([0,\pi/4]\),

\[
 a+b\ge\sqrt2d.
\]

At this lower value the following difference factors exactly:

\[
 (1+r)(\sqrt2d-1)-A(1+r-d)
                     =(c+d-1)(r-c)\ge0.
\tag{15}
\]

Thus \(Ad\ge(1+r)H\), and (12) gives
\(p\ge Ad/H\ge1+r\). This proof uses no upper bound on a
force ratio or a nonphysical zero force.

## 3. A single triangular enlargement of the complete angle domain

Set \(x=\beta_0\), \(y=\beta_1\). Equation (13) implies

\[
             y+\frac38x\le\frac\pi4.
\tag{16}
\]

Here is an elementary proof over the entire interval. Define

\[
 y_0(x)=\pi/4-3x/8,
\quad T(x)=\cos y_0(x)-\sin y_0(x)
                          -\sin x-\cos x+1.
\]

For \(0\le x\le\pi/4\),

\[
 T''(x)=\sin x+\cos x
       -\frac9{64}(\cos y_0-\sin y_0)>0.
\tag{17}
\]

Also \(T(0)=0\), and

\[
 T(\pi/4)=\sqrt2\sin(3\pi/32)-\sqrt2+1<0.
\tag{18}
\]

For the last strict sign, \(\pi<22/7\) and the fifth-order
Taylor upper bound for sine give

\[
 \sin(3\pi/32)
 <\frac{33}{112}-\frac16\left(\frac{33}{112}\right)^3
                 +\frac1{120}\left(\frac{33}{112}\right)^5
 <\frac{41}{140}<1-\frac1{\sqrt2}.
\tag{19}
\]

The middle positive rational reserve is
\(1733430901/704936673280\). The last comparison follows from
\(\sqrt2<99/70\), whose positive squared reserve is
\(1/4900\). The sine polynomial is increasing on \([0,1]\),
and its Taylor remainder has the required upper sign there. One may
use the elementary positive integral
\(\int_0^1 t^4(1-t)^4/(1+t^2)\,dt=22/7-\pi\)
for the stated upper bound on \(\pi\).

Convexity and the two endpoint values imply \(T(x)\le0\).
Since cosine minus sine is strictly decreasing on \([0,\pi/4]\),
(13) then implies \(y\le y_0(x)\), proving (16).

Together with \(x+y\ge\pi/4\) from (7), this puts every
original angle triple in the single closed triangle with vertices

\[
 \begin{array}{c|ccc}
 &\theta_0&\theta_1&\theta_2\\ \hline
 A&\pi/2&3\pi/4&3\pi/4\\
 B&3\pi/4&\pi/2&3\pi/4\\
 C&3\pi/4&21\pi/32&19\pi/32.
 \end{array}
\tag{20}
\]

This is one enlargement of the original domain, not a split into
small angular cases. The enlarged boundary angles \(\pi/2\) will
be included in every estimate below.

## 4. Eliminate all positive force ratios by a homogeneous quadratic

Put \(K=79/40\). Now normalize the forces by
\(\mu_0+\mu_1+\mu_2=1\). Define

\[
 s_i=\sin(\theta_i/2),\qquad
 c_2=1-h_2/\sqrt2\ge0,
\]
\[
 C_0=2+h_1,\qquad C_1=2+\sqrt2,\qquad C_2=2+h_0.
\tag{21}
\]

For nonnegative \(a,b\) and \(s\in[0,1]\), the square-root
chord inequality gives

\[
 \sqrt{s^2(a+b)^2+(1-s^2)(a-b)^2}
 \ge s(a+b)+(1-s)\frac{(a-b)^2}{a+b}.
\tag{22}
\]

For \(a+b>0\), divide by \(a+b\) and apply concavity of the
square root to the chord from \(s^2\) to 1. The zero case follows
by continuity. Since every adjacent sum of normalized magnitudes is
at most one, (22) implies

\[
 D_i\ge s_i(\mu_{i-1}+\mu_i)
                  +(1-s_i)(\mu_{i-1}-\mu_i)^2.
\tag{23}
\]

The sole remaining square root in the numerator can be bounded while
keeping its force coupling. Write \(p=\mu_1\), \(q=\mu_2\).
Then

\[
 E_2^2=(\sqrt2p+q)^2-2(\sqrt2-h_2)pq.
\]

The tangent upper bound for the square root, followed by
\(\sqrt2p+q\le\sqrt2\), gives

\[
 E_2\le\sqrt2p+q-
       \frac{(\sqrt2-h_2)pq}{\sqrt2p+q}
 \le\sqrt2p+q-c_2pq.
\tag{24}
\]

All denominators here are positive. Consequently

\[
                       N\le\sum_i C_i\mu_i-c_2\mu_1\mu_2.
\tag{25}
\]

Let \(Q_i=K(s_i+s_{i+1})-C_i\). Combining (23) and (25),
and homogenizing the linear term using \(\sum_i\mu_i=1\),
gives

\[
 K\sum_iD_i-N\ge\mu^{\mathsf T}M\mu,
\tag{26}
\]

where the symmetric matrix \(M\) is exactly

\[
 M_{ii}=2K-C_i,
\]
\[
 M_{i-1,i}=\frac12\left[
 K\left(\sum_j s_j+3s_i-2\right)-C_{i-1}-C_i
                 +{\bf1}_{i=2}c_2\right].
\tag{27}
\]

For clarity, (26) is simply

\[
 (\sum_i\mu_i)(\sum_iQ_i\mu_i)
 +K\sum_i(1-s_i)(\mu_{i-1}-\mu_i)^2+c_2\mu_1\mu_2.
\]

Thus no force ratio is discretized, optimized numerically, or omitted.
It remains to prove positivity of (27) for the whole angle triangle.

## 5. A controlled quadratic Taylor minorant for every matrix entry

Write \(\delta_i=\theta_i-2\pi/3\), so \(\sum_i\delta_i=0\).
Throughout \(\pi/2\le\theta_i\le3\pi/4\), Taylor's theorem
with the global second-derivative bounds gives

\[
 s_i\ge \widehat s_i
   :=\frac{\sqrt3}{2}+\frac{\delta_i}{4}
                                  -\frac{37}{320}\delta_i^2,
\]
\[
 h_i\le \widehat h_i
   :=\frac{1+\sqrt3}{2}
     +\frac{\sqrt3-1}{2}\delta_i-\frac12\delta_i^2.
\tag{28}
\]

Indeed \(s''(\theta)=-\sin(\theta/2)/4\ge-37/160\):
\(\cos(\pi/8)<37/40\), which follows on squaring from
\(400\sqrt2<569\) and \(569^2-2\cdot400^2=3761>0\).
Also \(h''=-h\le-1\). These are Taylor remainder bounds on
the entire interval, valid on both sides of the expansion point.

Define \(\widehat C_0=2+\widehat h_1\),
\(\widehat C_1=2+\sqrt2\), and
\(\widehat C_2=2+\widehat h_0\). Define
\(\widehat M\) by (27), replacing \(s_i,h_i,C_i,c_2\)
with
\(\widehat s_i,\widehat h_i,\widehat C_i,
1-\widehat h_2/\sqrt2\), respectively. Every coefficient of
an \(s_i\) in (27) is positive, and every coefficient of an
\(h_i\) is negative. Therefore

\[
                  M\ge\widehat M\quad\hbox{entrywise}.
\tag{29}
\]

We use this only on the actual nonnegative force vector:
\(\mu^{\mathsf T}M\mu\ge
\mu^{\mathsf T}\widehat M\mu\). Entrywise comparison is
not asserted to be an ordering of quadratic forms on arbitrary
signed vectors.

## 6. Derivation of the six exact control matrices

The following gives every entry of the finite calculation explicitly.
There are no fitted coefficients. Let the three rational vectors be

\[
 z_A=(-1/6,1/12,1/12),\quad
 z_B=(1/12,-1/6,1/12),\quad
 z_C=(1/12,-1/96,-7/96).
\tag{30}
\]

These are precisely \(\delta/\pi\) at the three vertices in
(20). For any \(U,V\in\{A,B,C\}\), allowing \(U=V\), put

\[
 L_i^{UV}=\frac\pi2(z_{U,i}+z_{V,i}),\qquad
 T_i^{UV}=\pi^2z_{U,i}z_{V,i},
\]
\[
 s_i^{UV}=\frac{\sqrt3}{2}+\frac14L_i^{UV}
                                      -\frac{37}{320}T_i^{UV},
\]
\[
 h_i^{UV}=\frac{1+\sqrt3}{2}
             +\frac{\sqrt3-1}{2}L_i^{UV}-\frac12T_i^{UV}.
\tag{31}
\]

Set \(C^{UV}=(2+h_1^{UV},2+\sqrt2,2+h_0^{UV})\).
The six symmetric matrices \(B_{UV}\) are given entry by entry by

\[
 (B_{UV})_{ii}=2K-C_i^{UV},
\]
\[
 (B_{UV})_{i-1,i}=\frac12\left[
 K\left(\sum_j s_j^{UV}+3s_i^{UV}-2\right)
 -C_{i-1}^{UV}-C_i^{UV}
 +{\bf1}_{i=2}\left(1-\frac{\sqrt2}{2}h_2^{UV}\right)
 \right].
\tag{32}
\]

For barycentric coordinates \(\lambda_A,\lambda_B,\lambda_C\ge0\)
with sum one, direct expansion of the quadratic in (28) gives the
identity

\[
 \widehat M=
 \lambda_A^2B_{AA}+\lambda_B^2B_{BB}+\lambda_C^2B_{CC}
 +2\lambda_A\lambda_B B_{AB}
 +2\lambda_A\lambda_C B_{AC}
 +2\lambda_B\lambda_C B_{BC}.
\tag{33}
\]

The six coefficients are nonnegative and sum to one. Equations
(30)--(32) derive all six quadratic Bernstein controls directly;
there is no recursive subdivision.

### 6.1. Exact rational bounds for the constants

For the following small arithmetic calculation use only

\[
 \frac{141421}{100000}<\sqrt2<\frac{141422}{100000},
 \qquad
 \frac{173205}{100000}<\sqrt3<\frac{173206}{100000},
\]
\[
 \frac{314159}{100000}<\pi<\frac{314160}{100000}.
\tag{34}
\]

The positive lower and upper squared reserves for the square roots
are, respectively,

\[
 \begin{array}{c|cc}
 &\text{lower reserve}&\text{upper reserve}\\ \hline
 \sqrt2&100759/10^{10}&45521/2500000000\\
 \sqrt3&1119/400000000&79609/2500000000.
 \end{array}
\tag{35}
\]

Here is also a short rational verification of the stated interval
for \(\pi\). The tangent addition formula gives Machin's identity

\[
                 \pi=16\arctan(1/5)-4\arctan(1/239).
\]

Indeed \(\tan(4\arctan(1/5))=120/119\), and subtracting
\(\arctan(1/239)\) gives tangent one; the angle is in
\((0,\pi/2)\). Put

\[
 A_4=\frac15-\frac1{3\cdot5^3}
                    +\frac1{5\cdot5^5}-\frac1{7\cdot5^7},
 \qquad A_5=A_4+\frac1{9\cdot5^9}.
\]

The alternating arctangent series yields

\[
 16A_4-\frac4{239}<\pi
 <16A_5-4\left(\frac1{239}-\frac1{3\cdot239^3}\right).
\tag{36}
\]

The left expression exceeds the lower endpoint in (34) by
\(21011/12547500000\), and the upper endpoint exceeds the right
expression by \(24584570819/3359651941406250\). This proves
(34) without importing a decimal approximation of \(\pi\).

### 6.2. Six displayed rational lower matrices

The formulas (30)--(32) and the rational intervals (34) give,
entrywise, \(B_{UV}>N_{UV}/1000\), where

\[
 N_{AA}=\begin{pmatrix}
 522&-142&-606\\-142&535&0\\-606&0&912
 \end{pmatrix},\qquad
 N_{BB}=\begin{pmatrix}
 912&-599&0\\-599&535&-147\\0&-147&522
 \end{pmatrix},
\]
\[
 N_{CC}=\begin{pmatrix}
 596&-267&-78\\-267&535&-411\\-78&-411&522
 \end{pmatrix},\qquad
 N_{AB}=\begin{pmatrix}
 563&-271&-258\\-271&535&-56\\-258&-56&563
 \end{pmatrix},
\]
\[
 N_{AC}=\begin{pmatrix}
 537&-146&-270\\-146&535&-184\\-270&-184&563
 \end{pmatrix},\qquad
 N_{BC}=\begin{pmatrix}
 694&-394&-18\\-394&535&-231\\-18&-231&522
 \end{pmatrix}.
\tag{37}
\]

For completeness the exact entry verification can be performed with
ordinary rational interval arithmetic: add endpoints for sums, reverse
endpoints for negation, and use the minimum and maximum of the four
endpoint products for multiplication. Evaluate (31) in its displayed
order, and then (32). The least lower-endpoint reserve over the nine
entries of each matrix is as follows:

| Control | Minimum lower-endpoint reserve over \(N_{UV}/1000\) |
| --- | --- |
| \(AA\) | \(1188713761/2880000000000\) |
| \(BB\) | \(1188713761/2880000000000\) |
| \(CC\) | \(45726851003/368640000000000\) |
| \(AB\) | \(897083982283/3686400000000000\) |
| \(AC\) | \(20646394735267/98304000000000000\) |
| \(BC\) | \(18560102883341/294912000000000000\) |

All six reserves exceed \(1/20000\). Thus every comparison in (37)
has a positive rational margin; no floating-point sign is needed.
The formula for an individual entry illustrates the calculation. For
the \(00\) entry of \(B_{AA}\), (30)--(32) give exactly

\[
 \frac{39}{20}-\frac{1+\sqrt3}{2}
       -\frac{(\sqrt3-1)\pi}{24}+\frac{\pi^2}{288}.
\]

Insert the upper endpoints for the two subtracted terms and the
lower endpoint for the final positive square. Subtracting \(522/1000\)
gives precisely the first reserve in the table. The same formulas
give each of the other entries; the table records the smallest
reserve rather than omitting a comparison at an unstated sign.

### 6.3. Six positive weighted-row identities

Each matrix in (37) has nonpositive off-diagonal entries. The following
are exact integer matrix-vector products:

| \(N\) | Positive vector \(w\) | \(Nw\) |
| --- | --- | --- |
| \(N_{AA}\) | \((10,4,7)\) | \((410,720,324)\) |
| \(N_{BB}\) | \((7,10,4)\) | \((394,569,618)\) |
| \(N_{CC}\) | \((10,17,15)\) | \((251,260,63)\) |
| \(N_{AB}\) | \((1,1,1)\) | \((34,208,249)\) |
| \(N_{AC}\) | \((1,1,1)\) | \((121,205,109)\) |
| \(N_{BC}\) | \((2,3,2)\) | \((170,355,315)\) |

For any real vector \(v\), the following identity verifies positivity
without an eigenvalue calculation or determinant certificate:

\[
 v^{\mathsf T}Nv
 =\sum_i\frac{(Nw)_i}{w_i}v_i^2
   +\sum_{i<j}(-N_{ij})w_iw_j
               \left(\frac{v_i}{w_i}-\frac{v_j}{w_j}\right)^2.
\tag{38}
\]

Every summand on the right is nonnegative, and the displayed row
products give, for all six matrices,

\[
             v^{\mathsf T}\frac{N}{1000}v
                         \ge\frac{21}{5000}\sum_i v_i^2.
\tag{39}
\]

The smallest row ratio is \(63/(15\cdot1000)=21/5000\), in
the \(CC\) row. This is the entire finite positivity calculation.

## 7. Whole-domain force gap and the original physical contradiction

For the actual positive force vector, the entrywise bounds in (37),
the six identities (39), and the convex decomposition (33) imply

\[
 \mu^{\mathsf T}\widehat M\mu
 >\frac{21}{5000}\sum_i\mu_i^2
 \ge\frac7{5000},
\tag{40}
\]

where the last step uses \(\sum_i\mu_i=1\). Combine
(26), (29), and (40), and then remove the force normalization:

\[
 \boxed{\qquad
 \frac{79}{40}\sum_iD_i-N
       >\frac7{5000}\sum_i\mu_i>0.
 \qquad}
\tag{41}
\]

This inequality holds for every positive force triple and every angle
triple in the one closed triangle (20). In particular it holds for
every actual constant-corner two-share configuration by (13)--(20).
Substitute the original virial identity \(N=R\sum_iD_i\) from
(6). Since \(\sum_iD_i>0\), (41) gives \(R<79/40\),
contradicting (1).

The reflection and cyclic cover from Section 1 proves the same result
for every placement of the two shares and for both constant corner
bits. Every actual shared mean, including \(\ell_i=1\), was retained
in the closure input; no zero endpoint weight or transmitter slider
was deleted. The conclusion concerns the entire first orbit of the
three-orbit cover, with all force ratios and both radius endpoints.
The mixed-corner two-share orbits require their separate proofs before
the complete two-share family can be marked closed.
