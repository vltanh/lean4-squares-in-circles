# A shoulder-owned outward endpoint normal retains the full upward transfer

November 1, 2026 America/Chicago / November 2 UTC. Complete hand
derivation of another physical owner branch. No mathematical program,
numerical search, Lean, Lake, or CI.

Put
\[
 Q=\frac{1105}{256},\quad r=\sqrt Q,\quad
 a=46,\quad b=\frac{27}{2},\quad k=\frac{207}{16},\quad
 \mu=k/b=23/24,\quad T=211/4,\quad\kappa=r-11/8,
 \quad\rho=91/60.
\]
Write H_S(v) for a centered unit square's support halfwidth and
h_S=H_S(e_x)=H_S(e_y).

## 1. Statement and physical owner premises

Let an actual horizontal four-chain M0<_xM1<_xM2<_xM3 and two
physical outsiders A,B be interior-disjoint in the centered disk of
radius R_0<=r. Write M=M0 and assume x_A<=-29/60.
Suppose the physical M-to-A separator is
\[
 n=(-t,s),\quad 0\le t\le s,\quad t^2+s^2=1,
 \quad n\cdot(c_A-c_M)\ge H_M(n)+H_A(n),               \tag{1}
\]
and n is parallel to a physical side axis of **A**, the shoulder.
Thus this is an outward, upward, nearvertical normal in the left-side
coordinates. No actual vertical projection comparison is assumed.

Suppose A toward B has a true right-and-upward separator (1,z),
where z>=0. Define
\[
 E_B(z)=H_B((1,z))+(1+z)h_B-(1+z)\ge0,
\]
\[
 D_A=(1+\mu)h_A+H_A((-1,\mu))-(1+\mu)\ge0,
\]
\[
 \Psi_A(z)=H_A((1,z))-h_A+z(h_A-\kappa)+D_A.
\]
Then every upward slope is covered:
\[
\begin{aligned}
 a(-x_M-h_M)+b(1-x_B-h_B)
 \le T-bE_B(z)-b\Psi_A(z)-bz(r-h_B-y_B)
                              -\frac{259}{8000}t.      \tag{2}
\end{aligned}
\]
The disk-support step is strict if R_0<r; the bound is strict if
t>0. In addition, the shoulder reserve satisfies, for every z>0,
\[
 \Psi_A(z)>\frac1{10}\min(z,1),\qquad
                         \Psi_A(z)>(21/10-r)z.         \tag{3}
\]
Consequently (2) can replace an ordinary upward transfer in the
all-upward or mixed-sign paired terminal. Horizontal reflection
supplies the right-side statement. Downward transfers with this
shoulder-owned endpoint normal are not asserted by this theorem.

## 2. Physical confinement forces t<5/9

The actual-four bounds give
\[
 h_M<8/15,\quad g_M=1/(4h_M)>15/32,\quad
 -\rho<x_M<-89/60,\quad |y_M|\le1/8.
\]
The outsider strip and side-column premise imply
\[
             2/5<d:=x_A-x_M<31/30.                   \tag{4}
\]
Also y_A<rho, so y_A-y_M<197/120.

Because A owns n, H_A(n)=1/2. The aligned inset in M gives
H_M(n)>=g_M(t+s). Substituting in (1), we obtain the necessary
inequality
\[
                  \frac{563}{480}s-\frac{139}{160}t>\frac12.
                                                               \tag{5}
\]
If t>=5/9, then s<=sqrt(56)/9<5/6, and the left side of (5)
would be less than
\[
          \frac{563}{480}\frac56-\frac{139}{160}\frac59
                             =\frac{95}{192}<\frac12.
\]
This contradiction proves t<5/9. In particular s>4/5.

## 3. A complete near-aligned main-square support bound

Let alpha>=beta>=0 be M's absolute side-axis components. The
main bound h_M<8/15 gives
\[
 \beta<1/14,\quad\alpha>27/28,\quad\beta/\alpha<2/27.
                                                               \tag{6}
\]
Write h=(alpha+beta)/2, j=(alpha-beta)/2. We prove
\[
 P_M:=a h_M+H_M(ae_x+kn)+kH_M(n)\ge k+as.              \tag{7}
\]
Both relative frame chiralities are needed; no common orientation
of M and A is assumed.

For the chirality with vertices (h,-j),(j,h),(-h,j),(-j,-h), use
the vertex (j,h) as a support witness for ae_x+kn=(a-kt,ks).
If beta<=t, the n-support is th+sj, giving
\[
                      P_M\ge(a+ks)\alpha+kt\beta.
\]
As a function of beta on [0,t] this is concave. Its endpoint values
are a+ks and as+k, respectively, so its minimum is at least as+k.
This algebraic comparison is valid even when the endpoint beta=t
lies outside M's narrower allowed orientation interval.

If beta>=t, the n-support instead is sh-tj, and
\[
 P_M\ge[a+k(s-t)]\alpha+k(s+t)\beta.
\]
Its derivative in beta on [t,1/14] is greater than
\[
                 k-\frac2{27}(a+k)=\frac{3703}{432}>0.
\]
Its minimum is therefore the beta=t value as+k.

For the other chirality, use the vertex (h,j) for ae_x+kn.
Here H_M(n)=sh+tj, so
\[
                 P_M\ge(a+ks)\alpha+(a-kt)\beta.
\]
This expression increases on [0,1/14], since its derivative is
at least a-k-2(a+k)/27>0. Its minimum a+ks is at least as+k.
These cases prove (7), including zero tilts and all support ties.

## 4. The physical cap retains the shoulder's actual orientation reserve

Because A owns n=(-t,s), its support penalty in the physical cap is
exactly
\[
 P_A:=b h_A+H_A(be_x-kn)+kH_A(n)=k+b(t+s).              \tag{8}
\]
Its reference vertical orientation reserve is also exact:
\[
                      D_A=(1+\mu)(s-1)+t.              \tag{9}
\]
Indeed h_A=(s+t)/2, j_A=(s-t)/2, and the outward-left-up vertex
gives H_A((-1,mu))=h_A+mu j_A, since s>=t and mu<1.

For the same physical support reduction as in the established
two-square weighted cap, put
\[
 A(t)=\sqrt{a^2+k^2-2ak t},
 \quad B(t)=\sqrt{b^2+k^2+2bk t},\quad K(t)=r(A(t)+B(t)).
\]
Then
\[
 a(-x_M-h_M)+b(-x_A-h_A)\le K(t)-P_M-P_A.              \tag{10}
\]
If R_0<r the support-radius step is strict. At zero,
\[
 K(0)=T+(a+b+2k),\qquad K'(0)=-k/2.
\]

### 4.1. A short exact curvature table

Direct differentiation gives
\[
       -K''(t)=r k^2\left(\frac{a^2}{A(t)^3}+
                                      \frac{b^2}{B(t)^3}\right).
\]
On 0<=t<=5/9 the following rational table proves -K''>27/2:

| t interval | Upper A | Upper B | Lower a²/A³ | Lower b²/B³ |
|---|---:|---:|---:|---:|
| [0,1/8] | 48 | 20 | 19/1000 | 22/1000 |
| [1/8,1/4] | 47 | 21 | 1/50 | 39/2000 |
| [1/4,3/8] | 45 | 22 | 23/1000 | 17/1000 |
| [3/8,5/9] | 43 | 24 | 53/2000 | 13/1000 |

A decreases and B increases. The exact squared values at the four
left endpoints for A are
\[
          (584545,546457,508369,470281)/256,
\]
and at the four right endpoints for B are
\[
          (100683,111861,123039,139185)/256.
\]
These prove the displayed integer upper bounds. The lower-column
checks are elementary cross-products; for the two smallest row sums,
the relevant comparisons are
\[
 2116\cdot50>47^3,\quad729\cdot2000>39\cdot4\cdot21^3,
\]
\[
 2116\cdot2000>53\cdot43^3,\quad729\cdot1000>13\cdot4\cdot24^3.
\]
Every row sum exceeds 79/2000. Finally r>33/16 and k²>167 give
\[
 -K''>\frac{5511}{16}\frac{79}{2000}
                  =\frac{435369}{32000}>\frac{27}{2}.
\]
Integration from zero therefore gives
\[
                K(t)\le K(0)-(k/2)t-(27/4)t^2.         \tag{11}
\]

### 4.2. The remaining scalar reserve is strictly positive

Insert (7)--(9),(11) in (10). The cap reserve beyond bD_A is at least
\[
             J(t)=(k/2)t+(27/4)t^2-(a-k)(1-s).          \tag{12}
\]
For t>0 put u=t/(1+s). Since t<5/9 and s>4/5,
u<25/81<31/100, and t=2u/(1+u²). Consequently
\[
 \frac{J(t)}t=\frac{207}{32}
       -\left(\frac{529}{16}-\frac{27}{2(1+u^2)}\right)u.
\]
The positive fraction satisfies
\[
 \frac{27}{2(1+u^2)}>
                 \frac{135000}{10961}>\frac{123}{10},
\]
the final cross-product difference being 1797. Therefore
\[
 \frac{J(t)}t>
        \frac{207}{32}-\frac{1661}{80}\frac{31}{100}
                           =\frac{259}{8000}>0.
\]
At t=0, J=0. We have proved
\[
 a(-x_M-h_M)+b(-x_A-h_A)
                 \le T-bD_A-(259/8000)t,              \tag{13}
\]
with strictness for t>0 or R_0<r.

## 5. The shoulder lies wholly above 3/8

This whole-square bound is required by the upward transfer, and is
proved here from the physical endpoint pair. It is not inferred
from center-height order.

The strengthened endpoint budget gives
\[
 y_M+h_M\ge3/8+(87/50)(h_M-1/2).
\]
With the main components alpha,beta from Section 3,
\[
 h_M-1/2> (53/110)\beta\quad(\beta>0),
\]
and hence y_M+h_M>=3/8+(4611/5500)beta, with the evident
weak interpretation at beta=0. Let tau=t/s and j_A=(s-t)/2.

For M's first chirality, if beta>=t, its exact n-support is
sh_M-tj_M. Equation (1) gives
\[
 y_A-h_A\ge y_M+h_M+\tau(d-j_M-j_A).
\]
Here j_M+j_A<=1 and d>2/5. Also t<=beta<1/14 implies
s>27/28. Thus the possible loss is less than
(3/5)(28/27)beta=(28/45)beta, while the endpoint reserve is
(4611/5500)beta. Their difference is
\[
                    4611/5500-28/45=10699/49500>0.
\]

If beta<=t, M's exact support is th_M+sj_M, and (1) gives instead
\[
 y_A-h_A\ge y_M+j_M+\tau(h_M+d-j_A).
\]
The first term is at least 3/8-(889/5500)beta, while
h_M+d-j_A>2/5 and tau>=t>=beta. The net reserve is therefore
at least (1311/5500)beta. If beta=0 and t>0 the last term is
strictly positive directly.

For M's other chirality H_M(n)=sh_M+tj_M, so (1) gives
\[
 y_A-h_A\ge y_M+h_M+\tau(d+j_M-j_A).
\]
Here j_M>25/56, d>2/5 and j_A<=1/2, making the parentheses
strictly positive. At t=0 equation (1) is a vertical comparison and
the same conclusion follows directly. All cases prove
\[
                              y_A-h_A\ge3/8.           \tag{14}
\]

## 6. Finish the upward transfer and its two all-slope reserves

Let d'=x_B-x_A and ell=r-h_B-y_B>=0. From (14),
y_B-y_A<=1+kappa-h_A-h_B-ell. Use this in the physical
A,B separator, retain E_B(z), and rearrange to obtain
\[
 1-d'-h_B+h_A\le D_A-\Psi_A(z)-E_B(z)-z\ell.
\]
Adding b times this inequality to (13) proves precisely (2).

The first bound in (3) is the already-proved universal 81/100 shoulder
reserve. The second also holds for every slope here. For 0<z<=1,
that reserve is at least (81/100-kappa)z>(21/10-r)z. For z>=1,
an outward-quadrant vertex gives
\[
                  \Psi_A(z)\ge D_A+z(s-\kappa).
\]
Since s>4/5>29/40 and kappa+(21/10-r)=29/40, this is strictly
greater than (21/10-r)z. Thus both paired-proof reserves survive
on the entire slope range, without a central-band slope bound.

## 7. Scope of the additional owner class

The upward side of a paired shoulder terminal may now use a
shoulder-owned, outward, nearvertical separator from its outer main,
provided its side-column premise holds. The central normal's owner
and upward slope remain arbitrary. At Q, a nonvertical endpoint
normal or a positive upward slope makes the paired conclusion strict.

The theorem has not treated a shoulder-owned inward endpoint normal,
a nearly horizontal endpoint normal, or a downward transfer based on
the outward shoulder-owned normal. Those remain separate physical
domains. No unrestricted A.2 or global equality claim is made.
