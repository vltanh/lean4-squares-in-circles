# No side channel of the all-unique alternating C6 is shared at both ends

Date: October 25, 2026.

**Status: complete hand derivation and exact reconstruction; independent
root full-source, geometry, global algebra and whole-certificate review
passed on October 25, 2026. See
REVIEW_SIX_CYCLE_DOUBLE_SHARED_CHANNEL_2026_10_25.md.** This excludes
one entire physical contact type. No existing C6 gate is closed or
subdivided, and no new gate ID is introduced.

**Current scalar proof:** Section2 of
`SIX_CYCLE_DOUBLE_SHARED_SLOPE_REDUCTION.md` supplies the analytic
torque bound, and `SIX_CYCLE_DOUBLE_SHARED_CIRCLE_SLOPE_TABLE_FREE.md`
supplies the analytic circle comparison. Independent complete review
passed in `REVIEW_C6_DOUBLE_SHARED_TABLE_FREE_2026_10_25.md`.
Both the old209-sign packet and its49-sign successor are superseded;
the complete scalar proof now has no coefficient certificate.
Sections1--4 below retain the physical derivation; Section5 is historical.

Retain the original alternating six-cycle, its three positively loaded
physical-unique-circle-corner units, its three true unloaded
degree-two side-normal transmitters, all original forces and application
means, and all three additional physical packing squares. Work throughout

\[
79/40\le R\le\sqrt{1105}/16.
\]

Use the accepted complete strict-turn and original-mean normal form in
SIX_CYCLE_UNIQUE_STRICT_TURN_AND_SHARED_NORMAL_FORM.md. The proper
loaded concurrences form the original counterclockwise triangle;
every turn satisfies \(\pi/2<\theta_i\le3\pi/4\). The two actual
applications on each loaded body are distinct points of one inner
side, at least one is a vertex, and at most one interface at that
body is genuinely shared.

**Theorem.** No actual side transmitter can have a positive-length
shared interface with both of its loaded neighbors.

The proof allows every original transverse position of all three
transmitters. It neither moves a transmitter nor replaces a shared
application mean by a vertex. The final contradiction is an exact
whole-domain torque sign, not a completion estimate or a sampled
configuration.

## 1. A doubly shared channel fixes the two endpoint frames

Suppose a transmitter W is shared with its two loaded neighbors B,C.
Rotate the actual channel so its outward side points upward. The
channel and endpoint half-plane theorem in
SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md, Section 5, gives positive
height h, the original application displacement of length one,
negative/positive horizontal endpoint-center signs, and nonnegative
vertical endpoint-center coordinates.

Both genuine shared interfaces make B and C parallel to W. Physical
uniqueness of their circle corners therefore fixes their actual
coordinates as

\[
\begin{gathered}
z_B=(-a,b),\quad z_C=(c,d),\qquad a,b,c,d>1/2,\\
B=[-a,1-a]\times[b-1,b],\qquad
C=[c-1,c]\times[d-1,d],\\
P_{BW}=(1-a,h),\quad P_{WC}=(c-1,h),\\
a+c=3,\qquad a^2+b^2=c^2+d^2=R^2.
\end{gathered}                                                    \tag{1}
\]

The vertical centers cannot be zero, because that would give two
physical circle corners. The horizontal center signs select the
left far corner of B and right far corner of C. Both original shared
means in (1), including their possible endpoint values, remain.

Let T be the third loaded square. At B,C, their other interface
cannot be shared, by the accepted at-most-one-share conclusion.
Its side transmitter owns its actual normal, so its singleton
application is a loaded vertex. The same-side application cover and
the actual positive circle-force vertical component force the other
ports to be

\[
p_B=(1-a,b-1),\qquad p_C=(c-1,d-1).
\]

More explicitly, the B-to-W force points right. The true B2 equation
and \((z_B)_y=b>0\) force the other outward B normal to have negative
vertical component. Its acute angle with the first outward normal
follows from \(\theta_B>\pi/2\); thus its horizontal component is
positive, selecting exactly the displayed bottom-right B vertex.
The reflected argument applies at C.

Write these original directions toward T as

\[
n_B=(\cos\alpha,-\sin\alpha),\qquad
n_C=(-\cos\beta,-\sin\beta).
\]

Their complete angular domain is

\[
\pi/4\le\alpha,\beta<\pi/2,\qquad
\pi/2<\Sigma:=\alpha+\beta\le3\pi/4.                \tag{2}
\]

Indeed \(\theta_B=\pi-\alpha\), \(\theta_C=\pi-\beta\),
and the remaining turn is \(\theta_T=\Sigma\). The weak
\(\pi/4\) endpoints are retained: unlike a diagonal transmitter,
a genuine shared side may have its original mean at a side endpoint.

The actual T applications, with both side-transmitter reserves exactly
one, are

\[
P=p_B+n_B,\qquad Q=p_C+n_C.                        \tag{3}
\]

## 2. The third load also has exactly one genuine shared interface

The two points P,Q are distinct points of one inner side of T, with
at least one a vertex, by the accepted strict-turn normal form.
Let \(Q-P=(\Delta_x,\Delta_y)\).
Because P minimizes \(n_B\) on T and Q minimizes \(n_C\), their
original support inequalities give

\[
-\cot\beta\,\Delta_x\le\Delta_y
                         \le\cot\alpha\,\Delta_x.
\]

Both cotangents are positive. A negative \(\Delta_x\) is impossible;
zero would force P=Q. Thus \(\Delta_x>0\). The side direction from
P toward Q has angle \(\phi\) satisfying

\[
\beta-\pi/2\le\phi\le\pi/2-\alpha,\qquad
|\phi|\le\pi/4.
\]

The square lies on the lower side of this directed inner side: its
inward normal must have nonnegative scalar products with both
\(n_B,n_C\). The opposite, upward-pointing choice cannot satisfy
both inequalities. In particular the side direction has
\(\cos\phi\ge1/\sqrt2\).

On the actual angular domain,

\[
\cos\alpha+\cos\beta>1/\sqrt2.                    \tag{4}
\]

For a complete verification put \(m=\Sigma/2\) and
\(e=(\alpha-\beta)/2\). Then \(|e|\le m-\pi/4\), and

\[
2\cos m\cos e\ge
2\cos m\cos(m-\pi/4)
=\cos(\Sigma-\pi/4)+1/\sqrt2\ge1/\sqrt2.
\]

Equality would require \(\Sigma=3\pi/4\) and one of
\(\alpha,\beta\) equal to \(\pi/2\), excluded by (2).

Using \(a+c=3\) in (3), we obtain

\[
0<\Delta_x=1-\cos\alpha-\cos\beta<1-1/\sqrt2.
\]

Consequently the actual side chord has length

\[
0<|Q-P|=\Delta_x/\cos\phi<\sqrt2-1<1.             \tag{5}
\]

It cannot have two vertex endpoints. Exactly one original application
is in the strict relative interior of T's side. Its normal is a
T side axis and is also a side axis of its side transmitter.
Their physical intersection is therefore a genuine positive-length
shared side. The other interface is a singleton, since two shared
interfaces at T would violate the strict-turn normal form.

Reflect across the vertical axis (x -> -x) and interchange B,C if needed so that Q is the
shared application. Put

\[
\begin{gathered}
u=\cos\beta,\quad v=\sin\beta,\quad
C_0=\cos\Sigma,\quad S_0=\sin\Sigma,\\
e=(v,-u),\quad f=(-u,-v),\\
\ell=\frac{1-\cos\alpha-u}{v}\in(0,\sqrt2-1).
\end{gathered}                                                    \tag{6}
\]

Here f points into T and its side points from P to Q along e.
These are the original axes fixed by the actual shared interface.
The orthonormal (e,f) coordinate chart reverses orientation but keeps
the original circle origin.

## 3. Equal circle radii determine the exact original T coordinates

The directions into T from B and C have (e,f) coordinates
\((S_0,-C_0)\) and \((0,1)\). Their positive force sum has both
coordinates positive, since \(S_0>0\) and \(C_0<0\).
T's actual unique circle corner is therefore \(z_T=(A,B_0)\),
with \(A,B_0>1/2\), and its unchanged points are

\[
T=[A-1,A]\times[B_0-1,B_0],\quad
P=(A-1,B_0-1),\quad Q=(A-1+\ell,B_0-1).
\]

Define

\[
\begin{array}{ll}
p=1+u+v+S_0,&q_1=1+v-u-C_0,\\
r_1=1+u-v-\ell,&s_1=2+u+v.
\end{array}
\]

Directly from (3), the two other actual circle corners are

\[
z_B=(A-p,B_0-q_1),\qquad
z_C=(A-r_1,B_0-s_1).                              \tag{7}
\]

For example the global differences are
\(z_B-P=(-1-\cos\alpha,1+\sin\alpha)\) and
\(z_C-Q=(1+u,1+v)\); taking their scalar products with e,f gives
(7) exactly. All three circle corners are physical originals.

The two equal-circle equations are

\[
pA+q_1B_0=(p^2+q_1^2)/2,\qquad
r_1A+s_1B_0=(r_1^2+s_1^2)/2.
\]

On the actual domain, \(p\ge2+1/\sqrt2\), \(s_1\ge3\),
\(1\le q_1\le2+1/\sqrt2\), and \(r_1\le1\), so

\[
\Delta:=ps_1-q_1r_1\ge4+\sqrt2>0.
\]

Hence, with no omitted denominator or root choice,

\[
\begin{split}
A&=\frac{s_1(p^2+q_1^2)-q_1(r_1^2+s_1^2)}{2\Delta},\\
B_0&=\frac{p(r_1^2+s_1^2)-r_1(p^2+q_1^2)}{2\Delta}.
\end{split}                                                     \tag{8}
\]

## 4. The true T2 equations require one normalized torque to vanish

Let \(m_B,m_C,\kappa>0\) be the original two pair magnitudes and the
circle scale of T. Its force equation gives

\[
m_B=\kappa A/S_0,\qquad
m_C=\kappa(B_0+A C_0/S_0).
\]

Its actual origin torque, with the original P,Q, is

\[
m_B[-C_0(A-1)-S_0(B_0-1)]
                     +m_C(A-1+\ell)=0.
\]

Reversal of the coordinate orientation reverses every determinant
and preserves this zero equation. Substitution and multiplication
by the positive \(S_0\) give

\[
F:=S_0[A-(1-\ell)B_0]+\ell C_0A=0.                \tag{9}
\]

The next section proves \(F<0\) throughout the complete actual
angular domain. It does not assume equal magnitudes or any chosen
shared-side mean.

## 5. Historical alternative: the original 209-sign polynomial proof

Enlarge the actual angles to the single closed triangle

\[
\alpha,\beta\ge\pi/4,\qquad \alpha+\beta\le3\pi/4.
\]

Let \(k=\sqrt2-1\), \(x,y\in[0,1]\), and set

\[
t=kx,\quad H_0=1+k^2x,\quad j=k(1-x)y,\qquad
\alpha=\pi/4+2\arctan t,\quad
\beta=\pi/4+2\arctan(j/H_0).
\]

For each alpha this is exactly the full allowed beta interval,
since \((k-t)/(1+kt)=k(1-x)/H_0\). The endpoint x=1
collapses all y to the allowed \((\pi/2,\pi/4)\).
Thus no angular subdivision or excluded edge is used.

Here are all polynomial definitions, over \(\mathbb Q(\sqrt2)\):

\[
\begin{gathered}
D_a=1+t^2,\quad D_w=H_0^2+j^2,\\
c_a=(1-2t-t^2)/\sqrt2,\quad
s_a=(1+2t-t^2)/\sqrt2,\\
U=(H_0^2-j^2-2H_0j)/\sqrt2,\quad
V=(H_0^2-j^2+2H_0j)/\sqrt2,\\
S=s_aU+c_aV,\quad C=c_aU-s_aV,\\
E_\ell=(D_a-c_a)D_w-D_aU,\quad T_0=D_aD_wV,\\
P=T_0+D_aV(U+V)+VS,\\
Q=T_0+D_aV(V-U)-VC,\\
T=T_0+D_aV(U-V)-D_wE_\ell,\\
W=2T_0+D_aV(U+V),\\
D=PW-QT,\\
\mathcal A=W(P^2+Q^2)-Q(T^2+W^2),\\
\mathcal B=P(T^2+W^2)-T(P^2+Q^2),\\
\mathcal N=S[D_aV(\mathcal A-\mathcal B)+E_\ell\mathcal B]
                           +E_\ell C\mathcal A .
\end{gathered}                                                   \tag{10}
\]

Polynomial T and W in (10) are numerator names only, not physical
bodies. The exact substitutions are

\[
\begin{gathered}
\cos\alpha=c_a/D_a,\quad
\sin\alpha=s_a/D_a,\quad u=U/D_w,\quad v=V/D_w,\\
S_0=S/(D_aD_w),\quad C_0=C/(D_aD_w),\quad
\ell=E_\ell/(D_aV),\\
(p,q_1,r_1,s_1)=(P,Q,T,W)/T_0,\quad
\Delta=D/T_0^2,\\
A=\mathcal A/(2T_0D),\qquad B_0=\mathcal B/(2T_0D).
\end{gathered}
\]

The factors \(D_a,D_w,V\) are positive on the whole rectangle;
in particular \(V=vD_w\) and \(v\ge1/\sqrt2\).
For every actual configuration, \(D=\Delta T_0^2>0\).

The exact polynomial division

\[
G=-\mathcal N/(D_aD_w^2V)
\]

has zero remainder. Its degree is (18,10), and the complete
cleared identity is

\[
\boxed{\quad G=-2D_a^2VD\,F.\quad}                 \tag{11}
\]

The accompanying standard-library checker independently rebuilds
all definitions (10), the zero remainder, the three unit-trigonometric
polynomial identities, (11), and the full coefficient identity below.
The JSON records every exact power coefficient and every Bernstein
coefficient as a rational pair \(r+s\sqrt2\).

For \(0\le i\le18\), \(0\le j\le10\), define exactly

\[
b_{ij}=
\sum_{\substack{k\le i\\l\le j}}
[x^ky^l]G\,\frac{\binom ik}{\binom{18}k}
                   \frac{\binom jl}{\binom{10}l}.
\]

Then the complete inverse identity is

\[
G(x,y)=\sum_{i=0}^{18}\sum_{j=0}^{10}
b_{ij}\binom{18}i x^i(1-x)^{18-i}
        \binom{10}j y^j(1-y)^{10-j}.              \tag{12}
\]

The following integers are exact lower bounds for \(10b_{ij}\).
Each was checked using exact rational arithmetic and the sign rule
for \(r+s\sqrt2\); no decimal approximation is a proof input.

| i | j=0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 56 | 53 | 49 | 45 | 42 | 41 | 43 | 50 | 62 | 81 | 105 |
| 1 | 54 | 51 | 47 | 44 | 41 | 41 | 44 | 51 | 63 | 81 | 104 |
| 2 | 52 | 49 | 46 | 42 | 41 | 41 | 44 | 52 | 64 | 81 | 103 |
| 3 | 49 | 47 | 44 | 41 | 40 | 41 | 45 | 53 | 65 | 82 | 103 |
| 4 | 47 | 44 | 42 | 40 | 40 | 41 | 46 | 54 | 66 | 82 | 103 |
| 5 | 44 | 41 | 40 | 39 | 39 | 42 | 47 | 56 | 67 | 83 | 103 |
| 6 | 40 | 39 | 38 | 37 | 39 | 42 | 48 | 57 | 69 | 85 | 104 |
| 7 | 37 | 36 | 36 | 36 | 39 | 43 | 50 | 59 | 71 | 86 | 104 |
| 8 | 34 | 33 | 34 | 36 | 39 | 44 | 51 | 61 | 73 | 87 | 105 |
| 9 | 31 | 31 | 33 | 36 | 40 | 46 | 53 | 63 | 75 | 89 | 105 |
| 10 | 28 | 30 | 32 | 36 | 41 | 47 | 55 | 65 | 77 | 90 | 106 |
| 11 | 26 | 29 | 32 | 37 | 43 | 50 | 58 | 68 | 79 | 92 | 106 |
| 12 | 26 | 29 | 34 | 39 | 46 | 53 | 61 | 71 | 82 | 94 | 107 |
| 13 | 27 | 32 | 37 | 43 | 49 | 57 | 65 | 74 | 84 | 95 | 107 |
| 14 | 31 | 36 | 42 | 48 | 55 | 62 | 70 | 78 | 87 | 96 | 107 |
| 15 | 39 | 44 | 50 | 55 | 62 | 68 | 75 | 82 | 90 | 97 | 106 |
| 16 | 51 | 56 | 61 | 66 | 71 | 76 | 81 | 87 | 92 | 98 | 104 |
| 17 | 70 | 73 | 76 | 80 | 83 | 86 | 89 | 92 | 95 | 98 | 101 |
| 18 | 98 | 98 | 98 | 98 | 98 | 98 | 98 | 98 | 98 | 98 | 98 |

All 209 coefficients exceed \(5/2\). The nonnegative basis terms
in (12) sum to one on the entire closed rectangle, so \(G>5/2\)
there. Equation (11) and its actual positive normalization imply
\(F<0\), contradicting the original torque equation (9).

The exact reproducible artifacts are
SIX_CYCLE_DOUBLE_SHARED_CHANNEL_CHECK.py and
SIX_CYCLE_DOUBLE_SHARED_CHANNEL_CERTIFICATE.json. The checker verifies
the full reverse Bernstein expansion, all exact coefficient bounds,
and the complete numerator-factor identity, not merely selected
values of a polynomial.

## 6. Whole physical scope and the remaining normal form

Every actual doubly shared channel forces the complete chart above.
The derivation retains both endpoint mean intervals, every original
force magnitude, the third loaded square's complete initial owner
cover, and all actual transverse transmitter positions. Its
contradiction precedes any completion-square allocation. Thus the
entire doubly shared channel type is excluded with all three extras
still present.

Consequently, in the remaining all-unique/shared alternating C6:

- each loaded square is incident to at most one genuine share, by
  the accepted strict-turn theorem;
- each transmitter is incident to at most one genuine share, by
  the present theorem;
- if there are three genuine shares, they form one of the two
  cyclic matchings between the three loads and three transmitters.
  Equivalently all three shares are incoming, or all three are
  outgoing in the common cycle orientation; their corner choices
  are respectively all \(\chi_i=0\) or all \(\chi_i=1\).

The last combinatorial conclusion follows because three distinct
load marks and three distinct transmitter marks exhaust both sides
of the alternating six-cycle. Its two perfect matchings are the
two cyclic choices. It does not replace the original chord lengths
or means by singleton values.

The full one-, two- and three-share completion problem remains
open until a complete additional exit is proved. No capacity claim,
new gate, Lean compilation, CI or post-extraction normal change is
made here.

The subsequent complete theorem
SIX_CYCLE_THREE_SHARED_MATCHING_EXCLUSION.md excludes both of the
three-share perfect matchings identified above, using their true
mean-preserving force value and one whole-angle inequality. Its
independent review is REVIEW_SIX_CYCLE_THREE_SHARED_MATCHING_2026_10_25.md.
The exact live residue is therefore one or two genuine shares, with
all original means, forces, sliders and extras still retained.


