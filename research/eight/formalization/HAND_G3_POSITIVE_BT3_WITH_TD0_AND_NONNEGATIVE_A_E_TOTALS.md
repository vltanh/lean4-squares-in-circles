# Positive BT3 with arbitrary TD0 and nonnegative A/E totals

## 1. Original scope

Use the actual high-GA G0--G2 boundary-neighbor cycle at
\[
 Q=9789/2500,\qquad h=7/10,
\]
with cyclic roles H,G,A,B,T,D,E. H,G,B,D are sorted outer
states with signed tangents respectively positive, negative,
negative, negative. E is nonpositive and can be outer or true
core; A and T have arbitrary signs and radial kinds. Retain
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=3,\quad TD=0,\quad
 DE\in\{2,3\},\quad EH\in\{0,1\}.                              \tag{1}
\]
All are actual weak witnesses. The actual real errors satisfy
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.                              \tag{2}
\]
No order of the real frames is assumed.

Let a and e be the nonnegative **selected signed primary
totals** at A and E, as in
[the nonnegative-A/E theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).
For one selected primary this is its actual nonnegative
error; for two it is their signed sum, and either individual
error may be negative. With no selected primary the total is
zero. Assume the actual BT3 error u is nonnegative. TD0 has
an arbitrary error.

**Theorem.** No such original cycle exists.

Put
\[
 R=\sqrt Q,\quad c_0=\sqrt{Q/2}-1/2,
 \quad a_0=\sqrt{Q-1/4}-1/2,\quad \eta=.293,
\]
\[
 \sigma=R\sqrt{1+\eta^2}-(1+\eta)/2,
 \quad f(u)=\cos u+\eta\sin u,
 \quad W(t)=\frac{1+\cos t+|\sin t|}{2}.
                                                               \tag{3}
\]
All terminating decimals below are exact rationals.

## 2. The actual positive-BT support identity

Choose positive weights k,l,m and give the seven actual
inequalities the weights
\[
                    (k,l,l,m,c,1,1),\qquad c=mf(u).              \tag{4}
\]
The actual T contribution in BT3 and TD0 is exactly
\[
 m\{a_T\sin u-y_T\cos u\}+cy_T
                         =m\sin u(a_T+\eta y_T)
                         \le m\sigma\sin u.                    \tag{5}
\]
The last bound uses the actual shifted circle
\((a_T+1/2)^2+(|y_T|+1/2)^2\le Q\). It is valid for
both signs and both radial kinds of T. No new owner, center,
or real frame is introduced.

The signed primary comparisons at A and E give their exact
lower charges
\[
                          lj(a)+j(e),                           \tag{6}
\]
where j is the sorted-circle support charge in the cited
nonnegative-A/E theorem. Its proved properties are
\[
 j(s)\le0,\qquad j(s)+j(t)\ge j(s+t),\qquad
 j''(s)\le-\tfrac12\cos s+.92\sin s.                             \tag{7}
\]
The piecewise support formula has matching first derivatives.
On \([0,1/6]\), replace .92 by .915.

Set
\[
                  \theta=a+u,\qquad\delta=a+u+e\le h.           \tag{8}
\]
After the comparisons (5)--(6), the ordinary angular arguments
have signed sum \(-\delta\) and variations
\[
                N=P+\delta,\qquad0\le P\le h-\delta.            \tag{9}
\]
This remains true when a selected A or E pair has opposite
signs: its removed positive variation is at least its signed
nonnegative total. Deleted arguments are virtual zeros only
inside the force expression.

There are four ordinary norm blocks with coefficient pairs
\[
                 H:(k,1),\quad G:(k,l),\quad
                 B:(l,m),\quad D:(1,c).                         \tag{10}
\]
Both HG owners yield the same scalar envelopes. The actual
TD0 error remains in D's full two-angle block.

For \(p\le q\), write
\[
 \begin{split}
 \overline S(p,q)&=R\sqrt{p^2+q^2}-(p+q)/2,\\
 V_{p,q}(t)&=q(\cos t-1)
       -R\{\sqrt{p^2+q^2-2pq\sin t}-\sqrt{p^2+q^2}\}.
 \end{split}                                                    \tag{11}
\]

## 3. The whole small-total interval

Let \(L=1/6\) and \(0\le\delta\le L\). Choose
\[
       l=1,\qquad k=.5866+.4956\delta,
       \qquad m=1.1642-.8874\delta.                              \tag{12}
\]
Here
\[
 .5866\le k\le.6692,
 \quad1.0163\le m\le c(u)\le1.1642,
                          \qquad0\le u\le\delta.                \tag{13}
\]
For the last bound use \(f(u)\le1+\eta\delta\): the
quadratic \((1.1642-.8874\delta)(1+\eta\delta)\)
decreases from 1.1642.

The complete two-angle D lemma and low-angle concentration in
[the sorted-D envelope](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md)
retain D's exact zero-angle support \((1+c)c_0\), while
using full circles at H,G,B. Their conclusion on (9) is that
the ordinary charge is at least
\[
                             V_{k,1}(\delta).                    \tag{14}
\]
This is where the actual sorting of D matters. The lemma
covers both D errors, all sign allocations and weak ties.
Its independent endpoint certificates are in
[the exact sorted-D endpoints](HAND_G3_POSITIVE_BT3_SORTED_D_ENDPOINT_CERTIFICATES.md).

Since l=1, (7) merges A/E into \(j(\delta-u)\). A necessary
nonpositive stress is therefore
\[
 \begin{split}
 F(u)={}&k+2+mW(u)+c(u)+2-m\sigma\sin u\\
 &-2\overline S(k,1)-\overline S(1,m)
       -(1+c(u))c_0+j(\delta-u)+V_{k,1}(\delta).                 \tag{15}
 \end{split}
\]
Keep \(\delta,k,m\) fixed while varying u in \([0,\delta]\).
The term \(c-(1+c)c_0\) has negative second derivative
\(-(1-c_0)c\). All other u-dependent terms give
\[
 F''(u)\le m\{-\tfrac12\cos u+.916\sin u\}
       -\tfrac12\cos(\delta-u)+.915\sin(\delta-u)<0.             \tag{16}
\]
For example, \(\cos u,\cos(\delta-u)\ge71/72\),
\(\sin u+\sin(\delta-u)\le\delta\), and (13) make
the right side less than \(-.8\). Thus only u=0 and u=δ
remain. Section 6 certifies both endpoints strictly positive
on this whole interval.

## 4. The two large-total families and concentration

Suppose \(\delta\ge L\), and put \(d=h-L=8/15\).
Use exactly the two weight families already certified in the
nonnegative-A/E theorem, renaming its base c to m.

For \(\theta\ge L\), put \(x=\theta-L\) and \(y=e\):
\[
                  x,y\ge0,\qquad x+y\le d,
\]
\[
 \begin{split}
 k&=.6692+.5218x-.5956x^2+.4216x^3+.28y,\\
 l&=1+.0175x-1.0932x^2+1.278x^3+.25y,\\
 m&=1.0163-.0209x-1.1486x^2+1.4069x^3+.25y.
 \end{split}                                                    \tag{17}
\]
For \(\theta\le L\le\delta\), put
\[
 x=L-\theta\in[0,L],\quad y=\delta-L\in[0,d],\quad e=x+y,
\]
\[
       k=.6692+.18x+.28y,
       \quad l=1+.25(x+y),\quad m=1.0163+.25(x+y).                \tag{18}
\]

The proved whole-domain weight bounds in Sections 4.1--4.2
of that theorem give, for every split \(0\le u\le\theta\),
\[
 \frac23<k<.85,\quad k<l<\frac32k,
 \quad .9<\frac ml<1.1,
 \quad k\le c(u)<1.2,\quad\frac{c(u)}l<\frac{23}{20}.           \tag{19}
\]
Every ordered pair in (10) has smaller-to-larger ratio above
2/3. Their q-coefficient ratio is below 6/5. To include both
m and c in this last assertion, if l≤1 use l>.88,
\(m/l<1.1\), \(c/l<1.15\); if l≥1, use l<1.2,
m<1.2 and c<1.2. These are precisely the balanced-envelope
hypotheses for the four ordinary full-circle blocks.

The established four-block concentration on (9) consequently
leaves only \(\min_{H,G,B,D}V_i(\delta)\). Moreover, the
proved D comparison in Section 8, equation (61), of the cited
nonnegative-A/E theorem gives
\[
         V_{\min(1,c),\max(1,c)}(\delta)\ge V_{k,1}(\delta).
                                                               \tag{20}
\]
Its hypotheses k≤c<1.2 and k≤1 are in (19). The D
alternative is redundant, and only H,G,B remain.

Define the full-circle baseline
\[
 \begin{split}
 B(u)={}&k+2l+mW(u)+c(u)+2-m\sigma\sin u\\
 &-\overline S(1,k)-\overline S(k,l)
       -\overline S(l,m)-\overline S(1,c(u)).
 \end{split}                                                    \tag{21}
\]
Feasibility would force
\[
             B(u)+lj(\theta-u)+j(e)
                         +\min_{i=H,G,B}V_i(\delta)\le0.         \tag{22}
\]

## 5. Exact split concavity at the large total

Fix θ,e and the weights k,l,m. Each of the three V terms
in (22) is independent of u. The c-dependent part, after its
circle half-shift is collected, is
\[
                  H(c)=\frac32c-R\sqrt{1+c^2}.
\]
It is concave and satisfies
\[
 H'(c)>-.021\quad(0<c\le1.2),
\quad (1.521)^2(1+1.2^2)-Q(1.2)^2
                         =158301/25000000>0.                    \tag{23}
\]
Since \(c''(u)=-c(u)\),
\[
                         (H\circ c)''\le.021c<.02415l.          \tag{24}
\]

Put a=θ−u. The other second derivatives are bounded above by
\[
 m\{-\tfrac12\cos u+.916\sin u\}
            +l\{-\tfrac12\cos a+.92\sin a\}.
\]
Using (19), \(a+u\le h\),
\(\cos a+\cos u\ge1+\cos h>1.7648\), and
\(\sin a+\sin u\le h\), this is less than
\[
        l\{-.45(1.7648)+1.012(.7)\}=-.08576l.
\]
Together with (24), every scalar in (22) has
\[
                            F_i''<-.06161l<0.                   \tag{25}
\]
The j transition has a continuous first derivative, so this
is global split concavity. It suffices to check u=0 and u=θ.

The u=0 endpoints are exactly the already positive A-endpoint
polynomials of the nonnegative-A/E theorem. Sections 7--8 below
certify the six new u=θ endpoints on the whole triangle and
rectangle.

## 6. Two small-total polynomial certificates

Use the rational upper constants
\[
 \overline R=1.978787508,\quad\overline a=1.414575672,
 \quad\overline\sigma=1.415477291,
 \quad\overline c=.899214066,
\]
whose positive-square bounds are already proved. Write
\[
                  J(t)=\frac{C_{10}(t)-1}{2}
                          +(1/2-\overline a)S_9(t).             \tag{26}
\]
On \([0,L]\), \(J\le j\) uses the actual tangent-zero
support formula.

Take native variable t=δ and the linear weights (12). The
nonradical lower parts for the two endpoints in (15) are
\[
 \begin{split}
 A_A={}&2k+11/2-\overline c+m(5/2-\overline c)+J(t),\\
 A_T={}&2k+11/2-\overline c\\
 &+m\{1+(3/2-\overline c)C_{10}(t)
       +(1/2+\eta(1-\overline c)-\overline\sigma)S_9(t)\}.
 \end{split}                                                    \tag{27}
\]
Add \(C_{10}(t)-1\) to each, and use squared norms
\[
       P_1=1+k^2-2kS_{11}(t),\quad
       P_2=1+k^2,\quad P_3=1+m^2.                               \tag{28}
\]
The masses defined below have respective rho constants
\[
              1.159353078,\quad1.159353078,\quad1.534718749.
                                                               \tag{29}
\]
For each P put \(P_0=P(0)\) and define the exact cubic
\[
 w=([P]_{\le3}-P_0)/P_0,\qquad
 r=\rho[1+w/2-w^2/8+w^3/16]_{\le3}.                             \tag{30}
\]
Every mass exceeds 1.10 on \([0,L]\). For either A in
(27), with its added cosine increment, let
\[
 N=2A\prod_{j=1}^3r_j
      -\overline R\sum_{j=1}^3(P_j+r_j^2)\prod_{q\ne j}r_q.
                                                               \tag{31}
\]
Then its endpoint stress is at least \(N/(2\prod r_j)\).
The exact coefficient bounds of Section 8 give

| Endpoint | Degree | Complete positivity certificate |
| --- | ---: | --- |
| A | 19 | N>.00122 on the whole interval |
| T | 20 | N'<-.026 and N(L)>.00468 |

Thus both small-total endpoints are strictly positive.

## 7. Six large-total polynomial certificates

Use native x,y and weights (17) or (18). In the triangle
\(\theta=L+x,e=y,\delta=\theta+e\); in the rectangle
\(\theta=L-x,e=x+y,\delta=L+y\). Set
\[
 C=m\{C_{12}(\theta)+\eta S_9(\theta)\},
\quad j_e^-=\begin{cases}
 J(e)-.002e^4,&\text{triangle},\\
 J(e)-.029e^4,&\text{rectangle}.
 \end{cases}                                                    \tag{32}
\]
These j bounds are the whole-domain support bounds already
proved in the nonnegative-A/E theorem. Start with
\[
 A=2k+3l+3+m\{1+2C_{10}(\theta)
       +(3\eta/2+1/2-\overline\sigma)S_9(\theta)\}+j_e^-         \tag{33}
\]
and
\[
        P_H=1+k^2,\quad P_G=k^2+l^2,
        \quad P_B=l^2+m^2,\quad P_D=1+C^2.                     \tag{34}
\]
For index H,G,B respectively, replace just its squared norm by
\[
        P_H-2kS_{11}(\delta),\quad
        P_G-2klS_{11}(\delta),\quad
        P_B-2lmS_{11}(\delta),                                 \tag{35}
\]
and add to A respectively
\[
                 v,\quad lv,\quad q_*v,
                 \qquad v=C_{10}(\delta)-1,                    \tag{36}
\]
where \(q_*=l+.15(d-x)\) on the triangle and \(q_*=m\)
on the rectangle. These dominate max(l,m), by the already
proved family bounds. As v≤0 this is the lower-bound direction.
The rotating coefficient occurs in D, while B has the fixed m.

Define four masses by (30), now using total-degree truncation
in x,y. Default rho constants in H,G,B,D order are
\[
          1.203257512,\quad1.203257512,
          \quad1.425785990,\quad1.451171531.
\]
At the one replaced norm in (35), use respectively
\[
                   1.107155480,\quad1.107155480,
                   \quad1.302177104.
\]
For the triangle G polynomial only, make the exact additional
changes
\[
                         r_G\leftarrow r_G-x^3/4,
             \qquad      r_D\leftarrow r_D+x^3/4.               \tag{37}
\]
No approximation property of any mass is required. Their
whole-domain coefficient lower bounds exceed .70 on the
triangle and .77 on the rectangle.

Define the four-mass numerator by the same formula (31), with
the index set H,G,B,D. The six degrees are 39 on the triangle
and 35 on the rectangle. The positive-mass inequality
\(\sqrt P\le(P+r^2)/(2r)\) makes each scalar at least
its numerator divided by twice the mass product.

On the triangle write the exact identity
\[
                         N(x,y)=N(x,0)+yH(x,y).                  \tag{38}
\]
The following whole-domain coefficient certificates apply:

| Index | Upper bound for H_y | Far-edge proof for H(x,d−x) |
| --- | ---: | --- |
| H | −.231 | whole-interval lower bound .041 |
| G | −.420 | whole-interval lower bound .116 |
| B | −.238 | derivative below −.583, right endpoint above .226 |

Thus every quotient H in (38) is positive. For the base
\(n(x)=N(x,0)\), the complete certificates are:

| Index | Base certificate on [0,d] |
| --- | --- |
| H | n(0)>.001786 and (n(x)−n(0))/x>.064 |
| G | both endpoint values exceed .001786; the chord quotient exceeds .085 |
| B | direct whole-interval coefficient lower bound .030 |

For G the chord quotient is
\[
 \frac{n(x)-n(0)-\{n(d)-n(0)\}x/d}{x(d-x)}.
\]
It is a polynomial by its vanishing numerator at both endpoints.
These facts prove all three triangle numerators positive.

On the rectangle write
\[
                         N(x,y)=N(0,y)+xH(x,y).                  \tag{39}
\]
The whole-rectangle lower bounds for H, in index order H,G,B,
are respectively .046, .136, .411. The base H polynomial
has direct whole-interval lower bound .00128. The base G and
B polynomials have the form \(n(0)+yq(y)\), with
\[
 \begin{array}{c|cc}
 &n(0)&q\text{ lower bound}\\\hline
 G&>.001786&>.070\\
 B&>.298&>1.99.
 \end{array}
\]
This proves all three rectangle numerators positive.

## 8. Explicit finite coefficient formulas and assembly

For univariate coefficient bounds use
\[
 a_{n0}=4^{-n}\binom{2n}{n},\quad
 a_{nj}=2\,4^{-n}\binom{2n}{n-j}\quad(1\le j\le n),
\]
zero otherwise. For \(P(t)=\sum p_nt^n\) on \([0,D]\),
\[
 b_j=\sum_np_nD^na_{nj},\qquad
                   b_0-\sum_{j>0}|b_j|\le P
                        \le b_0+\sum_{j>0}|b_j|.               \tag{40}
\]
For \(P(x,y)=\sum p_{ij}x^iy^j\), rectangle coefficients are
\[
                     b_{kl}=\sum_{ij}p_{ij}L^id^ja_{ik}a_{jl}.
\]
On the triangle substitute \(x=ds(1-t),y=dst\), to get
\[
 b_{kl}=\sum_{ij}p_{ij}d^{i+j}a_{i+j,k}
                     \sum_{r=0}^{i}(-1)^r\binom ir a_{j+r,l}.
                                                               \tag{41}
\]
The whole-domain bounds are again the constant coefficient
plus or minus the sum of the absolute values of every other
coefficient. These are the shifted Chebyshev identities and
\(|T_j|\le1\); each transform is applied to a whole domain.

All polynomials and masses have been given explicitly, and
(40)--(41) reproduce every rational outward bound in Sections
6--7. Quotients there mean exact polynomial division after
subtracting the indicated base or edge.

For δ≤L, the sorted-D envelope and split concavity reduce to
the two positive numerators of Section 6. For δ≥L, the
four-circle envelope and split concavity leave the previously
proved A endpoints and the six positive new endpoints of
Section 7. In every case the actual weighted demand minus
projection is strictly positive, contradicting feasibility.
This proves the theorem, including u=0 and all weak ties.

The proof permits arbitrary original TD0 error and opposite
individual signs within a selected A or E primary pair. It
does not assert a TD2 case with positive signed T total, a
negative A total, or a negative core-E total. No local transport,
new original witness, sampled minimum, state mesh, Lean
compilation, or CI is used.
