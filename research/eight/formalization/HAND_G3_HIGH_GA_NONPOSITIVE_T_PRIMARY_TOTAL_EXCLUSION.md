# High GA with every nonpositive signed T-primary total

## 1. Original scope

Work on the fixed-witness G0--G2 boundary at
\[
 Q=9789/2500,\qquad h=7/10.
\]
H,G,B,D are sorted outer states with signed tangents positive,
negative, negative, negative. E is nonpositive and has either
canonical radial kind. A and T may have either sign and radial
kind. Retain actual owners
\[
 HG\in\{0,2\},\ GA\in\{2,3\},\ AB\in\{0,2\},\
 BT\in\{2,3\},\ TD\in\{0,2\},\
 DE\in\{2,3\},\ EH\in\{0,1\},
\]
the actual neighboring inequalities, and
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.                       \tag{1}
\]
No frame order is assumed.

The A-primary owners are GA3 and AB2; the T-primary owners are
BT3 and TD2; the E-primary owners are DE3 and EH1. A **selected
primary total** means zero if neither primary is selected, its
actual error if exactly one is selected, and the signed sum of
both errors if both are selected. Secondary errors stay arbitrary.

**Theorem.** There is no such cycle when its selected T-primary
total is nonpositive and its selected E-primary total is
nonnegative. Every A-owner and A-error allocation is included.
A positive BT3 balanced by a larger negative TD2 is included.

**Outer-E corollary.** If E is outer, the nonnegative-E-total
hypothesis is unnecessary: every DE/EH owner and error allocation
is covered.

This is a complete signed-total region with BT3 allowed. It does
not assert the positive-T-total region or a negative core-E total.
Put
\[
 R=\sqrt Q,\quad a_0=\sqrt{Q-\tfrac14}-\tfrac12,\quad
 c_0=\sqrt{Q/2}-\tfrac12,\quad
 \phi(t)=\sin t+\cos t,\quad W(t)=\frac{1+\cos t+|\sin t|}{2}.
\]
All terminating decimals in this note are exact rationals.

## 2. The exact charge of a negative primary sum

Let an intermediate state have primary A and signed tangent Y,
with \(A\ge|Y|\), \(A>1/2\). Let \(u,v\in[-h,h]\) have sum
\(-s\), \(0\le s\le h\). Define
\[
 {\cal L}(u,v)=W(u)+W(v)-2-A(\sin u+\sin v)
                                  -Y(\cos v-\cos u). \tag{2}
\]
Then
\[
                         {\cal L}(u,v)\ge\phi(s)-1.  \tag{3}
\]
A single primary is included by setting the other argument to
zero in (2). This zero belongs only to the force expression;
an unselected secondary error remains in its original outer block.

Set \(C=\cos(s/2)\), \(S=\sin(s/2)\), \(\Delta=|u-v|/2\).
The coordinate part in (2) is bounded below by
\[
 2AS\cos\Delta-2|Y|S\sin\Delta
 \ge2AS(\cos\Delta-\sin\Delta)
 \ge S(\cos\Delta-\sin\Delta).                        \tag{4}
\]
Here \(0\le\Delta\le h<\pi/4\).
For two nonpositive errors, \(0\le\Delta\le s/2\) and the
right lower expression for (2) is
\[
                    (C+2S)\cos\Delta-S\sin\Delta-1.
\]
It decreases in \(\Delta\), and its value at \(s/2\) is
\(\phi(s)-1\).
For opposite signs,
\[
 s/2\le\Delta\le h-s/2,\qquad
 W(u)+W(v)-2=C(\cos\Delta+\sin\Delta)-1.
\]
Consequently (4) gives
\[
 {\cal L}\ge(C+S)\cos\Delta+(C-S)\sin\Delta-1
           =\phi(\Delta+s/2)-1\ge\phi(s)-1.
\]
This proves (3), including \(s=0\).

Every canonical boundary primary satisfies \(A>447/800\).
Put
\[
                       \kappa_0=847/800,\qquad M=41/100.
\]
On \(0\le s\le M\) the stronger inequality is
\[
                      {\cal L}(u,v)\ge
                         \kappa_0\{\phi(s)-1\}.       \tag{5}
\]
For two nonpositive errors, replace \(1/2\) in (4) by
\(447/800\); the decreasing expression at \(\Delta=s/2\)
is exactly the right side of (5).
For opposite signs the resulting expression is
\[
 (C+2(447/800)S)\cos\Delta
 +(C-2(447/800)S)\sin\Delta-1.                        \tag{6}
\]
Its two coefficients are positive; it is concave in \(\Delta\).
The first endpoint gives (5). At the far endpoint the weaker
(4) gives \(\phi(h)-1>.409\). But \(\phi(s)-1<1/3\) on
\([0,M]\): use \(\sin s\le s\), the degree-four cosine upper
bound, and monotonicity at M. Finally
\[
                        .409-\kappa_0/3=673/12000>0.
\]
Thus the far endpoint also exceeds (5). For a single negative
primary, (5) holds on all of \([0,h]\) directly from sorting.

## 3. Actual paired primaries have a short negative total

The actual T-primary projections are
\[
 P_{BT3}=a_B+a_T\sin u-y_T\cos u,\qquad
 P_{TD2}=a_T\sin v+y_T\cos v+b_D.
\]
Adding them gives
\[
                   {\cal L}(u,v)\le a_B+b_D-2
                                   <1.415+.9-2=.315. \tag{7}
\]
If their signed total is \(-s\le0\), (3) and monotonicity
force
\[
                                  s<M.              \tag{8}
\]
Indeed the ordinary alternating Taylor polynomials satisfy
\[
             C_6(M)+S_7(M)-1-63/200>.00073>0.         \tag{9}
\]
The same reasoning applies to GA3/AB2, whose outer terms are
\(a_G+b_B\). Hence a negative signed A-primary sum also has
magnitude below \(M<1/2\), regardless of individual signs.
This is a consequence of the two actual inequalities.

## 4. Every nonpositive A total is excluded by one fixed stress

Use weights
\[
 (k,l,l,c,c,1,1)=
 (31/40,31/20,31/20,2,2,1,1),\qquad\lambda=21/20.
\]
Section 2 of
[the negative-intermediate stress](HAND_G3_NEGATIVE_INTERMEDIATE_ERRORS_FIXED_STRESS_EXCLUSION.md)
gives the charged secondary-owner inequality
\[
                {\cal C}(\mathbf d)+\lambda\sum_i d_i>7/10000
                                                               \tag{10}
\]
whenever both virtual variations are at most h. It does not
require a zero signed sum.

Let the selected A and T totals be \(-r,-s\le0\), and the E
total be \(e\ge0\). Delete their selected primary arguments
inside the force expression. Its remaining sum is \(r+s-e\);
both variations decrease. Equation (3) and the concave chord
\(\phi(h)-1>.409\) give T gain
\[
               c\{\phi(s)-1\}\ge
                \left(\lambda+83/700\right)s.        \tag{11}
\]
The signed E comparison gives
\[
                              j(e)\ge-1.021e,        \tag{12}
\]
with the sorted-circle support charge j of
[the E-primary note](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md).

For two A primaries, Section 3 gives \(r<1/2\).
Since \(\phi(1/2)-1>17/48\), the chord and (3) give A gain
\[
                l\{\phi(r)-1\}\ge
                      (527/480)r=(\lambda+23/480)r.  \tag{13}
\]
For exactly one negative A primary, use its positive secant
multiplier from the negative-intermediate stress. Its exact
gain is at least
\[
                   (1121983/10^6)r
                         =(\lambda+71983/10^6)r.     \tag{14}
\]
With no A primary no change is needed. These cases exhaust
every nonpositive A total, including opposite signs in a pair.

The gains add exactly at the unchanged original states.
Combining (10)--(14), their positive weighted sum of actual
demands minus projections exceeds
\[
          7/10000+(23/480)r+(83/700)s+(29/1000)e>0.
\]
Feasibility makes this same sum nonpositive, a contradiction.
No A transport is needed.

## 5. Nonnegative A/E totals with small combined size

Now let \(a,e\ge0\), put \(\delta=a+e\le h\), and use their
exact charges \(lj(a)+j(e)\). Both signed-pair comparisons
permit opposite individual signs. The whole-interval facts
\[
 j(t)\le0,\qquad j(a)+j(e)\ge j(a+e)
\]
are proved in Section 2 of
[the nonnegative-total theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_TD0_OR_POSITIVE_TD2_EXCLUSION.md).

If \(\delta\le L:=1/6\), take
\[
             k=.78,\quad l=1.26,\quad c=1.8,\quad\lambda=1.03.
\]
Its charged four-circle baseline exceeds \(13/400\).
Deleting the T total \(-s\) and the A/E totals leaves sum
\(s-\delta\). Equation (3) gives
\[
 c\{\phi(s)-1\}\ge(3681/3500)s
                         =\lambda s+(19/875)s.
\]
As \(l>1\), \(lj(a)+j(e)\ge lj(\delta)\).
The existing small-total scalar therefore makes the actual
stress greater than
\[
       13/400+\lambda\delta+lj(\delta)+(19/875)s
                                     >49/15000>0.    \tag{15}
\]
An arbitrary secondary TD0 error is included here: the fixed
charged reference already controls its full two-angle D block.

## 6. A single negative BT3 reaches an actual alignment endpoint

Suppose \(\delta\ge L\). The retained BT2 cases are already
covered by the complete nonnegative-A/E theorems, for arbitrary
TD0 and for nonpositive TD2. If BT3 and TD2 are both selected,
Sections 2--3 give (5), (8); Sections 7--10 below exclude them.
It remains that BT3 alone has error \(-s\le0\), with TD0
of arbitrary error.

At \(s=0\), BT2 and BT3 coincide. For \(s>0\), either actual
BT2 is feasible, or the following genuine-primary entry holds:
\[
             a_T=7/12,\quad0<y_T<39/250,\quad s<1/4. \tag{16}
\]
No global T sign cut is needed.
If \(y_T\le0\), the original nonpositive-zero-source theorem
puts T on its outer arc; the negative high-quarter comparison
gives actual BT2.
If \(y_T>0\), set
\[
 K=a_T+1/2,\quad D=y_T+1/2,\quad
 X=a_B+1/2,\quad Z=b_B+1/2.
\]
When BT3 is feasible but BT2 is not, the contact-vector proof
in Section 3 of
[the negative-A entry lemma](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md)
applies to the identical formulas
\[
 P_3=a_B-a_T\sin s-y_T\cos s,\quad
 P_2=a_B\cos s-b_B\sin s-y_T.
\]
It gives
\[
 Q>1+K^2+D^2+2(D\cos s+K\sin s)\ge K^2+(D+1)^2.
\]
Thus T is not outer and D<1, so its true core is flat.
Substitution \(K=13/12\) gives (16), with the exact square
and Taylor reserves printed in that local proof.

Apply the reflected
[negative-core canceling companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_CANCELING_HG.md)
to the triple \((D,T,B)\).
Reflection and reversal change signs \((-,+,-)\) to
\((+,-,+)\), BT3 to GA1, and TD0 to HG2, preserving both
real errors. Only T moves, on its true flat core and strictly
inside its Q-circle, to one of two endpoints:

* BT is aligned and the actual BT2 witness is available;
* TD is aligned and the actual TD2 witness is available.

B,D and every other state and neighboring inequality stay
fixed. The changed errors keep their sum; at either aligned
endpoint their sum of absolute values equals the absolute
value of their sum. Both total variations therefore decrease
or stay unchanged.
At BT alignment use the complete BT2 theorem with nonnegative
E total. Its stress proofs need only the retained circles,
canonical T core, variation, and the original A entry cut,
which is unchanged. No marker is reapplied to the moved T.
At TD alignment both T primaries are actual witnesses and their
total is negative. Its magnitude need not be below the original
BT magnitude: the nonpositive companion-error branch can move
T toward D beyond its original frame. Reapply the actual paired
inequalities (7)--(9) at this endpoint to obtain its magnitude
below M. Those estimates use only the unchanged B/D circles,
the preserved canonical T state and the two actual projections.
The paired proof below therefore applies to that necessary system.

## 7. Concentration of the paired negative T total

We now have both T primaries selected, including an aligned
one if applicable, and \(0\le s\le M\). Choose
\[
 k=.75+.14e,\quad l=.95+.45e,\quad c=1.35,\qquad
               L\le\delta\le h,\quad0\le e\le\delta. \tag{17}
\]
Use weights \((k,l,l,c,c,1,1)\).
Deleting A/E primary arguments and both T arguments leaves
ordinary variation
\[
 P\le h-\delta,\qquad N\le h-s,\qquad N-P=\delta-s.   \tag{18}
\]
The T pair leaves B's primary coefficient c and D's transverse
coefficient c unrotated. D has just its ordinary DE argument,
or a virtual zero if DE3 is selected. This one-angle fact is
essential for its sorted-support minorant.

Write \(\overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2\) and
\[
 B(e)=k+2l+2c+2-\overline S(1,k)-\overline S(k,l)
                         -\overline S(l,c)-(1+c)c_0. \tag{19}
\]
The three pairs are H=(k,1), G=(k,l), B=(l,c), each with
\(p_i\le q_i\) and \(p_i/q_i\ge2/3\). Define
\[
 \begin{split}
 N_i(t)&=\sqrt{p_i^2+q_i^2+2p_iq_i\sin t},\\
 U_i(t)&=p_i(\phi(t)-1)-R\{N_i(t)-N_i(0)\},\\
 V_i(t)&=q_i(\cos t-1)-R\{N_i(-t)-N_i(0)\},\\
 U_D(t)&=-(c_0-\tfrac12)t.
 \end{split}                                        \tag{20}
\]
The existing concentration proof gives separate concavity,
concavity of U,V, and this D minorant.
For \(\delta\ge s\) it gives
\[
             \text{ordinary charge}\ge\min_iV_i(\delta-s).
                                                               \tag{21}
\]
Its bounds \(U_i(t)\ge-.545q_it\), \(V_i'(t)>.8\), and
\(.8-.545c=257/4000>0\) are established in
[the nonpositive-TD2 theorem](HAND_G3_NONNEGATIVE_A_E_TOTALS_NEGATIVE_TD2_EXCLUSION.md).

For \(e\le\delta\le s\le M\), strengthen these to
\[
 V_i'(t)>.82\quad(0\le t\le h),\qquad
 U_i'(t)>-.81\quad(0\le t\le h-L).                    \tag{22}
\]
For V, the existing endpoint bounds give \(V_H'>.824\)
and \(V_B'>1\). For G positive squaring reduces to the quartic
\[
 Qk^2l^2C_6(h)^2-(.82+lS_9(h))^2
                     \{k^2+l^2-2klS_{11}(h)\}>0.
\]
Its coefficients exceed
\(.0411,.1407,-.0032,-.0198,-.0028\), in ascending powers
of e. Drop the positive linear term and bound negative powers
at h; the lower bound exceeds .032.

For U, concavity reduces to \(t_*=8/15\).
Its derivative is
\[
 p(\cos t_*-\sin t_*)-
 \frac{Rpq\cos t_*}{\sqrt{p^2+q^2+2pq\sin t_*}}.       \tag{23}
\]
This decreases with q; set \(q=27/20\). It then decreases
with \(p\le2269/2000\). Indeed, for \(r=p/q<.85\), its
derivative in p is negative because
\[
 \cos t_*-\sin t_*<.5,\qquad
 \frac{R\cos t_*(1+r\sin t_*)}
      {(1+r^2+2r\sin t_*)^{3/2}}
 \ge\frac{1.97(.86)(1+.85(.5))}{1.61^3}>.5.
\]
The fraction decreases in r; its derivative numerator has sign
\(-2\sin t_*-3r-2r^2\sin t_*-r\sin^2t_*<0\).
The displayed endpoint reserve above .5 is \(655189/8346562\).
At \(p=2269/2000,q=27/20\), the square reserve for (23) >−.81,
using \(C_-=C_{10}(t_*),C_+=C_{12}(t_*)\) and
\(S_-=S_{11}(t_*),S_+=S_9(t_*)\), is
\[
 [p(C_--S_+)+.81]^2(p^2+q^2+2pqS_-)
                       -Qp^2q^2C_+^2>.0237.
\]
These comparisons prove (22) on whole intervals.

In different blocks, adding common positive and negative
variation now increases the lower charge, by derivative
greater than −.81+.82=.01. This includes \(U_D\), whose
derivative exceeds −.4.
A same-block charge at \(P\ge N\) differs from \(U_i(P-N)\) by
\[
 2q_i\sin(N/2)
 \left\{\frac{p_i}{q_i}
 [\cos(P-N/2)-\sin(P-N/2)]-\sin(N/2)\right\}.          \tag{24}
\]
Equation (18) gives
\[
 P-N/2\le h/2-L+M/2=233/600,\qquad N/2\le4/15.
\]
The brace in (24) is nonnegative: a lower bound is
\[
 \frac23\{1-233/600-(233/600)^2/2\}-4/15
                                      =98111/1080000>0.
\]
Thus all positive-excess saturation alternatives are dominated:
\[
       \text{ordinary charge}\ge
                  \min_{i=H,G,B,D}U_i(s-\delta)
                                      \quad(s\ge\delta).         \tag{25}
\]

Feasibility would therefore force a nonpositive scalar among
\[
 B(e)+lj(\delta-e)+j(e)+c\kappa_0\{\phi(s)-1\}
 +\begin{cases}V_i(\delta-s),&s\le\delta,\\
               U_i(s-\delta),&s\ge\delta.
   \end{cases}                                      \tag{26}
\]
For fixed \(\delta,e\), every alternative is concave in s on
its indicated interval. Only \(s=0,s=\delta,s=M\) remain,
with \(s=\delta\) present only for \(\delta\le M\).
The s=0 alternatives are exactly the three positive \(F_{Vi}\)
already certified in the nonpositive-TD2 theorem.
The eight new functions are: one equality and four U endpoints
on \(L\le\delta\le M\), and three V endpoints on \(M\le\delta\le h\).

## 8. Eight explicit polynomial numerators

Use
\[
 \bar R=1.978787508,\quad \bar a=1.414575672,\quad\bar c=.899214066.
\]
The cited nonpositive-TD2 proof verifies their positive-square
bounds and its support polynomial
\[
 J(t)=\frac{C_{10}(t)-1}{2}
       +(\tfrac12-\bar a)S_9(t)-.029t^4\le j(t),\quad0\le t\le h.
                                                               \tag{27}
\]
Take native variables x,y, put \(e=y,\delta=m+x\), on
\[
 0\le x\le D,\quad0\le y\le m+x,                     \tag{28}
\]
where \((m,D)=(L,M-L)\) for the five low functions and
\((m,D)=(M,h-M)\) for the three V functions.
Start with
\[
 A_0=2k+3l+\tfrac52c+\tfrac52-(1+c)\bar c
                                  +lJ(\delta-e)+J(e),             \tag{29}
\]
\[
             P_H=1+k^2,\quad P_G=k^2+l^2,\quad P_B=l^2+c^2.
\]
For the equality endpoint add
\(c\kappa_0(C_{10}(\delta)+S_{11}(\delta)-1)\) to \(A_0\),
without changing the P's.
For every cut endpoint first add the constant
\(c\kappa_0(C_{10}(M)+S_{11}(M)-1)\).
For U index i put \(t=M-\delta\), add
\(p_i(C_{10}(t)+S_{11}(t)-1)\), and replace \(P_i\) by
\(P_i+2p_iq_iS_9(t)\).
For D add \(-(\bar c-1/2)(M-\delta)\), without changing norms.
For V index i put \(t=\delta-M\), add \(q_i(C_{10}(t)-1)\),
and replace \(P_i\) by \(P_i-2p_iq_iS_{11}(t)\).
These are lower nonradical charges and upper squared norms.

For each resulting P let \(P_0=P(0,0)\), and put
\[
 w=\frac{[P]_{\le3}-P_0}{P_0},\qquad
 r=\rho[1+w/2-w^2/8+w^3/16]_{\le3},                 \tag{30}
\]
with total-degree truncation in x,y. Default rho constants
in H,G,B order are
\[
                     1.25,\quad1.210371844,\quad1.650757402.
\]
Only a replaced U norm changes its rho, to respectively
\[
                     1.387050338,\quad1.344744663,\quad1.828389667.
\]
For V the defaults still apply, since its angle is zero at the
native origin. Every mass exceeds one on its whole domain (28),
by the coefficient formula below; no approximation property of
these masses is used.

Let A be (29) with its indicated additions and define
\[
 {\cal N}=2Ar_Hr_Gr_B
          -\bar R\sum_{i=H,G,B}(P_i+r_i^2)\prod_{j\ne i}r_j.
                                                               \tag{31}
\]
Then the scalar is at least \({\cal N}/(2r_Hr_Gr_B)\), by
\(\sqrt{P_i}\le(P_i+r_i^2)/(2r_i)\).
The numerator degree is twenty, except for the three U numerators,
whose degree is twenty-one.

## 9. Whole-domain coefficient certificates

Put
\[
 a_{n0}=4^{-n}\binom{2n}{n},\quad
 a_{nj}=2\,4^{-n}\binom{2n}{n-j}\ (1\le j\le n),        \tag{32}
\]
zero otherwise. Then \(u^n=\sum_j a_{nj}T_j(2u-1)\),
where \(|T_j|\le1\).
For \(P(x,y)=\sum p_{ij}x^iy^j\), substitute
\(x=Du,y=(m+Du)v\), \(0\le u,v\le1\).
This covers (28) and gives tensor coefficients
\[
 b_{kl}=\sum_{ij}p_{ij}\sum_{r=0}^j
          \binom jr m^{j-r}D^{i+r}a_{i+r,k}a_{jl}.
\]
Hence
\[
                         P\ge b_{00}
                                      -\sum_{(k,l)\ne(0,0)}|b_{kl}|.
                                                               \tag{33}
\]
The exact displayed formulas give these strict numerator
lower bounds on the entire low trapezoid:

| Function | Lower bound |
| --- | ---: |
| equality endpoint | .183 |
| D cut endpoint | .141 |
| H cut-U endpoint | .139 |
| G cut-U endpoint | .170 |
| B cut-U endpoint | .157 |

For each V scalar, fix e. The established derivative estimates
\(j''<.02\), \(V_i''<-.0648q_i\) give
\[
             \partial_\delta^2 F_{Vi}
              <.02(1.265)-.0648(.95)=-.03626<0.       \tag{34}
\]
The remaining delta interval is \([\max(M,e),h]\).
It suffices to check \(\delta=M,\delta=e,\delta=h\).
For a one-variable polynomial \(\sum p_jt^j\) on \([0,D_0]\),
use
\[
 b_k=\sum_jp_jD_0^ja_{jk},\qquad
                          P\ge b_0-\sum_{k\ge1}|b_k|. \tag{35}
\]
Substitution of (31) gives:

| V index | delta=M, 0<=e<=M | delta=e, M<=e<=h | delta=h, 0<=e<=h |
| --- | ---: | ---: | ---: |
| H | .202 | .230 | .220 |
| G | .202 | .228 | .187 |
| B | .202 | .228 | .595 |

The middle column substitutes \(y=M+x\) on \([0,h-M]\).
The other columns set \(x=0\) or \(x=h-M\) and use e as
the variable. Every entry is a direct coefficient bound (35);
no subdivision or completed-square remainder is needed.
The same formulas prove every mass (30) greater than one.
Thus all eight scalar functions are positive on their complete
domains. The exact scalar concavity (34), rather than an
assertion of numerator concavity, joins the V boundaries.

## 10. Assembly

Section 4 excludes every nonpositive A total. For nonnegative
A/E totals Section 5 handles the small combined total.
At larger total, BT2 is already covered. A genuine single
negative BT3 reaches one of the actual alignment endpoints
in Section 6. The paired BT3/TD2 cases, including that aligned
output, have the capture and charge of Sections 2--3.
Sections 7--9 make every remaining intrinsic scalar strictly
positive, contradicting the retained inequalities.

For outer E, select the actual secondary DE2 or EH0 at each
nonpositive E-primary error, using
[the outer-E same-state comparison](HAND_G3_OUTER_E_NEGATIVE_PRIMARY_WITNESS_COMPARISON.md).
No state, frame, error or variation changes. Every E primary
that remains is positive, so its selected total is nonnegative;
the theorem proves the corollary.

This argument includes weak ties, both HG owners, arbitrary
A/T signs and both E radial kinds in the main statement.
It closes no positive-T-total or negative-core-E-total claim.
The eight polynomials concern intrinsic scalar endpoints on
two whole trapezoids. No state mesh, sampled minimum, numerical
acceptance premise, Lean compilation or CI is used.

