# The complete core/low pair entry by hand

This proves the entire C/L entry of the four-type frame-concentration
table, with lower cost **.91**. It covers all sixteen ordered source-axis
branches, and hence the retained target axes by reflected reversal.
The proof uses elementary circle supports, monotonicity, two coarse
endpoint tables, and five fixed polynomial inequalities. The latter have
47 explicitly displayed positive Bernstein coefficients. No optimization,
sampling, or adaptive subdivision is a premise.

The scope is the seven-state boundary ring after the independently proved
core, radial-boundary, cap, and common-point reductions. In particular the
directed center gap satisfies \(\delta>19/25\), and the four retained SAT
axes suffice. **No frame-concentration hypothesis is used here.**

## 1. States, markers, and elementary bounds

All terminating decimals below are exact rational numbers. Put

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 \beta=.18,\quad a_c=\frac7{12},
\]
\[
 K=7.506931,\quad g=1.077372,\quad
 \mu=.403875,\quad q=1.089065.
\]

The positive core state \((a,b)\in C\) lies on the side
\(a=a_c,\ 0\le b\le1/2\), followed by the corner

\[
 a=\frac12+\sqrt{\frac1{144}-(b-\frac12)^2},
 \qquad \frac12\le b\le c_C:=\frac12+\frac{\sqrt2}{24}.
\]

The positive low outer state \((a,b)\in L\) satisfies

\[
 (a+\tfrac12)^2+(b+\tfrac12)^2=Q,
 \qquad 0\le b/a\le\frac14.
\]

Write the endpoints of this low arc as \((a_0,0)\) and
\((a_1,b_1)\), where \(b_1=a_1/4\). The positive labels are

\[
 \ell_C=K(a_c-a)+gb,\qquad
 \ell_L=\mu(a-a_0)+qb.                                  \tag{1}
\]

For source and target signs \(\sigma,\tau\in\{-1,1\}\), use
the signed labels \(\sigma\ell_s,\tau\ell_t\). The cost is

\[
 \mathcal C=\phi-\beta h(\phi)+\sigma\ell_s-\tau\ell_t,
 \qquad h(\phi)=\frac{|\cos\phi|+|\sin\phi|-1}{2}.
                                                               \tag{2}
\]

The exact squared comparisons give

\[
 1.4145<a_0<1.415,\quad
 1.2987<a_1<1.2988,\quad b_1<.325,\quad R<1.979,
                                                               \tag{3}
\]
\[
 .558<c_C<.56,\qquad 0\le\ell_C<.786,
 \qquad 0\le\ell_L<.307.                               \tag{4}
\]

Here \(\ell_C\) increases with \(b\), so its maximum is at the
diagonal. Since \(\sqrt2>1.414\),

\[
 c_C>\frac{6707}{12000},\qquad
 \ell_C\le Ka_c-(K-g)c_C
 <\frac{9425464787}{12000000000}<.786.                    \tag{5}
\]

On the low arc put

\[
 r(b)=\frac{b+1/2}{a+1/2},\qquad a'(b)=-r(b).
\]

The function \(r\) increases, and (3) gives
\(0<r\le r(b_1)<.46<1\). Thus \(\ell_L\) increases. Its
endpoint value, denoted by \(E\), satisfies

\[
 E=(\mu+q/4)a_1-\mu a_0,\qquad .306<E<.307.             \tag{6}
\]

Two further useful consequences are

\[
 \ell_L\ge(q-\mu)b,\qquad \ell_L\le qb,
 \qquad \sqrt{a^2+b^2}\le a_0<1.415.                    \tag{7}
\]

The first follows from \(a_0-a\le b\), obtained by integrating
\(-a'\le1\); the second uses \(a\le a_0\). For the radius bound,
\(a^2+b^2=Q-a-b-1/2\), and \((a+b)'=1-r\ge0\).
Finally, for every angle,

\[
 0\le\beta h<.0378.                                    \tag{8}
\]

## 2. Reductions that cover whole sign and axis ranges

Let \((a,b)\) be the source and \((A,B)\) the target. The two
source separators retained after the cap and common-point lemmas are

\[
\begin{array}{ll}
 +f:&M_f=\sigma b+A\sin\phi-\tau B\cos\phi-W\ge0,\\
 -e:&M_e=a-A\cos\phi-\tau B\sin\phi-W\ge0,\\
 &W=1+h=\frac{1+|\sin\phi|+|\cos\phi|}{2}.
\end{array}                                             \tag{9}
\]

Reflection followed by reversal sends
\((s,t,\sigma,\tau,\phi)\) to
\((t,s,-\tau,-\sigma,\phi)\), preserves the cost and center gap,
and sends the retained target axes to these source axes. Therefore the
two ordered type pairs and the two axes in (9) give a complete cover.

The core relative angle has magnitude at most \(\pi/4\), and the low
angle at most \(\arctan(1/4)<1/4\). Thus \(\delta>.76\) and
\(\pi/4<.786\) imply

\[
 \phi>-.3.                                               \tag{10}
\]

For any signs, \(\phi\ge2.05\) is already harmless:

\[
 \mathcal C>2.05-.786-.31-.0378=.9162>.91.                \tag{11}
\]

We henceforth consider \(-.3<\phi<2.05\).

**A low source cannot separate a core target on \(+f\).** Indeed,

\[
 M_f<.325+\frac7{12}(|\sin\phi|+|\cos\phi|)-W
 =-.175+\frac{|\sin\phi|+|\cos\phi|}{12}<0.             \tag{12}
\]

This covers all four signs at once. We used only
\(\sqrt2<3/2\) in the last step.

For a core source on \(+f\), \(\phi\le0\) is impossible:
its projection is at most \(.56+.325<1\). For a core source on
\(-e\), every \(\phi\le\pi/2\) is impossible: since
\(\cos\phi\ge0\), its projection is at most
\(a_c+.325<1\).

For a low source on \(-e\), every \(|\phi|\le.3\) is
impossible, because

\[
 M_e<.915-1.058\cos\phi+.06|\sin\phi|
 \le .915-1.058(1-.3^2/2)+.06(.3)<0.                    \tag{13}
\]

Thus the remaining low-source primary cases have \(\phi>.3\).

On the primary axis \(M_e\) does not depend on the source sign.
Because both positive labels are nonnegative, it suffices there to use
the lower source contribution \(-\ell_s\). All primary estimates
below therefore cover both \(\sigma\) without changing the geometry.

## 3. Core source on the negative-primary axis

Only \(\pi/2<\phi<2.05\) remains. Write
\(s=\sin\phi>0\), \(d=-\cos\phi>0\).

### 3.1 Negative target sign

For \(\phi\ge7/4\), nonnegativity of the low label gives

\[
 \mathcal C>\frac74-.786-.0378=.9262>.91.                \tag{14}
\]

On \([\pi/2,7/4]\), Taylor bounds give
\(d<.185\) and \(s>.98\). The separator implies

\[
 Bs\ge W-a-Ad
 >-\frac1{12}+\frac{s}{2}-.915d.
\]

Consequently

\[
 B>\frac12-\frac{1/12+.915(.185)}{.98}
 =\frac{28487}{117600}.
\]

Using (7), (8), and \(\pi>3.1415\),

\[
 \mathcal C>
 \frac{3.1415}{2}-.786-.0378
 +(q-\mu)\frac{28487}{117600}
 =\frac{10736032753}{11760000000}>.91.                   \tag{15}
\]

### 3.2 Positive target sign

For \(\phi\le1.9\), we have \(d<1/3\), \(s>.9\), so

\[
 M_e\le\frac1{12}+(a_0-\tfrac12)d-\frac{s}{2}
 <\frac1{12}+.915/3-.9/2<0.
\]

Only \(1.9<\phi<2.05\) remains. Subtract the separator margin
with multiplier one. The source functional \(-\ell_C-a\) decreases
along the core boundary, so its minimum is
\(-\ell_C(c_C,c_C)-c_C\). Enlarge the target low arc to its complete
outer circle. The support of a functional \(uA+vB\) on that circle
is \(-(u+v)/2-R\sqrt{u^2+v^2}\). This gives

\[
 \mathcal C>
 \phi+d+\frac{345707}{800000}-RN(\phi),                 \tag{16}
\]
\[
 N^2=\mu^2+q^2+1-2(\mu\cos\phi+q\sin\phi).
\]

For clarity, the constant in (16) is exactly

\[
 -.0378-.786+\mu(1.41)+(\mu+q)/2-.06
 =.43213375.
\]

The function \(N\) increases in this quadrant. Taylor bounds and
squaring give \(N(2)<.84\), \(N(2.05)<.889\),
\(-\cos(1.9)>.32\), and \(-\cos2>.41\). Therefore the two
complete intervals have the respective lower costs

\[
\begin{array}{c|c}
 [1.9,2]&1.9+.32+.43213375-1.979(.84)>.98\\
 [2,2.05]&2+.41+.43213375-1.979(.889)>1.08.
\end{array}                                             \tag{17}
\]

This completes all four C-to-L primary branches.

## 4. Core source on the secondary axis

Here \(0<\phi<2.05\). A negative core source must lie on its
straight side. Indeed, (9) and (7) give

\[
 b\le A\sin\phi-\tau B\cos\phi-W
 \le\sqrt{A^2+B^2}-1<.415<\frac12.
\]

Subtract \(gM_f\) from the cost. For a positive source the remaining
core functional is \(\ell_C-gb=K(a_c-a)\ge0\); for a negative
source it is zero by the preceding side restriction. Thus both source
signs obey the same bound

\[
 \mathcal C\ge\phi-\beta h+gW-\tau c_L
 +\min_L\{(-\tau\mu-g\sin\phi)A
                   +\tau(g\cos\phi-q)B\},\qquad
 c_L=-\mu a_0.                                         \tag{18}
\]

Put

\[
 A_*=(g+\beta)/2=.628686,\qquad
 C_*=(g-\beta)/2=.448686.                               \tag{19}
\]

### 4.1 Negative target sign

The target functional in (18) has coefficients
\(\mu-g\sin\phi\) and \(q-g\cos\phi>0\). Its minimum on
the low arc occurs at one of the two endpoints. If its first coefficient
is nonnegative, this follows from concavity of \(a(b)\); if it is
negative, the functional increases with \(b\).

For \(0\le\phi\le\pi/2\), the axial endpoint gives

\[
 F_a(\phi)=\phi+A_*+C_*\cos\phi-(ga_0-C_*)\sin\phi.
                                                               \tag{20}
\]

The fixed polynomial \(P_-\) in Section 6 is a lower bound for
\(F_a-.91\) on this entire interval, and all seven of its Bernstein
coefficients are positive.

The cut endpoint gives

\[
 F_b(\phi)=\phi+A_*+E+D\cos\phi-B_*\sin\phi,
 \quad D=C_*-gb_1,\quad B_*=ga_1-C_*.
\]

From (3), \(0<D<.1\) and \(0<B_*<.952\). Thus
\(F_b'\ge1-\sqrt{D^2+B_*^2}>0\), and

\[
 F_b(0)=g+E-gb_1>g+.306-g(.325)>1.03.
\]

On \([\pi/2,2.05]\), the axial cosine coefficient becomes
\(-C_*\), and the cut cosine coefficient becomes
\(-C_*-gb_1\). Both functions then have strictly positive derivative,
since their sine coefficients remain negative and \(\cos\phi\le0\).
Their lower bounds therefore continue across this whole interval.

### 4.2 Positive target sign, the first interval

Enlarging the target low arc to the complete outer circle in (18) gives

\[
 F(\phi)=\phi+C_0+(g-\beta/2)\sin\phi
                  -(\beta/2)\cos\phi-RN_+(\phi),       \tag{21}
\]
\[
 C_0=(g+\beta+\mu+q)/2+\mu a_0,
 \qquad
 N_+^2=\mu^2+q^2+g^2+2g(\mu\sin\phi-q\cos\phi).
\]

On the entire interval \([0,1.2]\), the cubic

\[
 U(\phi)=.405+1.086\phi-.037\phi^2-.048\phi^3           \tag{22}
\]

is positive and strictly exceeds \(N_+\). The explicit polynomial
\(P_N\) in Section 6 proves this by squaring. The polynomial
\(P_F\) then proves \(F>.91\) throughout \([0,1.2]\).
These are two fixed rows of ten and nine positive coefficients.

### 4.3 Positive target sign, the cut endpoint and continuation

For \(1.2\le\phi\le2.05\), the target functional in (18)
decreases along the low arc. Its derivative is

\[
 (\mu+g\sin\phi)r(B)-(q-g\cos\phi).
\]

At \(\phi=1.2\), the bounds \(\cos1.2<.363\),
\(\sin1.2<.933\) imply

\[
 q-g\cos1.2>.46(\mu+g\sin1.2).
\]

Moreover the difference on the two sides increases, because
\(\sin\phi-.46\cos\phi>0\) on this whole interval. Since
\(r<.46\), the minimum is at \((a_1,b_1)\).

For \(\phi\le\pi/2\), its cost is

\[
 F_c(\phi)=\phi+A_*-E+(C_*+gb_1)\cos\phi-B_*\sin\phi.
                                                               \tag{23}
\]

The polynomial \(P_c\) in Section 6 proves \(F_c>.91\) on
\([1.2,\pi/2]\). On \([\pi/2,2.05]\), its cosine coefficient
becomes \(-C_*+gb_1<0\). Consequently its derivative is greater
than one, so the same bound continues. This completes all four
C-to-L secondary branches.

## 5. Low source on the negative-primary axis

Section 2 gives \(.3<\phi<2.05\). We use the lower source sign
\(-\ell_L\), which covers both actual signs.

First consider either a negative core target on its whole boundary,
or a positive core target on its straight side. The positive-target
corner will be treated separately in Section 5.3.

### 5.1 The complete interval \([.3,.6]\)

Subtract three times the separator margin. The source functional
\(-\ell_L-3a\) has the full-circle lower support

\[
 S=\mu a_0+(\mu+3+q)/2
              -R\sqrt{(\mu+3)^2+q^2}>S_0,
\]
\[
 S_0=\mu(1.4145)+(\mu+3+q)/2-1.979(3.574).
                                                               \tag{24}
\]

The radical bound follows by squaring. Write
\(v=g-3\sin\phi\). For a negative target the target functional is

\[
 \ell_C+3A\cos\phi-3B\sin\phi.
\]

On the side its minimum is
\(3a_c\cos\phi+\min(0,v/2)\). On the corner put
\(d=B-1/2\), \(e=A-1/2\). The circle identity gives
\(a_c-A\ge6d^2\), so the extra decrease from the side/corner
junction is at most

\[
 \frac{\max(-v,0)^2}{24(K-3\cos\phi)}
 <\frac{(1.8-g)^2}{24(K-3)}<.005.                        \tag{25}
\]

For a positive target on the side, the minimum is instead
\(3a_c\cos\phi+\min(0,-v/2)\). Therefore both target cases
are bounded below by the minimum of the following two functions:

\[
\begin{split}
 H_-(\phi)&=\phi+(3+\beta)/2+S_0+g/2
                   +3.16\cos\phi-.09\sin\phi-.005,\\
 H_+(\phi)&=\phi+(3+\beta)/2+S_0-g/2
                   +3.16\cos\phi+2.91\sin\phi-.005.
\end{split}                                             \tag{26}
\]

Both functions are concave on \([.3,.6]\). The four Taylor endpoint
checks give the complete table

\[
\begin{array}{c|cc}
 \phi&H_-(\phi)\text{ lower bound}&H_+(\phi)\text{ lower bound}\\\hline
 .3&2321515331/2000000000&543169921967/560000000000\\
 .6&2051464199/2000000000&114960155557/70000000000.
\end{array}                                             \tag{27}
\]

Every entry exceeds \(.96\), hence certainly \(.91\).

### 5.2 One variable multiplier covers \([.6,2.05]\)

Set \(\lambda=g/\sin\phi\). Since \(\sin\phi>.564\) on
this interval, the source functional \(-\ell_L-\lambda a\)
decreases on the entire low arc:

\[
 (\mu+\lambda)r-q
 <(\mu+g/.564)(.46)-q<0.
\]

Its minimum is therefore at \((a_1,b_1)\). For the negative core
target, the other functional is

\[
 \ell_C+\lambda A\cos\phi-\lambda B\sin\phi
 =\lambda a_c\cos\phi
     +(K-\lambda\cos\phi)(a_c-A)
 \ge\lambda a_c\cos\phi.                              \tag{28}
\]

Here \(K>g/.564\). For the positive target on its side the
functional equals \(\lambda a_c\cos\phi\), because the coefficient
of \(B\) cancels. In both cases we obtain the same scalar bound

\[
 G(\phi)=\phi-\beta h-E+
            \frac{g}{\sin\phi}(W-a_1+a_c\cos\phi).
                                                               \tag{29}
\]

For \(.6\le\phi\le\pi/2\), this is

\[
 G=\phi-\frac\beta2(\sin\phi+\cos\phi-1)-E+g/2
    +g\frac{(13/12)\cos\phi-(a_1-1/2)}{\sin\phi}.
                                                               \tag{30}
\]

The fixed degree-thirteen polynomial \(P_m\) in Section 6 bounds
\((G-.91)\sin\phi\) below and has fourteen positive Bernstein
coefficients. Thus \(G>.91\) on this entire interval.

For \(\pi/2\le\phi\le2.05\), the factor \(13/12\) in
(30) becomes \(1/12\) and the width term becomes
\(-\beta(\sin\phi-\cos\phi-1)/2\). Its derivative is

\[
 G'=1-\frac\beta2(\sin\phi+\cos\phi)
       +g\frac{(a_1-1/2)\cos\phi-1/12}{\sin^2\phi}.
\]

Using \(\sin\phi>.887\), \(-\cos\phi<.462\),
\(a_1-1/2<.8\), and \(\sin\phi+\cos\phi\le1\),

\[
 G'>1-.09-
     g\frac{.8(.462)+1/12}{.887^2}>0.                    \tag{31}
\]

Hence the bound continues to \(2.05\).

### 5.3 Positive core target on the corner

Now \(B\ge1/2\). The first quadrant is impossible, since (9)
would require

\[
 a\ge W+A\cos\phi+B\sin\phi
 \ge\frac12+\cos\phi+\sin\phi\ge\frac32>a_0.
\]

In the second quadrant write \(d=-\cos\phi\), \(s=\sin\phi\).
The necessary inequality is

\[
 a\ge\frac12+s-\frac d{12}.                            \tag{32}
\]

The right side decreases with \(\phi\). At \(\phi=1.9\),
it exceeds \(.5+.946-.324/12=1.419>a_0\). Thus
\(\phi>1.9\).

On \([1.9,2]\), (32) and Taylor bounds give
\(a>.5+.909-.417/12=1.37425\). The outer circle then forces
\(b<.14\), as verified by

\[
 (1.37425+.5)^2+(.14+.5)^2>Q.
\]

On \([2,2.05]\), the analogous bounds are
\(a>.5+.887-.462/12=1.3485\) and \(b<.23\), using
\((1.3485+.5)^2+(.23+.5)^2>Q\). Since \(\ell_L\le qb\),
the two lower costs are

\[
\begin{array}{c|c}
 [1.9,2]&1.9-.0378-.786-.14q>.923\\
 [2,2.05]&2-.0378-.786-.23q>.925.
\end{array}                                             \tag{33}
\]

This finishes all four L-to-C primary branches.

## 6. The five fixed polynomial inequalities

This section specifies every polynomial used above. Write \(S_j\) and
\(C_j\) for the sine and cosine Taylor polynomials truncated at degree
\(j\). On the physical positive-angle intervals used here,

\[
 S_7\le\sin\phi\le S_5,\quad \sin\phi\le S_9,
 \qquad C_6\le\cos\phi\le C_8.
\]

Their alternating remainders prove these statements directly. Put
\(\gamma=.91\), retain \(A_*,C_*\) from (19), and define

\[
\begin{split}
 P_-={}&\phi+A_*-\gamma+C_*C_6
                      -(g(1.415)-C_*)S_5,\\
 P_N={}&U^2-[\mu^2+q^2+g^2+2g(\mu S_9-qC_6)],\\
 P_F={}&\phi+(g+\beta+\mu+q)/2+\mu(1.4145)-\gamma
                   +(g-\beta/2)S_7-(\beta/2)C_8-1.979U,\\
 P_c={}&\phi+A_*-.307-\gamma
                  +(C_*+g(1.2987)/4)C_6
                  -(g(1.2988)-C_*)S_5,\\
 P_m={}&[\phi+\beta/2-.307+g/2-\gamma]S_7
            -(\beta/2)S_5^2-(\beta/2)S_5C_8
            +(13g/12)C_6-g(.7988).
\end{split}                                             \tag{34}
\]

For \(P_m\), the bracket multiplying \(S_7\) is positive when
\(\phi\ge.6\). On its physical interval \(\phi\le\pi/2\),
sine and cosine are nonnegative, so the product upper bounds
\(\sin^2\phi\le S_5^2\) and
\(\sin\phi\cos\phi\le S_5C_8\) are valid. Consequently
\(P_m\le(G-.91)\sin\phi\). All the other comparisons in
Sections 4--5 follow immediately from (3), (6), and these Taylor bounds.

For an interval \([l,u]\), use the Bernstein basis

\[
 B_{k,n}(\phi)=\binom nk
 \left(\frac{\phi-l}{u-l}\right)^k
 \left(\frac{u-\phi}{u-l}\right)^{n-k}.
\]

These functions are nonnegative and sum to one. The following lists are
strict lower bounds on the complete Bernstein coefficient lists of the
specified polynomials. **Every listed integer is divided by \(10^6\).**

| Polynomial | Entire interval | Degree | Positive coefficient lower numerators |
|---|---|---:|---|
| \(P_-\) | \([0,1.571]\) | 6 | 167371, 147526, 90767, 31856, 13144, 70276, 208525 |
| \(P_N\) | \([0,1.2]\) | 9 | 773, 2028, 2327, 2200, 2095, 2300, 2842, 3356, 2969, 178 |
| \(P_F\) | \([0,1.2]\) | 8 | 144942, 120668, 102475, 88215, 75631, 62718, 48109, 31369, 13139 |
| \(P_c\) | \([1.2,1.571]\) | 6 | 14274, 8519, 5400, 5338, 8710, 15824, 26898 |
| \(P_m\) | \([.6,1.571]\) | 13 | 38649, 23617, 13318, 7443, 5538, 7011, 11130, 17038, 23760, 30225, 35283, 37730, 36330, 29843 |

For example, these coefficients can be checked entirely by rational
arithmetic. If \(P(\phi)=\sum_{j=0}^n p_j\phi^j\), first expand

\[
 P(l+(u-l)y)=\sum_{j=0}^n c_jy^j.
\]

Then its Bernstein coefficient is exactly

\[
 b_k=\sum_{j=0}^k c_j\frac{\binom kj}{\binom nj}.
                                                               \tag{35}
\]

Substitution of (34) into (35) proves the displayed positive rows.
The bound \(\pi/2<355/226<1.571\) ensures that the rows with
upper endpoint \(1.571\) contain their complete required intervals.
For (22), positivity of \(U\) also follows directly from
\(1.086-.037(1.2)-.048(1.2)^2>0\).

## 7. Complete coverage and conclusion

The whole source-axis cover is as follows; every row covers both source
signs and the complete admissible angle range.

| Source, target | Source separator | Negative target sign | Positive target sign |
|---|---|---|---|
| C, L | \(+f\) | Section 4.1 | Sections 4.2--4.3 |
| C, L | \(-e\) | Section 3.1 | Section 3.2 |
| L, C | \(+f\) | Impossible, (12) | Impossible, (12) |
| L, C | \(-e\) | Sections 5.1--5.2 | Side: 5.1--5.2; corner: 5.3 |

The discarded angle ranges were all covered in Section 2, including the
unrestricted tail (11). The retained target axes follow by the exact
reflection/reversal in Section 2. The closed side/corner junction and
all listed interval endpoints are included in at least one proof case.
Consequently every admissible C/L boundary pair satisfies

\[
 \boxed{\delta-\frac9{50}h(\phi)+\psi_j-\psi_i>.91.}
\]

The optional arithmetic replay `verify_core_low_whole_pair_hand.py`
checks 120 strict rational comparisons, including the five fixed
Bernstein rows and all endpoint bounds used above. Its output is
`core_low_whole_pair_hand_arithmetic.json`. The continuous proof is the
argument above; the replay only verifies its displayed arithmetic.
\(\square\)
