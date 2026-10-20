# A negative flat-core A primary and positive TD2: whole-angle concentration

## 1. Scope and conclusion

Use the fixed-original-witness G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10}.
\tag{1}
\]
H, G, B and D are sorted outer states, with signed tangents
respectively positive, negative, negative and negative. A is positive
flat core, so \(a_A=7/12\). T and E may have either sign and either
radial kind. The original owners are
\[
 BT=2,\quad TD=2,\quad DE=2,\quad EH=0,\qquad HG\in\{0,2\},
\tag{2}
\]
and either

* GA3 has error \(-s\), \(0\le s\le1/4\), and AB0 has arbitrary error; or
* AB2 has error \(-s\), \(0\le s\le19/50\), and GA2 has arbitrary error.

Put \(z=d_{TD}\ge0\). The whole original cycle has positive and
negative variation each less than \(h\), as proved in Section 2 of
[the global path theorem](HAND_G3_GLOBAL_BT0_DE2_PATH_EXCLUSION.md).
No frame order is assumed.

The proof uses G1 only through these two variation bounds. It
therefore also applies to a necessary boundary cycle satisfying
the stated corner constraints and neighboring witness inequalities
when the variation bounds have been preserved by an earlier
A-only transport. No fresh G1 conclusion is required for that
transported cycle.

This note reduces the necessary inequalities to exactly the fourteen
whole-interval endpoint inequalities (8), (9) and (9a) in
[the companion scalar theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md).
The latter proves every one of those inequalities strictly positive.
Consequently the original class (2) is impossible.

The two continuous coefficient families are those of (10)--(11) in
the companion. They depend on \(z\), and are held fixed whenever
\(s\) varies. All their ranges used below are proved in Sections 2--4
of that note. This proof neither samples the angular domain nor
assumes that an original cycle has concentrated angles.

All decimals below denote exact rational numbers.

## 2. Secant weights and the exact scalar baseline

Set
\[
 \begin{gathered}
 \eta=\frac{293}{1000},\qquad K=\frac{13}{12},\qquad
 p=l\sec s,\qquad m=c(\cos z+\eta\sin z),\\
 \sigma=R\sqrt{1+\eta^2}-\frac{1+\eta}{2},\qquad
 c_0=\sqrt{Q/2}-\frac12,\\
 W(t)=\frac{1+\cos t+\sin t}{2}\quad(0\le t\le h),\qquad
 \phi(t)=\cos t+\sin t.
 \end{gathered}
\tag{3}
\]
Give GA and AB weights \((\lambda_G,\lambda_B)=(p,l)\) in the GA
alternative and \((l,p)\) in the AB alternative. The other weights,
in cyclic order, are
\[
                       HG:k,\quad BT:m,\quad TD:c,\quad DE:1,\quad EH:1.
\tag{4}
\]
These multiply the actual original witnesses.

For a negative GA3 error the weighted projection is
\[
 p\{a_G-a_A\sin s-y_A\cos s\}
                =p a_G-l y_A-\frac7{12}l\tan s.
\tag{5}
\]
For a negative AB2 error it is
\[
 p\{-a_A\sin s+y_A\cos s+b_B\}
                =l y_A+p b_B-\frac7{12}l\tan s.
\tag{6}
\]
Thus A's signed tangent cancels exactly. The corresponding outer
force has the same form as a zero-angle GA2 or AB0 force with
coefficient \(p\). This is an identity of weighted projections;
it does not introduce a new separating witness.

The TD2 force on T is
\[
                    c\sin z\,a_T+(c\cos z-m)y_T
                         =c\sin z(a_T-\eta y_T)
                         \le c\sigma\sin z.
\tag{7}
\]
The last bound holds for either radial kind and either sign, by the
actual corner \((a_T+1/2,|y_T|+1/2)\) in the radius-\(R\) disk.
The same support calculation was proved in Section 2 of
[the TD2 concentration theorem](HAND_G3_HIGH_GA_LOW_EH_TD2_ANGLE_CONCENTRATION.md).

Write \(S\) for the sorted outer support and \(\overline S\) for the
complete-circle support:
\[
 \begin{split}
 S(f,g)&=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},\\
 \overline S(f,g)&=R\sqrt{f^2+g^2}-\frac{f+g}{2}.
 \end{split}
\tag{8}
\]
The exact baseline is
\[
\begin{split}
 B_O(s,z)={}&k+\lambda_G+\lambda_B+m+cW(z)+2-c\sigma\sin z\\
 &-\overline S(1,k)-\overline S(\lambda_G,k)
       -\overline S(m,\lambda_B)-S(1,c)\\
 &+p\{W(s)-1\}+\frac7{12}l\tan s,
 \qquad O\in\{\mathrm{GA},\mathrm{AB}\}.
\end{split}
\tag{9}
\]
The actual sorted D support is retained. At \(s=0\) both baselines
agree; denote that common value by \(B_0(z)\).

One identity will account for every derivative of the baseline.
Put \(x=\tan s\), \(w=\sqrt{1+x^2}=\sec s\), and let
\[
 r=\frac{k}{l}\quad\hbox{in the GA alternative},\qquad
 r=\frac{m}{l}\quad\hbox{in the AB alternative}.
\]
All \(s\)-dependence in (9), after collecting its corner half-shifts,
is precisely
\[
 F_0(s)=l\{w+Kx-R\sqrt{w^2+r^2}\}.
\tag{10}
\]
In particular, with \(A=1+r^2\),
\[
 \begin{split}
 \frac{F_{0,xx}}l&=(1+x^2)^{-3/2}
                         -RA(x^2+A)^{-3/2},\\
 \frac{F_{0,s}}{l\sec^2s}
   &=K+\sin s\left(1-\frac R{\sqrt{1+r^2\cos^2s}}\right).
 \end{split}
\tag{11}
\]
The first expression increases with \(r\) whenever \(A>2x^2\),
which holds in every use below.

## 3. Concentration with \(s,z\) fixed

The three ordered coefficient pairs at fixed \(s\) are
\[
 (p_G,q_G)=(k,\lambda_G),\qquad
 (p_H,q_H)=(k,1),\qquad
 (p_B,q_B)=(\min(\lambda_B,m),\max(\lambda_B,m)).
\tag{12}
\]
Every pair has smaller-to-larger ratio at least \(1/2\). For such
a pair define
\[
 \begin{split}
 N_{p,q}(t)&=\sqrt{p^2+q^2+2pq\sin t},\\
 U_{p,q}(t)&=p\{\phi(t)-1\}-R\{N_{p,q}(t)-N_{p,q}(0)\},\\
 V_{p,q}(t)&=q(\cos t-1)-R\{N_{p,q}(-t)-N_{p,q}(0)\},\\
 \Psi_{p,q}(P,N)&=p\{\phi(P)-1\}+q(\cos N-1)
                       -R\{N_{p,q}(P-N)-N_{p,q}(0)\}.
 \end{split}
\tag{13}
\]
The functions \(U,V\) are concave on \([0,h]\), and \(\Psi\) is
concave separately in its two variables. These are the whole-interval
statements of Section 3 of the cited TD2 concentration theorem.
Its D-support minorant, which requires only \(k\le c\le2\) and
\(1/2\le k\le17/20\), is
\[
                  U_D(t)=-(c_0-\tfrac12)t,\qquad V_D(t)=V_H(t).
\tag{14}
\]
The companion's families satisfy all these hypotheses, including
after either secant coefficient in (12).

Delete the two fixed arguments \(-s,z\) only from the algebraic
angular vector. The remaining positive and negative variations obey
\[
             P\le h-z,\qquad N\le h-s,\qquad N-P=z-s.
\tag{15}
\]
As in Section 5 of the cited concentration theorem, a singleton
outer block may be enlarged by allowing its zero argument to vary.
The lost negative-A rotation and the fixed TD rotation are virtual
zeros in this scalar enlargement. This does not change the
original-witness interpretation of (5)--(9).

Fixing all positive variables and then all negative variables,
separate concavity concentrates each sign into one block. The
remaining common variation parameter has a concave objective.
Its intrinsic endpoints give exactly the following alternatives,
with
\[
               \theta=z-s,\qquad P_*=h-z,\qquad N_*=h-s:
\]

* if \(\theta\ge0\), a pure term \(V_i(\theta)\);
* if \(\theta\le0\), a pure term \(U_i(-\theta)\), including \(U_D\);
* a same-block term \(\Psi_i(P_*,N_*)\);
* a separated term \(U_i(P_*)+V_j(N_*)\), with D allowed through (14).

Thus the minimum of these expressions, added to \(B_O(s,z)\),
must be nonpositive for a feasible original cycle. This is the
only geometric input to the rest of the proof.

## 4. Norm derivative bounds on the whole signed interval

We strengthen one scalar fact from the cited concentration theorem.
For \(N(t)=N_{p,q}(t)\), put
\[
 C(t)=-RN''(t),\quad
 C_0=\frac{Rp^2q^2}{(p^2+q^2)^{3/2}},\quad
 C_1=\frac{Rpq\{(p^2+q^2)^2-3p^2q^2\}}{(p^2+q^2)^{5/2}},
 \quad D_0=\frac{Rpq}{\sqrt{p^2+q^2}}.
\tag{16}
\]
The function \(C\) is increasing and concave on all of \([-h,h]\).
Increasing was already proved there. For concavity at negative
arguments, put \(a=(p^2+q^2)/(pq)\in[2,5/2]\) and \(y=\sin t\).
The numerator of \(N''''\), after positive factors are removed, is
\[
 T(a,y)=4a^2-15+a(a^2-2)y+(10-a^2)y^2+2ay^3+y^4.
\tag{17}
\]
For \(-.645\le y\le0\),
\[
 T(2,y)=(1+y)^4>0,\qquad
 T_a\ge16-16.75(.645)-5(.645)^2-2(.645)^3
                     =\frac{10317811}{4000000}>0.
\tag{18}
\]
At nonnegative \(y\) the coefficients in (17) are positive.
Therefore
\[
                 C(t)\le C_0+C_1t,\qquad
                 RN'(t)\le D_0-C_0t
                 \quad(-h\le t\le h).
\tag{19}
\]
The second inequality is the tangent bound for the concave function
\(RN'\), since \(N'''<0\).

For all ratios \(r=p/q\in[1/2,1]\),
\[
            C_0/q<.7,\qquad C_1/q>1/3,\qquad D_0/q<1.4.
\tag{20}
\]
The middle bound follows by minimizing
\[
 R\,\frac{r(1-r^2+r^4)}{(1+r^2)^{5/2}}.
\]
Its only minimum in this interval has
\(r^2=(7+\sqrt{21})/14\in(.827,.828)\), so \(r>.909\),
\(1-r^2+r^4=6/7\), and \(\sqrt{1+r^2}<1.353\). The exact reserve is
\[
 3(1.97)\frac67(.909)-(1.828)^2(1.353)
                      =\frac{36562371}{437500000}>0.
\tag{21}
\]
We also use
\[
\begin{array}{c|ccc}
 \text{upper ratio}&C_0/q& C_1/q&D_0/q\\ \hline
 .84&<.627&>.346&<1.273\\
 .748&<.569& &<1.186\\
 .66&<.502& &<1.09
\end{array}
\tag{22}
\]
Here \(C_0/q,D_0/q\) increase with \(r\), while \(C_1/q\) decreases
on \([1/2,.84]\). Each endpoint assertion is a positive-square
comparison. For example the first row uses
\[
\begin{split}
 .627^2(1+.84^2)^3-Q(.84)^4&>0,\\
 Q(.84)^2(1-.84^2+.84^4)^2-.346^2(1+.84^2)^5&>0,\\
 1.273^2(1+.84^2)-Q(.84)^2&>0.
\end{split}
\tag{23}
\]
The particularly narrow last bound in (22) is the exact inequality
\(1.09^2(1+.66^2)>Q(.66)^2\).

For later reference, the same formulas and alternating Taylor
bounds give
\[
\begin{gathered}
 V'_{.66,1}(.32)<.913,\qquad
 V'_{.748,1}(.32)<1.032,\qquad
 V'_{.748,1}(.45)<.964,\\
 V'_{.6375,1}(h)>.61,\qquad V'_{.65,1}(h)>.64,\\
 V'_{.6375,1}(.5)>.76,\qquad V'_{.65,1}(.5)>.78.
\end{gathered}
\tag{24}
\]
These are endpoint bounds, not angular-domain samples. The exact
formula used is
\[
        V'_{r,1}(t)=-\sin t+
                    \frac{Rr\cos t}{\sqrt{1+r^2-2r\sin t}}.
\tag{25}
\]
For the three upper bounds in (24), lower bounds on the respective
square roots are \(1.010134,1.043509,.953307\).
For the four lower bounds they have respective upper bounds
\(.764872,.764865,.891706,.894007\).
All follow by squaring with \(S_{11}(t)<\sin t<S_9(t)\) and
\(C_{10}(t)<\cos t<C_{12}(t)\); these symbols denote the alternating
Taylor polynomials ending in the indicated degree.
One may use \(1.978787<R<1.978788\).

## 5. Every pure positive term increases after \(s=z\)

This section applies on both coefficient intervals. We prove that
\[
                   B_O(s,z)+U_i(s-z)
\tag{26}
\]
increases whenever \(s\ge z\) lies in the original core-angle range.
D is included.

First, uniformly for \(p/q\in[1/2,1]\),
\[
                         U'_{p,q}(t)>-.6q\qquad(0\le t\le.38).
\tag{27}
\]
Concavity reduces this to \(t=.38\). Taylor bounds give
\(\phi'(.38)>.557\), \(R\cos(.38)<1.839\), and
\(2\sin(.38)>.741\). With \(r=p/q\), positive squaring reduces
(27) to positivity of
\[
 P_U(r)=(.6+.557r)^2(1+r^2+.741r)-1.839^2r^2.
\tag{28}
\]
If \(P(r)=\sum a_j(r-r_0)^j\) on \([r_0-d,r_0+d]\), its elementary
whole-interval lower bound is \(a_0-\sum_{j\ge1}|a_j|d^j\).
For (28), \(r_0=3/4,d=1/4\), this lower bound is exactly
\[
                         \frac{30312841}{250000000}>.12125.
\tag{29}
\]

For an unaffected GA pair, (11), \(r=k/l>.55\), and
\(\cos(.25)>.968\) give
\[
       F_{0,s}/l>K-.75(.248)>.897.
\tag{30}
\]
Indeed \(R/\sqrt{1+.55^2(.968)^2}<1.75\).
Every unaffected larger coefficient is at most \(1.42l\), so (27)
pays its derivative with reserve
\[
                     K-.75(.248)-.6(1.42)=\frac{17}{375}>0.
\]
For an unaffected AB pair, \(s\ge z\) implies \(z\le.38\), hence
\(m/l>.8\). Since \(\cos(.38)>.928\),
\(R/\sqrt{1+.8^2(.928)^2}<1.6\), and
\[
                 F_{0,s}/l>K-.6(.371)>.86.
\tag{31}
\]
Its unaffected larger coefficient is at most \(l\), so (27)
again leaves a positive margin. The D derivative costs only
\(c_0-1/2<.4\), which both estimates also pay.

Consider the affected GA pair. Write \(r=k/l\) and
\[
 n^2=(x+r\cos z)^2+(1-r\sin z)^2.
\tag{32}
\]
Directly combining (10) with \(U_G(s-z)\) gives
\[
 \frac{(B_{\rm GA}+U_G(s-z))_s}{l\sec^2s}
 =K+\sin s+r\cos^2s\,\phi'(s-z)
                 -R\frac{x+r\cos z}{n}.
\tag{33}
\]
For \(0\le z\le s\), the last normalized ratio increases with \(z\).
At \(z=s\) it equals
\[
 \frac{\sin s+r\cos^2s}{\sqrt{1+r^2\cos^2s}}.
\]
Use \(.55<r<.85\), \(s\le.25\),
\(\phi'(.25)>.720\), and the denominator bound in (30).
The right side of (33) is greater than
\[
                K-.75(.248)-(1.75-.720)(.85)>.0218.
\tag{34}
\]

For the affected AB pair, first suppose \(p<m\). Its \(x\)-dependent
part is
\[
              l\{(K+\cos z+\sin z)x-Rn\}
\]
up to a constant, with \(r=m/l\). Its derivative is at least
\(l(K+1-R)>.103l\). If \(p\ge m\), the formula (33) applies
with \(r=m/l\in[.8,1.08]\). Since \(\sin s<.371\),
\(\cos^2s>.861\), and \(\phi'(s-z)>.557\), its lower bound is
\[
       K+.371+.557r-
               R\frac{.371+r}{\sqrt{1+.861r^2}}>0.
\tag{35}
\]
To justify the replacements, use the upper bound
\(D=R/\sqrt{1+.861r^2}>1\) for the norm coefficient in (33);
both \(1-D\) and \(.557-D\) are negative. Thus replacing
\(\sin s\) by \(.371\) and \(\cos^2s\) by \(1\) decreases
the resulting lower bound.
Positive squaring in (35) gives
\[
 P_A(r)=(K+.371+.557r)^2(1+.861r^2)-Q(.371+r)^2.
\]
Its centered lower bound on \([.8,1.08]\) is
\[
                   \frac{2092249892523197}{28125000000000000}
                       >.07439.
\tag{36}
\]
Both branches are continuous at \(p=m\). This proves the asserted
increase of every function (26). All pure positive alternatives
therefore reduce to the equal-angle baseline \(B_O(z,z)\).

## 6. Two general same-block comparisons

The following comparisons will dispose of most saturated cases.
Write \(r=q/p\).
If \(0\le P\le N\le h\), direct trigonometric subtraction gives
\[
\begin{split}
 \frac{\Psi(P,N)-V(N-P)}p
  ={}&(1-r\cos N)(\cos P-1)+(1-r\sin N)\sin P.
\end{split}
\tag{37}
\]
This is nonnegative whenever \(r\sin N\le1\).
If \(r\cos N\ge1\), both terms are already nonnegative.
Otherwise the expression decreases with \(r\), because its
\(r\)-coefficient is \(\cos N-\cos(N-P)\le0\).
Enlarge \(r\) to \(1/\cos N\); the resulting expression is
\((1-\tan N)\sin P\ge0\).

If \(0\le N\le P\le h\), then
\[
 \frac{\Psi(P,N)-U(P-N)}p
                    =\phi(P)-\phi(P-N)-r(1-\cos N).
\tag{38}
\]
For fixed \(N\), the difference of the two \(\phi\)'s decreases
with \(P\), since \(\phi\) is concave. At \(P=h\), (38) becomes
\[
                 (\phi(h)-r)(1-\cos N)+\phi'(h)\sin N.
\]
It is nonnegative for every \(r\le1.7\), using
\[
 \phi(h)>1.409,\quad \phi'(h)>.12,\quad
 \tan(h/2)<.366,\quad
                    .12-.291(.366)=\frac{6747}{500000}>0.
\tag{39}
\]

## 7. The low interval: pure terms

Suppose \(0\le z\le1/5\). The companion proves
\[
 \frac23<k\le.748,\quad1.023<l\le1.345,\quad
 .55<k/l<.66,\quad1<m/l<1.42,\quad
                  l\sec(.38)<M(z):=m+.4z.
\tag{40}
\]
The pure positive alternatives have already reduced to \(s=z\).
For \(0\le s\le z\), among the pure negative terms it is enough
to retain \(V_H(z-s)\).

Indeed the universal bounds in
[the scalar-envelope note](HAND_G3_TD2_CONCENTRATION_SCALAR_ENVELOPES.md)
give \(V_{p,q}(h)>.87p\). Concavity therefore implies, for the B
pair and every \(t\in[0,h]\),
\[
             V_B(t)\ge\frac{.87}{h}\min(\lambda_B,m)t
                      \ge\frac{87}{70}t\ge1.186t\ge V_H(t).
\tag{41}
\]
The middle inequalities are strict for \(t>0\).
The last step uses \(V_H'(0)<1.186\) from (22).

For G, keep its smaller coefficient \(k\) fixed and increase the
larger coefficient from \(1\) to \(\lambda_G\).
The coordinate-monotonicity argument of Section 5 of the
scalar-envelope note extends to \(0<t\le.2\).
In its notation, with \(u=\sin t\),
\[
 g'(u)=\frac{k^2(k-qu)}{(k^2+q^2-2kqu)^{3/2}}
                           \ge\frac3{25\sqrt5},
\]
because \(q/k\le2\) and \(u\le.2\). Consequently
\[
 \partial_q V_{k,q}(t)\ge
 t\left\{\frac{3R}{25\sqrt5}\frac{149}{150}-.1\right\}>0.
\tag{42}
\]
The bracket is greater than \(614/140625\), using
\(R>1.97,\sqrt5<2.25\). Thus \(V_G(t)\ge V_H(t)\)
for \(t\le.2\).

Now consider \(B_O(s,z)+V_H(z-s)\) as a function of \(x=\tan s\)
on \(0\le s\le z\le.2\). In (11) its basic ratio satisfies
\(r\le1.42\), and
\[
                         F_{0,xx}/l<-.139.
\tag{43}
\]
For detail, at \(r=1.42,x=0\) this is a positive-square comparison.
The expression decreases with \(x\) through \(x=.203>\tan(.2)\):
with \(A=1+1.42^2\), the required endpoint inequality is
\[
                 (A+.203^2)^5>QA^2(1+.203^2)^5.
\]
The ratio \((1+x^2)/(A+x^2)\) increases with \(x\), so this one
comparison proves the derivative sign on the whole interval.

Put \(\theta=z-s\). By (19), (22), \(\cos\theta>.98\), and
\(x<.203\),
\[
\begin{split}
 \frac{d^2}{dx^2}V_H(z-s)
 &=\frac{V_H''(\theta)+2xV_H'(\theta)}{(1+x^2)^2}\\
 &\le\frac{-.98+.569+2(.203)(1.186+.2(.569))}
              {(1+x^2)^2}<.117.
\end{split}
\tag{44}
\]
The sum is strictly concave, with margin at least \(.022\).
Its minimum is at \(s=0\) or \(s=z\).
This gives the low endpoints \(B_0+V_H(z)\) and \(B_O(z,z)\).

## 8. The low interval: saturated terms

H and B have coefficient ratio at most \(1.5\).
For \(N_*\ge P_*\), their same-block terms dominate the
corresponding pure terms by (37), since
\(1.5\sin h<1\). For \(P_*\ge N_*\), use (38)--(39).
Only the G same-block term remains.

We first record a useful low AB baseline bound:
\[
                    r=m/l\ge1,\quad 0\le s\le.38
                    \quad\Longrightarrow\quad F_{0,s}>1.04l.
\tag{45}
\]
Let \(y=\sin s\le.371\). Positive squaring shows
\[
       \frac R{\sqrt{2-y^2}}<1.4+.38y^2.
\]
The squared difference, as a polynomial in \(y^2\), is concave,
and is positive at \(0\) and \(.371^2\).
After (11), the desired bound reduces to
\[
 K-1.04-.4y+1.04y^2-.38y^3>0.
\]
At \(y=.2+v\), this polynomial is
\[
 \frac{71}{37500}-.0296v+.812v^2-.38v^3
       \ge\frac{71}{37500}-.0296v+.74702v^2>0.
\tag{46}
\]
Here \(-.2\le v\le.171\); the completed-square reserve is
\(2241221/1400662500>0\).

In the GA assignment, combine its G same-block term with (10).
The variable part is
\[
             l\{(K+\sin h)x-Rn\},
\tag{47}
\]
with \(n\) from (32) and \(r=k/l\).
For \(0\le x<.256\), \(r<.66\), \(0\le z\le h\),
\[
                    R\frac{x+r\cos z}{n}<1.59.
\tag{48}
\]
The ratio increases with \(x\) and \(r\).
At \(x=.256,r=.66\), it increases with \(z\), because
\(.66+.256\cos z-\sin z>0\).
Its maximum is therefore bounded at \(z=h\).
For a coarse exact check its numerator argument is below \(.761\)
and its other norm coordinate exceeds \(.5747\); squaring gives
\(Q(.761)^2<1.59^2\{(.761)^2+(.5747)^2\}\).
Thus (47) increases, with normalized derivative
\[
                         K+.6442-1.59>.137.
\tag{49}
\]
The same argument applies to the GA separated negative-G term,
where \(z\) inside (32) is replaced by the fixed value \(h\).

In the AB assignment, G's coefficients do not change with \(s\).
Differentiating its same-block term and using (19), (22), and (45)
gives
\[
\begin{split}
 \frac{d}{ds}\{B_{\rm AB}+\Psi_G(P_*,N_*)\}/l
 &>1.04+\sin(.32)-1.09-.502(.2)\\
 &>1.04+.3145-1.09-.1004=.1641.
\end{split}
\tag{50}
\]
Therefore both G same-block minima occur at \(s=0\), giving
\(B_0+M_G(z)\) from the companion's (7).

For separated terms use the universal envelope
\(U_i(t)\ge-.545q_it\), proved in the scalar-envelope note.
The positive D term obeys the same bound with \(q_i\) replaced
by \(M(z)\), since \(c_0-1/2<.4<.545M(z)\).
Every larger coefficient in (12) is at most \(M(z)\), by (40).
Equation (41) removes a negative B term. It therefore suffices
to consider
\[
 B_O(s,z)-.545M(z)(h-z)+V_j(h-s),\qquad j=G,H.
\tag{51}
\]
The subtracted term is independent of \(s\).
The affected GA-G case increases by (47)--(49).
For AB-G and AB-H, (24), (40), and (45) give respectively
\[
 \frac{d}{ds}(B_{\rm AB}+V_G(h-s))>.127l,\qquad
 \frac{d}{ds}(B_{\rm AB}+V_H(h-s))
                  >1.04(1.023)-1.032=.03192.
\tag{52}
\]

For the remaining GA-H case we need an absolute slope bound:
\[
                              F_{0,s}>.996.
\tag{53}
\]
At fixed \(s\le.25\), \(F_{0,s}\) is nondecreasing in \(k\)
and increasing in \(l\).
The \(k\)-derivative is nonnegative directly from (11), and is
positive when \(s>0\).
For the \(l\)-derivative use
\[
      \frac{1+2u}{(1+u)^{3/2}}\le\frac2{(3/2)^{3/2}}<1.09
      \quad(u\ge0);
\]
the remaining bracket is at least
\(K-(1.98(1.09)-1)(.248)>0\).
Thus set \(k=2/3,l=1.023\) to get a lower bound.
Since
\[
 \frac R{\sqrt{1+\{(2/3)/1.023\}^2(.968)^2}}<1.676,
\]
writing \(y=\sin s\le.248\) gives
\[
 F_{0,s}>
 1.023\,\frac{K-.676y}{1-y^2}
 \ge1.023\,\frac{K-.676(.248)}{1-(.248)^2}>.996.
\tag{54}
\]
The middle rational function decreases on this interval.
By (24), \(V_H'(h-s)\le V_H'(.45)<.964\), so the GA-H
expression in (51) increases as well.

All separated minima thus occur at \(s=0\).
Together with Section 7 and (50), these are exactly the five
low endpoint obligations (8) of the companion.
At \(s=z\) the GA baseline is no larger than the AB baseline:
here \(m\ge k\), \(p\ge l\), and
\[
 \sqrt{p^2+k^2}-\sqrt{l^2+k^2}
       \ge\sqrt{p^2+m^2}-\sqrt{l^2+m^2}.
\tag{55}
\]
This follows by integrating \(u/\sqrt{u^2+k^2}\ge
u/\sqrt{u^2+m^2}\) from \(l\) to \(p\).
Only \(B_{\rm GA}(z,z)\) is needed on the low interval.

## 9. The high interval: saturated terms are redundant

Suppose \(1/5\le z\le h\). The companion proves
\[
\begin{gathered}
 .676\le k\le.8385,\quad
 1.025\le l\le799/750,\quad
 .659<k/l<.82,\quad .77<m/l<1.032,\\
 m<l\ (z\ge.25),\qquad m<.92l\ (z\ge1/3),\qquad
 m>.8l\ (z\le.38).
\end{gathered}
\tag{56}
\]
For the full actual \(s\)-ranges, its pair bounds are
\[
\begin{array}{c|ccc}
 &p_i/q_i&q_{\max}&q_{\min}\\ \hline
 \mathrm{GA}&>.6375&<1.1&1\\
 \mathrm{AB}&>.65&<1.15&1 .
\end{array}
\tag{57}
\]

If \(\theta=z-s\ge0\), (37) removes every same-block term.
For the affected GA pair its condition follows from
\[
 \frac{l\sec s}{k}\sin(h-s)
   =\frac lk\{\sin h-\cos h\tan s\}
   <\frac{.645}{.659}<1.
\tag{58}
\]
The H and unaffected G ratios are smaller; all B ratios are
below \(1.5\), so their conditions are immediate.
For separated terms, (24), (57), and the universal positive
envelope give
\[
 U_i(P_*)+V_j(N_*)\ge V_j(\theta)+
 \begin{cases}
  (.61-.545(1.1))P_* &\mathrm{GA},\\
  (.64-.545(1.15))P_* &\mathrm{AB}.
 \end{cases}
\tag{59}
\]
The reserves are \(.0105\) and \(.01325\). D's positive
minorant also satisfies these estimates. Thus only pure V
terms remain.

If \(s\ge z\), every pair has larger-to-smaller ratio below
\(1.7\), so (38)--(39) remove same-block terms.
Now \(N_*\le P_*=h-z\le.5\). We use
\[
                       U'_{p,q}(t)>-.62q\qquad(0\le t\le.5).
\tag{60}
\]
As before, concavity reduces to the right endpoint.
Here \(\phi'(.5)>.398\), \(R\cos(.5)<1.738\), and
\(2\sin(.5)>.958\), so a lower bound for \(U'(.5)/q\) is
\[
                   g(r)=.398r-\frac{1.738r}{\sqrt{1+r^2+.958r}}.
\]
Its derivative is negative on \([1/2,1]\).
Indeed \((1+.479r)/(1+r^2+.958r)^{3/2}\) decreases there,
and its value at \(1\), multiplied by \(1.738\), exceeds
\(1.738(1.479)/(1.72)^3>.398\).
Finally
\[
 g(1)>.398-\frac{1.738}{1.719}>-.62,
\]
using \(1.719<\sqrt{2.958}<1.72\).

Concavity and (24) give \(V'_j(t)>.76q_j\) for GA and
\(>.78q_j\) for AB on \(0\le t\le.5\).
Comparing a separated term with \(U_i(P_*-N_*)\) therefore
leaves reserves at least
\[
                  .76-.62(1.1)=.078,\qquad
                  .78-.62(1.15)=.067.
\tag{61}
\]
All saturated terms are consequently dominated by pure U terms.
Section 5 reduces those to \(s=z\).

## 10. The high interval: affected pure negative curves

For the affected GA pair, combine (10) with \(V_G(z-s)\).
Its entire \(x\)-dependent part is
\[
                         l\{(K+\sin z)x-Rn\},
\tag{62}
\]
where \(n\) is (32), now with \(r=k/l\).
This is strictly concave in \(x\), since
\(1-r\sin z>0\). The identity and concavity hold on all of
\(0\le s\le z\), even when \(z>1/4\).
Hence the original subinterval is bounded below by the minimum
of the two scalar endpoints \(s=0,z\).

For the affected AB pair the same formula applies when \(p\ge m\),
with \(r=m/l\). If \(p<m\), then \(m>l\), so (56) forces
\(z<1/4\). Now \(1<r<1.032\), \(x<.256\), \(w<r\), and the
variable part is instead
\[
                      l\{w+Kx+r\cos(z-s)-Rn\}.
\tag{63}
\]
The second derivative of its non-norm part, divided by \(l\), is
\[
 w^{-3}
 +r\,\frac{-\cos z(1-2x^2)-3x\sin z}{w^5}
 \le\frac{1+.256^2-.96875(1-2(.256)^2)}{w^5}<.225.
\tag{64}
\]
On the other hand \(1-r\sin z>.742\) and
\(n^3\le(2r^2)^{3/2}<3.11\). The norm curvature is therefore
\[
                    \frac{R(1-r\sin z)^2}{n^3}
                        >\frac{1.97(.742)^2}{3.11}>.348.
\tag{65}
\]
At \(p=m\), the first derivative jumps downward by
\(p_x(\cos(z-s)-1)\le0\). Thus the complete affected AB curve
is concave on \(0\le s\le z\).

Both affected alternatives reduce to \(s=0,z\).
These equal-angle endpoints are algebraic scalar evaluations;
no original core state or separating witness is asserted at
\(s=z\) outside the original cut.
The companion certifies both \(B_{\rm GA}(z,z)\) and
\(B_{\rm AB}(z,z)\), so no unproved comparison between their
orientations is used on the high interval.

## 11. The high interval: unaffected GA curves

The unaffected pairs are H and B. They have fixed coefficients
as \(s\) varies. We prove concavity only on
\[
                      0\le s\le\min(z,1/4).
\tag{66}
\]
Here \(x<.256\). The basic ratio \(k/l<.82\) may be enlarged
to \(.85\) in (11).
Put \(A=1+.85^2\) and \(D=R/\sqrt A\in(1.507,1.508)\).
The binomial bounds give
\[
 \frac{F_{0,xx}}l
 \le1-D+\{-1.5+1.5D/A\}x^2+1.875x^4<-.507.
\tag{67}
\]
For the last step it suffices that
\(-1.5+1.5(1.508)/A+1.875(.256)^2<0\).

For any fixed pair, (19)--(20) imply
\[
\begin{split}
 V''(\theta)+2xV'(\theta)
 \le q\{-\cos\theta-2x\sin\theta+.7+2.8x
                                      +(1.4x-1/3)\theta\}.
\end{split}
\tag{68}
\]
The expression in braces is convex in \(\theta\in[0,h]\).
Its value at \(h\) minus its value at zero is at most
\[
             1-\cos h-h/3+2x(.7h-\sin h)<.001867.
\]
Consequently
\[
 \frac{d^2}{dx^2}V(z-s)
 \le q\,\frac{-.3+2.8x+.001867}{(1+x^2)^2}<.419q.
\tag{69}
\]
The rational function increases up to \(x=.256\), where the
asserted upper bound is a direct rational comparison.
Since \(q/l<1.1\), (67)--(69) give strict concavity with reserve
at least \(.507-.419(1.1)=.0461\).

The two endpoints of (66) are \(s=0\) and \(s=\min(z,1/4)\).
For \(z\le1/4\) the latter is the equal-angle baseline.
For \(z\ge1/4\) it is one of the actual GA-H or GA-B cut
functions (9a) of the companion.

## 12. The high interval: unaffected AB curves

The unaffected pairs are G and H. Their ratios are at most
\(.84\), and their larger coefficients obey \(q\le l\).
We prove concavity on the actual interval
\[
                      0\le s\le\min(z,.38),\qquad x<.4.
\tag{70}
\]
Using the first row of (22), the analogue of (68) is
\[
 V''(\theta)+2xV'(\theta)
 \le q\{-\cos\theta-2x\sin\theta+.627+2.546x
                                      +(1.254x-.346)\theta\}.
\]
This is convex in \(\theta\). Its endpoint at \(h\) is smaller
than that at zero, because
\[
 1-\cos h-.346h<0,\qquad .627h-\sin h<0.
\]
Thus
\[
 \frac{d^2}{dx^2}V(z-s)
                     \le q\,\frac{-.373+2.546x}{(1+x^2)^2}.
\tag{71}
\]

First take \(0\le x\le.35\). In (11) enlarge \(r\) to \(1.032\),
put \(A=1+1.032^2\), and use
\[
                       1.377<R/\sqrt A<1.378.
\]
The alternating binomial polynomials through degree four for the
first inverse power and through degree three for the second give
\[
                         F_{0,xx}/l<-.376-.35x^2.
\tag{72}
\]
For complete reproduction, with \(y=x^2\le.1225\), the coefficients
after the constant are bounded above by
\[
\begin{split}
 a_2&=-1.5+1.5(1.378)/A,\\
 a_4&=15/8-(15/8)(1.377)/A^2,\\
 a_6&=-35/16+(35/16)(1.378)/A^3,\qquad a_8=315/128.
\end{split}
\]
The cubic \(a_2+a_4y+a_6y^2+a_8y^3\) increases on this interval,
since \(a_4+2a_6(.1225)>0\), and its right endpoint is less than
\(-.3666<-.35\). The constant is less than \(-.377\), which
proves the weaker convenient bound (72).

If the numerator in (71) is negative, both curvatures are
already negative. Otherwise \(q\le l\) allows us to bound the
sum of (71)--(72), after multiplication by \((1+x^2)^2/l\), by
\[
 P(x)=-.749+2.546x-1.102x^2-1.076x^4-.35x^6.
\tag{73}
\]
This polynomial increases on \([0,.35]\), and
\[
                             P(.35)<-.0096.
\tag{74}
\]
For example \(P'(.35)>1.579\); all nonconstant terms in \(P'\)
decrease with \(x\), so this proves its positive derivative on
the entire interval.

For \(.35<x<.4\), \(\tan(1/3)<.35\) implies \(z\ge s>1/3\).
The restricted range (56) improves the basic ratio to \(r<.92\).
The first expression in (11), with \(r=.92\), decreases in \(x\)
through \(.4\). The same positive-square derivative test as in
Section 7 is
\[
 A=1+.92^2,\qquad
                 (A+.4^2)^5>QA^2(1+.4^2)^5.
\]
Therefore
\[
                 F_{0,xx}/l
                 \le F_{0,xx}(.35;\,.92)/l<-.481.
\tag{75}
\]
The last displayed value means the explicit first expression
in (11), evaluated at \(x=.35,r=.92\).
The rational bound in (71) increases through \(x=.4\), and
\[
                \frac{-.373+2.546(.4)}{(1+.4^2)^2}<.480.
\tag{76}
\]
Since its numerator is now positive and \(q\le l\), (75)--(76)
leave a curvature margin of at least \(.001l\).

This proves concavity on (70). Its endpoints are \(s=0\) and
\(s=\min(z,.38)\). When \(z>.38\), the latter is precisely the
actual AB-G or AB-H cut function (9a) of the companion.
No concavity beyond the actual AB cut is asserted.

## 13. The endpoint join and contradiction

At every fixed \(s,z\), Section 3 gives a necessary nonpositive
minimum. On the low interval:

* Section 5 sends every pure positive term to \(s=z\).
* Section 7 sends every pure negative term to \(s=0\) or \(s=z\).
* Section 8 sends every remaining saturated term to \(s=0\);
  its equal-angle comparison retains only the GA assignment.

These are exactly the five low scalar functions (8) of the
companion.

On the high interval, Section 9 removes all saturated terms.
Section 5 again handles pure positive terms.
Section 10 sends the affected pure negative curves to \(s=0,z\);
Sections 11--12 send unaffected curves to \(s=0\) or to the
actual cut when that occurs before \(s=z\).
Thus the only high obligations are the five functions (9) and
four functions (9a) of the companion.

Every required scalar is strictly positive by the companion's
exact whole-interval polynomial certificates. The endpoints
\(z=0\), \(z=1/5\), and the core cuts are included. A feasible
original cycle would have required at least one of these lower
bounds to be nonpositive, a contradiction.

All positive multipliers in this argument apply to the original
witness inequalities. The virtual zeros, single-sign blocks,
and equal-angle endpoints are enlargements or comparisons of
their scalar stress. No new physical packing, frame order,
nonneighbor condition, or original witness at an artificial
endpoint has been assumed.
