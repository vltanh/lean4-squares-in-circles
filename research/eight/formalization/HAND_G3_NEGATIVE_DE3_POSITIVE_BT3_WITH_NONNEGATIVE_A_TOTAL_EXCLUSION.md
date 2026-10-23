# Negative DE3 with positive BT3, arbitrary TD0 and nonnegative A total

## 1. Actual scope and conclusion

Put
\[
 Q=9789/2500,\qquad R=\sqrt Q,\qquad h=7/10,\qquad
 L=1/6,\qquad K=13/12.
\]
Use the actual high-GA G0--G2 boundary-neighbor cycle. H,G,B,D
are sorted outer states with signed tangents respectively
positive, negative, negative and negative. E is a nonpositive
true-core boundary state. A and T may have either sign and
either radial kind. Retain the actual weak witnesses
\[
 HG\in\{0,2\},\quad GA\in\{2,3\},\quad AB\in\{0,2\},
 \quad BT=3,\quad TD=0,\quad DE=3,\quad EH=0.                 \tag{1}
\]
The BT3 error is \(z\ge0\), the DE3 error is \(-s\le0\), and
the actual TD0 and EH0 errors are arbitrary. At A permit no
primary, one nonnegative primary, or two signed primaries with
nonnegative selected total a. Put \(\theta=a+z\). Assume the
actual neighboring inequalities, circles and captured variations
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+\le h.                            \tag{2}
\]
In particular \(0\le s,\theta\le h\). No real-frame order is
assumed.

**Theorem.** No such necessary system exists.

The proof applies after every established reduction preserving
these inputs. It includes s=0, z=0, opposite individual signs
inside the selected A pair, and all weak owner ties.
All terminating decimals below are exact rationals.

## 2. The retained secant force and the one actual D angle

Use the sorted support
\[
 S(f,g)=\max_{0\le b\le c_0}
 \left[f\left(\sqrt{Q-(b+1/2)^2}-1/2\right)+gb\right],
 \quad c_0=\sqrt{Q/2}-1/2,\quad d_0=c_0-1/2,
\]
and full-circle support
\[
 \overline S(f,g)=R\sqrt{f^2+g^2}-(f+g)/2,\qquad
 W(t)=(1+\cos t+|\sin t|)/2.                                  \tag{3}
\]
The actual EH0 inequality gives \(b_E\le a_0-1<.415\), where
\(a_0=\sqrt{Q-1/4}-1/2\). Thus the unchanged true-core E
lies on its flat side \(a_E=7/12\). This is the exact entry
argument in Section 2 of
[the negative-DE concentration theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_ANGLE_CONCENTRATION.md).

For positive k,l,m and a tilt \(\eta\ge0\), set
\[
 q=\sec s,\quad c=m(\cos z+\eta\sin z),\quad
 \sigma_\eta=R\sqrt{1+\eta^2}-(1+\eta)/2.
\]
Give the seven original inequalities the weights
\[
                           (k,l,l,m,c,q,1).                   \tag{4}
\]
The actual E tangent cancels because
\[
 qP_{DE3}(-s)=q a_D-\frac7{12}\tan s+b_E.
\]
The exact T contribution from BT3 and TD0 satisfies
\[
 m(a_T\sin z-y_T\cos z)+cy_T
       =m\sin z(a_T+\eta y_T)\le m\sigma_\eta\sin z.           \tag{5}
\]
The last inequality uses the actual shifted circle and is valid
for both T signs and both radial kinds. The signed A-primary
comparison supplies \(lj(a)\), with the same exact support
function as in
[the A-primary combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md).
Its useful curvature bound is
\[
                  j''(a)\le-\tfrac12\cos a+.92\sin a.         \tag{6}
\]
For \(a\le L\) replace .92 by .915. Its two support branches
have matching first derivatives.

The baseline retaining exact sorted D support is
\[
 \begin{split}
 B(s;a,z)={}&k+2l+mW(z)+c+q+1-m\sigma_\eta\sin z+lj(a)\\
 &-\overline S(1,k)-\overline S(k,l)-\overline S(l,m)-S(q,c)\\
 &+K\tan s-\frac12(q-1).
 \end{split}                                                  \tag{7}
\]
Its change from s=0, with all coefficients fixed, is exactly
\[
 F_c(s)=\frac{\sec s-1}{2}+K\tan s
                         -\{S(\sec s,c)-S(1,c)\}.             \tag{8}
\]
The actual D argument t is the remaining TD0 error, and its
increment is
\[
 \Delta(q,c;t)=c\{W(t)-1\}+S(q,c)-S(q+c\sin t,c\cos t).       \tag{9}
\]
This is one actual angle; the DE primary argument has been
removed by its secant identity.

Both coefficient families below satisfy
\[
 .862\le c\le1.2,\quad 1/2\le k\le\min(c,.85),
                         \quad1\le q\le\sec h<1.308.
\]
The complete signed estimate in
[the secant-D single-angle lemma](HAND_G3_SECANT_D_SINGLE_ANGLE_COMPARISON.md)
therefore gives
\[
 \Delta(q,c;t)\ge
 \begin{cases}
   -\gamma(s)t,&t\ge0,\\
   V_{k,1}(-t),&t\le0,
 \end{cases}
 \qquad\gamma(s)=.545\max(\sec s,c).                          \tag{10}
\]
It also proves that
\[
                  F_c(s)-\gamma(s)(s-\theta)
       \quad\hbox{strictly increases for }\theta\le s\le h.  \tag{11}
\]
In particular the pure positive D alternative is controlled
without an assertion of concavity for its exact diagonal branch.

## 3. The ordinary angular relaxation

For ordered \(p\le r\), use
\[
 \begin{split}
 N_{p,r}(t)&=\sqrt{p^2+r^2+2pr\sin t},\\
 U_{p,r}(t)&=p(\cos t+\sin t-1)-R\{N_{p,r}(t)-N_{p,r}(0)\},\\
 V_{p,r}(t)&=r(\cos t-1)-R\{N_{p,r}(-t)-N_{p,r}(0)\},\\
 \Psi_{p,r}(P,N)&=p(\cos P+\sin P-1)+r(\cos N-1)\\
                 &\hspace{15mm}-R\{N_{p,r}(P-N)-N_{p,r}(0)\}.
 \end{split}                                                  \tag{12}
\]
The ordinary pairs are
\[
 H:(k,1),\quad G:(k,l),\quad
             B:(\min(l,m),\max(l,m)).                        \tag{13}
\]
The original signed errors, after the actual primary
comparisons, have remaining variation
\[
 P\le h-\theta,\qquad N\le h-s,\qquad N-P=\theta-s.             \tag{14}
\]
For two signed A primaries their removed positive variation is
at least their total a; discarding their removed negative
variation only weakens the caps in (14).

Enlarge the one-angle D bound (10) to the separately concave
block \(-\gamma(s)P_D+V_H(N_D)\), allowing both nonnegative
variables. This is valid at the actual one-angle input and then
enlarges only the scalar minimization. All ordinary pairs have
smaller-to-larger ratio at least 1/2. The established separate
concavity and the two simplex concentrations consequently leave
the pure alternatives
\[
 \begin{array}{ll}
 V_i(\theta-s),&s\le\theta,\\
 U_i(s-\theta),\quad-\gamma(s)(s-\theta),&s\ge\theta,
 \end{array}                                                  \tag{15}
\]
ordinary saturated terms \(\Psi_i(h-\theta,h-s)\), and
separated terms
\[
 U_i(h-\theta)+V_j(h-s),\qquad
                -\gamma(s)(h-\theta)+V_j(h-s).                \tag{16}
\]
The D negative index is H; its own mixed endpoint occurs in
(16). All are added to the same baseline (7). No original
frame, circle or separating witness is changed.

We shall use the established uniform norm bounds
\[
 \begin{gathered}
 U_{p,r}(t)\ge-.545rt,\qquad U'_{p,r}(t)>-.72r,\\
 V_{p,r}(h)>.87p,\qquad
 V'_{p,r}(t)>(2/3)r\quad\hbox{if }p/r\ge2/3.
 \end{gathered}                                               \tag{17}
\]
For \(0\le t\le h-L\), the last two derivative constants
improve to \(-.64r\) and \(.78r\), respectively. These are
proved on the complete intervals in Sections 3--4 of the
negative-DE concentration theorem and its cited scalar envelopes.

## 4. The entire low-total interval

Suppose \(0\le\theta\le L\). Choose the positive-BT low family
\[
       k=.5866+.4956\theta,\qquad l=1,\qquad
       m=1.1642-.8874\theta,\qquad\eta=.293.                   \tag{18}
\]
Its proved ranges are
\[
 .5866\le k\le.6692,\qquad
                1.0163\le m\le c\le1.1642.                   \tag{19}
\]
Thus (10)--(11) apply. Negative B is dominated by H throughout
\([0,h]\): (17) gives \(V_B(t)\ge(.87/h)t\), whereas
\(V_H(t)\le1.101t\). On the pure negative interval
\(t\le L\), the sharper coordinatewise comparison gives the
same conclusion. H and G coincide.

### 4.1 Same-block and separated endpoints when \(s\le\theta\)

Set \(P=h-\theta\), \(N=h-s\), \(d=\theta-s=N-P\).
For B the standard same-block comparison applies, since its
coefficient ratio is below 1.5. For H and G the exact difference
from the pure negative term is
\[
       k\{\phi(h-\theta)-1\}+\cos(h-s)-\cos(\theta-s),
       \qquad\phi(t)=\cos t+\sin t.
\]
It increases with s. At zero it is the strictly positive
low-family correction proved in Section 7 of
[the sorted-D low envelope](HAND_G3_POSITIVE_BT3_SORTED_D_LOW_ANGLE_ENVELOPE.md).
Thus every ordinary same-block term dominates its pure term.

The secant in Section 8 of that same note is
\[
                  V_H(h)>V_H(\theta)+.75(h-\theta).            \tag{20}
\]
Concavity implies
\(V_H(h-s)-V_H(\theta-s)\ge V_H(h)-V_H(\theta)\).
Also \(q=\sec s\le\sec L<1.015<m\le c\). Hence every
ordinary positive term and the D linear term are at least
\(-.65P\), by (17),(19). After replacing negative B by H,
(20) discards every separated endpoint with positive reserve
\(.10P\). Only \(V_H(\theta-s)\) remains.

### 4.2 The endpoints when \(s\ge\theta\)

Now \(N\le P\). Every ordinary same-block term dominates its
pure positive term. Indeed \(r/p<1.705\), since
\(.5866(1.705)>1\), and the exact same-block difference has
the lower bound
\[
 p\{[\phi(h)-r/p](1-\cos N)+\phi'(h)\sin N\}>0
                                                        \quad(N>0),
\]
because \(\phi(h)>1.409\), \(\phi'(h)>.12\),
\(\tan(h/2)<.366\), and \(.12-.296(.366)>0\).

For a separated positive H/G term, (17) and
\(V_H(N)>(.541/h)N>.772N\) give a positive excess over
the corresponding pure U term. The same argument applies
to the D linear term, because
\(\gamma(s)\le.545(1.308)=.71286\).
It remains to compare a positive B term with negative H.
The following complete-interval comparison supplies it:
\[
       U_{1,m}(P)-U_{1,m}(P-N)+V_{k,1}(N)>0
                         \quad(0<N\le P\le h).               \tag{21}
\]

Here is a short proof of (21). Concavity makes U' decrease in
its angle; U' also decreases in m, while V' increases in k.
It therefore suffices to check
\[
 E'(N):=U'_{1,1.1642}(h-N)+V'_{.5866,1}(N)>0.
\]
For the positive B norm let \(C_B=-RN_B''\). Its proved
concavity and the positive-square bounds
\[
                 C_B(0)>.741,\qquad C_B(h)>.9615
\]
give \(C_B(t)>.741+.315t\). Also
\(\phi(t)\le1+t-t^2/2\) on \([0,h]\), directly from
\(C_4+S_5\). Thus
\[
 U_B''(t)>-.259-.685t+t^2/2>-.5.
\]
For the H norm define the signed curvature
\(C_H(v)=-RN_{.5866,1}''(v)\) on \([-h,h]\).
For this fixed coefficient its concavity also holds on the
negative half of the interval. To verify the extension, put
\(A=1+.5866^2\), \(B=.5866\), and \(u=-\sin v\in[0,.645]\).
The numerator of \(N''''(v)\), after its positive factor
\(B/N^7\) is removed, is
\[
 B(4A^2-15B^2)-A(A^2-2B^2)u
       +u^2\{B(10B^2-A^2)-2AB^2u\}+B^3u^4.
\]
Exact rational evaluation gives
\[
 \begin{split}
 B(4A^2-15B^2)-.645A(A^2-2B^2)&>.2416,\\
 B(10B^2-A^2)-.645(2AB^2)&>.3621.
 \end{split}
\]
Both bounds remain valid when .645 is replaced by u. Thus
\(N''''>0\) and \(C_H''<0\) on the negative interval too.
The tangent bounds
\(C_H(0)<.437\), \(C_H'(0)>.429\) now give
\(C_H(-N)<.437-.429N\), and hence
\[
 V_H''(N)<-.563-.429N+N^2/2\le-.563.
\]
Consequently E' decreases. At its right endpoint,
\[
                   U_B'(0)>-.502,\qquad V_H'(h)>.513,
\]
so \(E'(h)>.011\). The first is a direct positive-square
bound; the second follows from
\[
 \sqrt{1+.5866^2-2(.5866)\sin h}<.767010,\qquad
 -.6443+\frac{1.9787(.5866)(.7648)}{.767010}>.513.
\]
This proves (21), including its whole coefficient rectangle.
At N=0 equality is harmless.

All saturation has now been removed. For ordinary pure U terms,
\(F_c'(s)>.96\) on the complete domain, so
\[
                       F_c'(s)+U_i'(s-\theta)
                                >.96-.72(1.1642)>0.           \tag{22}
\]
For completeness, on an interior D branch
\[
 F_c'(s)=\sec^2s\left[K+\sin s
                   \left(1-\frac R{\sqrt{1+c^2\cos^2s}}\right)\right].
\]
The ratio is below 1.66 for \(c\ge.862\), and
\(.96y^2-.66y+K-.96>0\) by its negative discriminant.
On a diagonal branch the stronger bound is 1.045, as proved
in the secant-D lemma. The pure D term increases by (11).
Therefore \(s\ge\theta\) reduces to \(s=\theta\).

### 4.3 The two remaining s endpoints and the split

For \(0\le s\le\theta\le L\), D is diagonal because
\(\sec L<1.015<m\le c\). Its gain is independent of c:
\[
                         F_c(s)=K\tan s-d_0(\sec s-1).         \tag{23}
\]
It is concave on \([0,L]\). Indeed \(d_0>.399\),
\(\sec L<1.015\), \(\tan L<.169\) give
\[
 F_c''(s)<2K(1.015)^2(.169)-.399<0.
\]
Thus \(B(0;a,z)+F_c(s)+V_H(\theta-s)\) is concave in s
and reduces to zero or \(\theta\).

At zero the exact positive-BT low-envelope scalar is already
strictly positive for every split, by
[the positive-BT theorem](HAND_G3_POSITIVE_BT3_WITH_TD0_AND_NONNEGATIVE_A_E_TOTALS.md).
At \(s=\theta\), (23) is split independent and the same
low split curvature is below -.8. Only
\((a,z)=(\theta,0),(0,\theta)\) remain. The two new
equal-angle scalar functions are proved positive in Section 8.

## 5. High-total weights and concentration

For \(L\le\theta\le h\), set \(t=(15/8)(\theta-L)\), and use
\[
 \begin{split}
 k&=.670158+.113718t+.006506t^2+.009026t^3+.001t^4,\\
 l&=1.005069-.146411t-.157739t^2+.162815t^3,\\
 m&=1.021248-.168873t-.165381t^2+.175944t^3,\\
 \eta&=.293+.1351(\theta-L).
 \end{split}                                                  \tag{24}
\]
The first three are the already certified high-DE family, with
its base coefficient renamed m. The tilt is fixed when s or
the split \(a+z=\theta\) varies.

The old family bounds give
\[
 \begin{gathered}
 .670158\le k\le.800408,\quad .863<l\le1.005069,\quad
 .862<m\le1.021248,\\
 k<\min(l,m),\quad l<\tfrac32k,\quad .9<m/l<1.017,\\
 p_i/r_i>2/3,\quad r_{\max}<1.066,\quad
                           r_{\max}/r_{\min}<1.16.
 \end{gathered}                                               \tag{25}
\]
The last line refers to the three pairs (13). It also follows
directly from the preceding line, separating \(l\le1\) and
\(l\ge1\).

The new tilt obeys \(\eta\ge\tan(\theta/2)\) on this whole
interval. The difference is concave, so its two endpoint
comparisons suffice. The first is immediate; at h the exact
Taylor reserve is
\[
 \eta(h)C_6(h/2)-S_5(h/2)
                         =\frac{80190036029}{3456000000000000}>0.
\]
For fixed \(\theta\), concavity of \(\cos z+\eta\sin z\)
therefore gives
\[
             1\le\cos z+\eta\sin z<1.065,\qquad0\le z\le\theta.
\]
We used \(\eta<.366\) and \(1+.366^2<1.065^2\). Hence
\[
                 m\le c<1.2,\quad k<c,\quad
                         c/r_{\min}<1.09.                    \tag{26}
\]
Also \(\sigma_\eta<1.425\): this support charge increases
for \(\eta\ge.293\), and the endpoint bound is a positive
square at .366.

Every ordinary same-block term dominates its corresponding
pure term. For separated terms with \(s\le\theta\), the
ordinary comparison follows from (17),(25). To include a
positive D term, use the strengthened derivative consequence
\[
 V_j'(w)>(2/3+.288s)r_j\qquad(0\le w\le h-s).                 \tag{27}
\]
Indeed the established norm curvature gives
\(V_j''<-.288r_j\), and integrate backwards from h.
The function
\( .862(2/3+.288s)-.545\sec s\) is concave. Its endpoint
lower bounds are
\[
                         \frac{89}{3000},\qquad
                         \frac{133447}{3750000}>0,            \tag{28}
\]
using \(\sec h<1.308\) in the second. The alternative c in
\(\gamma(s)\) is paid by
\(2/3-.545(1.09)>0\), from (26). Thus every D-positive
separated term also dominates \(V_j(\theta-s)\), with its
actual negative index j retained.

If \(s\ge\theta\), then \(N\le P\le h-L\). The ordinary
separated comparison uses
\(.78r_{\min}-.64r_{\max}>0\). For a D positive term,
(26)--(28) give \(V_j'(w)>\gamma(s)\) for every negative
index j and \(0\le w\le N=h-s\). Hence
\(V_j(N)>\gamma(s)N\) when N is positive, and the same
comparison holds with equality at N=0.
Ordinary pure U terms increase by (22), and the pure D term
increases by (11). Thus all high-total possibilities reduce to
\[
                  B(s;a,z)+V_i(\theta-s),\qquad
                      i=H,G,B,\quad0\le s\le\theta.           \tag{29}
\]

## 6. Reduce the A/T split before the E angle

Keep \(\theta,s,k,l,m,\eta\) fixed in (29). Each V term is
independent of z. The only varying D part is
\[
                            H_q(c)=c-S(q,c).
\]
It is concave and increasing in c: S is convex, and every
maximizing sorted point has \(b\le c_0<1\), so
\(H_q'\ge1-c_0>0\). Its composition with
\(c(z)=m(\cos z+\eta\sin z)\) is concave, since c is concave
and positive. This argument covers the exact support transition
without a differentiability assumption there.

The remaining split second derivative is at most
\[
 m\{-\tfrac12\cos z+.925\sin z\}
       +l\{-\tfrac12\cos a+.92\sin a\}
 <l\{-.45(1.7648)+1.0175(.7)\}=-.08191l.                     \tag{30}
\]
Use (6), \(.9<m/l<1.1\), \(a+z\le h\), and
\(\cos a+\cos z\ge1+\cos h>1.7648\).
Consequently (29) is concave on the entire split interval.
Only the A endpoint \((a,z)=(\theta,0)\) and the T endpoint
\((0,\theta)\) remain.

At the A endpoint, \(c=m\), and every scalar in (29) is
identical to the A endpoint scalar of the existing negative-DE,
positive-TD2 proof. The tilt has no effect when z=0. Sections
8--9 of its concentration proof and the exact endpoint
certificates therefore prove all of these functions positive.

For the T endpoint, replace S by its full-circle upper bound.
This only lowers the stress. Write
\[
                   c_T=m(\cos\theta+\eta\sin\theta).
\]
The next section proves that each resulting pure V function
has its minimum at \(s=0\) or \(s=\theta\). Section 8 certifies
the resulting four T endpoint functions.

## 7. The whole high-T E-angle reduction

### 7.1 Shape and correlated coefficient bounds

Set \(x=\tan s\), \(w=\sqrt{1+x^2}\), \(d=\theta-s\).
Up to constants independent of s, a full-circle function in
(29) has the form
\[
 f(x)=F_0(x)+V_{p,r}(d),\qquad
                  F_0(x)=w+Kx-R\sqrt{w^2+c_T^2}.              \tag{31}
\]
The coefficients \(p,r,c_T\) remain fixed while x varies.
Direct differentiation gives
\[
 \begin{split}
 F_{0,xxx}&=3x\left\{
 \frac{R(1+c_T^2)}{(1+c_T^2+x^2)^{5/2}}
                     -\frac1{(1+x^2)^{5/2}}\right\},\\
 f'''&=F_{0,xxx}+
 \frac{-V'''(d)-6xV''(d)+2(1-3x^2)V'(d)}{(1+x^2)^3}.
 \end{split}                                                  \tag{32}
\]

The following new coefficient bounds hold on their entire
intervals:
\[
 \begin{gathered}
                    c_T<1.057\qquad(L\le\theta\le h),\\
 c_T\le1.0765-.305\theta
                              \qquad(.55\le\theta\le h).
\end{gathered}
\tag{33}
\]
For exact verification replace c_T by
\(C=m\{C_{12}(\theta)+\eta S_9(\theta)\}\).
Its derivative has whole-interval upper aggregate below -.176,
and \(C(L)<1.057\). On the late interval, put
\(D(\theta)=1.0765-.305\theta-C\). Its second derivative
has aggregate below -.925; its two endpoints exceed .00018
and .000048. Concavity proves the second bound in (33).
All these are coefficient sums of explicitly specified
polynomials; use the aggregate formula in Section 8.

### 7.2 The range \(s\le.55\)

The first term in (32) satisfies
\[
                             F_{0,xxx}>-.24.                  \tag{34}
\]
It decreases with c_T here, so use c=1.057. With
\(y=\sin s<.523\), positive squaring gives
\[
 \frac R{(1+c^2)^{3/2}}>.6423,\qquad
                       \frac{c^2}{1+c^2}>.5276.
\]
The positive binomial series therefore gives the polynomial
lower bound for \(F_{0,xxx}+.24\)
\[
 P(y)=.24+3y(1-y^2)^2
 \left\{-.3577+\frac52(.6423)(.5276)y^2
                       +\frac{35}{8}(.6423)(.5276)^2y^4\right\}.
                                                                    \tag{35}
\]
Expand \(P(.3+u)=\sum_{j=0}^9 a_ju^j\), and put
\[
 A_2=a_2-\sum_{j=3}^9|a_j|(.3)^{j-2}.
\]
Exact rational expansion gives
\[
                  A_2>2.0557,\qquad
                  a_0-a_1^2/(4A_2)>.0348.                    \tag{36}
\]
Since \(|u|\le.3\) contains the required y interval, (36)
proves (34) without an angle subdivision.

The norm bounds used in the old high-DE derivative argument
remain valid: \(V''<-.288r\), \(V'''<.312r\),
\(V'>(2/3)r\), and \(r>.862\). For
\(x\le1/\sqrt3\), the second numerator in (32) exceeds
\[
                   r(4/3-.312+1.728x-4x^2)>.685r.
\]
As \((1+x^2)^3\le64/27\), it exceeds .24 after division:
\(.685(.862)(27/64)>.24\).
For \(1/\sqrt3\le x\le\tan(.55)<.614\), one has \(d<.177\).
The sharper old norm bounds make that numerator greater than
\(.894r\), and
\(.894(.862)/(1+.614^2)^3>.24\).
These are exactly the two norm estimates in Section 9.1 of the
old concentration proof; only its adverse D bound has changed
from -.2 to -.24. They prove \(f'''>0\) on this whole range.

### 7.3 The range \(s\ge.55\)

Here \(x>.613\), \(d\le.15\), and every ordinary larger
coefficient r is at most 1, by (24)--(25). The old norm
calculation gives the lower numerator
\[
 rA_3(x),\qquad A_3(x)=47/15+1.8x-8.4x^2.                     \tag{37}
\]
The additional d terms are nonnegative; the exact expression
and sign check are (59) of the old concentration proof.
Also \(F_{0,xxx}>0\): positive squaring at
\(x=.613,c=.909\) proves this, with the ratio increasing
in x and decreasing in c.

If \(A_3\ge0\), these facts finish the proof. Otherwise use
\(r\le1\), the correlation (33), and define
\[
 \begin{gathered}
 c_*(x)=1.0765-.305\arctan x,\qquad
 T(x)=\frac{R(1+c_*^2)(1+x^2)^3}{(1+x^2+c_*^2)^{5/2}},\\
 H(x)=3x\{T(x)-\sqrt{1+x^2}\}+A_3(x).
 \end{gathered}                                               \tag{38}
\]
Then \((1+x^2)^3f'''\ge H(x)\). On the actual late range,
\[
       .613<x<.843,\quad .863\le c_*\le.90875<.909,\quad
                              T<1.83,\quad T'<3.              \tag{39}
\]
To verify the derivative, the first term of
\[
 \frac{T'}T
 =x\left(\frac6{1+x^2}-\frac5{1+x^2+c_*^2}\right)
 +c_*c_*'\left(\frac2{1+c_*^2}-\frac5{1+x^2+c_*^2}\right)
\]
is below 1.35. After clearing positive denominators it suffices
to check
\[
 1.35(1+x^2)(1+x^2+.827)-x(1+x^2+6(.827))>.1274,
\]
whose exact whole-interval coefficient aggregate gives the
displayed bound. The second term is below .257, since it is
at most
\[
 \frac{.305(.909)}{1+.613^2}
   \left\{\frac5{1+.613^2+.863^2}-\frac2{1+.909^2}\right\}<.257.
\]
Positive squaring gives \(T<1.83\) at \(x=.843,c=.863\),
and \(1.83(1.35+.257)<3\). Thus
\[
 H'<3(1.83-1.17)+3(.843)(3-.52)+1.8-16.8(.613)<-.24.
\]
At the right endpoint, \(c_*(\tan h)=.863\), so the old
far-end comparison is unchanged:
\[
 \begin{split}
 H(\tan h)>{}&3(.842288)(1.82777-1.30746)+47/15\\
              &+1.8(.842288)-8.4(.842289)^2>.0047.
 \end{split}                                                  \tag{40}
\]
The bounds \(.842288<\tan h<.842289\), \(\sec h<1.30746\)
and \(T(\tan h)>1.82777\) are direct Taylor and positive-square
comparisons. Therefore H is positive, completing \(f'''>0\)
also on the late range.

### 7.4 The endpoint derivative and the two s values

Section 8 supplies two exact whole-total polynomial certificates
for
\[
 F_{0,s}(\theta)<\frac{Rk}{\sqrt{1+k^2}},\qquad
 F_{0,s}(\theta)<\frac{Rkl}{\sqrt{k^2+l^2}}.                  \tag{41}
\]
The B initial negative slope is no smaller than the latter,
because \(m\ge k\). Hence every f in (31) has negative
first derivative at its right endpoint \(x=\tan\theta\).
By (32)--(40), that first derivative is convex. It can be
positive only on an initial interval; once nonpositive, it
stays nonpositive up to the right endpoint. Thus f has its
minimum at \(s=0\) or \(s=\theta\).

This leaves the three s=0 pure V functions and the common
equal-angle baseline at the T split endpoint.

## 8. Exact new scalar and derivative certificates

Use the alternating polynomials \(S_j,C_j\), the rational
upper constants
\[
 \overline R=1.978787508,\quad\overline a=1.414575672,\quad
 \overline c=.899214066,\quad\overline\sigma_0=1.415477291,
 \qquad \underline R=1.978787,\quad\eta_0=.293,
\]
and
\[
                         J(t)=\frac{C_{10}(t)-1}{2}
                              +(1/2-\overline a)S_9(t).       \tag{42}
\]
All positive-square bounds for these constants are already
proved in the positive-BT theorem.

For each positive squared-norm upper polynomial P, in its
native variable x, set \(P_0=P(0)\). Choose the unique positive
multiple \(\rho\) of \(10^{-12}\) such that
\[
 (\rho-\tfrac12 10^{-12})^2\le P_0
                         <(\rho+\tfrac12 10^{-12})^2,
\]
and define the rational cubic
\[
 w=([P]_{\le3}-P_0)/P_0,\qquad
                    r=\rho[1+w/2-w^2/8+w^3/16]_{\le3}.      \tag{43}
\]
This is an integer prescription by rational squaring. No
approximation property is assumed for the resulting mass.
For a nonradical lower polynomial A use the numerator
\[
 \mathcal N(A;\mathbf P)=2A\prod_i r_i
           -\overline R\sum_i(P_i+r_i^2)\prod_{j\ne i}r_j.    \tag{44}
\]
Positive masses imply that the associated scalar is at least
\(\mathcal N/(2\prod_i r_i)\).

### 8.1 The two low equal-angle endpoints

Take native \(x=\theta\in[0,L]\), weights (18), and define
\[
 \begin{split}
 A_A={}&2k+\frac{11}{2}-\overline c
                         +(\tfrac52-\overline c)m+J(\theta),\\
 A_T={}&2k+\frac{11}{2}-\overline c\\
       &+m\{1+(\tfrac32-\overline c)C_{10}(\theta)
          +(\tfrac12+\eta_0(1-\overline c)-\overline\sigma_0)
                                                   S_9(\theta)\}.
 \end{split}                                                  \tag{45}
\]
These are the same exact sorted-D baseline polynomials as in
the positive-BT low proof. Their whole-interval aggregates
exceed 7.4. Multiplying the desired equal-angle stress by
\(\cos\theta>0\), use
\[
 A=C_{10}(\theta)A_{A\text{ or }T}
          +K S_{11}(\theta)
          +(\overline c-1/2)(C_{10}(\theta)-1),               \tag{46}
\]
and squared norms
\[
 C_{12}(\theta)^2(1+k^2),\quad
 C_{12}(\theta)^2(1+k^2),\quad
 C_{12}(\theta)^2(1+m^2).                                    \tag{47}
\]
Formula (46) is exactly the lower-bound form of (23) after
multiplication. For both endpoints every mass exceeds 1.15,
and the whole-interval coefficient lower bound is
\[
                             \mathcal N>.0017.                \tag{48}
\]
Both numerator degrees are 32.

### 8.2 The four high T endpoint functions

Use native \(x=\theta-L\in[0,h-L]\) and (24). Put
\[
 w_\eta=\frac{\eta^2-\eta_0^2}{1+\eta_0^2},\qquad
 \sigma_*=(\overline\sigma_0+(1+\eta_0)/2)
       (1+w_\eta/2-w_\eta^2/8+w_\eta^3/16)-(1+\eta)/2.
                                                                    \tag{49}
\]
Since \(w_\eta\ge0\), the cubic Taylor upper bound for the
square root gives \(\sigma_*\ge\sigma_\eta\). Define
\[
 \begin{gathered}
 C=m\{C_{12}(\theta)+\eta S_9(\theta)\},\\
 A_T=2k+3l+3+m\{1+2C_{10}(\theta)
                     +(1/2+3\eta/2-\sigma_*)S_9(\theta)\},\\
 P_H=1+k^2,\quad P_G=k^2+l^2,\quad
                 P_B=l^2+m^2,\quad P_D=1+C^2.
 \end{gathered}                                               \tag{50}
\]
The sine coefficient is negative throughout. These are
pointwise lower and upper replacements in the required
directions. In particular the aggregate of \(A_T-1\) exceeds
7.98.

For an s=0 endpoint indexed H,G,B, respectively, replace its
squared norm by
\[
          P_H-2kS_{11}(\theta),\quad
          P_G-2klS_{11}(\theta),\quad
          P_B-2lmS_{11}(\theta),                             \tag{51}
\]
and add to A_T respectively
\[
 C_{10}(\theta)-1,\quad l\{C_{10}(\theta)-1\},\quad
              q_*\{C_{10}(\theta)-1\},\qquad
                       q_*=l+.15(h-\theta).                 \tag{52}
\]
The old coefficient-family proof gives \(q_*\ge\max(l,m)\).

For the equal-angle endpoint, multiply its full-circle stress
by \(\cos\theta>0\). Use
\[
 A=C_{10}(\theta)(A_T-1)+1+K S_{11}(\theta),                   \tag{53}
\]
and squared norms
\[
 C_{12}(\theta)^2P_H,\quad C_{12}(\theta)^2P_G,\quad
 C_{12}(\theta)^2P_B,\quad1+C^2C_{12}(\theta)^2.               \tag{54}
\]
Every mass in (51)--(54) exceeds .69. The exact complete
certificates for their numerators are:

| T endpoint | Whole-interval certificate |
|---|---|
| s=0, H | \(\mathcal N(0)>.00079\), and \((\mathcal N(x)-\mathcal N(0))/x>.13\) |
| s=0, G | \(\mathcal N>.0014\) |
| s=0, B | \(\mathcal N>.069\) |
| \(s=\theta\) | \(\mathcal N>.0024\) |

The first three degrees are 39; the last degree is 63. Together
with (48), these prove all six new scalar functions.

### 8.3 The two right-endpoint derivative comparisons

Let \(P=1+k^2\), \(b=k\) for H, or \(P=k^2+l^2\),
\(b=kl\) for G. Put
\[
 D=1+C^2C_{12}(\theta)^2,\quad
 A_P=P+r_P^2,\quad A_D=D+r_D^2,                               \tag{55}
\]
where the two cubic masses are given by (43). Both exceed
1.15. The following explicitly defined polynomials are positive:
\[
 \begin{split}
 M_i={}&2\underline R\,b\,C_{10}(\theta)^2 A_Dr_P
               +2\underline R S_{11}(\theta)A_Pr_D\\
       &-(K+S_9(\theta))A_PA_D,\\
                         M_H&>.518,\qquad M_G>.040.
 \end{split}                                                  \tag{56}
\]
The degrees are 81 and 84. To see why (56) suffices, use
\(A_P/(2r_P)\ge\sqrt P\) and
\(A_D/(2r_D)\ge\sqrt D\), clear their positive denominators,
and read (56) as the lower bound for
\[
 \frac{Rb\cos^2\theta}{\sqrt P}
       +\frac{R\sin\theta}{\sqrt{1+c_T^2\cos^2\theta}}
                                     -K-\sin\theta>0.
\]
Rearrangement is exactly (41).

### 8.4 Reproducing the finite rational bounds

For \(F(x)=\sum_n f_nx^n\) on the entire native interval
\([0,D]\), use
\[
 a_{n0}=4^{-n}\binom{2n}{n},\qquad
 a_{nj}=2\,4^{-n}\binom{2n}{n-j}\ (1\le j\le n),\qquad
 b_j=\sum_n f_nD^na_{nj}.
\]
Then
\[
                         b_0-\sum_{j>0}|b_j|\le F(x)
                                      \le b_0+\sum_{j>0}|b_j|.\tag{57}
\]
These are the shifted Chebyshev identities. They prove every
mass, coefficient-range, numerator and derivative-polynomial
bound stated above. For the H numerator use its exact first
quotient after subtracting the constant; for (36) use the
displayed centered power sum and completion of the square.
All polynomials, masses and intervals have been specified
explicitly. Each coefficient transform covers a whole analytic
interval; there is no mesh or generated coefficient-row premise.

## 9. Completion

Section 4 removes every low-total saturation and positive
remainder. Its s=0 functions are already positive by the
positive-BT low proof, and its two equal-angle endpoints are
positive by (48).

Sections 5--6 reduce the high-total problem to A/T split
endpoints while retaining the actual sorted D support. The A
functions are exactly the previously proved negative-DE scalar
functions. Section 7 reduces every T pure-negative function to
the two intrinsic E-angle endpoints; (51)--(56) supply the
required scalar and derivative certificates.

Thus every allowed scalar lower bound has strictly positive
weighted demand minus support, contradicting the original
separating inequalities. This proves the theorem for arbitrary
actual TD0 and EH0 errors, either HG owner, all selected
nonnegative A totals and all weak ties.

The only enlargements are of scalar angular domains and circle
support bounds. Every geometric state, weak witness and actual
circle remains in the original necessary system. No local
T-only transport, sampled minimum, optimizer certificate, Lean
compilation or CI is used.
