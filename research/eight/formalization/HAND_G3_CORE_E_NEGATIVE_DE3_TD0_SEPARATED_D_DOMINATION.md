# Eliminating separated positive D angles in the negative-DE TD0 extension

## 1. Scope and notation

This lemma supplies the fourth-block comparison for
[the negative-DE TD0 theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_A_TD0_EXCLUSION.md).
Use
\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 h=\frac7{10},\quad L=\frac16,\quad T=h-L=\frac8{15}.
\tag{1}
\]
Fix \(L\le a\le h\), and use the high coefficient family of
[the negative-DE scalar theorem](HAND_G3_CORE_E_NEGATIVE_DE3_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md),
with its total parameter equal to a and its TD2 parameter set
algebraically to zero. Thus \(m=c\), not an asserted original
TD2 witness. Explicitly, for \(t=(a-L)/(8/15)\),
\[
\begin{split}
 k&=.670158+.113718t+.006506t^2+.009026t^3+.001t^4,\\
 l&=1.005069-.146411t-.157739t^2+.162815t^3,\\
 c&=1.021248-.168873t-.165381t^2+.175944t^3.
\end{split}
\tag{2}
\]
The scalar theorem proves
\[
\begin{gathered}
 .670158\le k\le.800408,\quad .863<l<1.006,\quad
 .862<c<1.022,\quad .9<c/l<1.017,\\
 c\le1.073-.3a.
\end{gathered}
\tag{3}
\]
The last correlated bound is not needed for the estimates here.

For \(0\le s\le h\), put \(w=\sec s\). The ordinary pairs are
\[
 H=(k,1),\quad G=(k,l),\quad
 B=(\min(l,c),\max(l,c)),\quad
 D=(p_D,q_D)=(\min(c,w),\max(c,w)).
\tag{4}
\]
Define
\[
\begin{split}
 N_{p,q}(x)&=\sqrt{p^2+q^2+2pq\sin x},\\
 U_{p,q}(x)&=p(\cos x+\sin x-1)-R(N_{p,q}(x)-N_{p,q}(0)),\\
 V_{p,q}(x)&=q(\cos x-1)-R(N_{p,q}(-x)-N_{p,q}(0)).
\end{split}
\tag{5}
\]
The D coefficients are held fixed when differentiating U in its
angular argument. The allowed total positive and negative
masses at the saturated endpoint are
\[
                         P=h-a,\qquad N=h-s.
\tag{6}
\]

The conclusions, for each \(j\in\{H,G,B\}\), are
\[
\begin{array}{ll}
 U_D(P)+V_j(N)\ge V_j(N-P)+.057P,&s\le a,\\[2mm]
 U_D(P)+V_j(N)\ge U_D(P-N)+.027N,&s\ge a.
\end{array}
\tag{7}
\]
A comparison is strict when its displayed mass is positive.
Thus a separated positive D angle introduces no additional
scalar endpoint certificate.

## 2. Two norm derivative comparisons

Write \(u=\sin x\), \(v=\cos x\). Direct differentiation gives
\[
\begin{split}
 U'_{p,q}(x)&=p(v-u)-\frac{Rpqv}{\sqrt{p^2+q^2+2pqu}},\\
 V'_{p,q}(x)&=-qu+\frac{Rpqv}{\sqrt{p^2+q^2-2pqu}}.
\end{split}
\tag{8}
\]
Both U and V are concave on \([0,h]\), as proved in the
previous whole-angle concentration lemmas.

For V, its derivative increases with p whenever \(q>pu\):
\[
 \partial_p V'_{p,q}(x)
   =\frac{Rq^2v(q-pu)}{(p^2+q^2-2pqu)^{3/2}}>0.
\tag{9}
\]
For fixed p, its second q derivative has the sign of
\[
                  2u(p^2+q^2)-pq(3+u^2).
\tag{10}
\]
In particular, at either \(x=T\) or \(x=h\), and with
\(p=.670158\) or \(p=.721\), it is negative throughout
\(.863\le q\le1.006\). Indeed,
\[
 \frac{p^2+q^2}{pq}<2.17,\qquad u<.645,\qquad
                         2(.645)(2.17)<3.
\tag{11}
\]
So \(V'_{p,q}(x)\), as a function of q on this interval, is
concave and has its minimum at a q endpoint.

The resulting endpoint bounds are
\[
\begin{array}{c|c|c}
 p&x&V'_{p,q}(x)\text{ for every }q\in[.863,1.006]\\ \hline
 .670158&T&>.79\\
 .670158&h&>.677\\
 .721&h&>.77 .
\end{array}
\tag{12}
\]
These are rational Taylor comparisons at the two endpoints
proved sufficient by (10). To make their arithmetic explicit,
use \(1.978787<R<1.978788\), \(C_6(x)\le\cos x\), and
\(S_7(x)\le\sin x\le S_9(x)\). Upper bounds for the respective
negative-argument norms, in q order \(.863,1.006\), are
\[
\begin{array}{c|c|cc}
p&x&\sqrt{p^2+.863^2-2p(.863)\sin x}
&\sqrt{p^2+1.006^2-2p(1.006)\sin x}\\ \hline
.670158&T&.778339&.880701\\
.670158&h&.669865&.769748\\
.721&h&.680380&.772879
\end{array}
\tag{13}
\]
Each follows by squaring positive quantities using \(S_7(x)\).
Substitution in (8), with the lower cosine and upper negative
sine term, proves all of (12). The narrowest value in the
second row remains greater than .67746.

For B, \(r=p_B/q_B>.9\) and \(q_B>.862\). At a fixed x the
normalized positive term
\[
               \frac{r}{\sqrt{1+r^2-2r\sin x}}
\]
increases with r, since \(1-r\sin x>0\). Consequently
\[
                    V'_B(T)>.95,\qquad V'_B(h)>.89.
\tag{14}
\]
At \(r=.9\), the upper normalized norms at T and h are
.945975 and .806480. The same Taylor substitutions give
(14), after multiplying the positive normalized lower bound
by .862.

## 3. The case \(s\ge a\)

We first prove
\[
                       U'_D(x)>-.763
                         \qquad(0\le x\le T).
\tag{15}
\]
Concavity reduces to x=T. The derivative in (8) decreases
with q, so raise \(q_D\le\sec h<1.308\) to 1.308.
Also \(p_D\le c<1.022\). At q=1.308, the derivative with
respect to p is
\[
 \phi'(T)-R\cos T\,
   \frac{1+r\sin T}{(1+r^2+2r\sin T)^{3/2}},\qquad r=p/q.
\tag{16}
\]
The fractional term decreases with r. At the largest possible
\(r=1.022/1.308\) it is greater than .37. Since
\(\phi'(T)<.354\) and \(R\cos T>1.7\), (16) is negative.
It therefore suffices to substitute \(p=1.022,q=1.308\)
in (8). The positive-argument norm is greater than 2.028447;
using \(C_6(T),C_8(T),S_7(T),S_9(T)\) gives
\[
                        U'_{1.022,1.308}(T)>-.763.
\tag{17}
\]
All denominator comparisons are by positive squaring.

For H and G, (9)--(12) imply \(V'_j(x)>.79\) on
\(0\le x\le T\); H's coefficient q=1 is included in the
same interval. Equation (14) proves the stronger B estimate.
When \(s\ge a\), both \(P\) and \(N\) are at most T, and
\(P-N=s-a\ge0\). With the actual s and D coefficients fixed,
integrate (15) in the angular argument:
\[
 U_D(P)-U_D(P-N)>-.763N,\qquad V_j(N)>.79N
\]
for \(N>0\). This proves the second line of (7), including
its non-strict zero-mass endpoint.

## 4. The case \(s\le a\)

The universal whole-interval U bound is
\[
                       U_D(P)\ge-.545q_D P.
\tag{18}
\]
Its hypotheses hold because \(p_D/q_D> .862/1.308>1/2\).
Here
\[
                         q_D\le\max(c,\sec a).
\tag{19}
\]
Use two broad coefficient ranges to compare this cost with
the negative gain.

For \(L\le a\le.4\), \(\sec a<1.086\) and \(c<1.022\), so
\[
                         .545q_D<.592.
\tag{20}
\]
Equations (9)--(12) give \(V'_H(h),V'_G(h)>.677\).
For \(.4\le a\le h\), the positive coefficients of k in
the parameter t show
\[
 k\ge k(.4)=.7219473897705078125>.721.
\]
Hence (9)--(12) give \(V'_H(h),V'_G(h)>.77\), while
\[
                         .545q_D<.545(1.308)<.713.
\tag{21}
\]
The B derivative is greater than .89 in either range by
(14). Concavity of V makes these lower derivative bounds
valid at every argument between zero and h.

Now \(N-P=a-s\ge0\). Integrating from \(N-P\) to N shows
\[
 V_j(N)-V_j(N-P)>.677P
\]
in the first range, and \(>.77P\) in the second, for
\(P>0\). Combined with (18)--(21), the respective reserves
are greater than .085P and .057P. This is the first line of
(7), including its zero-mass endpoint.

## 5. Exact join to the three-block concentration proof

The original TD0/D force is
\[
                  (w+c\sin d_{TD},\ c\cos d_{TD}).
\tag{22}
\]
For a positive D angle its exact full-circle coefficient is
c in front of \(\phi(d)-1\); lowering that coefficient to
\(p_D=\min(c,w)\) gives U_D. For a negative D angle its
coefficient is c in front of \(\cos d-1\); raising it to
\(q_D=\max(c,w)\) gives V_D. Thus the ordinary fourth block
is a valid relaxation of the actual force, with no change
of its TD0 owner.

After the four-block simplex concentration, the possibilities
are pure U/V terms, same-block terms, and separated terms.
The main TD0 note proves \(V_D\ge V_H\). Every negative D
allocation can therefore be replaced by an H negative
allocation in a lower envelope. The D same-block term
dominates its own pure term: \(q_D/p_D<1.52<1.7\) and
\((q_D/p_D)\sin h<1\), so the two standard same-block
comparisons apply. For a positive excess its pure survivor
is U_D; for a negative excess its survivor is at least V_H.

If D carries the separated positive mass, (7) removes that
alternative pointwise, with all coefficient dependence on s
retained. Every remaining ordinary term belongs to the
unchanged H/G/B envelope. Its baseline is exactly the old
negative-DE high baseline at the pure-A split \(z=0\),
including the full D-circle support and its secant factor.
The D-negative replacement may put both scalar indices on H.
The old balanced separated comparison allows coincident
indices: its U and V estimates are independent. This is a
virtual scalar allocation, not a new original same-block
witness.
The original three-block s-concentration proof therefore
applies to these survivors without any new assumption.
In particular its old pure-U terms increase for \(s\ge a\)
and hence are minimized at \(s=a\); its old pure-V terms
reduce to \(s=0,a\).

The sole extra survivor is the pure term
\[
                  F_0(s)+U_D(s-a),\qquad a\le s\le h,
\tag{23}
\]
with its same constant baseline additions. Its separate
concavity and endpoint proof belong to the main TD0 note.
Thus the new fourth-block proof requires only its additional
\(s=h\) certificate; it does not silently reuse a three-block
theorem before the D allocations have been removed.
