# The three remaining same-sign secondary owners, on both whole angle halves

This note proves all six angle halves of the original outer/outer owners
\[
 (i,\sigma,\tau,j)=(2,-,-,3),\ (4,-,-,3),\ (6,+,+,1)
\]
for the short word 0010111. Every terminating decimal denotes an exact
rational. For each original weak separator, on the entire range
\(|\phi-\pi/2|\le .7\), its corrected cost satisfies
\[
                              C>.898.                       \tag{1}
\]
All nearest-axis ties and state endpoints are included.

The companion HAND_SHORT_WORD_SAME_SIGN_PRIMARY_COMPLETE_WITHOUT_TABLES.md
proves the three paired primary owners. These two notes replace the last
six near-aligned owner regimes and all their scalar-table tails. Together
with the earlier successors they finish all 96 original outer-quarter
angle halves. The mixed and zero-quarter components of the short word
remain separate dependencies.

## 1. Exact data and the original owner

Set
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad
 a(y)=\sqrt{Q-(y+1/2)^2}-1/2,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=a(0),\quad b_0=1-d.
\]
The two outer states satisfy \(a=a(b), A=a(B)\), \(0\le b,B\le d\).
For either outer coordinate write
\[
 r(y)=\frac{y+1/2}{a(y)+1/2},\quad
 r'(y)=\frac Q{[a(y)+1/2]^3},\quad
 r''(y)=\frac{3Q(y+1/2)}{[a(y)+1/2]^5}.
\]
Reflection and reversal of original axis 3 in the first two cases gives
exactly
\[
 C=\pi/2+x+c+pa+qb-PA-tB,
 \qquad b+A\cos x+B\sin x\ge W,
 \quad W=\frac{1+\cos x+|\sin x|}{2}.                       \tag{2}
\]
The three normalized tuples \((c,p,q,P,t)\) are
\[
\begin{aligned}
 &( -.53489,\ .33147,\ 1.1336,\ -.09133,\ .88074),\\
 &( -.53062,\ .20967,\ .83048,\ -.19335,\ .76744),\\
 &( -.20704,\ .21826,\ .83472,\ 0,\ .94766).
\end{aligned}                                               \tag{3}
\]
They are literal adjacent role-label differences. The reflection rule
is \((p,q,P,t,\sigma,\tau)\mapsto(-P,t,-p,q,-\tau,-\sigma)\),
and it preserves the corrected cost and the angle.

For all three tuples, \(q-p>0\) and \(Pr(B)-t<0\). Thus the source
cost increases with \(b\) and the target cost decreases with \(B\).
At alignment the contact \(b+A=1\) is the same as the companion primary
contact after exchanging the states. Section 2 of that companion proves
its whole aligned minimum greater than .8981, by monotonicity for rows 2
and 3 and one strongly convex scalar for row 1. That section has no
angle or state table. We shall use
\[
                      C\big|_{x=0}>.8981.                  \tag{4}
\]

The elementary bounds used here are
\[
\begin{gathered}
1.414575671<a_0<1.414575672,\quad
.899214065109<d<.899214065110,\quad R<1.978788,\\
\cos u>.764,\quad 0\le\sin u<.645\qquad(0\le u\le .7),
\quad a_0+1/2<1.915.
\end{gathered}                                               \tag{5}
\]
All radical bounds follow by positive squaring. Point trigonometric
comparisons use adjacent alternating Taylor sums.

## 2. The whole positive half for all three tuples

First, the independent arc minima give everywhere
\[
 C\ge\pi/2+x+c+pa_0-(P+t)d>.79494+x.                        \tag{6}
\]
Indeed \(pa+qb\) increases with \(b\), while \(-PA-tB\) decreases
with \(B\). The smallest of the three constants in (6) is the first
tuple's value, which exceeds .79494 by direct substitution.
Consequently any counterexample to (1) must have \(x<.108\).
This confinement follows from an analytic lower bound, not an angle mesh.

On \(0\le x\le .108\), reduce the source to its least feasible coordinate.
If that coordinate is zero with slack, increase \(B\), decreasing cost,
until contact. To see that contact is reached, write
\[
 b_c=\frac12+(\tfrac12-A)\cos x+(\tfrac12-B)\sin x.
\]
It increases strictly with \(B\), because
\[
 (b_c)_B=D/U>0,\quad U=A+1/2,\ V=B+1/2,\quad
 D=V\cos x-U\sin x
 >\tfrac12\cos(.108)-1.915\sin(.108)>0.
\]
At \(B=0\) the contact coordinate is negative; at \(B=d\) it is positive
and less than \(d\). These assertions follow throughout the strip from
monotonicity and the endpoint expressions
\(b_c(d,x)=1/2+(1/2-d)(\cos x+\sin x)\).
Thus the contact domain has just the two coordinate boundaries \(b=0\)
and \(B=d\), in addition to its angle endpoints.

On contact put \(H=tU-PV>0\). At an interior stationary point in \(B\),
\[
 q-pr(b)=H/D,\qquad
 C_x=1-H\left(1-\frac{\cos x-\sin x}{D}\right).              \tag{7}
\]
The same formula for the cost derivative holds along the moving
boundary \(b=0\), by implicit differentiation.
Here \(D<1.4\), \(\cos x-\sin x>.885\), and \(H<1.82\).
For the first two tuples the latter bound follows from
\(H\le R\sqrt{t^2+P^2}<1.82\); for the third, use
\(H=tU<.94766(1.915)<1.82\).
If the parenthesis in (7) is nonpositive, the derivative is at least 1;
otherwise
\[
 C_x>1-1.82(1-.885/1.4)>.33.                                \tag{8}
\]
On \(B=d\), the boundary derivative is
\[
 1+(q-pr(b))(1/2-d)(\cos x-\sin x)>1-1.2(.4)>0.
\]

Apply the compact minimum principle to this full contact strip. An
interior target minimum has (7); the zero-source boundary has the same
positive derivative, and the target-diagonal boundary has the preceding
positive derivative. In each case a positive angle can be decreased to
lower the cost, including at the upper angle endpoint. Therefore the
minimum is at alignment, where (4) applies. In combination with (6),
this proves the entire positive half for all three original owners.

## 3. A decreasing-target theorem for rows 2 and 3 on the negative half

Write \(x=-u\), \(s=\sin u,k=\cos u\), \(0\le u\le .7\).
The contact coordinate is
\[
 b_c=\frac12+(\tfrac12-A)k+(\tfrac12+B)s.                    \tag{9}
\]
It increases with both \(B\) and \(u\). Its derivative in the target is
\[
 C_B=(q-pr(b))(r(B)k+s)+Pr(B)-t.                             \tag{10}
\]
We prove \(C_B<0\) on the whole physical contact domain for rows 2 and 3.

Let \(M=1.915\), \(w=r(B)\), \(U=R/\sqrt{1+w^2}\), and
\[
 v=b_c+1/2=1+k+U(ws-k),\qquad X=s+wk.
\]
On an actual contact \(r(b)\ge v/M\). Therefore (10) is at most
\[
 E(w,u)=(q-pv/M)X+Pw-t.                                    \tag{11}
\]
At fixed \(u\), extend \(w\) from its actual value to 1. The expression
\(v\) increases because \(v_w=UX/(1+w^2)>0\), and on this extension
\[
 v\le1-(d-1/2)k+(d+1/2)s<1.6.
\]
As \(X^2\le1+w^2\), differentiation of (11) gives
\[
\begin{aligned}
 E_w&=qk+P-\frac pM\left(kv+\frac{UX^2}{1+w^2}\right)\\
 &>.83048(.764)-.19335-
                     \frac{.21826}{1.915}(1.6+1.915)>.04.
\end{aligned}                                               \tag{12}
\]
Thus it is enough to bound \(E(1,u)\).

Set \(z=p/M>0\). Since \(s-k\le0\) and \(d+1/2<1.4\),
\(v>1-.4k+1.4s\) at \(w=1\). Use
\(k\le1-s^2/2\) in the positive term and \(k>.764\) in the negative
term after expanding (11). This gives the single quadratic bound
\[
 E(1,u)\le c_0+c_1s-c_2s^2,                                \tag{13}
\]
where
\[
 c_0=q-.6z+P-t,\qquad c_1=q-1.764z,\qquad c_2=q/2+1.3z.
\]
Here \(c_0<0,c_2>0\). For row 2, exact rational substitution gives
\(4c_2(-c_0)-c_1^2>.0309\); for row 3 it gives
\(4c_2(-c_0)-c_1^2>.0086\).
A completed square therefore makes (13) strictly negative for every
real \(s\). Equations (11)--(13) prove the promised whole-domain
\(C_B<0\), without a target-coordinate partition.

Consequently every active contact for these two rows lowers its cost by
increasing \(B\) until \(B=d\) or \(b=d\). If the least source is zero
with slack, increasing \(B\) similarly reduces cost until contact;
the contact at \(B=d\) is positive for every negative-half angle.
Thus the two diagonal curves below exhaust all remaining minima.

## 4. The two complete diagonal curves

There is a unique \(u_*\in(.5558,.5559)\) at which both coordinates are
diagonal. It is defined by
\[
 \frac12+(\tfrac12-d)\cos u_*+(d+\tfrac12)\sin u_*=d.
\]
The derivative of the left side is positive on \([0,.7]\).
For \(u\le u_*\), the maximum feasible target in (9) is \(B=d\).
For \(u\ge u_*\), it is the source-diagonal contact \(b=d\).

### 4.1. The target-diagonal cost has no interior minimum

Put
\[
 b(u)=\frac12+(\tfrac12-d)\cos u+(d+\tfrac12)\sin u,
 \qquad h=b'>0,
\]
\[
 D(u)=\pi/2-u+c+pa(b(u))+qb(u)-(P+t)d.
\]
Throughout its physical domain \(b_0\le b\le d\),
\[
 b''=1/2-b,\qquad
 h^2=2d^2+1/2-(b-1/2)^2\ge Q/2.
\]
Direct differentiation gives
\[
 \frac{D'''}h=-p r''(b)h^2-3p r'(b)(1/2-b)-(q-pr(b)).        \tag{14}
\]
For \(b\le1/2\), all terms are negative. For \(b\ge1/2\),
\[
 (b+1/2)h^2\ge Q/2>.4(Q-1)
                \ge(b-1/2)[a(b)+1/2]^2.
\]
Since \(r''/r'=3(b+1/2)/[a(b)+1/2]^2\), this inequality shows
that the first term of (14) dominates its only potentially positive
term. Hence \(D'''<0\) throughout.
The initial derivatives in rows 2 and 3 both exceed .068.
Thus \(D'\) is concave and starts positive; it can become negative
only once and cannot return to positive. Therefore \(D\) has its
minimum at one of its two angle endpoints.
The initial value is covered by (4). The other endpoint is the join
with the next curve, whose whole cost is bounded below below.

### 4.2. One circle-speed bound covers the source-diagonal arc

Set \(k_0=1/2-d\), and, on \(u_*\le u\le .7\), put
\[
 Z=k+k_0,\quad Y=\sqrt{Q-Z^2},\quad
 U=Zk+Ys,\quad V=Yk-Zs,\quad A=U-1/2,\quad B=V-1/2.
\]
These equations give (9) with \(b=d\). With \(f=1-s/Y\),
\[
 U'=Vf,\quad V'=-Uf,\quad
 f'=N/Y^3,\quad N=(1-Q+k_0^2)k+k_0(1+k^2)<0.               \tag{15}
\]
The endpoint comparisons and these monotonicities give throughout
\[
\begin{gathered}
 1.399<U<1.533,\quad1.251<V<1.4,\quad
 .668<f<.727,\quad f'<-.372,\quad 0<Z<.451,\quad Y>1.925.
\end{gathered}                                               \tag{16}
\]
Here \(f''>0\): differentiating (15) gives
\(f''=N'/Y^3-3NZs/Y^5\), and both terms are positive.
In particular the upper bound for \(f'\) is its single right endpoint.
For an explicit global upper bound use \(k<.85,s<.645\) and
\(.399<-k_0<.4\). The same formula gives
\[
\begin{aligned}
 f''<&\frac{(Q-1-.399^2+.8(.85))(.645)}{1.925^3}\\
 &+\frac{3\{(Q-1-.399^2)(.85)+.4(1+.85^2)\}(.451)(.645)}{1.925^5}
 <.5.
\end{aligned}                                               \tag{17}
\]

The speed \(P_0(u)=Uf=-B'\) consequently satisfies on this entire arc
\[
\begin{aligned}
 P_0''&=-Uf^3+3Vff'+Uf''\\
 &<-1.399(.668)^3-3(1.251)(.668)(.372)+1.533(.5)<-.5.
\end{aligned}
\]
At the single reference \(u=.68\), direct radical substitution gives
\(P_0<1.025\) and \(|P_0'|<.007\).
Strong concavity and a square completion prove
\[
                   P_0<1.025+.007^2<1.026                 \tag{18}
\]
over the whole arc, without enclosing a sequence of moving contacts.

Its cost is
\[
 E(u)=\pi/2-u+c+(p+q)d-P(U-1/2)-t(V-1/2).
\]
Hence
\[
 E'=-1+(tU-PV)f.
\]
For row 2, (16)--(18) give
\[
 E'<-1+.76744(1.026)+.19335(1.4)(.727)<0;
\]
for row 3 they give \(E'<-1+.94766(1.026)<0\).
Both complete source-diagonal curves therefore decrease to their right
endpoints. The exact final costs exceed .89811 and .89810, respectively.
These are substitutions at \(u=.7\) into (15), with
\[
 .64421768723<\sin(.7)<.64421768724,\qquad
 .76484218728<\cos(.7)<.76484218729.
\]
The lower bound \(\pi/2>1.570795\) suffices for both comparisons.
This bounds the join in Section 4.1 as well as the entire later arc,
and completes both negative-half rows 2 and 3.

## 5. Row 1 on the whole negative half

A simple monotone support confines any possible low cost to a small
initial contact domain. Choose the single multiplier \(\lambda=.94\).
The source expression after subtracting its separator margin is
\(pa+(q-\lambda)b\). It is concave in \(b\), and its diagonal endpoint
exceeds its axial endpoint by more than .0032. Thus its minimum is
\(pa_0\). The full-circle target support gives
\[
 C\ge F(u):=\pi/2-u+c+pa_0+
            \frac{\lambda+P+t}{2}+\lambda\cos u-RN(u),
\]
\[
 N(u)^2=P^2+t^2+\lambda^2+2\lambda(P\cos u-t\sin u).        \tag{19}
\]
Here \(N>0\) and \(N'<0\), because \(P\sin u+t\cos u>0\) on the
whole interval. Also \(N(0)<1.224\). The exact norm identity
\[
 N''+N/4=\frac{(P^2+t^2-\lambda^2)^2}{4N^3}\ge0
\]
therefore implies
\[
 F''\le-\lambda\cos u+RN/4
       <-.94(.764)+1.978788(1.224)/4<-.11.                  \tag{20}
\]
The two fixed comparisons are
\[
                      F'(.7)>.06,\qquad F(.03)>.89929.
\]
Since \(F'\) decreases, (20) proves that \(F\) increases everywhere.
Thus every angle \(u\ge .03\) already has cost greater than .89929.
This is one whole-interval support and derivative proof, not a chain
of angle-table intervals.

It remains to examine the possible low-cost domain \(0\le u\le .03\).
Use the actual contact (9), which increases in both variables.
Its value at \(B=.35,u=.03\) is negative, and its values at \(B=d\)
are positive and less than \(d\). Hence its feasible interval has only
the endpoints \(b=0\) and \(B=d\), and throughout it \(B>.35\).
The same source reduction and target slack motion as before leave
exactly this contact domain.

Put \(U=A+1/2,V=B+1/2,D=Vk+Us\), and \(H=tU-PV\).
At an interior stationary target, and also along the moving zero-source
boundary, implicit differentiation gives
\[
 C_u=-1+H(1-s/D).                                          \tag{21}
\]
The positive circle functional \(H\) is concave in \(B\), and its smaller
endpoint is the diagonal. Consequently
\(H\ge(t-P)(d+1/2)>.97207(1.399)\).
Also \(D>.85\cos(.03)>.849\) and \(s<.03\). Thus (21) is positive
by the single comparison
\[
 .97207(1.399)(1-.03/.849)>1.
\]
On the other boundary \(B=d\), its cost derivative is at least
\[
 -1+(q-p)(d+1/2)\cos(.03)
 >-1+.80213(1.399)(.9995)>0.
\]
As in Section 2, the compact minimum principle now leaves only alignment,
where (4) applies. This completes the entire first negative-half owner.

## 6. Complete coverage and arithmetic

Section 2 proves every positive half. Sections 3--4 prove the full
negative halves of rows 2 and 3, including the target/source diagonal
transition. Section 5 proves the full first negative half. Each step
uses the stipulated weak original separator or its exact reflection,
so ties and both closed state endpoints are retained.

The aligned input (4) is the companion's complete scalar proof, not the
historical near-aligned note. All other fixed comparisons have their
formulas displayed here. Positive squaring, alternating trigonometric
series at the named rational points, and the rational Machin bound
for \(\pi/2\) verify them. The two discriminants in (13) are elementary
rational substitutions. The continuous arguments are (12)--(14), the
whole-arc curvature (17)--(18), and the support derivative (20).
No checker status, Bernstein row, state mesh, or moving-contact bracket
sequence is a premise of this theorem.
