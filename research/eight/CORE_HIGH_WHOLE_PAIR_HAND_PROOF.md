# Core/high whole-pair hand proof

## 1. Statement and fixed constants

Let two consecutive members of an exterior seven-cycle have boundary kinds \(C,H\), in either order, at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q.
\]
Use the exact four-type markers below. Then every genuine separating axis gives
\[
 \delta-\frac9{50}h(\phi)+\psi_j-\psi_i>\frac{8833}{10000}.
 \tag{1}
\]
This proves the complete \(C/H\) entry of the four-type table. It uses the hand exterior-core and common-point lemmas, which give
\[
 \frac{19}{25}<\delta<\frac{3\pi}{4}.
 \tag{2}
\]
It does not assume frame concentration.

Put
\[
 a_c=\frac7{12},\quad
 K=7.506931,\quad g=1.077372,\quad
 u=.569472,\quad v=.390886,\quad \beta=.18,
\]
and
\[
 d=\sqrt{Q/2}-\frac12,\qquad
 k=\frac\pi4+(u-v)d.
\]
All displayed terminating decimals denote exact rationals.

In sorted positive local coordinates, the two boundary arcs are
\[
 \begin{aligned}
 C_{\rm side}&:\ a=a_c,\quad 0\le b\le\tfrac12,\\
 C_{\rm corner}&:\ (a-\tfrac12)^2+(b-\tfrac12)^2=\tfrac1{144},
                  \quad \tfrac12\le b\le a,\\
 H&:\ (a+\tfrac12)^2+(b+\tfrac12)^2=Q,\quad
                 \tfrac37\le b/a\le1.
 \end{aligned}
\]
Their unsigned labels and signed potentials are
\[
 L_C=K(a_c-a)+gb,\qquad L_H=k-ua+vb,\qquad
 \psi=\alpha-\operatorname{sgn}(\alpha)L,
 \tag{3}
\]
where \(\alpha=\operatorname{sgn}(\alpha)\arctan(b/a)\). A deterministic representative may be chosen at a closed cut.

The actual centers in their respective square frames are \((a,-\sigma b)\)
and \((A,-\tau B)\); the signs \(\sigma,\tau\) refer to the frame-to-center
angles \(\alpha_i,\alpha_j\). Put
\[
 \phi=\delta+\alpha_j-\alpha_i,\quad s=\sin\phi,\quad c=\cos\phi,\quad
 h=\frac{|s|+|c|-1}{2},\quad W=1+h.
\]
The cost in (1) is
\[
 {\cal C}=\phi-\beta h+\sigma L_i-\tau L_j.
 \tag{4}
\]
The cap and backward-axis lemmas leave only two source inequalities:
\[
 M_f=\sigma b+As-\tau Bc-W\ge0,\qquad
 M_e=a-Ac-\tau Bs-W\ge0.
 \tag{5}
\]
Reversal followed by reflection preserves \(\phi,{\cal C}\), exchanges source and target, and negates both signs. Thus proving both orders and both inequalities in (5), with all signs, covers the remaining target axes too.

### 1.1. Elementary bounds

Let \((a_l,b_l)\) be the lower \(H\) endpoint, \(b_l=3a_l/7\). Direct squaring gives
\[
 \begin{gathered}
 R<1.978788,\quad .899214<d<.899215,\quad
 1.199256<a_l<1.199257,\\
 .5139<b_l,\quad
 .596<r:=\frac{b+1/2}{a+1/2}\le1,\quad
 .4639<L_H(a_l,b_l)<.464,\quad L_H(d,d)=\pi/4<.786.
 \end{gathered}
 \tag{6}
\]
Along \(H\), \(a'=-r\), so \(L_H'=ur+v>0\), whereas
\(L_H-gb\) and \(L_H-b\) decrease because \(u+v=.960358<1<g\).

On \(C\), \(a'=0\) on the side and \(-1\le a'\le0\) on the corner.
Thus \(L_C\) increases with \(b\), and its maximum is at
\(c_C=\tfrac12+1/(12\sqrt2)\). The bounds
\[
 .5589255<c_C<.5589256,\qquad 0\le L_C<.786
 \tag{7}
\]
follow by squaring and substitution. Core-center norm is \(<.8\);
every outer-center norm is \(<1.415\).

By (2), \(\phi>.76-\pi/2>-.812\). Also \(0\le h<.21\).
For \(\phi\ge2.5\), all signs satisfy
\[
 {\cal C}>2.5-2(.786)-.0378=.8902>.8833.
 \tag{8}
\]
We henceforth use \(-.812<\phi<2.5\).

The checker verifies the following deliberately coarse trigonometric brackets by alternating Taylor polynomials. A blank entry is unused.

| \(x\) | lower \(\sin x\) | upper \(\sin x\) | lower \(\cos x\) | upper \(\cos x\) |
|---|---:|---:|---:|---:|
| .812 | .725 | | .688 | |
| 1.2 | .932 | .933 | .362 | .3625 |
| 1.25 | | | .315 | |
| 1.4 | .985 | .986 | .169 | .17 |
| 1.5 | | | | .071 |
| 2.28 | .758 | | −.652 | |
| 2.4 | .675 | | −.738 | |
| 2.45 | .637 | | −.771 | |
| 2.5 | .598 | .599 | −.802 | −.8 |

We use \(3.14159<\pi<355/113\), already proved by the hand Machin estimate.

### 1.2. Two shared support facts

For a linear functional on \(H\), completing its circle gives
\[
 xa+yb\ge-\frac{x+y}{2}-R\sqrt{x^2+y^2}.
 \tag{9}
\]
If a norm \(N\) is that of a fixed vector of squared norm \(u^2+v^2\)
plus a rotating vector of length \(g\), direct differentiation gives
\[
 N''+\frac N4=\frac{(g^2-u^2-v^2)^2}{4N^3}>0.
 \tag{10}
\]
Here \(g>\sqrt{u^2+v^2}\), so no norm vanishes. Moreover,
\[
 \frac{RN}{4}<\frac{1.978788(g+.7)}4<.9<g-\frac\beta2.
 \tag{11}
\]

Two endpoint values recur:
\[
 \begin{aligned}
 B_{\parallel}&=\frac\pi4+g(1-d)>.8939,\\
 N_q&=\sqrt{(g-u)^2+v^2},\qquad .640901<N_q<.640902,\\
 B_{\perp}&=\frac\pi4+\frac{3g}{2}-(u-v)(d+\tfrac12)-RN_q>.88336.
 \end{aligned}
 \tag{12}
\]
The last strict comparison already follows on replacing \(\pi,d,R,N_q\)
by \(3.14159,.899215,1.978788,.640902\) in the adverse directions.

## 2. Source primary axis with source \(C\)

This section proves \(M_e\ge0\Rightarrow{\cal C}>.8833\) for all four sign pairs.

For \(-.812<\phi\le1.2\), (5) and (6) imply
\[
 M_e<\frac1{12}-1.399c+.4|s|
 \le\frac1{12}-1.399(.362)+.4<0.
 \tag{13}
\]
Thus \(\phi>1.2\).

If \(\tau=-1\), then for \(\phi\ge1.25\),
\[
 {\cal C}>1.25-.786+.463-.0378>.8833.
\]
For \(1.2\le\phi\le1.25\), primary separation forces
\[
 B\ge\frac12+\frac{(A+1/2)c-1/12}{s}
 >\frac12+1.399(.315)-\frac1{12}>.85.
\]
The outer circle then forces \(A<1\), whence
\(L_H>k-u+.85v>.7\). Consequently
\({\cal C}>1.2-.786+.7-.0378\).

If \(\tau=+1\), first-quadrant separation is impossible. In the second
quadrant through \(2.45\), put \(d_\phi=-c\). Then
\[
 M_e<\frac1{12}+.7d_\phi-1.0139s
 \le\frac1{12}+.7(.771)-1.0139(.637)<0.
\]
For \(2.45\le\phi\le2.5\), separation instead forces
\[
 B<\frac{1/12+.7(.802)}{.598}-\frac12<.6.
\]
The outer circle gives \(A>1.14\), so
\(L_H<k-1.14u+.6v<.54\), and
\({\cal C}>2.45-.786-.54-.0378\).

No source sign was excluded in these lower bounds.

## 3. Source secondary axis with source \(H\)

If \(\sigma=-1\), then its projection is at most the core-center norm,
hence \(M_f<.8-W<0\). It remains to take \(\sigma=+1\).

### 3.1. Negative core target

For \(\phi\ge0\), subtract \(gM_f\) from the cost. The source contribution
\(L_H-gb\) is minimized at \((d,d)\), and
\[
 L_C-gAs-gBc
 =-ga_cs+(K+gs)(a_c-A)+gB(1-c)\ge-ga_cs.
\]
Thus
\[
 {\cal C}\ge \phi-\beta h+gW+\frac\pi4-gd-ga_cs.
 \tag{14}
\]
On the first quadrant its derivative is positive because
\[
 \left(\frac{g-\beta}{2}\right)^2+
 \left(ga_c-\frac{g-\beta}{2}\right)^2<1.
\]
On the second quadrant it is \(>1\). Its minimum is \(B_\parallel\).

For \(\phi=-z<0\), choose instead \(\lambda=g/\cos z\).
Then \(L_H-\lambda b\) still decreases along \(H\). In the core
functional the \(B\) coefficient cancels, and
\(K-g\tan z>0\). We get
\[
 {\cal C}\ge F(z):=-z-\frac\beta2(\sin z+\cos z-1)+\frac\pi4+\frac g2
 +g\frac{(1/2-d)+(13/12)\sin z}{\cos z}.
 \tag{15}
\]
After multiplying \(F'(z)\) by \(\cos^2z\), use \(d-1/2<.4\) and
\(\cos z-\sin z\le1\):
\[
 \cos^2z\,F'(z)
 \ge \frac{13g}{12}-1.09+1.09\sin^2z-.4g\sin z
 \ge \frac{13g}{12}-1.09-\frac{(.4g)^2}{4(1.09)}>0.
\]
Again the minimum is \(F(0)=B_\parallel\).

### 3.2. Positive core target

For \(\phi\le0\), the projection is \(<b<.9\). For \(0<\phi\le.45\),
\[
 M_f<.4+\frac{s}{12}-\frac c2
 \le .4+\frac{.45}{12}-\frac{1-.45^2/2}{2}<0.
\]
For \(\phi>.45\), subtract \(M_f\). The source \(L_H-b\) is minimized at
\((d,d)\). The target functional
\[
 -L_C-As+Bc
\]
has derivative \((K-s)A'+c-g<0\), so it is minimized at
\((c_C,c_C)\). It remains to bound
\[
 F(\phi)=\phi-\beta h+W+\frac\pi4-d-L_C(c_C,c_C)+c_C(c-s).
 \tag{16}
\]
Its first-quadrant derivative is positive since
\((.41+c_C)^2+(c_C-.41)^2<.97^2+.15^2<1\).
Its second-quadrant derivative is \(>1-.15\). At \(.45\),
\[
 F>.45+.59+\frac{3.14159}{4}-.899215-.786
       +.968(1-.45^2/2)-.15(.45)>.94.
\]

## 4. Source secondary axis with source \(C\)

If \(\sigma=-1\) and separation holds, then
\(b<1.415-1<.5\), so the core source is on its side. Therefore
\[
 \sigma L_C-g\sigma b\ge0
\]
for both signs: it is \(K(a_c-a)\ge0\) for the positive sign and zero
for the negative sign. Subtracting \(gM_f\) gives the universal bound
\[
 {\cal C}\ge \phi-\beta h+gW-\tau k
 +\min_H\bigl((\tau u-gs)A+\tau(gc-v)B\bigr).
 \tag{17}
\]
This reduction covers all four sign pairs.

Write
\[
 A_*=\frac{g+\beta}{2},\qquad C_*=\frac{g-\beta}{2}.
\]

### 4.1. Negative high target

For \(\phi=-z\le0\), the target coefficients are
\(x=-u+g\sin z\), \(y=v-g\cos z<0\).
If \(x\ge0\), then \(xa'+y<0\). If \(x<0\), then
\[
 xa'+y\le |x|+y=u+v-g(\sin z+\cos z)<0.
\]
Thus the target minimum is diagonal. Formula (17) becomes
\[
 -z+A_*+\frac\pi4+(C_*-gd)\cos z+(C_*+gd)\sin z.
 \tag{18}
\]
Its derivative is positive: the positive trigonometric sum
\((gd-C_*)\sin z+(gd+C_*)\cos z\) is concave, and at the two endpoints
it is greater than \(1\). At \(z=.812\), the explicit bound is
\(.51(.725)+1.41(.688)>1\). The minimum is \(B_\parallel\).

For \(0\le\phi\le1.2\), the full-circle bound (9) gives
\[
 F_-(\phi)=\phi+C_-+(g-\beta/2)(s+c)-RN_-(\phi),
 \tag{19}
\]
where
\[
 C_-=A_*+(u-v)/2+k,\qquad
 N_-^2=g^2+u^2+v^2+2g(us-vc).
\]
By (10)–(11), \(F_-''<0\). At the endpoints,
\[
 N_-(0)<.892,\quad F_-(0)>.886;\qquad
 N_-(1.2)<1.575,\quad F_-(1.2)>1.02.
\]
Concavity proves the required bound on the whole interval.

For \(\phi\ge1.2\), the target coefficients satisfy \(x<0,y>0\), because
\(g\cos1.2<g(.3625)<v\). Hence the functional increases along \(H\) and
its minimum is at \((a_l,b_l)\). In the first quadrant the resulting
derivative is
\[
 1-(ga_l-C_*)c+(gb_l-C_*)s>1-.85>0.
\]
In the second quadrant it is \(>1\). It continues the endpoint bound
at \(1.2\).

### 4.2. Positive high target through \(1.4\)

For negative \(\phi\), the coefficient \(x=u-gs\) is positive, so the
target functional is concave in \(B\), and its minimum is at an endpoint
of the \(H\) arc.

For \(0\le\phi\le1.4\), the same is true when \(x\ge0\). If \(x<0\),
its derivative is at least
\[
 g(.596s+c)-.596u-v>0.
\]
The last trigonometric function is concave and positive at both \(0\)
and \(1.4\). Consequently it again suffices to use the two arc endpoints.

For either endpoint \((A_j,B_j)\), with label \(E_j\), the
first-quadrant bound is
\[
 F_j(\phi)=\phi+A_*-E_j+(C_*+gB_j)c-(gA_j-C_*)s.
 \tag{20}
\]
Its derivative is convex and negative at \(1.4\):
\(C_*+gB_j>1\), \(gA_j-C_*>.51\), and
\(.985+.51(.169)>1\).
A convex derivative whose right endpoint is negative cannot yield an
interior minimum of \(F_j\). Thus only \(0,1.4\) are needed.
For \(\phi=-z\), the bound
\[
 -z+A_*-E_j+(C_*+gB_j)\cos z+(C_*+gA_j)\sin z
\]
is concave in \(z\), so only \(0,.812\) are needed.
Substitution of (6) and the displayed trigonometric brackets gives
strict bounds \(>.8833\) at all these endpoints.

### 4.3. Positive high target beyond \(1.4\)

The full-circle support gives, for \(1.4\le\phi\le\pi/2\),
\[
 F_+(\phi)=\phi+C_++(g-\beta/2)s-\frac\beta2 c-RN_+(\phi),
 \tag{21}
\]
where
\[
 C_+=A_*-(u-v)/2-k,\qquad
 N_+^2=g^2+u^2+v^2-2g(us+vc).
\]
Here \(N_+\) increases to \(N_q<.641\), since \(vs-uc>0\).
Also \(g^2-u^2-v^2>.641^2\), so (10) gives \(N_+''>0\).
It follows that \(F_+''<0\). The two endpoint bounds are
\[
 N_+(1.4)<.536,\quad F_+(1.4)>.89,\qquad
 F_+(\pi/2)=B_\perp>.88336.
\]
For \(\pi/2\le\phi\le2.5\), formula (21) changes to
\[
 \phi+C_++(g-\beta/2)(s-c)-RN_+(\phi).
\]
It is concave by (10)–(11). At \(2.5\),
\(N_+<1.26\), \(s-c>1.398\), and the bound is \(>.98\).
Thus the quarter endpoint remains sufficient.

## 5. Source primary axis with source \(H\)

### 5.1. Lower angle exclusion and a universal core-side bound

For a negative core target and \(\phi\le0\),
\[
 M_e<1.2-.558(.67)-1<0.
\]
For a positive core target, the signed angle relation forces
\(\phi>\delta-\pi/4>-.026\). On this negative interval, and also for
\(0\le\phi\le.75\), the generic bound
\[
 M_e<.7-1.058c+.06|s|
 \le .7-1.058(1-.75^2/2)+.06(.75)<0
\]
applies. Hence every remaining primary case has \(\phi>.75\).

Use the adverse source sign \(-L_H\), and put \(\lambda=g/s\).
For a negative core target, subtracting \(\lambda M_e\) leaves the
core contribution
\[
 \lambda a_cc+(K-\lambda c)(a_c-A)\ge\lambda a_cc.
\]
For a positive core target on its side, the \(B\) term cancels exactly
and gives the same contribution. Here \(s>.598\), so
\(K-\lambda c>0\).

Applying (9) to the source therefore gives
\[
 H(\phi)=\phi-\beta h-k+\frac{-u+v+g}{2}
 +\frac gs+\frac{gwc}{s}
 -R\sqrt{(g/s-u)^2+v^2},
 \tag{22}
\]
where \(w=13/12\) in the first quadrant and \(w=1/12\) in the second.
This proves the desired bound for every negative core target and every
positive core target on its side, once (22) is estimated.

### 5.2. One polynomial for the whole interval \([.75,1.5]\)

Let
\[
 n(s)=\sqrt{(g-us)^2+v^2s^2}.
\]
Since \(gu>u^2+v^2\), this decreases on \([0,1]\). Moreover,
\[
 n(1)<.640902,\quad n'(1)>-.214,\quad
 0<n''(s)=\frac{g^2v^2}{n(s)^3}<.7.
\]
Taylor's theorem about \(s=1\) gives the explicit quadratic upper bound
\[
 n(s)<U(s):=.640902+.214(1-s)+.35(1-s)^2
            =1.204902-.914s+.35s^2.
 \tag{23}
\]

Put
\[
 R_+=1.978788,\quad
 k_+=\frac{355}{452}+(u-v)(.899215),\quad \gamma=.8833,
\]
and
\[
 \begin{aligned}
 B&=\beta/2-k_++(-u+v+g)/2-\gamma,\\
 B_0&=B+.914R_+,\quad
 B_2=\beta/2+.35R_+,\quad
 C_0=g-1.204902R_+.
 \end{aligned}
\]
Let \(S_m,C_m\) be the ordinary Taylor polynomials for sine and cosine
through degree \(m\). On \([.75,1.5]\), \(\phi+B_0>0\);
\(S_7\le s\le S_9\), \(C_6\le c\le C_8\), and the upper polynomials
are positive. Multiplying \(H-\gamma\) by \(s>0\) and using (23) gives
\[
 \begin{aligned}
 s(H-\gamma)&>
 P(\phi):=(\phi+B_0)S_7-B_2S_9^2-\frac\beta2S_9C_8
          +C_0+\frac{13g}{12}C_6.
 \end{aligned}
 \tag{24}
\]
This is a degree-18 rational polynomial on one fixed interval.

In the degree-18 Bernstein basis on \([3/4,3/2]\), every coefficient
of \(P\) is strictly greater than the corresponding entry below,
divided by \(10^7\):
\[
 \begin{split}
 (&34281,45678,53640,59000,62526,64903,66706,68387,70249,72436,\\
  &74913,77453,79629,80800,80112,76492,68645,55061,34020).
 \end{split}
 \tag{25}
\]
The Bernstein basis functions are nonnegative and sum to one.
Thus \(P>0\), proving \(H>.8833\) on the entire interval.
Equation (25) is a single algebraic identity/comparison row; its
nineteen entries are explicitly rational and can be checked by
binomial expansion.

### 5.3. The remaining primary interval

Write \(X=g/s-u\), \(N=\sqrt{X^2+v^2}\), and \(Z=RX/N<R<1.979\).

On \([1.5,\pi/2]\), differentiation of (22) gives
\[
 H'=1+.09(s-c)+\frac g{s^2}
       \left(c(Z-1)-\frac{13}{12}\right).
\]
Since \(c<.071\), the bracket is negative and
\[
 H'<1.09+g\left(.071(.979)-\frac{13}{12}\right)<0.
\]
Therefore \(H\ge H(\pi/2)=B_\perp>.88336\).

On \([\pi/2,2.5]\), \(Z\ge Z(\pi/2)>1.56\); the latter follows by
squaring. Direct differentiation gives
\[
 H''=.09(s-c)+\frac g{s^3}
     \left((1+c^2)(1-Z)+\frac c6\right)
     -\frac{Rv^2g^2c^2}{s^4N^3}
 <.09(1.5)-.56g<0.
\]
The left endpoint is \(B_\perp\). At the right endpoint \(N<1.294\),
and a direct lower bound is
\[
 2.5-.0378-k_++\frac{-u+v+g}{2}
 +\frac g{.599}-\frac{g(.802)}{12(.598)}
 -1.978788(1.294)>1.08.
\]
Concavity closes the whole second quadrant.

### 5.4. Positive core target on its corner

It remains to treat the positive core corner, which was not used in
(22). In the first quadrant, separation would require
\(a\ge.5+s+c\ge1.5>1.2\), which is impossible.

In the second quadrant, \(A\le a_c\), \(B\ge.5\) give the necessary bound
\[
 a\ge .5+s-\frac{-c}{12}.
 \tag{26}
\]
For \(\phi\le2.28\), its right side is at least
\(.5+.758-.652/12>1.2\). Thus \(\phi>2.28\).

For \(2.28\le\phi\le2.4\), (26) gives \(a>1.1135\).
The outer circle gives \(b<.646\), so
\[
 L_H<k_+-1.1135u+.646v<.565.
\]
The cost is \(>2.28-.786-.565-.0378=.8912>.8833\).

For \(2.4\le\phi\le2.5\), (26) gives
\(a>.5+.598-.802/12\). The circle gives \(b<.754\), and
\(L_H<.655\). The cost is then
\(>2.4-.786-.655-.0378=.9212>.8833\).

## 6. Coverage and exact arithmetic record

The proof has the following complete cover.

| Source kind | Source axis | Sign cases | Sections |
|---|---|---:|---|
| \(C\) | primary \(-e\) | all four | 2 |
| \(H\) | secondary \(+f\) | negative source impossible; both positive-source targets | 3 |
| \(C\) | secondary \(+f\) | all four through the universal reduction | 4 |
| \(H\) | primary \(-e\) | all four; positive core side/corner separated | 5 |

The reflected-reversed images cover all remaining target axes. Every
angle interval used above is closed; overlaps at \(\phi=0,\pi/2\),
at the core side/corner join, and at the lower \(H\) cut are harmless.

The accompanying dependency-free checker
verify_core_high_whole_pair_hand.js performs **143 strict exact rational
comparisons**, including the nineteen coefficients (25). It uses integer
fractions, fixed Taylor polynomials and a binomial change of basis.
The continuous geometric reductions, derivative signs and interval
coverage are established in this note. The JSON record contains every
rational comparison and its positive difference.

**Conclusion:** the full \(C/H\) entry is \(>.8833\), conditional only on
the already proved exterior seven-cycle geometry and the stated
four-type marker definitions.
