# Wrong word 0011011, edge 3: positive core to positive outer

## Theorem and complete scope

Let the source be a positive core-boundary state and the target a positive
outer-boundary state at \(Q=9789/2500\). On the entire quarter-one interval
\[
 p-\frac7{10}\le\phi\le p+\frac7{10},\qquad p=\frac\pi2,
\]
every true separating axis implies
\[
 C=\phi-.01449+g b-J(B)>\gamma,\qquad
 g=1.04240,\quad \gamma=.89765,
\tag{1}
\]
where
\[
 J(B)=.03965+3.85510B-1.49748B^2-1.89442A(B)B,\quad
 A(B)=\sqrt{Q-(B+.5)^2}-.5.
\tag{2}
\]
These are exactly the positive labels of roles 3 and 4 in the shared rational
label table. All decimals in this note are exact rationals.

The proof covers both core pieces, all four retained signed axes, every
angle endpoint, and all ties between axes. Its arithmetic consists of
166 fixed comparisons, including nine positive coefficients of one
degree-8 polynomial and thirty scalar endpoint comparisons. No sampled
minimum, adaptive state cover, or unproved contact selection is used.

Put
\[
 d=\sqrt{Q/2}-.5,\quad d_c=.5+\frac{\sqrt2}{24},\quad a_c=\frac7{12},
 \quad a_0=\sqrt{Q-.25}-.5,\quad \ell=p-.7.
\tag{3}
\]
The source has \(0\le b\le .5,a=a_c\) on its side and
\[
 .5\le b\le d_c,\qquad
 a=.5+\sqrt{1/144-(b-.5)^2}
\tag{4}
\]
on its corner. The target has \(0\le B\le d\) and \(A=A(B)\).
Own-frame centers are \((a,-b)\) and \((A,-B)\).

## 1. Derivatives, label bounds, and two absent axes

For the outer arc write
\[
 r=\frac{B+.5}{A+.5},\qquad
 A'=-r,\quad r'=\frac{Q}{(A+.5)^3},\quad
 \frac{r''}{r'}=\frac{3(B+.5)}{(A+.5)^2}<2.15.
\tag{5}
\]
With \(k=1.89442\),
\[
 \begin{aligned}
 J'&=3.85510-2.99496B-k(A-Br),\\
 J''&=-2.99496+k(2r+Br'),\\
 J'''&=k(3r'+Br'')>0.
 \end{aligned}
\tag{6}
\]
Thus \(J''\) is increasing and \(J'\) is convex. The fixed bounds
\[
 J'(.5)>.624,\quad -.032<J''(.5)<0,\quad J''(.55)>0
\]
show \(J'>0\): it decreases to the vicinity of .5, loses less than
\(.032(.05)\) between .5 and .55, and increases thereafter.
Convexity and the two outer endpoints give
\[
 0<J'(B)<1.176,\qquad J(d)<.763568.
\tag{7}
\]
Consequently every \(\phi\ge1.68\) satisfies
\[
 C\ge1.68-.01449-.763568>.9019>\gamma.
\tag{8}
\]

Let \(s=\sin\phi,c=\cos\phi\), \(W=(1+s+|c|)/2\).
The four possible signed separators are
\[
 \begin{array}{c|l}
 1&b+As-Bc\ge W,\\
 2&-ac+bs+A\ge W,\\
 3&as+bc-B\ge W,\\
 4&a-Ac-Bs\ge W.
 \end{array}
\tag{9}
\]
The letter \(a\) in the second row is the source coordinate, not the
constant \(a_c\). The core norm is less than .8 and \(W\ge1\), so axis 3
is impossible. Axis 4 is impossible below \(p\), since its left side is
at most \(a_c<1\). For \(\phi=p+x\), \(0\le x\le .11\), its margin is at most
\[
 a_c-.5+(a_0-.5)\sin x-.5\cos x<0.
\tag{10}
\]
This expression increases with \(x\), and its value at .11 is negative.
Since \(1.68<p+.11\), (8) and (10) cover every upper axis-4 angle.

Only axes 1 and 2 remain.

## 2. A contact derivative principle

If a differentiable function \(F\) has a concave derivative and
\(F'(L)>0\), then its minimum on \([L,H]\) is at an endpoint. Indeed,
the set where its derivative is nonnegative is an interval containing
the left endpoint: the function first increases and can subsequently
decrease, without creating an interior minimum.

For lower axis-1 contact,
\[
 b=W-As+Bc,\qquad
 F_B=g(rs+c)-J',
\quad F_{BBB}=gsr''-J'''<0.
\tag{11}
\]
For lower axis-2 side contact,
\[
 b=\frac{W+a_c c-A}{s},\qquad
 F_B=\frac{gr}{s}-J',
\quad F_{BBB}=\frac{gr''}{s}-J'''<0.
\tag{12}
\]
Both strict signs follow on the whole outer arc from
\[
 3k>2.15g,\qquad 3k>\frac{2.15g}{\sin\ell}.
\tag{13}
\]
Whenever a displayed contact coordinate is negative, the actual source
coordinate is at least zero; the separate zero-coordinate endpoint
arguments below handle that region. Ignoring an upper bound on a contact
coordinate only enlarges the domain and is always a valid relaxation.

## 3. Axis 1 below the quarter turn

### 3.1. The interval \(\ell\le\phi\le1.3\)

At \(B=.5\) and \(B=d\), the derivative in (11) is positive throughout
this angle interval. For each endpoint \(B\), its trigonometric term
is concave in \(\phi\), so the two angle endpoints suffice. Since
\(F_B\) is concave in \(B\), it is positive on \([.5,d]\).
Hence all \(B\ge.5\) reduce to \(B=.5\); it suffices to bound \(B\le.5\).

Here \(J\) is concave. The following four upper tangents,
\(J(B)\le k_0+qB\), use exact rational coefficients rounded upward:
\[
\begin{array}{c|r|r|r}
\phi\text{ interval}&\text{tangent point}&q&k_0\\ \hline
[\ell,1]&.172&.878955401&.063716016\\
[1,1.1]&.209&.828547105&.073303502\\
[1.1,1.2]&.252&.776312419&.085318707\\
[1.2,1.3]&.302&.724514843&.099625668
\end{array}
\tag{14}
\]
Subtract \(g\) times the axis-1 SAT margin from the cost and minimize
the remaining target linear functional on its full circle. This gives
\[
 F(\phi)=\phi-.01449-k_0+\frac{g+q}{2}
 +g\sin\phi-R\sqrt{g^2+q^2-2gq\cos\phi},\quad R=\sqrt Q.
\tag{15}
\]
The same bound is valid when the relaxed contact coordinate is negative.

For \(N^2=g^2+q^2-2gq\cos\phi\),
\[
 N''+\frac N4=\frac{(g^2-q^2)^2}{4N^3}\ge0.
\]
Together with
\[
 g\sin\ell>\frac{R\sqrt{g^2+.879^2}}4
\]
this proves \(F''<0\). Both endpoints of every row in (14) exceed .8993.
Thus (1) holds on this entire interval.

### 3.2. The interval \(1.3\le\phi\le p\)

The zero-source contact has the explicit parametrization
\[
 \begin{aligned}
 Z&=.5+\sin\phi,&Y&=\sqrt{Q-Z^2},\\
 U&=Z\sin\phi+Y\cos\phi,&V&=Y\sin\phi-Z\cos\phi,\\
 B_z&=V-.5,&f&=1-\cos\phi/Y.
 \end{aligned}
\tag{16}
\]
Here \(U=A(B_z)+.5\), \(B_z>.39\), and
\[
 B_z'=Uf>0,\qquad U'=-Vf,\qquad
 f'=\frac{-.5\sin^2\phi+(Q-1.25)\sin\phi-.5}{Y^3}>0.
\tag{17}
\]
The numerator in \(f'\) increases with \(\sin\phi\) on this interval.
At \(p\), \(U=1.5\) and
\[
 B_z=B_1:=\sqrt{Q-2.25}-.5<d.
\tag{18}
\]

At the zero contact, \(rs+c=Y/U\). Therefore \(F_B(B_z)>0\) follows from
the five fixed interval bounds
\[
 \frac{gY(H)}{U(L)}
  -\max\{J'(B_z(L)),J'(B_z(H))\}>.007
\tag{19}
\]
for
\[
 [L,H]=[1.3,1.4],[1.4,1.5],[1.5,1.55],
 [1.55,1.56],[1.56,p].
\]
The monotonicity of \(Y,U,B_z\) and convexity of \(J'\) justify every
endpoint selection in (19).

For \(B\le B_z\), the zero-source cost decreases with \(B\), because
\(J'>0\). For \(B\ge B_z\), the principle in Section 2 applies.
Thus only \(B_z\) and \(d\) need be considered.

The diagonal endpoint is
\[
 F_d(\phi)=\phi-.01449-J(d)+g/2
          +g(.5-d)\sin\phi+g(.5+d)\cos\phi.
\tag{20}
\]
Its second derivative is positive at 1.3 and increases up to \(p\);
its first derivative is negative at \(p\). It therefore decreases
throughout, and
\[
 F_d(p)=p-.01449+g(1-d)-J(d)>.897798.
\tag{21}
\]

At the zero endpoint put \(K_s(\phi)=\phi-.01449-J(B_z)\).
On each of \([1.3,1.35]\) and \([1.35,1.4]\), the endpoint bounds
\[
 J'(B_z)B_z'\le
 \max\{J'(B_z(L)),J'(B_z(H))\}\,U(L)f(H)<1
\tag{22}
\]
give \(K_s'>0\). Hence \(K_s\ge K_s(1.3)>.9053\) there.

On \([1.4,p]\), (17) gives
\[
 V<1.291,\quad U\ge1.5,\quad f\le1,\quad f'>.72,
\quad B_z''=-Vf^2+Uf'>-.22,\quad B_z'>1.3.
\]
Also \(J''(B_z(1.4))>.161\). Thus
\[
 K_s''=-J''(B_z')^2-J'B_z''
 <-.161(1.3)^2+1.176(.22)<0.
\tag{23}
\]
Its two endpoints exceed .914 and .9025. This completes lower axis 1.

## 4. Both axes above the quarter turn

By (8), it suffices to take \(0\le x=\phi-p\le .11\).

### 4.1. Axis 1

Its least nonnegative source coordinate is the nonnegative part of
\[
 b=.5-(A-.5)\cos x-(B-.5)\sin x.
\tag{24}
\]
The right side increases in \(B\), since \(r\cos x-\sin x>0\).
It has a unique zero \(B_z\in[B_1,d]\): its value at \(B_1\) is
\[
 \tfrac12(1-\cos x)-(B_1-.5)\sin x\le0,
\]
and its value at \(d\) is positive. The first sign follows from
\(\tfrac12\tan(x/2)<B_1-.5\); equality at \(x=0\) is included.

On \(B\ge B_z\), the contact cost is strictly concave in \(B\). In fact
both here and for axis 2 below, its second derivative is at most
\[
 2.99496-3.78884r+(g\sec(.11)-kB)r'<0,
\tag{25}
\]
because \(B\ge B_1>.79\), \(r>.85\),
\(3.78884(.85)>2.99496\), and \(k(.79)>g\sec(.11)\).
Hence only the zero and diagonal endpoints matter.

At \(d\), the cost is
\[
 p+x-.01449-J(d)+g/2-g(d-.5)(\cos x+\sin x);
\tag{26}
\]
its derivative is at least \(1-.4g>0\). At the zero endpoint,
\[
 B_z'=\frac{(B-.5)\cos x-(A-.5)\sin x}{r\cos x-\sin x}
 \le\frac{.4}{r(B_1)\cos(.11)-\sin(.11)}<.54.
\tag{27}
\]
Therefore its cost derivative is at least \(1-1.176(.54)>0\).
At \(x=0\), the two endpoints have the bounds (21) and .9025.

### 4.2. Axis 2

The source projection \(a\sin x+b\cos x\) increases along the complete
core boundary: on the corner its derivative is \(\cos x-t\sin x>0\),
where \(0\le t\le1\). At the side endpoint \(b=.5\), its margin is
\(A-.5+(a_c-.5)\sin x>0\). Thus a least feasible source lies on the side
or at its zero-coordinate endpoint. The side contact is
\[
 b=.5-(A-.5)\sec x-\frac{\tan x}{12}.
\tag{28}
\]
Again its zero lies in \([B_1,d]\), and (25) gives strict concavity beyond
that zero.

The diagonal cost is
\[
 p+x-.01449-J(d)+g/2-g(d-.5)\sec x-\frac g{12}\tan x.
\tag{29}
\]
Its derivative is positive, as follows by bounding \(x\) by .11 in its
two negative derivative terms. At the zero endpoint,
\[
 A_{\rm req}=.5+.5\cos x-\sin x/12,\qquad
 B_z'=\frac{.5\sin x+\cos x/12}{r}<.17.
\]
Its cost derivative is therefore positive too. Both minima occur at
\(x=0\) and have the already established bounds.

## 5. Axis 2 below the quarter turn: source side

Set \(a=a_c\). The contact coordinate and derivative are (12).

### 5.1. Target \(B\le .65\)

The single upper affine bound
\[
 J(B)\le k_0+qB,\qquad
 q=.643398450,\quad k_0=.128316398
\tag{30}
\]
holds on \([0,.65]\). It is the upper tangent at .42, rounded upward.
Concavity proves it through .5. Thereafter \(J'\) is convex and
\(J'(.5)<q\), so \(J-qB\) has no interior maximum above its two endpoint
values; the endpoint at .65 is also below \(k_0\).

The circular support bound is
\[
 G(\phi)=\phi-.01449-k_0+\frac{g+q}{2}
 +\frac{g(1+13\cos\phi/12)
        -R\sqrt{g^2+q^2\sin^2\phi}}{\sin\phi}.
\tag{31}
\]
For \(\phi\le1.46\), the following single polynomial proves
\(G>\gamma\) on a slightly larger interval. Put \(x=p-\phi\),
\( .11\le x\le .7\), and
\[
 K=\frac{\pi_{\rm lower}}2-.01449-k_0+\frac{g+q}{2}-\gamma,
 \quad \pi_{\rm lower}=3.141592653589793238.
\]
Let \(C_n,S_n\) denote the degree-\(n\) alternating cosine and sine sums.
Set
\[
 A_*=C_{10}(x)(K-x)+g+\frac{13g}{12}S_{11}(x),\qquad
 P=A_*^2-Q\{g^2+q^2C_8(x)^2\}.
\tag{32}
\]
Here \(K-x>0\), \(A_*>0\), \(C_{10}\le\cos x\), \(S_{11}\le\sin x\),
and \(C_8\ge\cos x>0\). Thus \(P>0\) implies (31) strictly.
Discard terms of degree at least 9 and subtract .000267 from the constant
term. The absolute negative discarded tail on \(0\le x\le .7\) is less
than .000267. The resulting degree-8 polynomial has Bernstein coefficients
on \([.11,.7]\) exceeding, in order,
\[
 \begin{array}{rrrrr}
 .0096312,&.0320782,&.0392637,&.0362823,&.0282149,\\
 .0194898,&.0134423,&.0122873,&.0174390.
 \end{array}
\tag{33}
\]
All are positive, so the whole interval is proved.

For \(\phi\ge1.46\), the direct bound
\[
 C\ge1.46-.01449-J(.65)>.8999
\tag{34}
\]
finishes this target range.

### 5.2. Target \(B\ge .65\)

The derivative in (12) is positive at .65 because
\(gr(.65)-J'(.65)>.060\).
If its zero-source endpoint \(B_z\) lies above .65, then
\(F_B(B_z)\ge gr(B_z)-J'(B_z)>0\):
the latter function is concave and positive at .65 and \(B_1\), where
its value exceeds .015.
Section 2 therefore reduces the contact cost to .65, \(d\), and the
zero endpoint. The .65 endpoint is covered above.

At \(d\), the scalar is
\[
 \phi-.01449-J(d)+g/2+g(.5-d)\csc\phi+\frac{13g}{12}\cot\phi.
\tag{35}
\]
Its derivative is negative: after multiplication by \(\sin^2\phi\),
its numerator is bounded above by
\[
 1-\frac{13g}{12}+\frac{g^2(d-.5)^2}{4}<0.
\]
Its minimum is the common aligned value (21).

For the zero endpoint define
\[
 \begin{aligned}
 m&=.5\sin\phi+\tfrac{13}{12}\cos\phi,&
 v&=\tfrac{13}{12}\sin\phi-.5\cos\phi,\\
 U&=1+m,&V&=\sqrt{Q-U^2},&B_z&=V-.5.
 \end{aligned}
\tag{36}
\]
Then \(m^2+v^2=205/144\), \(B_z'=Uv/V\), and
\[
 \frac{B_z''}{(B_z')^2}
 =\frac{mV}{Uv^2}-\frac{Q}{U^2V}>-1.264
\tag{37}
\]
on \(B_z\in[.65,B_1]\). Indeed,
\(m\ge.5,V\ge1.15,U\le1.62,v^2\le205/144,U\ge1.5\) give
\[
 \frac{.5(1.15)}{1.62(205/144)}-\frac{Q}{2.25(1.15)}
 >-1.264.
\]
Also
\[
 \frac{J''}{J'}>1.264
\tag{38}
\]
on this interval. It holds at .65; the ratio increases because
\(J'''>6.8,J'>.684,J''<2.003\), and
\(6.8(.684)-(2.003)^2>0\).
Here the monotonicity of the radial derivatives gives the indicated
endpoint bounds.

For \(K_p=\phi-.01449-J(B_z)\), equations (37)–(38) imply
\(K_p''<0\). The lower endpoint angle is greater than 1.466, since
\(B_z(1.466)<.65\); its cost exceeds
\(1.466-.01449-J(.65)>.9059\).
At \(p\) the cost exceeds .9025. This completes the source side.

## 6. Axis 2 below the quarter turn: source corner

For \(\phi\ge1.16\), the lower bound
\[
 C\ge1.16-.01449+g/2-J(d)>\gamma
\tag{39}
\]
is direct. For \(\phi\le1.16\) and \(B\le.5\), the direct bound is
\[
 C\ge\ell-.01449+g/2-J(.5)>\gamma.
\tag{40}
\]
Only \(\ell\le\phi\le1.16\), \(B\ge.5\), and \(.5\le b\le d_c\) remain.

At fixed \(b\), increase \(B\), decreasing the cost, until contact or
\(B=d\). If \(d\) is reached with slack, decrease \(b\), also decreasing
the cost, until contact. This must happen before \(b=.5\), because there
the required primary target coordinate is
\(.5+13\cos\phi/12>d\). Thus every remaining case reduces to
\[
 A_{\rm req}(b)=W+a(b)\cos\phi-b\sin\phi,\qquad
 B(b)=\sqrt{Q-(A_{\rm req}+.5)^2}-.5.
\tag{41}
\]

To consider all \(.5\le b\le d_c\) at once, allow this target circle
temporarily beyond its folded diagonal endpoint. This is an explicit
relaxation: it includes the actual contact subset. Throughout the extended
interval,
\[
 A_{\rm req}>.84,\quad .516<B<.95,\quad J'>0,\quad J''>0.
\tag{42}
\]
The bounds follow from the two rectangle corners because \(A_{\rm req}\)
decreases with both \(b\) and \(\phi\). Positivity of \(J''\) begins at .516
and persists by (6); positivity of \(J'\) persists too.

Write \(a'=-t\), \(0\le t\le1\). Since
\(|a''|=12(1+t^2)^{3/2}\), differentiation of (41) gives
\[
 B''=\frac{|a''|\cos\phi}{r}
       -\frac{r'(\sin\phi+t\cos\phi)^2}{r^3}>0.
\tag{43}
\]
For completeness, after multiplying by \(r^3/r'\), the positive term is
\[
 12\cos\phi\,\frac{(B+.5)^2(A_{\rm req}+.5)}Q
 (1+t^2)^{3/2}.
\]
Its prefactor exceeds \(12(.399)(1.3)/4>1\), whereas
\((\sin\phi+t\cos\phi)^2\le1+t^2\).
Consequently the contact cost is strictly concave:
\[
 C_{bb}=-J''(B')^2-J'B''<0.
\tag{44}
\]
It suffices to use \(b=.5,a=a_c\) and \(b=a=d_c\).

For either fixed endpoint, put
\[
 A_e(\phi)=.5+(.5-b_e)\sin\phi+(.5+a_e)\cos\phi,\quad
 B_e(\phi)=\sqrt{Q-(A_e+.5)^2}-.5.
\]
Here \(B_e\) and \(J(B_e)\) increase with \(\phi\). Hence on any displayed
fixed interval \([L,H]\),
\[
 C\ge L-.01449+g b_e-J(B_e(H)).
\tag{45}
\]
The following exact endpoint comparisons give lower bounds, rounded down:

| Angle interval | Side endpoint | Core diagonal endpoint |
|---|---:|---:|
| [ℓ, .89] | 0.901810 | 0.903330 |
| [.89, .91] | 0.904024 | 0.905928 |
| [.91, .93] | 0.907117 | 0.909079 |
| [.93, .95] | 0.910189 | 0.911915 |
| [.95, .97] | 0.913146 | 0.914370 |
| [.97, .99] | 0.915901 | 0.916381 |
| [.99, 1.01] | 0.918371 | 0.917893 |
| [1.01, 1.03] | 0.920482 | 0.918850 |
| [1.03, 1.05] | 0.922163 | 0.919205 |
| [1.05, 1.07] | 0.923351 | 0.918911 |
| [1.07, 1.09] | 0.923986 | 0.917928 |
| [1.09, 1.11] | 0.924013 | 0.916217 |
| [1.11, 1.13] | 0.923382 | 0.913745 |
| [1.13, 1.15] | 0.922047 | 0.910482 |
| [1.15, 1.16] | 0.931102 | 0.918544 |

Every entry exceeds \(\gamma\). These are thirty fixed scalar comparisons;
the contact-coordinate concavity already removed the entire core interval.

## 7. Arithmetic and coverage ledger

The companion JavaScript checker expands (32), subtracts its stated tail
allowance, and verifies all nine displayed Bernstein bounds directly.
It also checks every tangent, derivative, radical endpoint, and fixed
comparison used above, using rational BigInt arithmetic. Square roots are
enclosed by integer-square-root bounds of denominator \(10^{14}\).
Trigonometric endpoints use the alternating Taylor series, and the stated
rational pi bracket follows from the Machin identity and alternating arctangent
series. Every comparison is fixed in the file.

There are 166 strict rational comparisons in total. Their full values and
the exact degree-8 power and Bernstein coefficients are printed in
wrong_0011011_edge3_positive_core_to_positive_outer_arithmetic.json.

Coverage is exhaustive: (8) treats all late angles; axes 3 and 4 are absent
on the remaining interval; Section 3 treats all lower axis-1 cases; Section 4
treats all upper axis-1 and axis-2 cases; Sections 5 and 6 treat both lower
axis-2 core pieces. All shared endpoints are included. Thus (1) holds on
the complete stated domain.

