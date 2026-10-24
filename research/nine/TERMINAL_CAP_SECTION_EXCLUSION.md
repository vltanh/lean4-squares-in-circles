# A quantitative terminal-cap exclusion for path completion

This is a complete analytic single-square theorem. It uses the proved
support and concavity argument in
[OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md](OWNED_AXIS_TERMINAL_CAP_EXCLUSION.md),
with explicit modifications below. It does not assume common square
orientations or use an interval table.

Put

\[
D=\{(x,y):x^2+y^2\le17/4\},\quad
E_0=[1,2]\times[-1/2,1/2],\quad d_0=19/120.
\]

**Theorem.** Let \(n=(b,a)\), where \(0\le a\le b\) and
\(a^2+b^2=1\). There is no unit square \(T\subset D\cap\{y\ge0\}\),
interior-disjoint from \(E_0\), with center coordinate
\(1/2<c_x<1\), such that

\[
 \min_{p\in T} n\cdot p
 \ge k(a):=\frac12+a\left(\frac{19}{120}+\frac1{2b}\right).
 \tag{1}
\]

The constant is chosen for its exact completion consequence:

\[
\frac32-d_0=\frac{161}{120}>\frac3{\sqrt5},
\qquad 25921>25920.
\tag{2}
\]

All side halfwidths below refer to the actual square orientation.

## 1. Squares wholly above the terminal's top

First suppose \(T\subset\{y\ge1/2\}\). If \(a\ge5/12\), then
\(b\le\sqrt{119}/12\), and

\[
\frac{19}{120}+\frac1{2b}
\ge\frac{19}{120}+\frac6{\sqrt{119}}
>\frac{19}{120}+\frac{11}{20}
=\frac{17}{24}>\frac1{\sqrt2}.
\]

Here \(6/\sqrt{119}>11/20\) is exactly \(14400>14399\).
The complete theorem in
[POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md](POSITIVE_NORMAL_CAP_FLOOR_EXCLUSION.md)
therefore applies.

It remains to handle \(0\le a\le5/12\). Write

\[
\lambda=1-a,\quad v=n+\lambda e_y=(b,1),\quad
r=|v|=\sqrt{2-a^2},\quad R=\sqrt{17}/2.
\]

The two lower support constraints imply

\[
k(a)+\lambda/2+H(n)+\lambda H(e_y)+H(v)\le Rr.
\tag{3}
\]

Since \(1/b\ge1\), the first two terms are at least
\(1+19a/120\). As proved by orientation concavity in the cited cap-floor
theorem, the minimum of the support sum occurs at one of the frames
parallel to \(n,e_y,v\). Its three values are

\[
S_n=1+(1-a)(a+b),\quad S_y=1+b,\quad
S_v=r+b(1-a)/r.
\]

Use the elementary estimates

\[
b\ge1-3a^2/5,\quad
707/500-19a^2/50\le r<99/70-707a^2/2000,\quad R<33/16.
\tag{4}
\]

For the \(e_y\) frame they give

\[
1+19a/120+S_y-Rr
>93/1120+19a/120+(4131/32000)a^2>0.
\]

For the \(n\) frame the difference is greater than

\[
N(a)=93/1120+19a/120-(27869/32000)a^2+(3/5)a^3.
\]

This cubic is strictly concave on \([0,5/12]\), since
\(N''=-27869/16000+18a/5<0\). Its endpoint values are
\(N(0)=93/1120\) and \(N(5/12)=53173/1290240\), both positive.

For the \(v\) frame, multiply the difference by \(r>0\).
Using (4), the result is greater than

\[
V(a)=289/1000-(46567/60000)a+(33/400)a^2+(3239/6000)a^3.
\]

Its derivative is increasing and satisfies
\(V'(5/12)=-613733/1440000<0\). Thus \(V\) is decreasing on this
interval, and \(V(a)\ge V(5/12)=196903/10368000>0\).
All three frames contradict (3). This settles every orientation when
the square lies wholly above \(y=1/2\).

## 2. An up-left separator owned by the square

Suppose the square owns a side normal \(m=(-B,A)\), where
\(A,B\ge0\), \(A^2+B^2=1\), and its separation from the terminal gives

\[
\min_{p\in T}m\cdot p\ge A/2-B.
\tag{5}
\]

The elementary inequality
\((1-a^2)^{-1/2}\ge1+a^2/2\) gives

\[
k(a)\ge k_*(a):=1/2+(79/120)a+a^3/4.
\tag{6}
\]

If \(a\ge1/\sqrt6\), then
\(k_*(a)\ge1/2+7a/10\), so the complete owned-axis cap theorem applies.
Hence restrict to \(0\le a\le1/\sqrt6<5/12\).

Retain the notation from that theorem:

\[
\lambda=1-a,\quad f=b/2-a,\quad h=b+a/2,\quad
C=1+\lambda f,\quad D_1=\lambda h,
\]

but replace its constant \(E\) by

\[
E_*=k_*+\lambda=3/2-(41/120)a+a^3/4.
\]

Set \(\alpha=bA+aB\), \(\beta=aA-bB\). The same exact support
calculation shows that (1), (5) and disk containment would require

\[
E_*+C\sqrt{1-\beta^2}+D_1\beta+\max(\beta,0)
\le R\sqrt{1+\lambda^2+2\lambda\beta},
\quad -b\le\beta\le a.
\tag{7}
\]

We prove the strict reverse. The \(\beta\ge0\) branch is strictly
concave after subtracting the right side, exactly as before: its
second derivative is independent of \(E_*\).

### 2.1. The squared negative branch remains strictly concave

The proof in the owned-axis cap theorem uses three explicit inequalities.
We check each under the new constant. Write

\[
E_0'=3/2-3a/10,\quad
U_*=E_*C,\quad K_*=(17/4)\lambda-E_*D_1,
\quad S=C^2+D_1^2,\quad r_0=22/25.
\]

First, \(U_*,K_*>(11/5)\lambda\). The assertion for \(K_*\) follows
as before from \(E_*\le E_0'\le3/2\) and \(h<9/8\).
For \(U_*\), the lower bound on \(b\) gives

\[
\begin{aligned}
U_*-(11/5)\lambda
\ge{}&1/20-(9/16)a+(25/16)a^2+(703/1200)a^3\\
&-(191/400)a^4+(7/40)a^5+(3/40)a^6\\
\ge{}&1/20-(9/16)a+(25/16)a^2+a^3/4.
\end{aligned}
\]

The second inequality uses only \(0\le a\le5/12\). With \(x=a-1/6\),
the last cubic is exactly

\[
7/8640-x/48+(27/16)x^2+x^3/4
\ge7/8640-x/48+(3/2)x^2
\ge17/23040>0,
\]

because \(x\ge-1/6\).

Second, the first weighted diagonal dominance inequality remains strict.
The old proof gives

\[
E_0'C-S+r_0C/h
>a(39/20-7a/10-3a^2/10).
\]

Since \(E_*\ge E_0'-a/24\) and \(C\le3/2\), subtracting the possible
loss leaves the positive lower bound

\[
a(151/80-7a/10-3a^2/10)\ge0.
\]

The strict comparison in the preceding display also covers \(a=0\).

Third, the second weighted diagonal dominance inequality improves:
\(E_*\le E_0'\) increases \(K_*\), while all other terms are unchanged.
Its strictly positive polynomial lower bound in the owned-axis theorem
therefore still applies.

These three inequalities give exactly the same strictly positive
quadratic form used there, and hence strict concavity of

\[
\left(E_*+C\cos t-D_1\sin t\right)^2
-(17/4)(1+\lambda^2-2\lambda\sin t),
\quad 0\le t\le\pi/2-\arcsin a.
\]

The unsquared left expression is positive, since
\(E_*-D_1=k_*+\lambda(1-h)>3/8\).
It remains to check the three endpoints of the two branches.

### 2.2. Endpoint \(\beta=0\)

Here the left side of (7) is at least

\[
J_*(a)=3-(221/120)a+(7/10)a^2+(11/20)a^3>0.
\]

For \(x=a-1/3\in[-1/3,1/12]\), direct expansion gives

\[
\begin{aligned}
J_*^2-(17/4)(1+\lambda^2)
={}&38089/1166400-(16469/64800)x+(146047/43200)x^2\\
&-(1331/5400)x^3+(151/600)x^4+(11/8)x^5+(121/400)x^6.
\end{aligned}
\]

The cubic term is at least \(-1331x^2/64800\), and the fifth-degree
term is at least \(-11x^2/216\). The remaining fourth- and sixth-degree
terms are nonnegative. The resulting coefficient of \(x^2\) exceeds
\(3\). Since the constant exceeds \(3/100\) and
\(16469/64800<13/50\), completing the square bounds the entire
expression below by

\[
3/100-(13/50)^2/12=731/30000>0.
\]

### 2.3. Endpoint \(\beta=-b\)

The left side is
\(1/2+(199/120)a+a^3/4\). Dropping its nonnegative cubic term and
using \(b\ge1-3a^2/5\), its squared difference from the right side is
at least

\[
T_*(a)=1/4+(199/120)a-(95039/14400)a^2+(51/10)a^3.
\]

This is strictly concave on \([0,5/12]\):
\(T_*''(5/12)=-3239/7200<0\), and its second derivative is increasing.
Its endpoint values are \(1/4\) and \(13609/82944\), both positive.

### 2.4. Endpoint \(\beta=a\)

The left side is \(2+b+(19/120)a+a^3/4\); the right side is
\(R\sqrt{2-a^2}\). By (4), their difference exceeds

\[
93/1120+(19/120)a+(4131/32000)a^2>0.
\]

All three endpoints contradict (7), proving the owned up-left case.

## 3. Exhaust the physical terminal separators

The separating-axis theorem supplies a normal owned by either the
axis-aligned terminal or the actual square \(T\).

An axis of the terminal separates \(T\) either to its left, to its right,
above, or below. The left case forces
\(c_x\le1-H_T(e_x)\le1/2\); the right case forces \(c_x\ge5/2\);
the lower case contradicts \(T\subset\{y\ge0\}\). The upper case is
settled by Section 1.

For a square-owned normal directed from the terminal toward \(T\),
a down-right direction is impossible because \(c_x<1<3/2\) and
\(c_y\ge1/2\). An up-left normal is exactly Section 2.
It remains to route the other two signs; their zero-coordinate
boundaries are included by the same inequalities.

For an up-right normal \(m=(A,B)\), the exact separation inequality is

\[
A c_x+B c_y\ge2A+B/2+1/2.
\]

If \(B=0\), this is impossible. If \(B>0\), use \(c_x<1\) to obtain
\(B c_y\ge A+B/2+1/2\ge B(1+A+B)/2\). The last comparison follows from
\(A(2-B)+A^2\ge0\). Thus
\(c_y\ge(1+A+B)/2\), and the owned frame gives
\(\min_T y\ge1/2\). Section 1 applies, including \(A=0\).

Finally suppose \(m=(-A,-B)\), with \(A,B\ge0\). The exact separation
inequality gives

\[
A c_x+B c_y\le A-B/2-1/2.
\]

Upper-half-plane containment gives \(c_y\ge(A+B)/2\). Consequently

\[
A c_x\le A-1/2-B/2-B(A+B)/2
\le A-A(A+B)/2,
\]

where the second inequality follows from
\(1+B+B^2\ge A^2\). If \(A=0\), separation is already impossible;
otherwise the resulting upper support bound is
\(\max_T x=c_x+(A+B)/2\le1\). Thus
\(c_x\le1-H_T(e_x)\le1/2\), a contradiction.

All physical separating axes have been exhausted. This proves the
theorem, including every square orientation and limiting separator.
\(\square\)
