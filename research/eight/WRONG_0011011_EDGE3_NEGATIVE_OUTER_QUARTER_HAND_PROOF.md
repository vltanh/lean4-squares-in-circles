# Whole negative outer quarter row for word 0011011

**Table-free successor.** The three primary-speed rows and six
zero-target scalar intervals below are replaced in
[`formalization/HAND_WRONG_0011011_EDGE3_NEGATIVE_WITHOUT_TABLES.md`](formalization/HAND_WRONG_0011011_EDGE3_NEGATIVE_WITHOUT_TABLES.md).
The replacement proves this complete component with its original four
axes and both angle halves. The whole-word gate remains open.

## 1. Statement and exact data

Put
\[
 Q=\frac{9789}{2500},\qquad
 d=\sqrt{Q/2}-\frac12,\qquad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\qquad 0\le b\le d.
\]
Write \(a_0=a(0)\), \(b_1=\sqrt{Q-9/4}-1/2\), and
\[
 \gamma=\frac{17953}{20000}=.89765.
\]
All terminating decimals in this note are exact rationals.

This note proves the whole edge-3 outer/outer row with folded signs
\((-, -)\), and therefore its reflected edge-5 row with signs \((+,+)\).
Its two labels are exactly those in the declared rational role table:
\[
\begin{aligned}
 T(b)&=.01670+2.42322b-.91744b^2-.95769\,a(b)b,\\
 K(B)&=-.02112\,a(B)+.29090B+.44642\,a(B)B.
\end{aligned}                                                   \tag{1}
\]
If
\[
 \phi\in[\pi/2-.7,\pi/2+.7]
\]
and the pair of outer squares satisfies any retained separating-axis
inequality, then
\[
 \boxed{\quad \phi-T(b)+K(B)>.89777>\gamma.\quad}                 \tag{2}
\]
Here the four retained inequalities, with \(a=a(b)\), \(A=a(B)\), are
\[
\begin{array}{rcl}
-b+A\sin\phi+B\cos\phi&\ge&W,\\
-a\cos\phi-b\sin\phi+A&\ge&W,\\
a\sin\phi-b\cos\phi+B&\ge&W,\\
a-A\cos\phi+B\sin\phi&\ge&W,
\end{array}\qquad
 W=\frac{1+\sin\phi+|\cos\phi|}{2}.                              \tag{3}
\]
The already proved cap and angular lemmas justify retaining these four
axes. The argument below proves each of (3) separately. It imposes no
additional center-gap constraint, state sample, contact-order assumption,
or computer-generated cover.

The companion
**verify_wrong_0011011_edge3_negative_outer_quarter_hand.py**
checks 134 fixed rational comparisons appearing below. Its only
transcendental inputs are the displayed radicals, alternating Taylor
bounds for sine and cosine, and the Machin bounds specified in Section 8.
The complete continuous proof is in this note.

## 2. Scalar facts

For \(u=a(b)+1/2\), \(v=b+1/2\), \(r=v/u\), we have
\[
 a'=-r,\qquad r'=\frac Q{u^3},\qquad r''=\frac{3Qv}{u^5}.
\]
For an arbitrary label \(c+pa+qb+sb^2+tab\),
\[
\begin{aligned}
 L'&=-pr+q+2sb+t(a-br),\\
 L''&=2s-2tr-(p+tb)Q/u^3,\\
 L'''&=-3Q\{tQ+(p-t/2)v\}/u^5. 
\end{aligned}                                                   \tag{4}
\]
For (1) these formulas give
\[
 .609<T'<1.069,\quad T''' >1.6,\quad T'''\text{ increases},
 \qquad 0<K'<.928,\quad K''<-.221,\quad K'''<0.                  \tag{5}
\]
Also \(T'(d)<.774\), \(K'(d)>.31\).

Here are explicit justifications of the global extrema in (5).
For \(T\), the numerator controlling the derivative of \(T'''\) is
\[
 Q(5v-\tfrac12)-2v^2>0.
\]
It increases on \(1/2\le v<1.4\) and is positive at \(v=1/2\).
The check \(T'''(0)>1.6\) therefore gives the claimed global bound.
At \(b=.6\),
\[
 T'(.6)>.6101,\qquad |T''(.6)|<.049.
\]
Strong convexity of \(T'\), integrated from that point, yields
\[
 T'>.6101-\frac{.049^2}{3.2}>.609.
\]
Since \(T'\) is convex, its maximum is at an endpoint; the two endpoint
comparisons prove the upper bound in (5). For \(K\), the numerator
\(.44642Q-.24433v\) in \(-K'''\) is positive throughout the interval.
Thus \(K''\) decreases; \(K''(0)<-.221\) proves strict concavity of \(K\).
Its first derivative then decreases between the two checked endpoint
values.

We also need \(K'''(B)\le K'''(0)<-.742\). Its derivative has the
sign opposite to
\[
 5(.44642)Qv-.24433(Q+4v^2).
\]
This expression is positive at \(v=1/2\), and its derivative is
positive through \(v=1.4\). Hence \(K''''<0\), proving the asserted
bound.

The basic geometric bounds used below are
\[
 .899<d<.9,\quad 1.4145<a_0<1.415,\quad .7905<b_1<.791,\quad
 a(.415)+\tfrac12>1.75.                                       \tag{6}
\]

Define the increasing primary-coordinate label
\[
 M(a)=-T\!\left(\sqrt{Q-(a+\tfrac12)^2}-\tfrac12\right).
\]
Thus \(M'=T'(b)/r\). On \(d\le a\le1\), equivalently
\(b_1\le b\le d\),
\[
 M'<.9.                                                       \tag{7}
\]
Indeed \(r>.86\) and, by convexity of \(T'\), \(T'<.774\) there.

We shall also use the following lower bounds:
\[
 M'>.76\quad(d\le a\le a_0),\qquad
 M'>.84\quad(a\ge1.1),\qquad M'>1\quad(a\ge1.2).                \tag{8}
\]
For completeness, put \(g(b)=T'(b)-.76r\). Direct differentiation gives
\[
 g''=\frac{3Q\{.95769Q-1.238845v\}}{u^5}>.7.
\]
The last inequality follows from \(Q>3.9\), \(u<2\), \(v<1.4\), and
\(.95769(3.9)-1.238845(1.4)>2\). At \(b=.84\),
\[
 g>.00726,\qquad |g'|<.016.
\]
Consequently \(g>.00726-.016^2/1.4>0\), proving the first bound
in (8). If \(a\ge1.1\), then \(b<.665\), \(r<.75\),
\(T''<.17\), and \(r'>3.9/8\). Hence
\[
 T''r-T'r'<.17(.75)-.609(3.9/8)<0.
\]
So \(M'\) increases with \(a\) on this interval. The fixed evaluations
\(M'(1.1)>.84\) and \(M'(1.2)>1\) finish (8).

At exact alignment \(\phi=\pi/2\), axes 1 and 2 require \(A-b\ge1\),
and axes 3 and 4 require \(a+B\ge1\). The first two have a larger
bound established below. For the latter two, the least permissible
target is \(B=\max(0,1-a)\). On \(d\le a\le1\),
\[
 \frac d{da}\{M(a)+K(1-a)\}<.9-.901<0,
\]
because \(1-d<.101\) and \(K'(.101)>.901\). On \(a\ge1\), \(M\)
increases and \(B=0\). Therefore the aligned minimum is
\[
 \pi/2-T(b_1)+K(0)>.939.                                      \tag{9}
\]

## 3. The first two axes

Write \(x=|\phi-\pi/2|\), so \(0\le x\le.7\), and write
\(s=\sin x\), \(c=\cos x\).

### 3.1. Axis 1 below alignment

For \(\phi=\pi/2-x\), axis 1 says
\[
 b\le b_{\max}(B,x):=(A-\tfrac12)c+(B-\tfrac12)s-\tfrac12.
\]
The bound \(b_{\max}<\sqrt{Q-2a_0}-1/2<.543<d\) follows from
\((A-1/2)^2+(B-1/2)^2=Q-2(A+B)\) and \(A+B\ge a_0\).
Thus there is no source-diagonal clamp, and increasing \(b\) reduces
the cost until contact. On contact its derivative with respect to \(B\)
is
\[
 C_B=K'(B)+T'(b_{\max})(r(B)c-s)>0.
\]
To prove the last sign, it suffices when \(r c-s<0\) to bound it below by
\[
 G(B)=K'(B)+1.069\{r(B)\cos(.7)-\sin(.7)\}.
\]
This function is strictly concave: by (4), its second derivative has
the sign of
\[
 -.44642Q+\{.24433+1.069\cos(.7)\}(B+\tfrac12)<-.261.
\]
Both endpoint values of \(G\) exceed .44. When \(r c-s\ge0\),
the desired sign follows directly from \(K'>0\).

At each fixed angle the feasible contact interval therefore has its
minimum at \(B=0\), if that point is feasible, or at a zero-source
endpoint \(b_{\max}=0\). These are all the possibilities because
\(b_{\max}\) is concave in \(B\).
On the \(B=0\) boundary,
\[
 b=(a_0-\tfrac12)c-\tfrac12s-\tfrac12.
\]
Feasibility ends when \(b=0\), before \(x=.571\). The speed of this
decreasing coordinate satisfies
\[
 (-b')^2=Q-2a_0-(b+\tfrac12)^2.
\]
For \(0\le b\le a_0-1<.415\), both \(T'(b)\) and this speed decrease
with \(b\), because \(T''(.42)<0\). Thus
\[
 T'(b)(-b')\le T'(0)(a_0-\tfrac12)<1.069(.915)<1.
\]
The cost decreases with \(x\). At its last feasible endpoint it is
strictly larger than
\[
 \pi/2-.571-T(0)+K(0)>.953.                                   \tag{10}
\]
For a zero-source endpoint, if \(x\le.626\), the direct bound is
\[
 \pi/2-.626-T(0)+K(0)>.8982>.89777.
\]
If \(x\ge.626\), feasibility forces \(B>.1\). Indeed on
\(B\in[0,.1]\) the function \(b_{\max}\) decreases in \(x\), and
increases in \(B\), while
\[
 \sin(.626)-r(.1)\cos(.626)>0,\qquad
 b_{\max}(.1,.626)<-.0166<0.
\]
Consequently every such later zero-source endpoint has cost
\[
 \pi/2-.7-T(0)+K(.1)>.9157.
\]
This covers the complete lower half.

### 3.2. Axis 1 above alignment

For \(\phi=\pi/2+x\),
\[
 b\le(A-\tfrac12)c-(B+\tfrac12)s-\tfrac12
 \le a_0-1<.415.
\]
A direct bound is now enough:
\[
 \phi-T(b)+K(B)\ge\pi/2-T(.415)+K(0)>1.175.                    \tag{11}
\]

### 3.3. Axis 2 below alignment

The contact requirement is
\[
 A\ge\tfrac12+(a+\tfrac12)s+(b+\tfrac12)c.
\]
Since \(a\ge b\) and \(s+c\ge1\), it implies \(A\ge1+b\);
in particular \(b<a_0-1<.415\). Thus \(a+1/2>1.75\).
For \(x\ge.25\), the right side would exceed
\[
 \tfrac12+1.75\sin(.25)+\tfrac12\cos(.25)>1.415>a_0,
\]
because \(1.75\sin x+\tfrac12\cos x\) increases throughout this
range. Hence \(x<.25\), and
\[
 \phi-T(b)+K(B)>
 \pi/2-.25-T(.415)+K(0)>.925.                                 \tag{12}
\]

### 3.4. Axis 2 above alignment

Now
\[
 A\ge\tfrac12+(b+\tfrac12)c-(a-\tfrac12)s.
\]
If \(x\le.1\), then
\[
 b\le .915\,\frac{1+\sin(.1)}{\cos(.1)}-\tfrac12<.512,
\]
and the cost is greater than \(\pi/2-T(.512)+K(0)>1.1\).
For \(x\ge.1\), the direct bound
\[
 \pi/2+.1-T(d)+K(0)>.96                                      \tag{13}
\]
suffices. This completes axes 1 and 2, including their alignment cases.

## 4. The upper halves of axes 3 and 4

For axis 3 at \(\phi=\pi/2+x\), take the least feasible target
\[
 B=\max\{0,\tfrac12-(a-\tfrac12)c-(b-\tfrac12)s\}.
\]
This threshold is always smaller than
\(\tfrac12+\tfrac12\sin(.7)<d\). On its positive part the
cost derivative in \(x\), at fixed \(b\), is at least
\[
 1-.928(.4)>0.
\]
On its zero part the derivative is 1. Thus every such cost is bounded
below by its value at alignment, already covered by (9).

For axis 4 above alignment, the least allowed primary coordinate is
\[
 a=\max\{d,\tfrac12+(\tfrac12-B)c-(A-\tfrac12)s\}.
\]
The unclamped threshold is at most 1. On its active part \(M'<.9\)
by (7), and the absolute angular speed is at most
\[
 \sqrt{(A-\tfrac12)^2+(B-\tfrac12)^2}
 \le\sqrt{Q-2a_0}.
\]
Since \(.9\sqrt{Q-2a_0}<1\), the cost again increases with \(x\);
it also increases on the clamped part. This proves the whole upper half
of axis 4 by (9).

## 5. Axis 4 below alignment

The least primary coordinate is
\[
 a=\max\{d,a_*(B,x)\},\qquad
 a_*=\tfrac12+(\tfrac12-B)c+(A+\tfrac12)s.                      \tag{14}
\]
The threshold strictly increases with \(x\):
\[
 \partial_xa_*\ge1.399\cos(.7)-\tfrac12\sin(.7)>0.
\]
On an active contact,
\[
 (\partial_xa_*)^2=Q-2B-(a-\tfrac12)^2.
\]
The bounds (8) give \(M'\partial_xa_*>1\). The following three
fixed comparisons make the statement explicit:
\[
\begin{array}{c|c}
\text{primary range}&\text{lower bound for }(M'\partial_xa_*)^2\\ \hline
[d,1.1]&.76^2(Q-1.8-.6^2)>1\\
[1.1,1.2]&.84^2(Q-1.8-.7^2)>1\\
[1.2,a_0]&Q-1.8-.915^2>1.
\end{array}                                                   \tag{15}
\]
Consequently the cost decreases on the clamped part \(a=d\) and
increases on the active part. Its minimum at fixed \(B\) is at
alignment or at the source-diagonal transition \(a_*=d\).
There is a transition before \(x=.7\) whenever one is needed:
\(a_*(B,.7)\) is concave in \(B\), and both its endpoint values
exceed \(d\).

For the source-diagonal transition put \(k=1/2-d<0\) and
\[
 Z=c+k,\quad Y=\sqrt{Q-Z^2},\quad
 U=Yc-Zs,\quad V=Ys+Zc,\quad B=V-\tfrac12,\quad f=1-s/Y.
\]
Then
\[
 B'=Uf>0,\qquad B''=-Vf^2+Uf'<0,
\]
because
\[
 f'=\frac{(1-Q+k^2)c+k(1+c^2)}{Y^3}<0.
\]
The relevant \(U,V,f\) are positive; the final diagonal contact is
reached before \(x=.556\), as the direct substitution \(B(.556)>d\)
shows. Because \(K\) is increasing and concave, the cost
\[
 \pi/2-x-T(d)+K(B(x))
\]
is strictly concave. Its two endpoint bounds are
\[
 \pi/2-T(d)+K(1-d)>.953,\qquad
 \pi/2-.556-T(d)+K(d)>.9388.                                  \tag{16}
\]
These and (9) finish the whole of axis 4.

## 6. Axis 3 below alignment: reduction to its boundary

Only the lower half of axis 3 remains. Write
\[
 B_*(b,x)=\tfrac12-(a-\tfrac12)c+(b+\tfrac12)s,\qquad
 C(b,x)=\pi/2-x-T(b)+K(B_*(b,x)).                              \tag{17}
\]
Since \(K\) increases, use \(B=\max(0,B_*)\).
Where \(B_*<0\), the cost decreases as \(b\) increases. Moreover
\(\partial_bB_*>0\), and \(B_*(d,x)\ge1-d>0\).
Thus this inactive portion continues to \(B_*=0\).
It remains to study the compact active domain
\[
 0\le b\le d,\quad 0\le x\le.7,\quad 0\le B_*(b,x)\le d.
\]

Set
\[
 u=a+\tfrac12,\quad r=(b+\tfrac12)/u,\quad
 k=rc+s,\quad v=(a-\tfrac12)s+(b+\tfrac12)c,\quad z=B-\tfrac12.
\]
Then
\[
 B_b=k>0,\quad B_x=v>0,\quad
 C_b=-T'+K'k,\quad C_x=-1+K'v,\quad
 C_{xx}=K''v^2-K'z.                                          \tag{18}
\]
We prove that \(C\) has no interior minimum on the active domain.

### 6.1. An interior stationary point with \(B\ge.1\)

At a stationary point in \(x\), \(v=1/K'\), and therefore
\[
 C_{xx}=v^2\{K''-(B-\tfrac12)(K')^3\}.                         \tag{19}
\]
On \([.1,.5]\), the expression in braces strictly decreases, because
its derivative is
\[
 K'''-(K')^3-3(B-\tfrac12)(K')^2K''<0.
\]
Its value at \(B=.1\) is negative by one fixed comparison.
For \(B\ge.5\), it is manifestly negative. Hence every such
stationary point has a negative second derivative in the \(x\)
direction and cannot be a minimum.

### 6.2. An interior stationary point with \(0\le B\le.1\)

Again suppose \(C_x=0\). The circle identity and \(v=1/K'\) give
\[
 u(B)=\frac{Q+1-(B-\tfrac12)^2-(K'(B))^{-2}}2.                  \tag{20}
\]
Here
\[
 u''=-1+\frac{K'''}{(K')^3}
       -\frac{3(K'')^2}{(K')^4}<-2.1.
\]
For the last bound one may use
\[
 -1-\frac{.742}{.928^3}-\frac{3(.221)^2}{.928^4}<-2.1.
\]
The endpoint and tangent comparisons are
\[
 u(0),u(.1)>1.752,\qquad u(0)<1.7521,\qquad u'(0)<.224.
\]
Concavity gives the lower bound, while its strengthened tangent gives
\[
 u<1.7521+\frac{.224^2}{4.2}<1.765.
\]
Consequently
\[
 .394<b<.42,\quad v>1.077,\quad
 Q+1-3.53<q<Q+1-3.504,\qquad q=Q+1-2u.
\]
The exact projection-speed identity is
\[
 \frac{k}{v}=\frac{Q-u}{uq}+\frac{rz}{qv}.                      \tag{21}
\]
Since \(-.5\le z\le-.4\), it yields
\[
 \frac{k}{v}\ge
 \frac{Q-1.765}{1.765(Q+1-3.504)}
 -
 \frac{(.92/1.752)(.5)}{(Q+1-3.53)(1.077)}
 >T'(.394)+.007.
\]
The function \(T'\) decreases on \([.394,.42]\), so (18) implies
\(C_b=-T'+k/v>0\). This contradicts stationarity in \(b\).

Sections 6.1 and 6.2 prove that every global minimum of (17) lies on
one of its six boundary curves:
\[
 b=0,\quad b=d,\quad B=0,\quad B=d,\quad x=0,\quad x=.7.        \tag{22}
\]
There are no hidden contact alternatives: \(B_b,B_x>0\), and the active
domain is exactly the intersection of the six displayed closed
inequalities. Intersections of boundary curves are included in them.

## 7. The six boundary curves

### 7.1. Alignment, zero source, and diagonal source

The boundary \(x=0\) has the aligned bound (9).

For \(b=0\), on the active portion,
\[
 C_x\le -1+.928\sqrt{Q-2a_0}<0.
\]
At the final angle the direct evaluation is
\[
 \pi/2-.7-T(0)+K(B_*(0,.7))>.936.                             \tag{23}
\]
The zero-target inactive portion has already been reduced to \(B=0\).

For \(b=d\), one always has \(B\ge1-d>.1\).
The argument (19) shows that every interior stationary point of this
one-variable cost has a negative second derivative. Its minimum
therefore occurs at one of its two endpoints. They are the first and
last double-diagonal values in (16), since \(B_*(d,.556)>d\).

### 7.2. The zero-target boundary

On \(B=0\), the contact equation is
\[
 (a-\tfrac12)c-(b+\tfrac12)s=\tfrac12.
\]
It has the explicit parametrization
\[
 Z=\tfrac12+c,\quad Y=\sqrt{Q-Z^2},\quad
 U=Zc+Ys,\quad V=Yc-Zs,\quad b=V-\tfrac12,\quad f=1-s/Y.
\]
On \(0\le x\le.571\),
\[
 U'=Vf>0,\qquad V'=-Uf<0,\qquad
 f'=\frac{\tfrac12+(\tfrac54-Q)c+\tfrac12c^2}{Y^3}<0.
\]
The true physical arc ends at \(b=0\), before \(x=.571\);
the harmless displayed extension has \(V>.49\), \(f>.62\).
For
\[
 H(x)=\pi/2-x-T(b(x))+K(0)
\]
we have \(H'=-1+T'(b)Uf\).

The following six fixed rows give bounds for this derivative and one
reference value in each interval. For a row \([l,h]\), use \(U(l)f(h)\)
as a lower bound for \(Uf\), \(U(h)f(l)\) as an upper bound, the global
lower bound \(T'>.609\), and the maximum of the two endpoint values
of the convex function \(T'\). Clip the last \(b\)-interval at zero.
These rules produce the two middle columns using only the written
radicals and trigonometric values.

| \(x\)-interval | midpoint \(m\) | lower bound for \(T'(b)Uf\) | upper bound for \(T'(b)Uf\) | \(H(m)>\) |
|---|---:|---:|---:|---:|
| \([0,.1]\) | .05 | .843 | 1.078 | .9374 |
| \([.1,.2]\) | .15 | .835 | .999 | .9289 |
| \([.2,.3]\) | .25 | .812 | 1.073 | .9210 |
| \([.3,.4]\) | .35 | .780 | 1.181 | .9197 |
| \([.4,.5]\) | .45 | .744 | 1.301 | .9283 |
| \([.5,.571]\) | .5355 | .723 | 1.356 | .9448 |

Every row implies \(|H'|<3/8\). Every midpoint value exceeds .919,
and no interval has half-length greater than .05. The mean value
inequality therefore gives, throughout the physical arc,
\[
 H>.919-\frac38(.05)>.9.                                     \tag{24}
\]
This is a fixed six-row scalar estimate, not an adaptive subdivision
or numerical minimum.

### 7.3. The diagonal-target boundary

For \(B=d\), the contact runs from the double-diagonal point to
\(x=.7\), with
\[
 x>.5,\qquad b>.75.
\]
These follow directly from \(B_*(d,.5)<d\) and \(B_*(.75,.7)<d\).
Along the curve \(b_x=-v/k\), and
\[
 \frac vk=u-\frac{s}{k}.
\]
Here \(u<1.535\), \(s>.479\), \(k\le c+s<1.415\), and
\(T'(b)<.774\) on \([.75,d]\) by convexity and the endpoint
bounds. Consequently
\[
 \frac d{dx}\{\pi/2-x-T(b(x))+K(d)\}
 =-1+T'\frac vk
 <-1+.774\!\left(1.535-\frac{.479}{1.415}\right)<0.             \tag{25}
\]
Thus this boundary reaches its minimum at \(x=.7\).

### 7.4. The fixed endpoint angle

At \(x=.7\), put \(s_7=\sin(.7)\), \(c_7=\cos(.7)\), and
\[
 B(b)=\tfrac12-(a(b)-\tfrac12)c_7+(b+\tfrac12)s_7,\qquad
 J(b)=\pi/2-.7-T(b)+K(B(b)).
\]
One has \(B(0)>0\), and the interval is \(0\le b\le b_{\max}\), where
\[
\begin{aligned}
 Z&=c_7+\tfrac12-d,\qquad Y=\sqrt{Q-Z^2},\\
 b_{\max}&=Yc_7-Zs_7-\tfrac12,\qquad
 .7518<b_{\max}<.752.
\end{aligned}                                                   \tag{26}
\]
For \(k=rc_7+s_7\),
\[
 k'=\frac{Qc_7}{u^3},\qquad k''=\frac{3Q(b+\tfrac12)c_7}{u^5}.
\]
Differentiating gives
\[
 J'''=-T'''+K'''k^3+3K''kk'+K'k''.
\]
All terms except the last are negative. Uniformly on (26),
\[
 J'''<
 -1.6+\frac{.928(3Q)(1.252)(.765)}
               {(a(.752)+\tfrac12)^5}<-.36.                  \tag{27}
\]
Thus \(J''\) strictly decreases and \(J'\) is strictly concave.
The fixed values
\[
 J'(.4)>.06,\qquad J''(.4)>.24
\]
show that \(J\) is strongly convex on \([0,.4]\). At \(b=.275034\),
\[
 J>.8977814,\qquad |J'|<10^{-6}.
\]
The integrated tangent bound yields
\[
 J>.8977814-\frac{10^{-12}}{.48}>.89778
 \qquad (0\le b\le.4).                                      \tag{28}
\]
On \([.4,b_{\max}]\), the strict concavity of \(J'\), together with
\(J'(.4)>0\), permits at most a crossing from positive to negative.
There is no interior minimum of \(J\) on this interval. Its left
endpoint is already covered by (28), and the right endpoint has the
explicit radical bound
\[
 J(b_{\max})=
 \pi/2-.7-T(b_{\max})+K(d)>.8977831.                           \tag{29}
\]
This proves the remaining boundary, and hence all of axis 3.

## 8. Arithmetic and conclusion

For \(T_n(t)=\sum_{j=0}^{n-1}(-1)^jt^{2j+1}/(2j+1)\), Machin's
identity gives
\[
 8T_{16}(1/5)-2T_5(1/239)
 <\pi/2<
 8T_{15}(1/5)-2T_4(1/239).
\]
These imply
\(1.57079632679489<\pi/2<1.57079632679490\).
Every sine in the fixed arithmetic is enclosed by its alternating
Taylor sums through degrees 11 and 13; every cosine by those through
degrees 14 and 12. All evaluated angles are at most .7.
Positive radicals use rational lower and upper endpoints whose squares
are compared with the radicand.

The companion file reproduces the stated comparisons using exact
fractions. It contains neither an optimizer nor a state enumeration;
the 126 strict comparisons verify only the scalar bounds explicitly
used above. Equations (10)--(16) and (22)--(29) cover every axis and
both angle halves. Their least asserted final bound is strictly above
.89777, proving (2). The row therefore contributes positive reserve
above \(\gamma\) to the wrong-word cyclic sum.

