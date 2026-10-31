# The whole exterior pocket of the unique-corner diagonal six-cycle channel is empty

**Status: complete hand geometric theorem; root and separate independent
full hand/algebra audits passed.** Work in
\[
 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 Q=\frac{1105}{256},\qquad s=\frac1{\sqrt2},\qquad A=2+\sqrt2.
\tag{1}
\]
Let the entire selected positive component be an alternating six-cycle
with three loaded bodies, all having one **physical** circle corner,
and exactly one diagonal transmitter.

**Theorem.** No additional physical unit square can lie in the actual
exterior pocket of that diagonal channel. All genuine shared means at
the loaded body opposite this channel remain unrestricted.

Together with SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md, this puts at most
one of the three completion squares in the whole central free union,
none in the diagonal pocket, and at least two in the union of the two
actual side-transmitter pockets. It does not yet bound that union or
close the whole one-diagonal completion family.

The proof below is a full geometric separating-axis cover. Its four
polynomial certificates are exact identities on complete parameter
rectangles; no sampled angle, interval subdivision or numerical sign is
a premise.

## 1. The complete diagonal endpoint domain and the actual pocket

Use the endpoint and turn conclusions of
SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md, Section2. Write
\[
\begin{gathered}
 X=[-a,1-a]\times[b-1,b],\qquad
 Y=[c-1,c]\times[d-1,d],\\
 a+c=A,\qquad a^2+b^2=c^2+d^2=R^2,\\
 a>b>\frac12,\qquad c>d>\frac12.
\end{gathered}
\tag{2}
\]
The strict comparisons follow also directly from that source's
\(45^\circ<\eta_X,\eta_Y<90^\circ\): the first comparison is
\[
 (h+1-b)-(1-a+ah/b)=(a-b)(1-h/b)>0,
\]
and the second is its reflection.

The actual diagonal transmitter W has center
\[
 \delta=\frac{c-a}{2}=\frac A2-a,\qquad c_W=(\delta,h),
\]
and vertices
\[
 (1-a,h),\quad(c-1,h),\quad(\delta,h+s),\quad(\delta,h-s).
\]
Its genuine side-interior applications and proper endpoint concurrences
give
\[
 b-1<h<b,\quad d-1<h<d,\qquad
 h\ge b(1-1/a),\quad h\ge d(1-1/c).
\tag{3}
\]

The actual cap theorem SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md gives every
putative exterior square E the whole inclusion \(E\subset\{y\ge h\}\).
It also gives
\[
                         E\subset\{-a\le x\le c\}.
\tag{4}
\]
Indeed the occupied crosscut from \((-a,b)\) to \((c,d)\) and its upper
circle arc have their entire horizontal projection in this interval.
Both endpoint heights are positive, so the upper circle arc has no
horizontal excursion beyond its endpoints. The bounded Jordan region
lies in the convex hull of its boundary. The same compact-interior
homotopy argument in that source includes every weak contact limit.
Thus (4) concerns the whole physical E, not only its center.

Here are two useful full-domain bounds:
\[
                  \frac{10}{7}<a,c<2,\qquad h>\frac25.
\tag{5}
\]
If \(a\ge2\), then \(c\le\sqrt2\), so (2) gives both \(R^2>17/4\)
and \(R^2<2c^2\le4\), impossible. If \(a\le10/7\), then
\[
 R^2\ge(A-10/7)^2+1/4>2(10/7)^2\ge2a^2,
\]
again impossible. The strict middle gap is greater than \(93/980\),
using \(\sqrt2>7/5\). Reflection gives the bounds on c.

For the height, let \(x=\min(a,c)\in(10/7,A/2]\) and let y be its
corresponding corner height. If \(h\le2/5\), then
\[
 R^2=x^2+y^2\le g(x):=x^2+\frac4{25}\frac{x^2}{(x-1)^2}.
\]
The function is strictly convex, since
\[
 g''(x)=2+\frac8{25}\frac{2x+1}{(x-1)^4}>0.
\]
Both endpoint bounds contradict \(R\ge R_0\):
\[
 g(10/7)=1684/441<R_0^2,\qquad
 g(A/2)=99/50+(33/25)\sqrt2<1353/350<R_0^2.
\]
This proves (5).

Every contained unit center satisfies
\[
 |c_E|\le M:=\sqrt{R^2-1/4}-1/2<91/60.
\tag{6}
\]
This is the universal center/halfwidth bound, not a boundary premise.

## 2. The full separating-axis cover

Take a separating side axis of W or E, directed from W toward E.
Its vertical component must be positive. To see this, if it has
nonpositive vertical component and negative horizontal component, its
support at W is at least its value at \((1-a,h)\). Since E lies above
h, the separator puts all of E to the left of \(x=1-a\).
Together with (4) and the minimum horizontal unit width one, this forces
E to be axis-aligned with horizontal interval \([-a,1-a]\).
Its avoidance of X and its lower height \(h>b-1\) force its bottom
height at least b. Its upper-left corner then has squared radius at
least \(a^2+(b+1)^2>R^2\). The positive-horizontal case is reflected;
a purely downward axis is impossible already from W's lower vertex.

A purely upward separator would put E above \(h+s\), and its center
above \(h+s+1/2>91/60\), contrary to (5)--(6).
Reflect horizontally if necessary. The separating normal therefore
points strictly northwest. It is either W's northwest side axis or
an E side axis.

Choose E's own orthonormal directions
\[
 n=(u,v),\qquad m=(-v,u),\qquad u,v\ge0,\quad u^2+v^2=1,
 \qquad w=u+v,\quad \mu=\max(u,v).
\tag{7}
\]
The E-owned northwest alternative has \(u,v>0\) and normal m.
The W-owned alternative has normal \((-1,1)/\sqrt2\), and includes
the axis-aligned E endpoints in (7).

For X and E, the separating-axis theorem and (4) leave exactly the
following nonexclusive cover:
\[
 \begin{array}{c|c}
 \text{X separator}&\text{whole condition}\\ \hline
 \text{horizontal}& \min_E x\ge1-a\\
 \text{vertical}& \min_E y\ge b\\
 \text{E-owned northeast}&\min_E(n\cdot x)\ge u(1-a)+vb .
 \end{array}
\tag{8}
\]
For clarity, a separator with negative horizontal and positive vertical
components exposes X's upper-left corner; because \(x\ge-a\) throughout
E, it implies the vertical row. A separator with positive horizontal
and negative vertical components exposes X's lower-right corner;
because \(y\ge h>b-1\), it implies the horizontal row. A separator with
both components nonpositive is impossible. The only remaining strict
northeast separating side axis is E's n. These arguments retain all
support endpoints and do not assume that E touches an obstacle.

## 3. The whole horizontal row is impossible

Write \(c_E=(x,y)\). The horizontal row gives \(x\ge1-a+w/2\).

If W owns the northwest separator, then
\[
 y-x\ge h+a-1+\mu.
\]
The actual top E vertex has height
\[
 y+w/2\ge h+w+\mu\ge h+2>R.
\]
Here \(w+\mu\ge2\), since for \(\mu\ge\nu\ge0\),
\((2\mu+\nu)^2-4=\nu(4\mu-3\nu)\ge0\).

If E owns that separator, then
\[
 -vx+uy\ge-v\delta+uh+s\mu+1/2.
\]
Its actual top vertex consequently has height at least
\[
 h+v+\frac{1+s(\mu-v)}u\ge h+s+1>21/10>R.
\tag{9}
\]
For \(u\ge v\), use \(1/u\ge1\) and \(1-sv>0\);
for \(v\ge u\), use \(v\ge s\). Thus both horizontal alternatives
are excluded without any frame or physical mask for E.

## 4. The whole E-owned northeast row

### 4.1. Both separators owned by E

The two center projections satisfy
\[
 p:=n\cdot c_E\ge u(1-a)+vb+1/2,\qquad
 q:=m\cdot c_E\ge uh-v\delta+s\mu+1/2.
\]
Both of the following lower bounds on the farthest own coordinates are
positive, by \(a<2\), (5), and (2):
\[
 |p|+1/2\ge1+(1-a)u+bv,\qquad
 |q|+1/2\ge1+(2/5)u-v\delta+s\mu.
\]
Containment would therefore require
\[
 F:= [1+(1-a)u+bv]^2+
       [1+(2/5)u-v\delta+s\mu]^2-a^2-b^2\le0.
\tag{10}
\]
We prove the strict opposite on the complete parameter domain.

Put
\[
                  \bar a(b)=\frac{Q+4-b^2}{4}.
\tag{11}
\]
Since \((a-2)^2\ge0\) and \(a^2+b^2\le Q\), we have \(a\le\bar a\).
The expression (10) is affine and nonincreasing in a.
For \(u\ge v\), half its a-coefficient is
\[
 v-u-u^2-(A/2)v^2+(2/5+s-b)uv<0.
\]
For \(u\le v\), it is
\[
                         v-u-1+(2/5-b)uv\le0.
\]
The first follows from \(u\ge v\), \(u^2+(A/2)v^2\ge1\),
\(uv\le1/2\), and \(2/5+s-b<1\). The second includes equality only
at the harmless axis endpoint \(u=0,v=1\).
Thus replacing a by \(\bar a\) lowers F.

Certificates I and II in Section7 prove the resulting strict positivity
on both entire angular sectors and \(1/2\le b\le3/2\).
They contradict (10). This excludes this whole owner combination.

### 4.2. The northwest separator owned by W

If \(u\ge v\), this reduces directly to Section4.1. With
\(p_0=u(1-a)+vb+1/2\) and
\(q_0=uh-v\delta+s u+1/2\), the W-owned condition is
\[
                    (v-u)p+wq\ge h-\delta+s+u.
\]
At \(p=p_0\), its lower bound on q exceeds \(q_0\) by exactly
\[
 \frac{u-v}{w}\,[\,1+v(b-h)-sw\,]\ge0.
\tag{12}
\]
The bound on q is nondecreasing in p. Hence the E-owned northwest
inequality also holds, and Section4.1 applies.

It remains to cover \(u\le v\), with no assumption on a contact mean.
Use the actual top vertex \(z=c_E+(n+m)/2\). It satisfies
\[
 n\cdot z\ge A_1:=1+(1-a)u+bv,\qquad
 \frac{z_y-z_x}{\sqrt2}\ge B_1:=\frac{H+2v}{\sqrt2},
 \quad H=h+a-1.
\tag{13}
\]
If either bound exceeds R, containment already fails.
Otherwise both active normals have positive coefficients in the
closest-point combination. Indeed
\[
 A_1-\frac{R}{\sqrt2}(v-u)
 =1+(1-a+R/\sqrt2)u+(b-R/\sqrt2)v>0,
\tag{14}
\]
using \(a<2\), \(R/\sqrt2>1\), \(b\le R/\sqrt2\),
\(v\le1\), and \(R/\sqrt2<3/2\). Thus
\(A_1>((v-u)/\sqrt2)B_1\). In the other direction,
\[
 H+2v-(v-u)A_1
 =h+a-1+w+(a-1)u(v-u)-bv(v-u)>23/70>0.
\tag{15}
\]
For its lower bound use
\(w-bv(v-u)\ge w-b(v-u)\ge-1/2\).
Equations (14)--(15) prove the stated positive-coefficient property.

Consequently every z satisfying (13) has norm at least that of the
intersection of the two equality lines. This follows directly by
writing that intersection as a positive sum of the two unit normals,
taking scalar products with z, and applying Cauchy.

In E coordinates its second coordinate is
\([H+2v-(v-u)A_1]/w>0\). Hence its squared norm is increasing in h.
Replace h by \(h_0=2/5\). In original coordinates that intersection is
\[
 z_x^*=1-a+u-v+\frac{v(b-h_0)}w,\qquad
 z_y^*=w+\frac{h_0u+bv}{w}.
\tag{16}
\]
Its squared excess above \(a^2+b^2\) is affine and decreasing in a:
the coefficient is
\[
 -2\left[1+u-v+\frac{v(b-h_0)}w\right]<0.
\]
Replace a by (11). Certificate III proves that the resulting squared
excess is strictly positive for every \(u\le v\) and
\(1/2\le b\le3/2\). This contradicts containment.
The entire northeast row (8) is now excluded.

## 5. One exact center-cap inequality for the whole vertical row

Put
\[
 T=\sqrt{R^2-1/4},\quad D=T-1,\quad M=T-1/2.
\]
If E is above b, its center height is at least \(Y=b+1/2\).
If \(b>D\), this is already greater than M. We may assume \(b\le D\).

We prove the following full scalar inequality whenever \(b\le D\),
with all the endpoint conditions (2), and with any
\(h\ge d(1-1/c)\):
\[
 \boxed{\quad
 \sqrt{M^2-(b+1/2)^2}<h+a-1+s-(b+1/2).
 \quad}
\tag{17}
\]
The right side is strictly positive. This assertion does not require
\(h<b\), so its later auxiliary use is included.

Here are the complete rational reductions used for its certificate.
The condition \(b\le D\) gives
\[
 a^2\ge2T-3/4>49/16,\qquad a>7/4>A/2,\qquad a>c,\quad d>b.
\tag{18}
\]
Use \(T>191/100\) for the strict comparison. Since \(d\le c\),
\[
 d=b+\frac{A(a-c)}{b+d}
       \ge b+\frac{A(a-c)}{b+c}.
\]
Set
\[
 C=c(b+c),\qquad
 N=(c-1)\,[b(b+c)+A(a-c)],\qquad
                         h_{\rm rat}=N/C\le h .
\tag{19}
\]
We have \(h_{\rm rat}>3/20\); hence
\(a+h_{\rm rat}-b+s-3/2>1/12>0\).

Also \(a<79/40\). Indeed \(c\ge d\) gives
\[
 a\le f(b):=2A-\sqrt{2A^2+b^2}\le f(1/2)<79/40.
\]
For the last comparison the squared gap is
\(239/1600-\sqrt2/10>73/11200>0\).
Since \(T<121/60\), we have \(T+a<4\), and therefore
\[
 T-a=\frac{b^2-1/4}{T+a}\ge\frac14(b^2-1/4),
 \qquad M^2\le a^2+\frac34b^2-a+\frac1{16}.
\tag{20}
\]

The complete parameter rectangle for the remaining rational inequality
is obtained as follows. The secant inequality on \(7/4\le a\le2\)
gives \(a^2\le(15/4)a-7/2\), so
\[
 a\ge\frac{3947}{2000}-\frac4{15}b^2.
\]
On \(1/2\le b\le61/60\), \(\sqrt{2A^2+b^2}<5\), whence
\(f'(b)<-b/5\). Integrating from \(1/2\) gives
\[
                         a<2-b^2/10.
\]
Thus there exist \(x,t\in[0,1]\) with
\[
 b=\frac12+\frac{31}{60}x,\qquad
 a=\frac{3947}{2000}-\frac4{15}b^2+
                  \left(\frac{53}{2000}+\frac16b^2\right)t .
\tag{21}
\]

Certificate IV proves strict positivity, on that entire rectangle, of
\[
 \begin{split}
 {\cal P}={}&
 \left(a+b+\frac3{16}+\frac14b^2-a^2\right)C^2\\
 &+\left[(a-b+s-3/2)C+N\right]^2 .
 \end{split}
\tag{22}
\]
Divide by \(C^2>0\), use (19)--(20), and increase \(h_{\rm rat}\)
to h. This proves (17), with positive right side as asserted.

## 6. The whole vertical row has no northwest separator from W

Assume \(\min_E y\ge b\). By (6), the center belongs to the closed cap
\[
                   K=\{(x,y):x^2+y^2\le M^2,\ y\ge Y\},
                  \qquad Y=b+1/2 .
\tag{23}
\]
It suffices to prove, for every northwest unit normal r,
\[
                          h_K(r)<h_W(r)+1/2.
\tag{24}
\]
Every unit contains its open radius-\(1/2\) disk, so (24) contradicts
any W-to-E separating normal, regardless of which square owns it.

Let \(X_0=\sqrt{M^2-Y^2}\), and write the left cap endpoint relative
to \(c_W=(\delta,h)\) as
\[
 (-X_0,Y)-c_W=(-v_0,u_0),\qquad
                  v_0=X_0+\delta,\quad u_0=Y-h.
\]
For the actual channel \(u_0>1/2\). Equation (17) gives
\[
                              u_0+v_0<\sqrt2.
\tag{25}
\]
We also have the whole-domain estimate
\[
                       u_0<53/50<3s/2.
\tag{26}
\]
If \(b\le24/25\), this follows from \(h>2/5\).
For \(b\ge24/25\), \(b\le D\) implies
\(a^2\ge2b+5/4\), so \(a>89/50\).
The function
\[
 h_C(a,b)=\sqrt{b^2+A(2a-A)}\,\left(1-\frac1{A-a}\right)
\]
is increasing in b, and increasing in a throughout this domain.
For the second claim, with \(c=A-a\) and
\(d=\sqrt{b^2+A(2a-A)}\le c\), its a-derivative has positive numerator
\(Ac(c-1)-d^2\ge c[(A-1)c-A]>0\), because \(c>10/7>\sqrt2=A/(A-1)\).
These inequalities hold along the comparison down to
\(a=89/50,b=24/25\) as well.
At that point \(h_C>23/50\): after squaring positive quantities the
numerator difference is
\[
                 \frac{1566167-1106424\sqrt2}{250000}>0,
\]
using \(\sqrt2<99/70\). Consequently
\(u_0<317/300<53/50\). The last comparison in (26) follows from
\(106^2<2\cdot75^2\).

The left cap endpoint satisfies every northwest support inequality in
(24). If \(v_0<0\), this follows directly from (26):
for \(r=(-\sin\theta,\cos\theta)\),
\[
 r\cdot((-X_0,Y)-c_W)-s\max(\sin\theta,\cos\theta)
 <\max(u_0-s,0)<1/2.
\]
If \(v_0\ge0\), then
\[
 v_0-u_0<23/20-1/2=13/20<s.
\]
Here \(v_0<X_0<\sqrt{(91/60)^2-1}<23/20\), using \(\delta<0\).
If \(u_0-v_0\ge s\), the endpoint's distance to W's top vertex
is at most \(\sqrt2(u_0-s)<1/2\), by (26).
Otherwise the endpoint is inside W or its nearest upper-left edge
has distance \((u_0+v_0-s)/\sqrt2<1/2\), by (25).
This proves the strict support claim at the left endpoint.

For completeness, that endpoint check extends to the whole cap,
not merely to its boundary point. Put
\(\theta_0=\arccos(Y/M)\). For \(\theta\ge\theta_0\),
\(h_K(r)=r\cdot(-X_0,Y)\), already handled. For
\(0\le\theta\le\theta_0\), \(h_K(r)=M\).
On each of the intervals separated by \(\pi/4\), the difference
\(h_W(r)+1/2-M\) is a positive-coefficient sine/cosine combination
plus a constant, hence concave. Its possible minimum endpoints are
\(0,\theta_0\), and \(\pi/4\) if \(\theta_0\ge\pi/4\).
The first is positive because
\[
                           h+s+1/2>M;
\]
the second is the endpoint check.

To include the possible intermediate endpoint \(\pi/4\), set
\[
 b'=M/\sqrt2-1/2\ge b,\quad
 a'=\sqrt{R^2-b'^2},\quad c'=A-a',\quad
 d'=\sqrt{R^2-c'^2},\quad h'=d'(1-1/c').
\]
We have \(b'\le D\), \(a'>7/4>A/2\), \(c'\ge c\),
\(c'\ge d'>b'>1/2\), and all the hypotheses of the scalar inequality
(17) hold for this auxiliary endpoint tuple. Apply it at
\(Y'=M/\sqrt2\). It yields
\[
                         h'+a'-1>\sqrt2 M-s.
\tag{27}
\]
At fixed \(R^2\), the function
\(a-1+d(1-1/c)\), \(c=A-a\), is increasing in a:
its derivative is \(1-f'(c)>0\), where
\[
 f'(c)=d/c^2-(c-1)/d<1/c<1.
\]
Since \(a'\le a\), (3) and (27) imply
\(h+a-1>\sqrt2 M-s\). This is exactly
\(h_W((-1,1)/\sqrt2)+1/2>M\).
Concavity now proves (24) on the whole remaining normal interval.
The entire vertical row is excluded.

Sections3,4,6 exhaust every physical separating-axis possibility in
Section2. No extra unit exists in the diagonal exterior pocket.

## 7. Four explicit exact polynomial certificates

Here is one common notation making the algebra entirely reproducible.
For a polynomial \(P(x,y)\) of degree at most n in x and m in y, put
\[
 \beta_{ij}(P;n,m)=
 \sum_{\substack{k\le i\\l\le j}}
 [x^ky^l]P\,
       \frac{\binom ik}{\binom nk}\frac{\binom jl}{\binom ml}.
\tag{28}
\]
Then the exact Bernstein identity is
\[
 P(x,y)=\sum_{i=0}^n\sum_{j=0}^m
 \beta_{ij}\binom ni x^i(1-x)^{n-i}
                 \binom mj y^j(1-y)^{m-j}.
\tag{29}
\]
The displayed basis terms are nonnegative and sum to one on
\([0,1]^2\). In every table below, the integer in row i,column j is
a lower bound for \(1000\beta_{ij}\). All entries are positive.

All coefficient comparisons are exact in \(\mathbb Q(\sqrt2)\).
They can be checked by (28) and the two integer-squared bounds
\[
 \frac{1414213562373095}{10^{15}}
       <\sqrt2<
 \frac{1414213562373096}{10^{15}}.
\tag{30}
\]
For a coefficient \(r+t\sqrt2\), use the lower rational endpoint
when \(t\ge0\) and the upper one when \(t<0\). Thus the tables are
rational lower certificates, not rounded numerical sign assertions.

### Certificates I and II: both E-owned axes

Put \(z=(\sqrt2-1)x,\ b=1/2+y\),
\(\alpha=(Q+4-b^2)/4,\ k=2/5+s\).
For Certificate I, use
\[
 P_I=\sum_{j=0}^4p_j z^j,\qquad
 \begin{array}{ll}
 p_0=(1+k)^2-Q,&
 p_1=4\alpha(1+k-b)+8b-2A(1+k),\\
 p_2=2b^2+4(1-A)\alpha+A^2+2-2k^2,&
 p_3=4\alpha b-4(A/2-\alpha)(1-k),\\
 p_4=(1-k)^2-b^2.&
 \end{array}
\]
This is exactly \((1+z^2)^2F\) in the sector
\(u=\cos\theta,v=\sin\theta,0\le\theta\le\pi/4,z=\tan(\theta/2)\),
after \(a=\alpha\).

For Certificate II, reverse the angle and use the same z,b,alpha with
\[
 \begin{array}{ll}
 p_0=1+2b,&p_1=4(1+b)-4\alpha(1+b-2/5),\\
 p_2=6-4\alpha-4b^2+16/25,&
 p_3=4(1-b)+16/5-4\alpha(7/5-b),\\
 p_4=5-4\alpha-2b.&
 \end{array}
\]
This is the same squared excess for
\(u=\sin\theta,v=\cos\theta,\ 0\le\theta\le\pi/4\).

Both use \((n,m)=(4,3)\).

| i | I: j=0 | j=1 | j=2 | j=3 |
|---|---:|---:|---:|---:|
|0|123|123|123|123|
|1|390|332|253|257|
|2|434|361|287|421|
|3|326|324|378|779|
|4|127|320|640|1428|

| i | II: j=0 | j=1 | j=2 | j=3 |
|---|---:|---:|---:|---:|
|0|2000|2666|3333|4000|
|1|1702|2266|2903|3716|
|2|1335|1768|2318|3191|
|3|862|1165|1600|2458|
|4|127|320|640|1428|

### Certificate III: W-owned northwest, E-owned northeast

Use \(z=(\sqrt2-1)x,b=1/2+y,\alpha=(Q+4-b^2)/4,h_0=2/5\), and
\[
\begin{split}
 K_z&=(b-h_0)+2z+6z^2+2z^3-(2+b-h_0)z^4,\\
 T_z&=1+b+(4+2h_0)z+2z^2+(-4+2h_0)z^3+(1-b)z^4,\\
 D_z&=1+z^2,\qquad W_z=1+2z-z^2,\\
 P_{III}&=K_z^2+T_z^2-2\alpha K_zD_zW_z-b^2D_z^2W_z^2.
\end{split}
\tag{31}
\]
For \(u=\sin\theta,v=\cos\theta,z=\tan(\theta/2)\), this is exactly
\(D_z^2W_z^2(|z^*|^2-a^2-b^2)\) from (16), after \(a=\alpha\).
Its denominator is positive throughout the closed sector.
Use \((n,m)=(8,3)\).

| i | j=0 | j=1 | j=2 | j=3 |
|---|---:|---:|---:|---:|
|0|1606|1012|934|1873|
|1|1861|1312|1247|2218|
|2|2073|1604|1589|2630|
|3|2210|1853|1922|3074|
|4|2240|2023|2210|3512|
|5|2122|2070|2403|3891|
|6|1808|1941|2445|4147|
|7|1239|1570|2259|4193|
|8|350|880|1757|3920|

### Certificate IV: the complete vertical center-cap inequality

Use exactly the rectangle map (21), with t replaced by y in (28).
Define c,C,N by (19), and take \(P_{IV}\) to be the polynomial
\({\cal P}\) in (22). Its degree is at most \((10,5)\);
use the degree-elevated identity (29) with \((n,m)=(20,5)\).
No rectangle is subdivided.

| i | j=0 | j=1 | j=2 | j=3 | j=4 | j=5 |
|---|---:|---:|---:|---:|---:|---:|
|0|391|467|533|587|629|658|
|1|287|361|424|477|516|541|
|2|199|268|328|377|411|431|
|3|129|192|247|289|318|331|
|4|82|136|182|217|237|241|
|5|62|102|137|161|170|163|
|6|73|95|114|124|120|99|
|7|121|119|118|110|89|51|
|8|211|178|151|120|79|21|
|9|351|278|219|160|92|10|
|10|548|425|325|231|132|21|
|11|810|625|474|338|202|56|
|12|1147|886|674|486|305|118|
|13|1570|1215|928|678|444|209|
|14|2090|1622|1244|921|624|333|
|15|2721|2115|1630|1219|848|493|
|16|3478|2708|2094|1579|1121|691|
|17|4378|3410|2644|2007|1448|931|
|18|5438|4237|3290|2510|1833|1218|
|19|6681|5202|4043|3096|2284|1555|
|20|8129|6323|4914|3773|2805|1946|

The formulas and tables prove all four strict inequalities on their
complete continuous domains, including every parameter endpoint.

## 8. Completion scope

The empty pocket is the original exterior diagonal region proved in
the physical cap source. No square was moved or forced to acquire an
extra contact. The two side pockets retain their full slider means and
every original extra; they are not replaced by abstract caps for a
capacity assertion.

The present theorem, together with central capacity one, leaves a
precise joint completion gate: at least two of the three extras must
fit in the two actual side pockets. No bound on their total capacity
is asserted here. Physical radial loaded masks and the zero-diagonal
alternating class keep their separate full domains. This proof uses no
Lean compilation, CI, sampled frame or numerical optimization premise.

