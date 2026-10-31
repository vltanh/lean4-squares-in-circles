# A near-radial loaded two-force port is impossible

Status: complete local proof, awaiting independent review. This file was saved
after the workspace rollback of 2026-10-27. It contains a new owner-free
extension of the radial side-port estimate.

Put
\[
 Q_*=1105/256,\qquad \sqrt{17}/2<R\le\sqrt{Q_*}.
\]
All squares below are actual closed unit squares, with pairwise disjoint
interiors, contained in the original circle. Normals and application points
are the original selected ones. In particular no mean is moved to an endpoint.

## 1. Local theorem

Let the physically circle-boundary square \(D\) have true degree two in the
positive body graph, with one of its two actual neighbors physically on the
circle. Assume that \(D\) has exactly one physical circle corner \(Z\).
Let \(n\) be the unit normal pointing from its other neighbor into \(D\),
and let \(Q\) be their actual shared application point. Suppose
\[
 \frac{59}{60}<|Q|<\frac{1001}{1000},\qquad
 u:=Q\cdot n>0,\qquad
 \frac{|Q\cdot Jn|}{u}<\frac3{11}.                 \tag{1}
\]
Then this original configuration is impossible. The two neighbors need not
touch, and their degrees and circle masks are arbitrary.

The true two-force concurrence theorem is
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Its proof uses the true
degree two of \(D\), a boundary neighbor, and the actual force and moment
equations. It does not require an edge between the two neighbors. It gives
\[
 q=Q+\rho n=\lambda Z,\qquad \rho\ge0,\quad\lambda>0. \tag{2}
\]
The physical single-corner mask is essential here: it makes the complete
circle resultant a positive multiple of this actual \(Z\).

Write \(v=Q\cdot Jn\). From (1),
\[
 \frac{|Q|}{u}<\frac{\sqrt{130}}{11}<\frac{23}{22},
 \qquad u-|v|>\frac8{11}u>\frac{16}{23}|Q|.       \tag{3}
\]
The second strict comparison in the first inequality follows by squaring:
\(130/121=520/484<529/484=(23/22)^2\).

### An actual side port

If \(D\) owns the normal \(n\), its minimum \(n\)-side has support \(u\)
and its opposite side has support \(u+1\). The corner \(Z\) is on that
opposite side. Indeed a corner on the minimum side has inward unit segment
in direction \(n\), whose other endpoint has squared norm larger by
\(2u+1>0\), contradicting containment if the first corner were on the circle.
Thus \(Z\cdot n=u+1\), and (2) gives
\[
 \lambda=\frac{u+\rho}{u+1}\ge\frac{u}{u+1}.
\]
Taking transverse components in (2),
\[
 Z\cdot Jn=v/\lambda,\qquad
 R^2=(u+1)^2+(v/\lambda)^2
 \le (u+1)^2\left(1+\frac{v^2}{u^2}\right).
\]
Consequently
\[
 R\le |Q|+\frac{|Q|}{u}
   <\frac{1001}{1000}+\frac{23}{22}
   =\frac{22511}{11000}<\frac{\sqrt{17}}2,       \tag{4}
\]
which is impossible. The last squared reserve is
\(17/4-(22511/11000)^2=30019516/484000000>0\).
This argument includes every actual shared-side mean and both side endpoints.

### An actual vertex port

Otherwise \(Q\) is an actual vertex of \(D\). Let \(f,j\) be its two
orthogonal inward unit side directions. The fact that \(Q\) minimizes the
linear functional \(n\) means that \(n\) belongs to the closed positive
cone of \(f,j\). Hence the direction of \(f+j\) differs from \(n\) by at
most \(\pi/4\). Expressing this vector in the \(n,Jn\) frame gives
\[
 Q\cdot(f+j)\ge u-|v|.
\]
This follows directly from its length \(\sqrt2\), its \(n\)-component at
least one, and the absolute value of its \(Jn\)-component at most one.
The actual opposite corner of \(D\) therefore satisfies, by (3),
\[
\begin{split}
 |Q+f+j|^2
 &\ge |Q|^2+2+2(u-|v|)\\
 &> (59/60)^2+2+\frac{32}{23}\frac{59}{60}\\
 &=Q_*+\frac{24713}{1324800}>R^2.              \tag{5}
\end{split}
\]
This is a physical containment contradiction. It does not use any force
equation or single-corner condition. Together (4) and (5) cover all actual
features, without choosing or changing a contact normal.

## 2. Exact near-south root calculation

The following is a convenient full-equation caller. Let an actual aligned
genuine S root \(A\) occupy
\[
 A=[h-1,h]\times[-v,1-v],\qquad
 0\le\eta\le h\le\varepsilon<1/60,\quad
 1<v\le1+\varepsilon.
\]
Its genuine radial leaf has inner support point \((\eta,-v)\). The strict
lower-right-vertex case has \(\eta=h\); the owned south-side case has
\(\eta=0\). Keep the full true three-force equation at \(A\): the real
leaf, its east neighbor at actual mean \(P=(h,-k)\), and \(D\). Assume
\(0<k<13/50\), and that the actual \(AD\) feature is its northwest
vertex
\[
 Q=(-X,-a_0),\qquad X=1-h,\quad a_0=v-1,
\]
with incoming normal \(n=(-a,b)\), \(a,b>0\), \(a^2+b^2=1\).

Writing the genuine leaf force and using the unchanged force and origin
moment equations gives exactly
\[
 a(k-a_0)=b\left(X+\frac{k\eta}{v}\right).       \tag{6}
\]
For example, the east force has moment \(\mu k\); the radial leaf moment
is zero. Eliminating the leaf magnitude from the two components and that
moment gives (6). In particular \(k>a_0\). Direct substitution gives
\[
 \tan\angle(Q,n)
 =\frac{k(X+a_0\eta/v)}
 {X^2+a_0^2+k(X\eta/v-a_0)}.                    \tag{7}
\]
The denominator is positive. Since \(X>59/60\), \(a_0,\eta<1/60\),
\(X\le1\), \(v>1\), and \(k<13/50\), (7) implies
\[
 \tan\angle(Q,n)
 <\frac{(13/50)(1+1/3600)}{(59/60)^2-13/3000}
 =\frac{46813}{173270}<\frac3{11}.              \tag{8}
\]
The final integer reserve is
\(3\cdot173270-11\cdot46813=4867>0\).
Also
\[
 59/60<|Q|\le\sqrt{1+1/3600}<1001/1000.
\]
Thus Section 1 excludes this caller whenever \(D\) has its stated true
degree, boundary neighbor and unique physical corner. It does not matter
whether \(D\) owns the original \(AD\) normal. In particular a parallel
force pair at the east neighbor does not create an owner-selection exception.

## 3. Scope

This is a local theorem and a local full-force caller. It makes no whole
adjacent-C4 claim. The hypotheses on \(k\) and on the actual northwest
feature must be established by the caller. All remaining physical squares,
including all three completion squares, stay in the original packing.
The vertex half of the theorem is force-free; the side half retains both
original pair forces, the actual mean, and the full genuine circle force.
