# The whole central hole of the unique-corner one-diagonal six-cycle is empty

**Status: complete hand region theorem; root and separate independent
full hand audits passed.** Work in
\[
 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad \sigma=\frac1{\sqrt2}.
\tag{1}
\]
Let the entire selected positive component be an alternating six-cycle,
with three loaded bodies having one **physical** circle corner each,
and exactly one diagonal transmitter.

**Theorem.** The opposite loaded body has exactly one genuine
shared-side transmitter interface. The whole bounded central free
region contains no additional unit square.

Every original shared application mean and all three completion squares
are retained. Combined with the already proved empty diagonal exterior
pocket, all three extras must therefore lie in the two actual side
pockets. Their joint capacity is still a separate obligation.

## 1. The full opposite-body feature cover forces one shared side

Use the complete domain of SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md.
Write the cycle
\[
                    B-W-C-U_C-T-U_B-B.
\]
The diagonal transmitter W has center \((\delta,h)\), with left and
right applications \((1-a,h),(c-1,h)\), where
\[
 \begin{gathered}
 a+c=2+\sqrt2,\quad a^2+b^2=c^2+d^2=R^2,\\
 a>b>\tfrac12,\quad c>d>\tfrac12,\quad a,c<2,\quad h>\tfrac25,\\
 Y_B=h+1-b\in(0,1),\qquad Y_C=h+1-d\in(0,1).
 \end{gathered}
\tag{2}
\]
The bounds \(a,c<2,h>2/5\) are the elementary whole-domain
preliminaries of SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md, Section1;
no polynomial certificate is needed for those bounds.

Put
\[
 \begin{gathered}
 n_B=(\cos\eta_B,-\sin\eta_B),\qquad
 n_C=(-\cos\eta_C,-\sin\eta_C),\\
 \frac\pi4<\eta_B,\eta_C<\frac\pi2,\qquad
                \Sigma:=\eta_B+\eta_C\le\frac{3\pi}4.
 \end{gathered}
\tag{3}
\]
The actual T applications are
\[
 P=(1-a,b-1)+n_B,\qquad Q=(c-1,d-1)+n_C.
\tag{4}
\]
In particular
\[
              Q_x-P_x=\sqrt2-\cos\eta_B-\cos\eta_C>0.
\tag{5}
\]

The full unique-corner turn proof in the inner-capacity source,
Section1, gives the following exhaustive consequence when the turn
at T is \(\Sigma>\pi/2\). Its two applications lie on one actual
inner side, and at least one is a vertex of T. Indeed two T-owned
axes give turn at most \(\pi/2\). With exactly one T-owned axis,
the only larger-turn alternatives are the bottom-side application
with its lower-left vertex, or the reflected left-side alternative.
With no T-owned axis, the opposite-vertex pair has turn at most
\(\pi/2\), leaving precisely the two adjacent pairs on an inner side.
All zero-vector and shared-mean endpoints are covered in that source.
The applications here cannot coincide, by (5).

Let \(t=(\cos\phi,\sin\phi)\) be the direction of that side from P
toward Q. Its first coordinate is positive. The interior of T lies
below this directed side. To verify the sign without a drawing, its
inward unit normal has nonnegative scalar product with both n_B,n_C.
A vector with nonnegative vertical component cannot have this property:
if its vertical component is positive, the two scalar products require
opposite strict signs of its horizontal component; the horizontal
zero-height case also cannot work. Thus the inward normal is \(-Jt\).

P is the left side endpoint if it is a vertex, and Q is the right
side endpoint if it is a vertex. Their actual inward normal cones,
including the side-interior zero tangent component, therefore give
\[
                     \eta_C-\frac\pi2
                       \le\phi\le\frac\pi2-\eta_B.
\tag{6}
\]
In particular \(|\phi|<\pi/4\), and \(t_x>\sigma\).

On the other hand
\[
                  \cos\eta_B+\cos\eta_C>\sigma.
\tag{7}
\]
For an exact check put \(m=\Sigma/2\) and
\(e=(\eta_B-\eta_C)/2\). Then
\[
 |e|<m-\pi/4,\qquad
 2\cos m\cos e>
 2\cos m\cos(m-\pi/4)
 =\cos(\Sigma-\pi/4)+\sigma\ge\sigma .
\]
Equations (5),(7) give \(Q_x-P_x<\sigma\).
Consequently the actual side chord has length
\[
                         |Q-P|<1.
\tag{8}
\]
Its endpoints cannot both be vertices. Exactly one is in the strict
relative interior of the T side. The corresponding force normal is
a T side axis; it is also a side axis of its side-normal transmitter.
Their actual physical intersection therefore has positive length,
even if the transmitter's original mean is a side endpoint.
The other interface cannot be shared, since that would give two
T-owned axes and turn at most \(\pi/2\).

After reflection and relabeling B,C, suppose the shared interface is
with \(U_C\). Then
\[
 t=(\sin\eta_C,-\cos\eta_C),\qquad
 N=Jt=(u,v):=(\cos\eta_C,\sin\eta_C),\quad 0<u<v.
\tag{9}
\]
The actual T side is supported outward by N.

## 2. Two complete endpoint inequalities

We record two whole inequalities used below. For either endpoint,
write its own positive corner coordinates as \(\alpha>\beta>1/2\),
its side-channel angle as \(\eta\in(\pi/4,\pi/2)\), and
\(Y=h+1-\beta\in(0,1)\). The actual proper radial concurrence gives
\[
 k=\cot\eta\in(0,1),\qquad
                       Y=\frac{\alpha-\beta}{\alpha-\beta k}.
\tag{10}
\]
We know \(\alpha<2,h>2/5\). Then
\[
 \boxed{\quad
 Y<\sigma(1+k),\qquad
 Y+\tan(\eta/2)<1+\sigma .
 \quad}
\tag{11}
\]

If \(\beta\ge(1-\sigma)\alpha\), the concave quadratic
\[
       \sigma(1+k)(\alpha-\beta k)-(\alpha-\beta)
\]
is nonnegative at \(k=0\) and strictly positive at \(k=1\).
It is strictly positive for \(0<k<1\), proving the first inequality.

For the second, the function
\[
       \frac{\alpha-\beta}{\alpha-\beta k}
                         +\sqrt{1+k^2}-k
\]
is convex on [0,1]. Its endpoint values are
\(2-\beta/\alpha\le1+\sigma\) and \(\sqrt2<1+\sigma\).
Every interior value is therefore strictly below \(1+\sigma\).
Here \(\sqrt{1+k^2}-k=\tan(\eta/2)\).

It remains to cover \(\beta<(1-\sigma)\alpha\).
Then \(1/2<\beta<3/5\), and \(Y>7/5-\beta\). Since \(\alpha<2\),
\[
 k=\frac{\alpha Y-\alpha+\beta}{\beta Y}
 >
 \frac{4/5-\beta}{\beta(7/5-\beta)}
 \ge\frac5{12}>\sqrt2-1.
\tag{12}
\]
The rational function is decreasing on \([1/2,3/5]\);
its value at \(3/5\) is \(5/12\).
Thus \(\sigma(1+k)>1>Y\). Also
\[
 \tan(\eta/2)
 =\sqrt{1+k^2}-k
 <\sqrt{1+(5/12)^2}-5/12=\frac23<\sigma .
\]
Both inequalities (11) follow. No angle or radius subinterval is
left outside this argument.

## 3. A radius-free unit-square sandwich in the diagonal strip

We prove the exact geometric lemma needed for the central hole.

Let
\[
             W_0=\{(x,y):|x|+|y|\le\sigma\}
\]
be a unit square with horizontal and vertical diagonals. Let E be any
interior-disjoint unit square satisfying
\[
                     E\subset\{|x|\le\sigma,\ y\le0\}.
\tag{13}
\]
For every unit vector \(N=(u,v)\) with \(v\ge u\ge0\), put
\[
 L_0=(1-\sigma)u+(1+\sigma)v,\qquad
 L_1=1+\sigma v.
\]
Then
\[
                 \boxed{\quad
                   \min_{z\in E}N\cdot z\le-\min(L_0,L_1).
                 \quad}
\tag{14}
\]

Choose E's own axes
\[
 e=(A,B),\quad f=(-B,A),\quad
 A,B\ge0,\quad A^2+B^2=1,
 \quad w=A+B,\quad \mu=\max(A,B).
\]
If its center is \((x,y)\), (13) gives
\[
 |x|\le L:=\sigma-w/2,\qquad y\le-w/2.
\tag{15}
\]
Write \(H_E(N)=\tfrac12(uA+vB+|vA-uB|)\).
Let
\[
                         D=-N\cdot c_E+H_E(N)
                           =-\min_E N\cdot z.
\tag{16}
\]

Every separating side axis from W_0 toward E has strictly negative
vertical component. Otherwise its support at one of W_0's horizontal
vertices, together with \(y\le0\), would put all of E outside
\([-\sigma,\sigma]\); a horizontal separator is equally impossible.
The complete remaining possibilities are W_0's two downward diagonal
axes, E's southeast axis \((B,-A)\), or E's southwest axis \((-A,-B)\).
The zero denominator limits below correspond to horizontal axes and
are absent.

### 3.1. The two W-owned axes and the E-owned southeast axis

First suppose the separator is W_0's southeast diagonal.
Using \(x\le L\) and \(y\le x-\sigma-\mu\) gives
\[
 D\ge-\sigma u+\frac12(u+v)w+v\mu+H_E(N).
\tag{17}
\]
The southwest diagonal gives a lower bound larger by
\(u(2\sigma-w)\ge0\), so it suffices to consider (17).

For E's southeast axis, with A>0, its own halfwidth is 1/2, giving
\[
 D\ge-\sigma u+\frac12uw+vC+H_E(N),\qquad
 C=\frac{\sigma(\mu-B)+1/2+Bw/2}{A}.
\tag{18}
\]
Define
\[
                     K=C+w/2
                       =B+\frac{1+\sigma(\mu-B)}A.
\tag{19}
\]

Both (17) and (18) are at least \(L_0\). Here is the full elementary
piecewise-linear verification. Divide their difference from \(L_0\)
by \(v>0\), and put \(\kappa=u/v\in[0,1]\). The only possible bend
is at \(\kappa=A/B\), present only when \(A\le B\).
It suffices to check the two endpoints and that bend.

For (17), the endpoint differences are
\[
              w+\mu-1-\sigma,\qquad w+2\mu-2-\sigma.
\]
They are nonnegative: \(w+\mu\ge2\), and
\(w+2\mu=3\mu+\min(A,B)\ge2\sqrt2>2+\sigma\).
The latter follows by concavity of
\(3\sqrt{1-t^2}+t\) on \(0\le t\le\sigma\) and its two endpoint
values. At the bend the difference, multiplied by B, is
\[
                  (1-A)(1-B)+B(B-\sigma)\ge0.
\tag{20}
\]

For (18), the endpoint differences are
\[
                           K-1-\sigma,\qquad K+\mu-2-\sigma .
\]
If \(A\ge B\), the first follows from
\(K\ge1+\sigma+(1-\sigma)B\), and the second from the identity
\[
            A(K+A-2-\sigma)=(A-1)^2+B(A-\sigma)\ge0.
\tag{21}
\]
If \(A\le B\), use \(K=B+1/A\),
\(B\ge\sigma\), and \(1/A\ge\sqrt2\).
At the bend, the difference multiplied by AB is
\[
                           w(1-A)-\sigma AB\ge0.
\tag{22}
\]
To check (22), write it as
\(A(1-A)+B[1-(1+\sigma)A]\).
If the bracket is nonnegative the claim is immediate. Otherwise
\(B\le1\) bounds it below by
\(1-A^2-\sigma A\ge0\), since \(A\le\sigma\).
These finite linear pieces cover every N and every E frame, including
all axis-aligned endpoints.

Thus all three separator alternatives in this subsection satisfy
\(D\ge L_0\), which is stronger than (14).

### 3.2. The E-owned southwest axis

Here B>0. Its support and (15) give
\[
 D\ge
 \frac{v(\sigma\mu+1/2)-|vA-uB|L}{B}+H_E(N).
\tag{23}
\]
Let \(\theta=\arg e\) and \(\eta=\arg N\), so
\(\eta\in[\pi/4,\pi/2]\).

Suppose first \(vA-uB\ge0\), equivalently \(\theta\le\eta\).
The right side of (23) simplifies exactly to
\[
               u(\sigma-B)+
               v\left[A+\frac{1+\sigma(\mu-A)}B\right].
\tag{24}
\]
This is at least \(L_1\).
If \(A\le B\), subtract \(\sigma v\) from (24).
The result is the scalar product of N with
\[
                \left(\sigma-B,\ A+\frac{1-\sigma A}{B}\right).
\]
Its first coordinate is nonpositive and its second positive.
Its scalar product with an angle-\(\eta\) unit vector increases
as \(\eta\) runs from \(\theta\) to \(\pi/2\); at
\(N=(A,B)\) it equals exactly one.
If \(A\ge B\), the corresponding vector is
\[
                    (\sigma-B,\ A+1/B-\sigma),
\]
with nonnegative coordinates. Its scalar product on
\(\eta\in[\pi/4,\pi/2]\) is concave, so its minimum is at an
endpoint. There the values are respectively
\[
              \sigma(A-B+1/B)\ge1,\qquad
                              A+1/B-\sigma\ge\sqrt2>1.
\]
This proves \(D\ge L_1\) in the first whole case.

Finally suppose \(vA-uB\le0\), so \(\theta\ge\eta\ge\pi/4\)
and \(\mu=B\). The right side of (23) becomes
\[
 f(\theta)=u(A+B-\sigma)
           +v\left[\sigma+\sigma A/B+B-A\right].
\tag{25}
\]
Its minimum on \(\eta\le\theta\le\pi/2\) is at an endpoint.
For full verification,
\[
 f'(\theta)=(v-u)B+(u+v)A-\frac{\sigma v}{B^2}.
\]
With \(t=\cot\theta\),
\[
 B^2f'(\theta)=
       \frac{(v-u)+(u+v)t}{(1+t^2)^{3/2}}-\sigma v .
\tag{26}
\]
The derivative of the first term with respect to t has numerator
\[
                  (u+v)-3(v-u)t-2(u+v)t^2,
\]
which is strictly decreasing on \(t\ge0\) and has one positive
zero. That term has one maximum and no interior minimum.
At \(\theta=\eta\), \(f'(\eta)=1-\sigma/v\ge0\).
It follows that, as \(\theta\) increases, \(f'\) can change sign
only from nonnegative to nonpositive; f has no interior minimum.
The two endpoint values are
\[
                         f(\eta)=1+\sigma v=L_1,\qquad
                         f(\pi/2)=L_0.
\]
Thus (25) is at least \(\min(L_0,L_1)\), proving (14) in the
last separator alternative. This completes the radius-free lemma.

## 4. The whole weak central region supplies the sandwich premises

Translate the actual W center to zero.
The six actual contact vertices of the selected cycle are
\[
 (-\sigma,0),\quad(\sigma,0),\quad
 (\sigma,-Y_C),\quad Q,\quad P,\quad(-\sigma,-Y_B),
\tag{27}
\]
where now
\[
 P=(-\sigma+\cos\eta_B,-Y_B-\sin\eta_B),\qquad
 Q=(\sigma-u,-Y_C-v).
\tag{28}
\]
All vertices are in \(\{|x|\le\sigma,y\le0\}\).
The winding-one region of this polygon is contained in its convex
hull, so any whole central completion unit E satisfies (13).

Moreover the actual T side through P,Q is a supporting line of
the entire contact polygon:
\[
                             N\cdot x=-D,\qquad
                             D=1-\sigma u+vY_C.
\tag{29}
\]
Every other contact vertex is strictly on its upper side.
Relative to Q, the C inner vertex has N-projection1; the right W
vertex has projection \(1+vY_C\), and the left W vertex has
projection \(1+vY_C-\sqrt2u>0\). Relative to P, the B inner
vertex has N-projection \(-\cos\Sigma>0\).
Thus every central E also satisfies
\[
                              \min_E N\cdot x\ge-D .
\tag{30}
\]

These inclusions concern the entire central free union. At shared
junctions use the arbitrarily small physical routing and compact
interior winding argument of CONTACT_RING_HOLE_AREA.md and
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md. Every central extra interior
has winding one in the limiting actual contact polygon. A point
outside any closed half-plane containing all its vertices has
winding zero. Taking closures therefore gives (13),(30) for the
whole unit. Additional unstressed physical contacts can only
subdivide this region; no artificial routing face avoids these
half-planes.

The extra is also interior-disjoint from W. The complete sandwich
lemma applies and gives \(D\ge\min(L_0,L_1)\).

## 5. The exact strict contradiction

Apply (11) to the C endpoint, so \(k=u/v\) and \(Y=Y_C\).
Its first inequality yields
\[
 D=1-\sigma u+vY<1+\sigma v=L_1.
\]
Its second yields
\[
 \begin{split}
 D-L_0
 &=1-u+v(Y-1-\sigma)\\
 &=v\left[\tan(\eta_C/2)+Y-1-\sigma\right]<0.
 \end{split}
\]
Hence \(D<\min(L_0,L_1)\), contradicting Section4.
No central completion unit exists.

This is a whole region theorem for every unique-physical-corner,
one-diagonal alternating six-cycle. It uses no motion, no added force,
no fixed transmitter mean, no numerical stationary core and no
classification of algebraic roots. The three actual extras now all
lie in the two side pockets, because the diagonal exterior pocket is
already excluded. Physical radial loaded masks and the zero-diagonal
alternating family retain their separate domains. The joint side-pocket
capacity remains open; no whole C6 or nine-square closure is claimed.

