# A D leaf at a bowtie tip: the entire nonparallel articulation is impossible

**Status: complete whole-owner hand argument; root and separate independent
full audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\qquad s=1+\sqrt2-R.
\tag{1}
\]
The exact positive graph consists of the two triangles
\(H-A-B-H\), \(H-C-E-H\), and the leaf \(A-L\).
The leaf L is radial D. Thus A has exact positive degree three,
H has degree four, and B,C,E have degree two. All three remaining
physical units are retained.

**Theorem.** In the common selected certificate, the two triangle
reactions at A cannot be nonparallel. This excludes the whole
nonparallel D-leaf articulation, with every H frame, B circle mask,
mutual-contact owner and actual side mean. The parallel D articulation
and both S-leaf articulation types are outside this theorem.

## 1. The complete local selection does not require H to be loaded

The radial-D leaf classification gives
\[
 A=[-s,1-s]\times[h-1,h],\qquad 0<h<1,
\tag{2}
\]
with its positive leaf force directed east through \((1-s,0)\).
A is physically circle-clear. The degree-two triangle bodies B,C,E
are loaded: an unloaded degree-two transmitter cannot have physically
touching neighbors. H is physically circle-clear, since otherwise
H,C,E would be a physical triangle of boundary bodies.

We extend the articulation selection in
D_LEAF_GENERIC_CONTACT_SELECTION.md using only the three true
forces at A and the physical triangle A,B,H.

A vertical A-normal is impossible by the strict support-span lemma:
the other triangle normal has the opposite vertical sign, putting
that whole neighboring unit strictly short of the first one's
supporting horizontal line. If one normal is horizontal, both are
horizontal. Thus in the nonparallel case both normals are nonaxis,
and their actual applications are fixed distinct vertices at heights
h and h-1.

Let those normals and applications be \(n_1,n_2,p_1,p_2\).
Eliminating the two magnitudes from A's vertical force and origin
torque equations gives
\[
 (n_1)_y\det(p_2,n_2)-(n_2)_y\det(p_1,n_1)=0.
\tag{3}
\]
If the first edge is free vertex/vertex, the coefficient of
\((n_1)_x\) in (3) is \((n_2)_y(p_1)_y\ne0\). The same finite
open-dense selection as in that source removes it. The distinct
vertex applications are distinct physical junctions, so
four-junction matching does not couple their parameters.

Prelist all these physical A-stars, including arbitrary degrees and
loads on their two triangle neighbors, before the multiplier theorem.
Impose (3)'s avoidance together with all earlier finite exclusions.
Uncrossing preserves surviving point normals and adds only shared
side forces; thinning only deletes atoms. Every eventual star is in
the prelist, and the preliminary vertical/horizontal argument retains
all shared-side means. No already extracted normal is changed.

Consequently each nonaxis A contact is a vertex of A in a relative
side interior of its neighbor. Opposite A vertices cannot be used:
the radius-free opposite-vertex support-span proof in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2, applies to any
physical unit triangle. The two vertices have opposite heights, so
they lie on one vertical side of A. They cannot both lie on the right
side, because both corresponding horizontal force components and
the leaf component would be positive. They are the two left vertices.

Reflect vertically to place B at the upper vertex. Write
\[
\begin{aligned}
 P&=(-s,h),& n&=(-b,a),& a,b&>0,&a^2+b^2&=1,\\
 Q&=(-s,h-1),&m&=(-d,-c),&c,d&>0,&c^2+d^2&=1,\\
 v&=Jn=(-a,-b),& k&=Jm=(c,-d),\\
 K&=ad+bc>0,&L&=bd-ac.
\end{aligned}
\tag{4}
\]
Here n points A to B, m points A to H, and P,Q are relative
side-interior points of B,H. In particular
\[
                    m=Ln+Kv,\qquad k=-Kn+Lv.
\tag{5}
\]
Normalize the positive leaf magnitude to one. The exact A equations
give the positive AB,AH magnitudes
\[
 \mu=\frac cK,\qquad \nu=\frac aK,\qquad
 h=\frac{ad}{K},\qquad 1-h=\frac{bc}{K}.
\tag{6}
\]
No symmetry of the two neighbors has been imposed.

The elementary bounds used below are
\[
 \frac13<s<\frac49,\qquad \frac9{10}<D<\frac{61}{60}.
\tag{7}
\]
They follow directly from (1) by squaring. Since P belongs to the
boundary square B, \(|P|\ge R-\sqrt2=1-s\); hence
\[
                       h^2\ge1-2s>\frac19,\qquad h>\frac13.
\tag{8}
\]

## 2. Keep the whole opposite triangle and its true resultant

Let g be the B-to-H unit contact normal, T its actual application,
and \(\gamma>0\) its magnitude. The true B equation is
\[
                          F_B=\mu n-\gamma g.
\tag{9}
\]
Let M be the sum of the two true circle resultants of C,E. The
degree-four H equation and the C,E equations give
\[
              M=\nu m+\gamma g,\qquad
              \nu\det(Q,m)+\gamma\det(T,g)=0.
\tag{10}
\]
The complete end-triangle support theorem gives
\[
                   M\ne0,\qquad h_H(M/|M|)<D.
\tag{11}
\]
Here \(h_H\) uses the original circle origin. We never replace the
C,E petal by a radial leaf.

If m,g are independent and their lines meet at q, (10) gives
\(q\parallel M\). Whenever \(q\cdot m>0\) and \(M\cdot m>0\),
this puts q on the positive M ray. No degree-two or circle-load
equation is assigned to H.

If B has one physical circle corner and BH is free, the two B
applications are distinct fixed points: P is side-interior and
T is a vertex. GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes this
entire free case. Its simultaneous preselection is compatible with
Section 1. Thus every surviving free BH contact has B physically
radial S.

## 3. A positive-quadrant support contradiction

When \(L\ge0\), (6) implies
\[
 Q\cdot m=sd+\frac{bc^2}{K}
  >\frac13\sqrt{1-c^2}+c^3
  \ge\frac13-\frac{c^2}{3}+c^3
  \ge\frac{239}{729}>\frac3{10}.
\tag{12}
\]
Indeed \(b\ge c\), \(K\le1\), and
\[
 c^3-\frac{c^2}{3}+\frac4{729}
             =(c-\tfrac29)^2(c+\tfrac19)\ge0.
\]

Suppose M has positive m- and k-coordinates and its positive ray
meets \(Q+[0,\infty)m\). Then \(Q\cdot k>0\), and the angle of
\(M/|M|\) from m is between zero and the angle of Q from m.
The actual point Q+m belongs to H. Its projection is a positive
sine/cosine combination, whose minimum on that interval occurs
at an endpoint. The endpoint values are
\[
       1+Q\cdot m,\qquad |Q|+\frac{Q\cdot m}{|Q|}.
\]
Each is at least \(2\sqrt{Q\cdot m}\). Equation (12) gives
\[
              h_H(M/|M|)>\sqrt{\frac65}>\frac{61}{60}>D,
\tag{13}
\]
contrary to (11). This does not assume that q lies inside H.

## 4. The B-owned transverse normal: a whole scalar inequality

Suppose \(g=v\). If \(L<0\), T minimizes m and maximizes k on H,
so \(T=Q+\rho k\), \(0<\rho<1\). Then
\[
                    n\cdot(T-P)=-a-K\rho<0,
\]
contrary to P being on B's minimum-n side. Thus \(L\ge0\), or
equivalently \(a^2\le h\).

Put
\[
 w=1-h,\qquad x=a/b,\qquad t=\gamma/\mu>0,\qquad
                 0<x\le\sqrt{h/w}.
\tag{14}
\]
In southwest coordinates,
\[
 \nu m=-(h,wx),\qquad M=-(h+wtx,\ w(x+t)),\qquad
                       \nu=\sqrt{h^2+w^2x^2}.
\tag{15}
\]

### 4.1. The actual B circle mask bounds t

B's circle resultant in its own frame is \((\mu,-\gamma)\).
Its farthest n-coordinate is
\[
                         X=1+sb+ah.
\tag{16}
\]
Its farthest negative-v coordinate Y is at least \(1/2\), and
\(X^2+Y^2=R^2\). For the unique mask \(t=Y/X\); for the physical
two-corner mask, arbitrary nonnegative weights give \(t\le Y/X\).

The function \(s\sqrt{1-a^2}+ha\) is concave on
\([0,\sqrt h]\). Its value at zero is s, and at \(\sqrt h\) is
strictly greater than s, since \(\sqrt h>s\). Hence \(X\ge1+s>4/3\).
It follows that
\[
             0<t<\frac{\sqrt{5849}}{64}<\frac65.
\tag{17}
\]
The final comparison is \(25\cdot5849<36\cdot4096\).

### 4.2. Project the actual point Q+m

Let
\[
 \alpha=\arctan(wx/h),\qquad
 \beta=\arctan\frac{w(x+t)}{h+wtx},\qquad
 \beta_0=\arctan(wt/h),\qquad
 \beta_1=\arctan\sqrt{w/h}.
\tag{18}
\]
Then \(0\le\beta-\alpha\), and this difference decreases in x:
\[
 \alpha'=\frac{wh}{h^2+w^2x^2},\qquad
 \beta'=\frac{w(h-wt^2)}
                {(h+wtx)^2+w^2(x+t)^2}.
\tag{19}
\]
If \(h-wt^2\le0\), this is immediate. Otherwise the second
denominator is strictly larger than the first, and its numerator
is smaller. Also \(\beta\) is monotone, with endpoints
\(\beta_0,\beta_1\). Thus
\(\cos(\beta-\alpha)\ge\cos\beta_0\).

The projection of Q+m on \(M/|M|\) is
\[
             F=\cos(\beta-\alpha)+s\cos\beta+w\sin\beta.
\tag{20}
\]
The last two terms are concave in \(\beta\). Consequently
\[
 F\ge\min\left\{
 \frac{(1+s)h+w^2t}{\sqrt{h^2+w^2t^2}},
 \quad
 \frac h{\sqrt{h^2+w^2t^2}}+s\sqrt h+w\sqrt w
 \right\}.
\tag{21}
\]

For the first expression, replace s by \(1/3\). As a function
of t it increases and then decreases, so its minimum on
\([0,6/5]\) occurs at an endpoint. At zero it is \(4/3\).
At \(6/5\) it is
\[
 f(h)=\frac{18h^2-16h+18}
                  {3\sqrt{61h^2-72h+36}}.
\]
Its derivative has numerator \(6(h-1)(61h^2-47h-4)\).
The quadratic has exactly one positive root, between \(1/3\) and 1.
Thus f increases and then decreases, and
\[
               f(h)\ge\min\{f(1/3),f(1)\}=\frac{44}{39}.
\tag{22}
\]

For the second expression in (21), convexity in h gives
\[
              h^2+\frac{36}{25}(1-h)^2\le1
                        \quad(1/3\le h\le1),
\]
since its endpoint values are \(169/225\) and 1. That expression
is therefore at least
\[
                       G(h)=h+\frac13\sqrt h+(1-h)^{3/2}.
\]
Here \(G''>0\), and
\(G'(1/3)=1+\sqrt3/6-\sqrt{3/2}>0\). Hence
\[
 G(h)\ge G(1/3)=\frac13+\frac1{3\sqrt3}+\frac{2\sqrt6}{9}
      >\frac13+\frac4{21}+\frac8{15}=\frac{37}{35}.
\tag{23}
\]
The rational comparisons use \(1/\sqrt3>4/7\) and \(\sqrt6>12/5\).
Thus
\[
                 F>\frac{37}{35}>\frac{61}{60}>D,
\tag{24}
\]
contrary to (11). This excludes all \(g=v\), including \(L=0\).

## 5. A radial-B sign lemma for the obtuse frame sum

Suppose B is physical radial S along n and \(L\le0\). Its facing
side has n-coordinate D, so
\[
                     sb+ha=D,\qquad P\cdot v=sa-hb.
\tag{25}
\]
We claim \(P\cdot v>0\).
Indeed \(L\le0\) is equivalent to \(h\le a^2\). If \(sa-hb\le0\),
then \(s\le ab\), and
\[
                       D=sb+ha\le sb+a^3\le a.
\]
Thus \(D<1\), and monotonicity of \(u\sqrt{1-u^2}\) for
\(u>1/\sqrt2\) gives
\[
                         s\le D\sqrt{1-D^2}.
\tag{26}
\]
This is impossible throughout (1). If \(R\le2\), then
\[
 s\ge\sqrt2-1>\frac25,\qquad
 D\sqrt{1-D^2}<\frac{9\sqrt{19}}{100}<\frac25.
\]
If \(R\ge2\) and \(D<1\), then
\[
 D^2\ge\frac{19}{4}-\sqrt{15}>\frac78,\qquad
 D\sqrt{1-D^2}<\frac{\sqrt7}{8}<\frac13<s.
\]
The cases \(D\ge1\) were already excluded by \(D\le a<1\).
Therefore
\[
                              P\cdot v>0.
\tag{27}
\]

## 6. Every side-axis owner and sign

The triangle side-normal lemma at B and H gives
\[
                         n\cdot g\le0,\qquad m\cdot g\ge0.
\tag{28}
\]
If B owns g, the only possibilities are \(-n,v\).
If H owns g, the only possibilities are \(m,k\).
This covers all shared contacts as well as point contacts with
an owner. We have excluded \(g=v\).

### 6.1. The B-owned normal \(-n\)

Equation (9) gives \(F_B=(\mu+\gamma)n\). Since P's n-coordinate
is positive, the only physical mask with zero transverse circle
resultant is radial S along n, with its two corner weights equal.
Equation (28) gives \(L\le0\), so (27) applies.

T maximizes n on H. In H's frame \(n=Lm-Kk\), and Q is in the
relative interior of its minimum-m side. Thus
\[
                  T=Q+j m-\rho k,\qquad
                  0\le j\le1,\quad0<\rho<1,
\]
with \(j=0\) when \(L<0\); the full \(L=0\) side mean remains.
Using \(v=Km+Lk\),
\[
                 T\cdot v=P\cdot v+b+jK-\rho L>0.
\]
But B's true origin torque requires
\[
                         \mu(P\cdot v)+\gamma(T\cdot v)=0,
\tag{29}
\]
contradicting (27).

### 6.2. The H-owned normal k

If \(L<0\), T is B's minimum-n/minimum-v vertex, so
\(T=P-u v\), \(0<u<1\). Then
\[
                       m\cdot(T-Q)=-c-uK<0,
\]
contrary to Q minimizing m on H. Thus \(L\ge0\).
At \(L=0\), \(k=-n\), already excluded.
For \(L>0\), T lies on H's minimum-k side:
\[
                 T=Q+j m-\rho k,\qquad0\le j\le1,\quad0<\rho<1.
\]
The two incoming force lines meet at \(q=Q+j m\).
Here \(M=\nu m+\gamma k\); (10) makes q a positive multiple of M,
because \(q\cdot m=Q\cdot m+j>0\).
All premises of Section 3 hold, giving (13).

### 6.3. The H-owned normal m

Equation (28) gives \(L\le0\), and
\[
                    M=(\nu+\gamma)m,\qquad h_H(M/|M|)=1+Q\cdot m.
\tag{30}
\]
T lies on H's minimum-m side. On B it lies on the maximum-v side
(with the full side retained if \(L=0\)). Write
\(T=P+j n+t v\), where \(0<t<1\), and \(j=0\) if \(L<0\).
The equality \(m\cdot(T-Q)=0\) gives \(tK=c\). In particular \(c<K\).

We claim \(Q\cdot m>1/60\). Otherwise
\(Q\cdot m=sd+bc^2/K\le1/60\) would imply \(d<1/20\),
\(c>19/20\), and, using \(c<K=ad+bc\le d+b\), \(b>9/10\).
But then
\[
                Q\cdot m\ge bc^2>
                   \frac9{10}\left(\frac{19}{20}\right)^2>\frac1{60}.
\]
Equation (30) is therefore greater than \(61/60>D\), contrary to (11).

## 7. Every surviving free BH normal

Section 2 leaves only physical radial B. Its center must be on n:
its n-coordinate is \(P\cdot n+1/2>1/2\), so it cannot be radial
along the transverse axis. Thus its inner face is \(n\cdot x=D\)
and \(-1/2<P\cdot v<1/2\). The free contact cannot be a circle
vertex. Its actual vertex and strict normal have the form
\[
 T=Dn+\varepsilon\frac12v,\qquad
                 g=-p n+\varepsilon qv,\qquad p,q>0,\quad
                 \varepsilon\in\{-1,1\}.
\tag{31}
\]
B's exact torque is
\[
                \mu(P\cdot v)+
                    \gamma\varepsilon(Dq+\tfrac12p)=0.
\tag{32}
\]

At H, (28) and strictness in its vertex cone give \(m\cdot g>0\).
T therefore lies on the same minimum-m side as Q.
Writing \(T=P+t v\) gives \(tK=c>0\). This excludes
\(\varepsilon=-1\), which would give \(t=-1/2-P\cdot v<0\).
Hence \(\varepsilon=1\), and (32) gives \(P\cdot v<0\).
Section 5 then forces \(L>0\).

The exact actual displacement is
\[
                  T=P+\frac cK v=Q-\frac aK k.
\tag{33}
\]
Since Q is side-interior, \(0<a/K<1\). T is H's
minimum-m/minimum-k vertex, so \(g\cdot m,g\cdot k>0\).
Its line meets the AH line at
\[
                 q_H=Q+\frac{a(g\cdot m)}{K(g\cdot k)}m.
\tag{34}
\]
The coefficient is positive. Equations (10) make \(q_H\) a positive
multiple of \(M=\nu m+\gamma g\), whose m- and k-coordinates
are positive. Section 3 again gives (13).

This exhausts both B circle masks and every actual BH contact type.
H has never been treated as a loaded degree-two tip.

## 8. Exact conclusion and retained parent branches

The common pre-certificate selection removes only the explicitly
listed fixed-point free normals. Every remaining side-axis owner,
parallel owner sign, shared application mean and radial free normal
has been included. Thus no nonparallel D-leaf articulation occurs
in this six-body bowtie-tip-leaf graph.

The parallel D articulation and S-leaf alternatives remain open.
The argument preserves all six core units and all three extras.
It uses no completion motion, numerical pose assumption, angle
subdivision, Lean compilation or CI.

