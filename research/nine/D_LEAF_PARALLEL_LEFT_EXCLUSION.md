# The entire parallel-left D-leaf triangle branch is impossible

**Status: complete exact hand proof; two independent hand audits passed.** In the
declared radius window, no positive D-leaf triangle-plus-leaf component
can have its two triangle reactions on the articulation both horizontal
and leftward. The proof covers arbitrary orientations of both loaded
neighbors, every shared-side application mean, and every circle-corner
weight mask. It excludes the core itself, without a completion premise.

Together with `D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md`, the exhaustive
contact localization and legitimate simultaneous normal selections,
this supplies the second complete D alternative. The S alternative is
separately excluded in `S_LEAF_TRIANGLE_EXCLUSION.md`.

## 1. Setup, load signs, and uniform constants

Write

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[h-1,h],\quad 0<h<1.                  \tag{1}
\]

The D leaf is attached to the right side of \(A\), through
\((1-s,0)\), with a positive horizontal bridge force. The two
other triangle bodies \(B,C\) are loaded, touch each other, and
receive horizontal rightward forces from \(A\). Thus both have
rightmost support line

\[
                              x=-s.                    \tag{2}
\]

Let their actual wall application points be
\(p_B=(-s,y_B)\), \(p_C=(-s,y_C)\), with positive force
magnitudes \(\mu_B,\mu_C\). The points may be weighted means
on shared sides. In all cases

\[
 -1<y_B,y_C<1,\qquad |y_B-y_C|\le1,
 \qquad \mu_By_B+\mu_Cy_C=0.                            \tag{3}
\]

The last identity is origin-moment balance on \(A\).

Write \(m_B,m_C\) for the two positive circle-load vectors.
As proved in `TRIANGLE_LEAF_CORE_REDUCTION.md`, every positively
weighted circle corner of these bodies has negative horizontal
coordinate, and all such corners are pairwise acute. In particular
\((m_B)_x,(m_C)_x<0\). Let \(f\) be the positive contact
force from \(B\) to \(C\). The two body equations are

\[
 \mu_Be_x+f+2m_B=0,\qquad
 \mu_Ce_x-f+2m_C=0.                                     \tag{4}
\]

The force \(f\) cannot be horizontal. A horizontal separator
between two positive-width squares whose rightmost coordinates are
both \(-s\) is impossible: it would require the rightmost
coordinate of one to be at most the strictly smaller leftmost
coordinate of the other. Consequently the vertical load components
are nonzero. Label the bodies so that

\[
                  (m_B)_y>0>(m_C)_y,\qquad f_y<0.        \tag{5}
\]

The needed uniform estimates are

\[
                 \frac13<s<\frac9{20},
                 \qquad R^2>\frac{61}{16}.              \tag{6}
\]

The upper bound on \(s\) and the squared-radius comparison are in
`D_LEAF_ARTICULATION_CONTACT_LOCALIZATION.md`. For the lower
bound, \(\sqrt2>24/17\) and

\[
 \frac{1105}{256}<\frac{662}{153}
  =\frac{22}{9}+\frac{32}{17}
  <\left(\sqrt2+\frac23\right)^2
\]

show \(R<\sqrt2+2/3\), hence \(s>1/3\).

We also use its support-span lemma and all reflected versions:
if \(p\) minimizes \(n\cdot x\) on a unit square and
\(n_x<0\), then its rightmost coordinate is strictly less than
\(p_x+1\).

## 2. A corner-positioned square is strictly inside the circle

The following estimate will settle every shared-side wall case.
Put

\[
 Y=\sqrt{R^2-(s+1)^2},\qquad k=Y-1.
\]

We have

\[
 Y^2>\left(\frac{79}{40}\right)^2
          -\left(\frac{29}{20}\right)^2
       =\frac{2877}{1600}>\frac{16}{9},
 \qquad Y>\frac43.                                     \tag{7}
\]

**Lemma 2.1.** Every unit square with rightmost support \(x=-s\)
and top support \(y=k\) is strictly contained in the circle of
radius \(R\).

*Proof.* Its vertices, for some \(a,b\ge0\) with
\(a^2+b^2=1\), are

\[
 (-s,k-a),\quad(-s-b,k),\quad
 (-s-a-b,k-b),\quad(-s-a,k-a-b).                         \tag{8}
\]

This parametrization includes both aligned endpoint orientations.
Let \(w=a+b\), so \(1\le w\le\sqrt2\). The first
two vertices are strictly inside because their absolute horizontal
coordinates are at most \(s+1\), and their absolute vertical
coordinates are strictly less than \(Y\).

For the left vertex, the squared-radius deficit is

\[
\begin{aligned}
 D_L
 &=(s+1)^2+Y^2-(s+a+b)^2-(Y-1-b)^2\\
 &=2s(1-w)-2ab+2Y(1+b)-1-2b-b^2\\
 &>\frac{77}{30}
       -\left(\frac9{10}a+\frac7{30}b+b^2+2ab\right).
\end{aligned}                                                   \tag{9}
\]

Here we used \(s<9/20\), \(w\ge1\), and \(Y>4/3\).
Cauchy--Schwarz gives

\[
 \frac9{10}a+\frac7{30}b
 \le\frac{\sqrt{778}}{30}<\frac{14}{15}.
\]

Also \(b^2+2ab<13/8\), since

\[
 13a^2+5b^2-16ab
    =\frac{(13a-8b)^2+b^2}{13}>0.
\]

Therefore \(D_L>77/30-14/15-13/8=1/120>0\).

For the bottom vertex the deficit is

\[
\begin{aligned}
 D_D
 &=(s+1)^2+Y^2-(s+a)^2-(Y-1-w)^2\\
 &=2s(1-a)+(2Y-1)+2(Y-1)w-a^2-2ab\\
 &>\frac73-(a^2+2ab)\ge\frac13>0.
\end{aligned}                                                   \tag{10}
\]

Thus every vertex is strictly inside the disk, and convexity gives
the assertion for the entire square. \(\square\)

## 3. Exclude every case with an aligned wall neighbor

Suppose one of \(B,C\) has a vertical right support side, hence
is axis-aligned. Reflect and interchange the bodies if needed so it
is \(B\) in (5). Since its horizontal interval is
\([-s-1,-s]\), its positive upper circle corner has height
\(Y\) from (7), and necessarily

\[
                  B=[-s-1,-s]\times[k,k+1].             \tag{11}
\]

Indeed \(Y>1\), so its center cannot have zero vertical coordinate;
the upper loaded form has its whole vertical interval positive.
In particular the actual wall mean satisfies \(y_B\ge k>0\),
and (3) gives \(y_C<0\).

If \(C\) is also aligned, its negative circle load puts it in
\([-s-1,-s]\times[-Y,1-Y]\), strictly below \(B\).
They cannot touch. Thus we may assume \(C\) has a unique
rightmost vertex, namely its wall application \(p_C\).

Write \(n=f/|f|\). By (5), \(n_y<0\).

If \(n_x<0\), its maximum on \(B\) is at the bottom-left
corner \((-s-1,k)\). The same point minimizes \(n\) on
\(C\). The support-span lemma puts the rightmost coordinate
of \(C\) strictly below \(-s\), contradicting (2).

If \(n_x>0\), its maximum on \(B\) is the bottom-right
corner \((-s,k)\). This is a point of \(C\) on its right
support line, so it must equal the unique vertex \(p_C\).
That would give \(y_C=k>0\), again a contradiction.

The remaining possibility is \(n=(0,-1)\). Then \(C\)
has top support \(y=k\), in addition to its right support
\(x=-s\). Lemma 2.1 makes it strictly circle-clear, contradicting
its positive circle weight.

This excludes every case in which either wall support is a side,
including arbitrary aggregate application points on shared sides.

## 4. Exact section geometry when both wall supports are vertices

Both right supports are now unique vertices. Write

\[
 p_B=(-s,y_B),\quad
 B=p_B+[0,1](-a,b)+[0,1](-b,-a),\qquad a,b>0,\quad a^2+b^2=1,
                                                               \tag{12}
\]

\[
 p_C=(-s,y_C),\quad
 C=p_C+[0,1](-c,d)+[0,1](-d,-c),\qquad c,d>0,\quad c^2+d^2=1.
                                                               \tag{13}
\]

The common separating normal has negative vertical component.
Applying it to the two wall vertices gives \(y_B\ge y_C\).
Equality would make the wall vertices coincide, and both squares
would contain a short open segment directed horizontally left from
that point in their open interiors, because all four horizontal
inward-axis components in (12)--(13) are strictly negative.
This is impossible. Thus (3) implies

\[
                 y_B>0>y_C,\qquad
                 0<\Delta:=y_B-y_C\le1.                \tag{14}
\]

Put \(a=\cos\theta,b=\sin\theta\) and
\(c=\cos\psi,d=\sin\psi\), with both angles in
\((0,\pi/2)\). Horizontal reflection followed by interchanging
the two bodies replaces \((a,b,c,d)\) by \((d,c,b,a)\).
We can therefore assume

\[
                                  b\le c.               \tag{15}
\]

Measure horizontal depth \(x\ge0\) to the left of their common
wall. Their lower and upper section boundaries are

\[
 \ell_B(x)=
 \begin{cases}
 y_B-(a/b)x,&0\le x\le b,\\
 y_B-1/a+(b/a)x,&b\le x\le a+b,
 \end{cases}
\]

\[
 u_C(x)=
 \begin{cases}
 y_C+(d/c)x,&0\le x\le c,\\
 y_C+1/d-(c/d)x,&c\le x\le c+d.
 \end{cases}                                             \tag{16}
\]

At every depth shared by the two squares, their actual supporting
separator with negative vertical normal forces \(\ell_B(x)\ge
u_C(x)\). A physical contact makes equality hold somewhere.
Both breakpoints \(b,c\) occur before depth one, whereas both
full widths exceed one, so these are genuine common-depth
breakpoints.

If \(b<c\), the difference in (16) has negative initial slope,
middle slope \((bc-ad)/(ac)\), and positive final slope.
If \(\theta\le\psi\), its minimum occurs at \(x=c\)
(possibly throughout the middle interval), and contact requires

\[
 \Delta=\frac{1+ad-bc}{a}
        =\frac{1-\sin(\theta-\psi)}a>1,
\]

contradicting (14). Therefore \(\theta>\psi\), its minimum
is at \(x=b\), and

\[
 \Delta=a+\frac{bd}{c}\le1,\qquad
 T=p_B+(-b,-a)=p_C+\frac bc(-c,d).                     \tag{17}
\]

The contact lies in the relative interior of the upper side of
\(C\), with outward normal from \(B\) to \(C\)
equal to \((-d,-c)\). Moreover (17) gives
\(\tan\psi\le(1-a)/b=\tan(\theta/2)\). Together with
\(b<c\), which means \(\theta+\psi<\pi/2\), this yields

\[
                0<\psi<\frac\pi6,\qquad
                d<\frac12,\quad c>\frac{\sqrt3}{2}.      \tag{18}
\]

The equality case \(b=c\) is handled separately next. No
supporting normal is assigned to its vertex/vertex contact by (17).

## 5. The coincident-breakpoint case b=c is impossible

If \(b=c\), then \(a=d\), and the minimum in (16) is at
the common breakpoint. Thus \(\Delta=2a\le1\), so
\(a\le1/2\) and \(b\ge\sqrt3/2\).

By (14), the unique farthest vertex of \(B\) is its leftmost
vertex, and likewise for \(C\). For example the squared-norm
differences between the left vertex of \(B\) and its upper or
lower vertices are respectively

\[
                1+2bs-2ay_B>1-2a+2bs>0,
                \qquad 1+2as+2by_B>0.
\]

The corresponding inequalities for \(C\) follow by reflection.
The wall vertices themselves belong to the circle-clear \(A\).

Put \(\tau=(y_B+y_C)/2\) and \(X=s+a+b\). The two
circle vertices are \((-X,\tau+b)\) and \((-X,\tau-b)\).
Their equal squared radius gives \(\tau=0\). Hence
\(y_B=a,y_C=-a\), and the mutual contact is
\((-s-b,0)\).

Vertical circle-force balance gives equal positive circle weights
\(\lambda_B=\lambda_C=\lambda\). Equation (3) then gives
\(\mu_B=\mu_C\), and the horizontal components of (4)
force the mutual contact force to be vertical. Its magnitude is
\(2\lambda b\), while \(\mu_B=2\lambda X\). Moment
balance on \(B\) requires

\[
                            aX=b(s+b).                  \tag{19}
\]

But their difference is

\[
 aX-b(s+b)=s(a-b)+2a^2+ab-1<0,
\]

because \(a<b\), \(s>0\), \(2a^2\le1/2\), and
\(ab\le1/2\). This contradicts (19), for every possible
strict common normal at the mutual vertex/vertex contact.

## 6. In the strict case, both circle loads are unique left vertices

Assume now \(b<c\), so (17)--(18) hold. The left vertex of
\(C\) is

\[
                         z_C=(-s-c-d,y_C+d-c).            \tag{20}
\]

It is strictly farther from zero than its upper vertex, by the
positive squared-norm difference \(1+2ds-2cy_C\), and
than its lower vertex, by

\[
                     1+2cs+2dy_C>1-2d+2cs>0.
\]

Its wall vertex is in \(A\) and cannot touch the circle.
Thus (20) is the unique circle vertex of \(C\).

In fact

\[
                              -y_C>\frac14.              \tag{21}
\]

Otherwise, putting \(v=c-d>0\), \(w=c+d\), its circle
equation would give

\[
\begin{aligned}
 R^2
 &=(s+w)^2+(v-y_C)^2\\
 &\le s^2+\frac{33}{16}+(2s+\tfrac12)c+(2s-\tfrac12)d\\
 &\le s^2+\frac{33}{16}+\sqrt{8s^2+\tfrac12}\\
 &<\frac{81}{400}+\frac{33}{16}+\frac32
   =\frac{753}{200}<\frac{61}{16}<R^2,
\end{aligned}                                                   \tag{22}
\]

a contradiction.

For \(B\), its left vertex is strictly farther than its lower
vertex, because the difference is \(1+2as+2by_B>0\).
Its only other possible circle vertex is the upper one
\((-s-a,y_B+b)\). If that vertex touched the circle and
\(y_B\le3/4\), then

\[
\begin{aligned}
 R^2
 &\le(s+a)^2+(\tfrac34+b)^2\\
 &\le s^2+\frac{25}{16}+\sqrt{4s^2+\frac94}\\
 &<\frac{81}{400}+\frac{25}{16}+\frac95
   =\frac{713}{200}<\frac{61}{16}<R^2.
\end{aligned}                                                   \tag{23}
\]

Thus any such upper circle vertex would require \(y_B>3/4\),
which with (21) contradicts \(y_B-y_C\le1\).
Consequently \(B\) too has a unique circle vertex,

\[
                         z_B=(-s-a-b,y_B+b-a).            \tag{24}
\]

This derivation excludes all two-circle-corner weight masks by actual
geometry, rather than assuming a single positive atom in advance.
By (5), the vertical coordinates in (24) and (20) are strictly
positive and strictly negative, respectively.

## 7. The two exact torque equations contradict the available wall height

Each body's horizontal wall-force line and its mutual-contact force
line are nonparallel. Force and torque balance imply that their
intersection lies on the line of its unique radial circle load.
Equivalently, take moments about that intersection: both contact
forces have zero moment there, so the remaining circle vector must
pass through it.

For \(B\), intersect the horizontal line \(y=y_B\) with
the line through \(T\) in direction \((-d,-c)\). This gives

\[
 q_B=\left(-s-\frac{bc-ad}{c},\;y_B\right).             \tag{25}
\]

Let \(S_B=s+a+b\) and \(Y_B=y_B+b-a>0\). Collinearity
with (24) says

\[
 S_By_B=\left(s+\frac{bc-ad}{c}\right)Y_B.
\]

Substituting \(y_B=Y_B-(b-a)\) simplifies this exactly to

\[
                \frac{a(c+d)}c\,Y_B=S_B(b-a).            \tag{26}
\]

All other factors are positive. Therefore

\[
                           b>a,\qquad b>1/\sqrt2.        \tag{27}
\]

For \(C\), the corresponding intersection with \(y=y_C\)
is

\[
                         q_C=(-s-b/c^2,y_C).             \tag{28}
\]

Using its circle vertex (20), and writing \(v=c-d\),
\(w=c+d\), \(x=b/c^2\), collinearity gives

\[
                         y_C(w-x)=-(s+x)v.              \tag{29}
\]

The right side is negative, and \(y_C<0\); hence \(w-x>0\)
and

\[
                         -y_C=\frac{v(s+x)}{w-x}.       \tag{30}
\]

We now prove that this last expression is strictly greater than one,
contradicting \(y_C>-1\) in (3).

**Lemma 7.1.** For \(0\le\psi\le\pi/6\), with
\(c=\cos\psi,d=\sin\psi,v=c-d,w=c+d\),

\[
           F(\psi):=\frac{1+v}{\sqrt2\,c^2}+\frac v3-w>0.
                                                               \tag{31}
\]

*Proof.* Since \(v'=-w\), \(w'=v\), differentiation gives

\[
 F'(\psi)
 =\frac{-1-d^2+cd+2d}{\sqrt2\,c^3}-\frac w3-v.
\]

The numerator of the fraction is at most \(1/2\), using
\(d\le1/2\) and \(cd\le1/2\). Its denominator is at
least \(3\sqrt6/8>3/4\), so the fraction is strictly less
than \(2/3\) (also immediately if the numerator is negative).
Meanwhile \(w\ge1\) and
\(v\ge(\sqrt3-1)/2>1/3\), so \(w/3+v>2/3\).
Thus \(F'<0\) throughout the interval. At its right endpoint,

\[
 F(\pi/6)=\frac{\sqrt6+\sqrt2-\sqrt3-2}{3}>0,
\]

because the positive quantities \(\sqrt6+\sqrt2\) and
\(\sqrt3+2\) have squared values differing by exactly one.
This proves (31). \(\square\)

By (6), (27), and (31),

\[
\begin{aligned}
 v(s+x)-(w-x)
 &=vs+(1+v)\frac b{c^2}-w\\
 &>\frac v3+\frac{1+v}{\sqrt2\,c^2}-w
 =F(\psi)>0.
\end{aligned}
\]

Since the denominator in (30) is positive, this proves
\(-y_C>1\), the required contradiction.

## 8. Complete scope

The wall-support split is exhaustive: each support face is either a
side, handled in Section 3, or a unique vertex, handled in
Sections 4--7. The latter proof retains coincident section
breakpoints and their freely chosen mutual vertex/vertex normal,
and proves uniqueness of the circle corners only after covering
all alternatives. Shared-side wall applications were never fixed
at arbitrary endpoints.

**Theorem 8.1.** The entire parallel-left alternative of a positive
D-leaf triangle-plus-leaf component is impossible throughout (1).
This is a physical force-and-torque contradiction for the full
alternative, independent of every remaining square.

Combined with the independently proved S exclusion, the complete
D contact localization, the permitted simultaneous generic normal
selections, and the nonparallel owner exclusion, this supplies a
whole-cell exclusion for C1.3.b1 once the assembled prerequisite
chain is independently audited. It is not an unrestricted
nine-square lower bound: other mixed cyclic cells and the general
seven-cycle completion remain separate.
