# Equal-type transmissions from a common loaded corner

**Status:** independently reviewed exact conditional hand proof. This
excludes a further subcase of the three-loaded five-cycle, including
nonparallel directions. It does not handle every mixed five-cycle.

Work in the radius window

\[
                       79/40\le R\le3/\sqrt2,
 \qquad b=R-\sqrt2.
                                                               \tag{1}
\]

In particular

\[
                         11/20<b\le1/\sqrt2.                \tag{2}
\]

The contact and loaded-leaf formulas used below are those of
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) and
[CYCLIC_STRESS_REDUCTIONS.md](CYCLIC_STRESS_REDUCTIONS.md).

## 1. A supported square cannot cross the horizontal axis

Set P=(−b,0). Let

\[
 0\le\theta\le\pi/4,\quad c=\cos\theta,\quad s=\sin\theta,
 \quad n=(c,s),\quad Q=P+n=(c-b,s).
\]

Suppose a unit square K has Q on its supporting face with inward normal n:

\[
                 Q\in K,\qquad n\cdot(X-Q)\ge0
                 \quad\hbox{for every }X\in K.             \tag{3}
\]

**Lemma.** If K meets the closed lower half-plane y<=0, every vertex of K
has norm strictly less than R.

First observe the uniform bound

\[
 \begin{aligned}
 |Q|^2&=1+b^2-2bc\\
 &\le1+b^2-\sqrt2b
 <1+\left(\frac{11}{20}\right)^2
                  -\frac75\frac{11}{20}
 =\frac{213}{400}<\frac9{16}.                              \tag{4}
 \end{aligned}
\]

Here the quadratic in b decreases on the interval (2), and sqrt(2)>7/5.
Thus Q and any vertex at distance at most one from Q are strictly inside
the radius-R disk.

If theta<=pi/8, there is an even stronger bound. Since
cos(pi/8)>10/11 and b>11/20,

\[
                 |Q|^2=1+b^2-2bc<b^2.
\]

Every point of K is within sqrt(2) of Q, so its norm is less than
b+sqrt(2)=R. This proves the lemma for these angles without any further
condition on K.

### 1.1. Q is a square vertex

Assume theta>=pi/8. Because K reaches y<=0 and s>0, exactly one of the
two edges out of Q points downward. Write the two unit edge directions as

\[
                  (\cos\phi,-\sin\phi),\qquad
                  (\sin\phi,\cos\phi).
\]

The support condition and the requirement that the downward edge reach
y<=0 give

\[
                         \theta\le\phi\le\pi/2-\theta.    \tag{5}
\]

Three vertices are already covered by (4). The fourth is Q plus a vector
of length sqrt(2) with polar angle pi/4−phi. The polar angle of Q is at
least theta, since c−b>=0 and subtraction of b from its horizontal
coordinate rotates (c,s) toward the positive vertical axis. On the other
hand,

\[
                    \pi/4-\phi\le\pi/4-\theta\le\theta.
\]

For the possible angles in (5), their differences from the angle of Q
lie between zero and pi. Therefore the norm of the fourth vertex is
maximized when phi=theta. Its squared norm is at most

\[
                             (2c+s-b)^2+c^2.               \tag{6}
\]

Put M=sqrt(2)+2c+s. Then M>1, while Cauchy--Schwarz and elementary radical
bounds give

\[
 M\le\sqrt2+\sqrt5<\frac{17}{12}+\frac94=\frac{11}{3}.
\]

As the function \((M+1/M)/2\) increases for M>1,

\[
 \frac{M^2+c^2}{2M}
 \le\frac{M+1/M}{2}
 <\frac{65}{33}<\frac{79}{40}\le R.                         \tag{7}
\]

Since 2c+s−b=M−R, inequality (7) is exactly the strict comparison of (6)
with R². This proves the vertex case.

### 1.2. Q lies on a side

The side-normal condition fixes the square's frame. With
\(n^\perp=(-s,c)\), write

\[
 K=Q+[0,1]n+[-u,1-u]n^\perp,
 \qquad 0\le u\le1.
\]

Its lowest coordinate is s−uc, so intersection with y<=0 requires
u>=s/c. Each vertex depends affinely on u. By convexity of the norm, it
is enough to check u=1 and u=s/c. The first endpoint is covered by the
vertex case. At the second endpoint the four vertices are

\[
 \begin{aligned}
 V_{00}&=(1/c-b,0),\\
 V_{01}&=(1/c-s-b,c),\\
 V_{10}&=(1/c+c-b,s),\\
 V_{11}&=(1/c+c-s-b,c+s).
 \end{aligned}                                             \tag{8}
\]

For V_00 and V_01, the absolute horizontal coordinate is less than one
and the absolute vertical coordinate is at most one. Indeed
\(1\le1/c\le\sqrt2\), \(0\le s\le1/\sqrt2\), and (2) imply
these horizontal bounds directly. Their norms are less than sqrt(2)<R.

For V_10, use \(c+1/c\le3/\sqrt2<9/4\). Its horizontal coordinate
is positive and less than 17/10, so

\[
                 |V_{10}|^2<\frac{289}{100}+\frac12
                            =\frac{339}{100}<R^2.          \tag{9}
\]

For V_11, write its positive coordinates as x,y. Then

\[
                   1\le y\le\sqrt2,\qquad
                   x+y=1/c+2c-b\le3-b<49/20.               \tag{10}
\]

The inequality \(1/c+2c\le3\) follows by monotonicity on
\(1/\sqrt2\le c\le1\). The convex quadratic
\((49/20-y)^2+y^2\) attains its maximum on this interval at an endpoint.
At y=1 its value is 1241/400. At y=sqrt(2), use sqrt(2)>7/5 to bound its
value strictly below \((21/20)^2+2=1241/400\). Hence

\[
                         |V_{11}|^2<1241/400<R^2.           \tag{11}
\]

This proves the side case and the lemma.

## 2. Consequence for the mixed five-cycle

Suppose an entire positive component is

\[
                         A-U-C-V-B-A,
\]

with precisely A,B,C loaded and U,V unloaded degree-two transmitters.
Assume that both contacts on C coincide and that U and V are both side
transmitters of width one.

Aggregate the two positive contact forces at their common point. Their
sum supports C at that point, and torque balance makes the aggregate
force line radial. The loaded-leaf calculation applies. A radial side
type has its effective contact at the midpoint of its inward side, while
a radial diagonal type has its effective contact at the inward vertex.

If the common point lies in the relative interior of a side, its supporting
normals coincide. Both transmissions then point the same way, a case
excluded by
[PARALLEL_MIXED_FIVE_CYCLE.md](PARALLEL_MIXED_FIVE_CYCLE.md).
Otherwise the point is a vertex. The loaded-leaf classification makes C
radial diagonal type, and after rotation its common contact is P=(−b,0).
Its outward normal cone there consists of directions with angles in
[−pi/4,pi/4]. The two outgoing transmission directions lie in this cone.

The total circle load on C is horizontal. Thus its force equation makes
the two outgoing directions lie on opposite sides of the horizontal axis,
unless both are horizontal. The horizontal case was already excluded;
if either angle alone were zero, force balance would force the other
to be zero as well. We may therefore write the directions as theta>0 and
−eta<0, with theta,eta<=pi/4.

The contacts on A and B are respectively P+n_theta and P+n_{−eta}, by
the exact width-one transmission formula. A and B lie on the outward
sides of the corresponding supporting lines, so the lemma applies to A
and, after horizontal reflection, to B. Because both squares are loaded,
A must lie wholly in y>0 and B wholly in y<0. They cannot touch, contrary
to the positive edge A--B.

Therefore two side transmitters in this mixed five-cycle cannot have
coincident contacts on C. This includes the nonparallel common-corner
subcase and does not require a symmetry assumption on the five squares.

## 3. Two diagonal transmitters are impossible as well

Retain the coincident-contact hypothesis, but suppose both unloaded
transmitters are diagonal type. A common contact in the relative interior
of a C side again gives parallel directions, already excluded. At a
common vertex the aggregate argument above again makes C radial diagonal
type with contact P=(−b,0).

The two outgoing directions have angles theta and −eta, where
\(0\le\theta,\eta\le\pi/4\). Each diagonal transmitter has at P an
interior angle of pi/2, centered on its outgoing ray. If theta+eta<pi/2,
these two open tangent cones overlap, and the two transmitter interiors
overlap near P. Hence disjointness requires

\[
                         \theta=\eta=\pi/4.
\]

The far contacts are therefore \(Q_+=(1-b,1)\) and
\(Q_-=(1-b,-1)\). A unit square supported at Q_+ with inward normal
\((1,1)/\sqrt2\) cannot extend more than \(1/\sqrt2\) downward from
Q_+. For vertex support, one of its incident edges rises and the only
possible downward edge has angle at least −pi/4. For side support, the
side descends by at most \(1/\sqrt2\), while translation in the inward
normal direction raises height. Thus the upper endpoint square has

\[
                            y\ge1-1/\sqrt2>0.
\]

The reflected lower endpoint square lies wholly below the horizontal
axis. Once again they cannot touch. This argument uses no genericity or
selected-normal convention.

Consequently a mixed three-loaded five-cycle with coincident C contacts
must have one side transmitter and one diagonal transmitter. The two
equal-type cases are excluded by Sections 2 and 3.
