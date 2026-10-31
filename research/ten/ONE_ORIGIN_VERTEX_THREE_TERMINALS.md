# One origin-vertex square and three radial terminals leave capacity nine

**Status:** hand proof with two independent mathematical audits. This is a complete
physical capacity bound at squared radius 17/4, not an assertion that an
arbitrary minimizing packing has the specified configuration.

Put Q=17/4. A **radial side terminal** in this note is a unit square with
center (3/2)e and side axes e,Je for a unit vector e. Its inward side is the
segment e+[-1/2,1/2]Je. Its two outer vertices lie on the circle of squared
radius Q.

**Theorem.** A packing in D_Q that contains one unit square with a vertex at
the origin and at least three radial side terminals has at most nine squares.
All other squares may have arbitrary orientations.

The proof uses the test circle of radius rho=11/10. In addition to the arc
bound already proved in
[THREE_ORIGIN_VERTEX_SQUARES.md](THREE_ORIGIN_VERTEX_SQUARES.md), we need a
small positive arc bound for centers nearer the origin.

## 1. A square whose center norm is at least 1/2 occupies more than 3/40 radians

**Small-center arc lemma.** A unit square in D_Q with center norm at least
1/2 intersects the rho-circle in arcs of total angular length greater than
3/40.

For center norm at least 1/sqrt(2), the existing arc lemma gives the stronger
bound gamma=2arcsin(10/11)-pi/2>2pi/9. Thus assume that the squared center norm
r^2 lies between 1/4 and 1/2. Use the square's own coordinates, with center
(u,v), u>=v>=0, and put

\[
 U=u+1/2,\qquad V=v+1/2,\qquad
 \phi(x)=\arcsin(x/\rho),\qquad \rho=11/10.
\]

The square's left-edge vertices have squared norms at most

\[
                  r^2+1/2-u+v\le1<\rho^2,
\]

whereas its upper-right vertex has squared norm

\[
             r^2+1/2+u+v\ge r^2+1/2+r\ge5/4>\rho^2.     \tag{1}
\]

Also v<=1/2 and V<=1<rho. The part with negative first coordinate, if any,
lies entirely inside the rho-circle: both of its vertices on the left edge
and both vertices on the line x=0 lie inside that disk.

If U>=rho, the positive-angle circle arc from angle zero to phi(V) lies in
the square. Its length is at least phi(1/2)>3/40. Hence it suffices to treat
U<rho. The circle intersection then has total angular length exactly

\[
 L(u,v)=\phi(U)+\phi(V)-\pi/2
       +\max\{0,\phi(U)+\phi(1/2-v)-\pi/2\}.              \tag{2}
\]

The first term is the positive-angle arc near the upper-right corner; it is
positive by (1). The second is the possible negative-angle arc near the
lower-right corner. No component comes from the left edge, whose whole
segment is inside the test disk.

### 1.1 Reduce the minimization to center radius 1/2

For fixed u, (2) is nondecreasing in v>=0. Where the second term vanishes
this is immediate. Where it is positive, the derivative in v is

\[
                    \phi'(1/2+v)-\phi'(1/2-v)\ge0,
\]

because phi' is increasing on [0,rho). Therefore decrease v until either
u^2+v^2=1/4 or v=0. In the latter case u>=1/2 and

\[
                 L(u,0)=2\bigl(\phi(u+1/2)+\phi(1/2)-\pi/2\bigr),
\]

which increases with u. Its minimum is attained at u=1/2. Thus the global
minimum of (2) lies on

\[
          u^2+v^2=1/4,\qquad 1/(2\sqrt2)\le u\le1/2.      \tag{3}
\]

Reducing these center coordinates preserves disk containment, so no
infeasible comparison square has been introduced.

### 1.2 Locate the exact minimum on that quarter-circle

Write v=sqrt(1/4-u^2). The second term in (2) is positive precisely when

\[
 U^2+(1/2-v)^2>\rho^2
 \quad\Longleftrightarrow\quad u-v>23/50.                  \tag{4}
\]

Before this threshold only the first term contributes, and it decreases as
u increases. Here is an exact derivative check. Put s=u+v. On (3),

\[
\begin{split}
 &u^2\bigl(\rho^2-(u+1/2)^2\bigr)
  -v^2\bigl(\rho^2-(v+1/2)^2\bigr)\\
 &\qquad=(u-v)\left(\frac{71}{100}s-\frac18-\frac12s^2\right)\ge0.
                                                                    \tag{5}
\end{split}
\]

The parenthesis is positive for 1/2<=s<=1/sqrt(2): its derivative is
71/100-s>0 and its value at 1/2 is 21/200. Formula (5), after multiplying
by the positive square-root denominators, gives the asserted nonpositive
derivative of phi(U)+phi(V).

After the threshold, v<1/10. Indeed v>=1/10 and u<=1/2 would give
u-v<=2/5<23/50. On 2/5<=x<=3/5,

\[
 \phi''(x)=\frac{x}{(\rho^2-x^2)^{3/2}}<1,
\]

since rho^2-x^2>=17/20 and (3/5)^2<(17/20)^3. The derivative of (2) along
(3), while its second term is positive and v>0, consequently satisfies

\[
\begin{split}
 \frac{dL}{du}
 &=2\phi'(U)-\frac{u}{v}
       \bigl(\phi'(1/2+v)-\phi'(1/2-v)\bigr)\\
 &>2/\rho-2u\ge20/11-1>0.                                \tag{6}
\end{split}
\]

Continuity includes the endpoint v=0. Therefore the exact minimum occurs at

\[
 u_0=(\sqrt{721}+23)/100,\qquad
 v_0=(\sqrt{721}-23)/100,                                  \tag{7}
\]

where u_0^2+v_0^2=1/4 and u_0-v_0=23/50. The second arc has zero length
there.

### 1.3 A rational lower bound for the minimum angle

Let U_0=u_0+1/2 and V_0=v_0+1/2. At (7),

\[
 U_0^2+(1-V_0)^2=\rho^2.
\]

For L_0=phi(U_0)+phi(V_0)-pi/2>0, the angle-addition formula gives

\[
 \sin L_0
 =\frac{U_0V_0-(1-V_0)\sqrt{\rho^2-V_0^2}}{\rho^2}.      \tag{8}
\]

The elementary bound sqrt(721)>134/5 gives

\[
 U_0>499/500,\quad V_0>269/500,\quad 1-V_0<231/500,
 \quad \sqrt{\rho^2-V_0^2}<24/25.
\]

Substitution in (8) yields

\[
 L_0\ge\sin L_0>
 \frac{(499/500)(269/500)-(231/500)(24/25)}{121/100}
 =\frac{23351}{302500}>\frac3{40}.                         \tag{9}
\]

The last difference is 1327/605000. This proves the small-center arc lemma.

## 2. One origin vertex limits the number of smaller centers

The specified origin-vertex square contains the full unit circular sector
in its right-angle tangent cone. Every other center has norm at least 1/2:
otherwise its open inscribed radius-1/2 disk contains the origin and meets
the specified square's interior near that vertex.

There are at most two centers of norm strictly below 1/sqrt(2). For such a
center, its direction lies outside the occupied right-angle sector and more
than pi/4 from each bounding ray. Otherwise its distance from the bounding
unit radial segment would be less than 1/2, contradicting inscribed-disk
disjointness. All these directions therefore lie in one open semicircle.
Two such centers must have angular separation greater than pi/2: if not,
their squared distance is less than the sum of their squared radii, hence
less than one. Three directions in an open semicircle cannot have each
successive separation greater than pi/2. Thus there are at most two.

## 3. Count the arcs and exclude a tenth square

Set

\[
 t=\arccos(10/11),\qquad \gamma=\pi/2-2t,\qquad \sigma=2t.
\]

A radial side terminal occupies an arc of length exactly sigma on the
rho-circle. In its radial coordinates it is [1,2]x[-1/2,1/2]; the circle
condition x>=1 gives the interval [-t,t], and its endpoint transverse
coordinates have absolute value sqrt(21)/10<1/2.

If ten squares were present and at most one center were below 1/sqrt(2),
the nine other squares would contradict the existing gamma>2pi/9 arc
bound. Hence exactly two centers must be smaller. They still have norm
at least 1/2 and contribute more than 3/40 each. Among the other eight
squares at least three are radial side terminals. Total angular measure is
therefore strictly greater than

\[
 5\gamma+3\sigma+2(3/40)=5\pi/2-4t+3/20>2\pi.             \tag{10}
\]

For an exact elementary verification of the last inequality, t<43/100
and pi>157/50 suffice. The latter follows, for example, from Archimedes'
bound pi>223/71. For the former, the alternating Taylor bound gives

\[
 \cos(43/100)\le1-\tfrac12(43/100)^2+\tfrac1{24}(43/100)^4
 =\frac{2181538801}{2400000000}<\frac{10}{11}.
\]

The difference in the last comparison is 3073189/26400000000. Since cosine
decreases on [0,pi], t<43/100. Hence

\[
 \pi/2-4t+3/20>157/100-172/100+15/100=0.
\]

As in the earlier arc proof, each square's circle trace differs from its
interior trace at only finitely many points. Their angular measures add
because the square interiors are disjoint. Inequality (10) is impossible,
proving total capacity at most nine.

## 4. Consequence for the side-plus-vertex tree case

At q=17/4, suppose a positive tree component has exactly two unloaded bodies,
one with the origin in the relative interior of a side and one with the
origin at a vertex, and all loaded bodies are the radial side terminals
described above. These are the precise structural hypotheses of TREE.11 in
[the pinned n=9 inventory](https://github.com/vltanh/lean4-squares-in-circles/blob/901678d95a5197017db81343c7d0182661cc92fc/research/nine/TREE_RADIUS_QUANTIZATION.md).

If it has at least three loaded terminals, the theorem excludes every
ten-square completion. If it has exactly two loaded bodies,
[PHYSICAL_TREE_REDUCTIONS.md](PHYSICAL_TREE_REDUCTIONS.md) reduces it to the
four-square staggered S-S chain. The vertex-origin body is then a boundary
value of one of the two transverse slide parameters; its completion remains
part of the explicitly open staggered-chain problem.

Thus this result excludes the whole three-or-more-terminal part of TREE.11,
while retaining its two-terminal chain boundary. It does not assert an
unrestricted classification of minimizing contact graphs or exclude their
cyclic components.
