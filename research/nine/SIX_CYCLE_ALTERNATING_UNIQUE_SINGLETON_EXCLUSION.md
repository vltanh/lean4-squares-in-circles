# The alternating six-cycle with unique loaded corners and singleton side contacts is impossible

**Status: complete whole-interface hand exclusion; root and separate
independent full hand audits passed.**
Work in
\[
                       \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Suppose the exact positive component is an alternating six-cycle
with three loaded bodies \(S_0,S_1,S_2\) and three unloaded
**side-normal** transmitters, one between each consecutive loaded pair.

Assume that each \(S_i\) has exactly one physical circle corner,
and that all six loaded/transmitter intersections are physical
singletons. Retain the existing strict point-normal convention and
diagonal avoidance, every actual transmitter-side application mean,
and all three additional physical units.

**Theorem.** This entire interface family is impossible.

The proof covers both adjacent and opposite choices among the
non-circle vertices, all three possible loaded frames, and both
directions of corner choice. It does not assume that every remaining
alternating C6 lies in this family: physical radial loaded bodies and
genuine shared loaded/transmitter sides are explicitly outside the
present hypotheses.

## 1. Actual singleton features and proper force geometry

Every transmitter's force direction is its own side axis. A selected
point-only vertex/vertex contact cannot have that normal, since the
normal must be strict in both vertex cones. Thus each assumed singleton
intersection is a vertex of its loaded unit in the strict relative
interior of the transmitter's side. The loaded vertex cannot be its
circle corner, because a containing-circle point cannot be shared.

The two actual applications on any one \(S_i\) are distinct.
If they coincided, the two different transmitters would both contain,
near that point, an open half-disk on their respective support sides.
The two open half-planes have nonempty intersection unless their
outward loaded normals are opposite. The latter is excluded by
SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md. Hence a coincidence would
make the two transmitters overlap in their interiors.

Use SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md. Its proper loaded
concurrences \(q_i\) lie inside \(S_i\), since these bodies have unique
physical circle corners. They form a strictly convex triangle
containing the origin. Let its counterclockwise directed forces be
\[
                   f_i=\mu_i n_i,\qquad\mu_i>0,
\tag{2}
\]
on the channel from \(S_i\) to \(S_{i+1}\). Let \(p_i^-,p_i^+\)
be the actual incoming and outgoing loaded applications. Then
\[
 p_i^--q_i=-\alpha_i^- n_{i-1},\qquad
 p_i^+-q_i=\alpha_i^+ n_i,\qquad\alpha_i^\pm\ge0.
\tag{3}
\]
Write
\[
                    \theta_i=\angle(n_{i-1},n_i)\in(0,\pi).
\]
The three force turns satisfy
\[
                            \sum_i\theta_i=2\pi.
\tag{4}
\]

In fact both coefficients in (3) are positive. For an application
adjacent to the circle corner \(z\), the identity \(q=p\) would put
\(z\) parallel to one side of its square, impossible because both
own coordinates of a far circle corner are at least \(1/2\).
The only remaining non-circle vertex is the opposite inner vertex.
It is radial precisely in the radial-D pose: the far corner has
own coordinates \((R/\sqrt2,R/\sqrt2)\). If \(q\) were that inner
vertex, the other distinct non-circle application is an adjacent
vertex and its outward normal would point along a positive own axis.
It exposes an outer face of support \(R/\sqrt2>R-1\), beyond which
a unit neighbor cannot fit. Thus \(q\) is not either application,
and \(\alpha_i^\pm>0\).

## 2. The opposite-vertex alternative is completely excluded

A unique loaded square has three non-circle vertices. Two distinct
ones are either adjacent or the two vertices opposite each other
across the square's other diagonal.

For two adjacent applications, use coordinates
\((0,0),(1,0)\) on their side and \(q=(x,y)\) inside the unit.
Nonparallelism and (3) give \(y>0\). If the angle \(\phi\) between
the two outward rays from \(q\) is acute, then
\[
                         \cot\phi
                             =y-\frac{x(1-x)}y\le1.
\tag{5}
\]
The nonacute case already has \(\phi\ge\pi/2\).
Thus always \(\phi\ge\pi/4\), and
\[
                              \theta_i\le\frac{3\pi}{4}.
\tag{6}
\]
Equality in (6) requires \(q\) to be one of the two opposite vertices
of the unit. Its positive radial relation to the unique circle corner
excludes the adjacent one, so equality requires \(q=z\).

For two opposite applications, their diagonal is a diameter of the
square's circumcircle. Every \(q\) inside the square sees that diameter
under an angle at least \(\pi/2\). Explicitly, for square center \(c\),
\[
            (p_i^--q)\cdot(p_i^+-q)=|q-c|^2-\frac12\le0.
\tag{7}
\]
Hence \(\theta_i\le\pi/2\). Equality puts \(q\) at one of the other
two square vertices. The inner radial-D vertex is excluded by the
outer-face argument in Section1; therefore equality again gives
\(q=z\).

If one loaded body used opposite applications, (4), (6), (7) would
force precisely the turns \(\pi/2,3\pi/4,3\pi/4\), and each \(q_i\)
would equal its actual circle corner \(z_i\). The concurrence triangle
would be a right triangle inscribed in the original circle. The circle
origin would then be the midpoint of its hypotenuse, contradicting
strict origin containment. Two or three opposite-application bodies
already contradict the sum (4).

Consequently **all three application pairs are adjacent**, and
\[
                          \frac\pi2\le\theta_i\le\frac{3\pi}{4}.
\tag{8}
\]

## 3. Exact contact-chord and torque identities

Put
\[
                     u_i=p_i^+-p_i^-,
                     \qquad |u_i|=1,\qquad v_i=-Ju_i.
\tag{9}
\]
The loaded unit lies on the right side of its directed inner contact
side. Indeed, (3), strict positivity of its two coefficients, and the
positive force turn put \(q_i\) strictly to the right of
\(p_i^-p_i^+\). Thus \(v_i\) is its inward unit normal.

There is a unique \(\chi_i\in\{0,1\}\) such that its far circle
corner is
\[
                       z_i=p_i^-+\chi_i u_i+v_i.
\tag{10}
\]
No common value of \(\chi_i\) is yet assumed.

Each side-normal transmitter has exact reserve1, so its actual
application displacement is
\[
                         p_{i+1}^--p_i^+=n_i.
\]
Summing around the actual ring gives
\[
                             \sum_i(n_i+u_i)=0.
\tag{11}
\]
This retains all transverse transmitter means.

Write
\[
                 F_i=f_{i-1}-f_i=2\lambda_i z_i,\qquad\lambda_i>0,
\tag{12}
\]
and define
\[
          K_i=\chi_i f_{i-1}+(1-\chi_i)f_i,\qquad
          g_i=K_i+JF_i,\qquad E_i=|g_i|.
\tag{13}
\]
Actual loaded torque about \(z_i\), using (10), is exactly
\[
                        \det(u_i,K_i)+u_i\cdot F_i=0.
\tag{14}
\]
Hence \(u_i\) is parallel to \(g_i\). The sign is positive:
\[
 \begin{split}
 u_i\cdot g_i
  &=K_i\cdot u_i+F_i\cdot v_i\\
  &=f_{i-1}\cdot(z_i-p_i^-)-f_i\cdot(z_i-p_i^+)\\
  &=H_i(f_{i-1})+H_i(f_i)+H_i(F_i)>0,
 \end{split}
\tag{15}
\]
where \(H_i\) is the support halfwidth of the centered unit \(S_i\).
The final identity follows because \(p_i^-\) minimizes \(f_{i-1}\),
\(p_i^+\) maximizes \(f_i\), and the unique circle corner \(z_i\)
maximizes \(F_i\). Thus
\[
                                  u_i=\frac{g_i}{E_i}.
\tag{16}
\]

## 4. Mixed corner directions cannot close

We prove that all three \(\chi_i\) agree. A cyclic relabeling and,
if necessary, reflection followed by reversal of the cycle reduce
any mixed pattern to
\[
                              (\chi_0,\chi_1,\chi_2)=(1,1,0).
\tag{17}
\]
Reflection with cycle reversal changes every \(\chi\) to \(1-\chi\)
and preserves the counterclockwise force-turn convention.

Here is the full angular content of (16). Rotate an incoming normal
to \((1,0)\), let the outgoing normal have angle
\(\theta\in[\pi/2,3\pi/4]\), and write its two positive magnitudes
as \(p,q\). For \(\chi=1\), the vector \(g\) has coordinates
\[
                       (p+q\sin\theta,\ p-q\cos\theta).
\tag{18}
\]
Its angle \(\eta\) from the incoming normal satisfies
\[
                         \theta-\pi/2\le\eta\le\pi/4.
\tag{19}
\]
For \(\chi=0\), those coordinates are
\[
                     (q(\cos\theta+\sin\theta),\
                           p+q(\sin\theta-\cos\theta)),
\tag{20}
\]
giving
\[
                         \theta-\pi/4\le\eta\le\pi/2.
\tag{21}
\]
These intervals include \(\theta=3\pi/4\), when the first coordinate
of (20) vanishes. At \(\theta=\pi/2\), the \(\chi=1\) angle is
strictly below \(\pi/4\), since \(p,q>0\).

Now choose the absolute force-normal angles
\[
             \arg n_0=0,\quad \arg n_1=\theta_1,\quad
             \arg n_2=2\pi-\theta_0.
\]
Let the offsets of \(u_i\) from \(n_{i-1}\) be \(\eta_i\).
Equations (19)--(21) imply
\[
 \begin{split}
 (u_0)_y&\le-\sin(\theta_0-\pi/4),\\
 (u_1)_y&\le1/\sqrt2,\\
 (u_2)_y&\le-\sin(\theta_0+\pi/4).
 \end{split}
\tag{22}
\]
For the last inequality, its absolute angle lies in
\[
 [\,7\pi/4-\theta_0,\ \theta_1+\pi/2\,]
                                      \subset[\pi,5\pi/4],
\]
where sine is decreasing. The first follows on the corresponding
fourth-quadrant interval.

The vertical component of the left side of (11) is therefore at most
\[
 \begin{split}
 \sin\theta_1-\sin\theta_0
     -\sin(\theta_0-\pi/4)+\frac1{\sqrt2}
     -\sin(\theta_0+\pi/4)
 &=\sin\theta_1+\frac1{\sqrt2}
                       -(1+\sqrt2)\sin\theta_0\\
 &\le1+\frac1{\sqrt2}
                       -\frac{1+\sqrt2}{\sqrt2}=0.
 \end{split}
\tag{23}
\]
Equality in the second line would require
\(\theta_1=\pi/2\) and \(\theta_0=\theta_2=3\pi/4\).
But then \((u_1)_y<1/\sqrt2\) by the strict endpoint statement
after (21). Thus (23) is **strictly negative**, contradicting (11).
All corner directions must agree.

## 5. A convex six-point functional is exactly the physical radius

For either now constant \(\chi\), define
\[
                  \Phi(t)=\sum_i\bigl(|f_i+t|+|g_i+t|\bigr).
\tag{24}
\]
Each \(f_i\) and \(g_i\) is nonzero. The exact channel closure
(11) and (16) give
\[
                         \nabla\Phi(0)
                              =\sum_i(n_i+u_i)=0.
\tag{25}
\]
Since \(\Phi\) is convex, zero is its global minimizer.

The loaded virial identity is also exact. From (12),
\[
                 \sum_i F_i\cdot z_i=R\sum_i|F_i|.
\]
Summation by parts, the actual reserve1 equations and (15) give
\[
 \begin{split}
 R\sum_i|F_i|
   &=\sum_i f_i\cdot(z_{i+1}-z_i)\\
   &=\sum_i\mu_i+
       \sum_i\bigl[
           f_{i-1}\cdot(z_i-p_i^-)-f_i\cdot(z_i-p_i^+)
              \bigr]\\
   &=\sum_i\mu_i+\sum_i E_i
    =\Phi(0).
 \end{split}
\tag{26}
\]

The three force vectors \(f_i\), considered as points, form a
nondegenerate counterclockwise triangle. Their positive lengths
and the turns in (8) put them in their circular order, with the
origin inside that triangle. Its perimeter is exactly
\(\sum_i|F_i|\).
The points \(g_i\) in (13) are precisely the consistently selected
derived corners in TRIANGLE_SQUARE_CORNER_FERMAT_BOUND.md.
That complete inequality, together with (25)--(26), now gives
\[
                       R\le
               \frac{1+\sqrt{4+\sqrt3}}{\sqrt3}
                         <\frac{79}{40},
\tag{27}
\]
contradicting (1).

Sections1--5 exhaust the assumed unique-physical-corner,
all-singleton, three-side-transmitter family. Genuine shared sides
or physical two-corner loads have not been substituted by singleton
or unique-corner limits. They remain separate unresolved cases of
the alternating C6 domain. All original three extra units have been
retained throughout this direct core contradiction.

