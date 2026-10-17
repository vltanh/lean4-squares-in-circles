# Equality pullback to the original eight squares

This is a hand theorem about the equality interface. Its input is the
global terminal capture for every boundary representative. That global
input is already available in the computer-assisted proof and is still
being replaced analytically. No equality information about a translation
path, a numerical minimizer, or an artificial boundary center is assumed.

The conclusion classifies the seven original exterior squares: five
centers and both orientation clusters are rigid; two centers have precisely
the indicated one-dimensional freedoms. Classifying the admissible eighth
square and the full joint parameter domain is a further, explicitly
retained equality obligation.

## 1. Keep the initially chosen separating axes

Let an actual optimal packing be in the disk of squared radius \(q_*\).
The central-core theorem selects its unique square containing the closed
radius-\(1/12\) disk in its open interior. Cyclically order the other seven
squares and choose one actual signed separating axis on each adjacent pair.

The radial-boundary proof in
[CYCLIC_RADIAL_BOUNDARY_REDUCTION.md](CYCLIC_RADIAL_BOUNDARY_REDUCTION.md)
can retain **these same seven signed axes for its entire deformation**.
Indeed, when moving square \(i\), use the two initially selected adjacent
inequalities. They are still valid by induction, since every earlier
motion retained them. Their normals are fixed because all square frames
are fixed. Their intersection has a nonzero recession direction: use
the sum of the inward halfplane normals, or a perpendicular direction
if the normals are opposite. Move to first contact with the outer or
core boundary. The same two inequalities remain valid, and all other
selected inequalities are unchanged.

This proves a strengthening of that boundary theorem: for any initially
selected seven-axis assignment there is a boundary representative with
the same labels, actual frames, cyclic order, and all seven selected
signed witnesses. The centers and their individual rays need not remain
fixed. No such stronger positional assertion is required here.

## 2. Equality at a captured boundary representative fixes the original frames

Assume the completed capture supplies a canonical labeling
\(A,B,T,D,E,H,G\), a tilt \(t\in[.1,.16]\), the allowed signed
owners, the projected-slider bounds, and \(S\le1/500\), for this
boundary representative at its original squared radius \(q_*\).
Any use of an outer-radius expansion is pulled back before this step,
as in the unrestricted radius proof.

The exact terminal inequality is
\[
q_*\ge q_*+\frac{3\mu_H}{8}(t-t_*)^2+
 \sum_{i=A,B,D,E,H}\mu_i
 \left|p_i+o_i+\frac{F_i}{2\mu_i}\right|^2+
 \frac9{100000}S .
\]
Every coefficient displayed here is strictly positive. Therefore
\[
 t=t_*,\qquad S=0.
\]
The actual A,B,T,D,E frames coincide modulo quarter turns, and the
actual H,G frames coincide at tilt \(t_*\). These are also the
**original** square frames, since the boundary deformation never changed
any frame. We may rotate the entire original packing so that the
A,B,T,D,E frame is zero.

The seven selected normals are among the terminal's allowed witnesses.
At \(S=0\), either allowed owner of an aligned edge supplies the same
normal, so the residual owner ties cause no ambiguity.

## 3. Reapply the exact stationary dual directly to the original centers

Use the stationary solution \((q_*,y_*,t_*)\) and put
\[
\begin{aligned}
x_1&=\sqrt{q_*-y_*^2},&
x_2&=\sqrt{q_*-(y_*+2)^2},&
x_3&=x_2-3,\\
y_3&=\sqrt{q_*-x_3^2},&
y_4&=y_3-2,&
x_4&=-\sqrt{q_*-y_4^2}.
\end{aligned}
\]
Write \(e=(\cos t_*,\sin t_*)\), \(f=(-\sin t_*,\cos t_*)\), and
\[
 h_1=(\cos t_*)x_1+(\sin t_*)y_*-2-\cos t_*,
 \qquad
 h_2=-(\sin t_*)x_4+(\cos t_*)y_4-1-\sin t_*.
\]
The five stationary centers are
\[
\begin{array}{c|c}
 A&(x_1-\tfrac12,\ y_*+\tfrac12)\\
 B&(x_2-\tfrac12,\ y_*+\tfrac32)\\
 D&(x_3+\tfrac12,\ y_3-\tfrac12)\\
 E&(x_4+\tfrac12,\ y_4+\tfrac12)\\
 H&(h_1+\tfrac12)e+(h_2+\tfrac12)f.
\end{array}                                                   \tag{1}
\]
Denote them by \(p_i^0\).

The hand adaptive-dual theorem supplies positive disk weights
\(\mu_i\), with \(\sum_i\mu_i=1\), and positive contact weights
\(\lambda_e\). The selected offsets are
\[
 o_A=(\tfrac12,-\tfrac12),\quad
 o_B=(\tfrac12,\tfrac12),\quad
 o_D=(-\tfrac12,\tfrac12),\quad
 o_E=(-\tfrac12,-\tfrac12),\quad
 o_H=-\tfrac12e-\tfrac12f .
\]
For the original centers, let \(g_e\ge0\) be the gap on the initially
selected signed separator. It is nonnegative because that separator
was chosen from the original packing. Define
\[
 {\cal D}=\sum_i\mu_i|p_i+o_i|^2-\sum_e\lambda_e g_e.
\]
All seven normals now have exactly their stationary directions.
The force identities give
\[
 F_i=-2\mu_i(p_i^0+o_i)\quad(i=A,B,D,E,H),
 \qquad F_T=F_G=0.
\]
Completing the five center squares therefore gives the exact identity
\[
 \boxed{{\cal D}=q_*+
   \sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2.}                \tag{2}
\]
The constant is \(q_*\), since the stationary comparison has its five
selected vertices on the circle and all seven contact gaps zero.

Containment and the nonnegative original gaps give
\[
 q_*-{\cal D}
 =\sum_i\mu_i\bigl(q_*-|p_i+o_i|^2\bigr)
      +\sum_e\lambda_e g_e\ge0.                        \tag{3}
\]
Equations (2)–(3) force every squared displacement to vanish:
\[
 p_A=p_A^0,\ p_B=p_B^0,\ p_D=p_D^0,\ p_E=p_E^0,\
 p_H=p_H^0.                                           \tag{4}
\]
They also force \(g_e=0\) on all seven selected edges, because every
contact weight is positive. This conclusion concerns the original
packing, before any boundary deformation.

Notice that no original projected-slider bounds or original center
proximity are needed in (2). At zero frame error both slider forces
vanish identically. Thus transferring only the frames and the initially
selected signed witnesses is sufficient.

## 4. The two exterior slider freedoms

The D→T and T→B contact normals are the positive horizontal axis.
Their zero gaps imply
\[
 (p_T)_x=(p_D)_x+1=(p_B)_x-1=x_2-\tfrac32.
\]
The H→G contact normal is \(e\), with support sum 1. Therefore
\[
 \boxed{p_T=(x_2-\tfrac32,z),\qquad
        p_G=p_H^0+e+\eta f.}                            \tag{5}
\]
The other mixed contact G→A fixes the same \(e\)-coordinate of G,
so it supplies no additional condition on \(\eta\). Every exterior
frame and every other exterior center is already fixed by (1),(4).

Consequently, up to a Euclidean isometry and relabeling, every optimal
packing consists of the five rigid squares in (1), the two sliders in
(5) with their fixed frames, and one remaining unit square. The remaining
variables must satisfy disk containment and the actual pairwise
nonoverlap conditions. Their full allowed domain, including the
remaining square's possible orientations, must be specified to finish
the equality classification.

The converse for any explicitly specified feasible parameter domain is
immediate: the five selected stationary vertices have norm
\(\sqrt{q_*}\), so every resulting feasible eight-square packing attains
exactly the sharp radius.

## 5. Scope of uniqueness

The exact construction already proves three independently variable
positions on nondegenerate intervals. Hence an isolated configuration
cannot be the uniqueness conclusion. The remaining goal is an exact
classification of the whole equality family, with a necessary and
sufficient parameter domain, modulo the ordinary isometries and square
relabeling.

This note closes the equality transfer through the boundary deformation,
conditional on global hand capture. It does not claim that the remaining
central-square parameter domain has been classified.
