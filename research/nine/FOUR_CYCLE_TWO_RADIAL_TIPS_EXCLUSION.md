# The entire two/two physical-circle-corner opposite-load C4 mask is impossible

**Status: complete hand exclusion; root and independent full hand audits passed.**
Work in the compatible strict selected physical certificate, in
\[
                      79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Suppose the positive component is A--B--U--D--A with one pendant
radial leaf at A, with B,D loaded and U unloaded. Assume **both B,D
have two physical circle corners**. Every split of each body's two
circle weights is retained, including a zero weight at one corner.

**Theorem.** This entire two/two mask is impossible. Both radial leaf
types at A, every orientation, all shared-side means, and all four
arbitrary completion squares remain in the argument.

Unlike FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md, this theorem does not need
the secondary minimizer or a physical AU contact.

## 1. The complete channel and transverse domain

Put
\[
                         h=\sqrt{R^2-1/4}-1.
\tag{2}
\]
The radius window gives h>9/10 and
\(\varepsilon=\max(h-1,0)<1/60\).
The unit-bypass theorem puts U in a side-normal channel. Choose its
vertical direction upward and its transverse direction toward A:
\[
 \begin{split}
 U&=[X-1,X]\times[Y,Y+1],\\
 A&\subseteq\{x\ge X+g\},\qquad g\ge0,\\
 B&\subseteq\{y\le Y\},\qquad
 D\subseteq\{y\ge Y+1\}.
 \end{split}
\tag{3}
\]
A's vertical projection contains [Y,Y+1]. Its radial leaf gives a
point of A in the closed epsilon-disk, so
\[
                               X+g\le\varepsilon.
\tag{4}
\]
The two actual channel applications, with arbitrary possible side
means, have the same vertical force line by U's torque equation:
\[
                         p=(x,Y),\qquad p+e_y=(x,Y+1),
                         \qquad x\le X\le\varepsilon.
\tag{5}
\]
Their common positive force magnitude is gamma.

A parallel to U is already excluded for every load mask by
FOUR_CYCLE_PARALLEL_BYPASS_EXCLUSION.md. Thus A is oblique. Its
unique leftmost vertex lies strictly between the heights Y and Y+1:
its two vertical distances to the upper and lower extreme vertices
are positive and strictly less than one, while its vertical projection
contains the entire unit interval. Consequently neither p nor p+e_y
can belong to A, even if x=X=X+g.

Every two-physical-circle-corner unit square is radial S: in its
radial/tangential frame it is [h,h+1] times [-1/2,1/2]. This is a
physical classification; it does not impose equal circle weights.

## 2. Neither loaded tip can be parallel to U

First consider an oblique lower tip B. Its unique top vertex is p.
Write its inward axes
\[
                r=(c,-s),\quad t=(-s,-c),\qquad
                c,s>0,\quad c^2+s^2=1.
\tag{6}
\]
A physical circle vertex cannot be shared with U. Hence p is one
of B's two inner vertices, and its radial direction is either r
or t. The two exact possibilities are
\[
                  p=h r-\tfrac12t,
                  \qquad p=-\tfrac12r+h t.
\tag{7}
\]
The first has x-coordinate hc+s/2>1/2 because h>1/2 and c+s>1.
It contradicts (5). The second is therefore necessary, and gives
\[
                   p=-\tfrac12r+h t,
                   \qquad x=-c/2-hs<-1/2.
\tag{8}
\]
The analogous upper-tip calculation, with inward axes
r_D=(c_D,s_D), t_D=(-s_D,c_D), gives the same dichotomy and the
same strict negative bound whenever D is oblique.

If B is parallel to U, its physical radial direction can only be
downward. A horizontal radial direction would put B's top at1/2,
so D's farthest vertical projection would be at least5/2>R.
An upward radial direction would put B's top at h+1, making that
projection even larger. Therefore
\[
       B=[-1/2,1/2]\times[-h-1,-h],\quad Y=-h,
       \qquad -1/2\le x\le1/2.
\tag{9}
\]
Reflection gives the only parallel upper-tip possibility:
\[
       D=[-1/2,1/2]\times[h,h+1],\quad Y+1=h,
       \qquad -1/2\le x\le1/2.
\tag{10}
\]
A parallel tip and an oblique tip cannot share the force line (5),
by (8)--(10). Two parallel tips would give h=1/2, impossible.
Thus both B and D are oblique, and both take the negative-x
possibility (8).

## 3. The two complete radial frames are forced to be mirrors

Both channel vertices have squared norm h^2+1/4. Since they are
p and p+e_y, this forces
\[
                                  Y=-1/2.
\tag{11}
\]
The lower and upper coordinate equations are
\[
                   2hc-s=1,
                   \qquad 2hc_D-s_D=1.
\tag{12}
\]
For fixed h, the function 2h sqrt(1-z^2)-z is strictly decreasing
on (0,1). Hence c_D=c and s_D=s. Moreover
\[
                                   s>1/2.
\tag{13}
\]
Indeed the function's value at1/2 is h sqrt(3)-1/2>1 because
h>9/10>sqrt(3)/2.

The two bodies are therefore
\[
 \begin{split}
 B&=p+[0,1]r+[0,1]t,
      &r=(c,-s),\quad t=(-s,-c),\\
 D&=p+e_y+[0,1]r_D+[0,1]t_D,
      &r_D=(c,s),\quad t_D=(-s,c),
 \end{split}
\tag{14}
\]
with p=-r/2+h t and p+e_y=-r_D/2+h t_D.

## 4. Every A application lies on the relative interior of an inner face

Let q_B,q_D be the actual applications to A, including any weighted
means of genuine shared segments. They lie in A, and by (3)
\[
                         (q_B)_y\le Y,
                         \qquad (q_D)_y\ge Y+1.
\tag{15}
\]
We cover all four B faces and their endpoints.

The left lateral face p+[0,1]t has x-coordinate at most x<=X+g.
Except possibly at p it is strictly to A's left. The endpoint p
cannot belong to A by Section1. Thus no A application is there.

The outer radial face p+t+[0,1]r has support h+1 in direction t.
A distinct unit neighbor across that face would have maximum
t-projection at least h+2>R, since every unit square has width at
least one. It cannot be contained in the disk. Its two endpoints
are also unshareable circle vertices. Thus this entire face is
excluded.

Every point q on the right lateral face p+r+[0,1]t has
\[
                              q_y\le Y-s.
\]
Its vertical distance from q_D in (15) is at least1+s>3/2>sqrt(2).
No two points of the unit square A can have that distance. This
excludes the whole face, including its inner endpoint p+r.

The only remaining A-contact set on B is consequently the relative
interior of its inner face p+[0,1]r. Reflection gives the upper
statement, so
\[
             q_B=p+\tau r,\qquad
             q_D=p+e_y+\sigma r_D,
             \qquad 0<\tau,\sigma<1.
\tag{16}
\]
This conclusion retains any actual shared-side means. The unique
support normals from A into the two bodies are t and t_D. No free
vertex-normal or side-ownership assumption has been introduced.

## 5. Positive force and torque exclude all remaining weight splits

Let the A-tip force magnitudes be mu_B,mu_D>0. The two resultant
circle vectors, with whatever nonnegative corner weights the
certificate assigns, are
\[
              F_B=\mu_Bt-\gamma e_y,
              \qquad F_D=\mu_Dt_D+\gamma e_y.
\tag{17}
\]
Their coordinates in their respective inward frames are
\[
 \begin{array}{ll}
 F_B\cdot r=\gamma s>0,
     &F_B\cdot t=\mu_B+\gamma c>0,\\
 F_D\cdot r_D=\gamma s>0,
     &F_D\cdot t_D=\mu_D+\gamma c>0.
 \end{array}
\tag{18}
\]
The two contact lines on B intersect at
\[
                         Q_B=p-(\tau/s)e_y.
\]
Its own coordinates are
\[
                    Q_B\cdot r=-1/2+\tau,
                    \qquad Q_B\cdot t=h+\tau c/s>0.
\tag{19}
\]
Torque about Q_B makes it collinear with F_B: every circle force
is radial, so its total origin torque is zero. The positive second
coordinates in (18)--(19) make the proportionality positive. The
first coordinate in (18) then forces tau>1/2.

The reflected calculation at D gives sigma>1/2. Therefore (16)
has vertical separation
\[
             (q_D)_y-(q_B)_y
                      =1+s(\tau+\sigma)>1+s>3/2>\sqrt2.
\tag{20}
\]
Again both applications belong to the same unit square A, whose
diameter is sqrt(2). This is the final contradiction.

All physical two-circle masks, including either zero individual
corner weight, were kept in (17)--(19). The proof has not selected
equal weights or replaced a side mean by a vertex.

## 6. Exact remaining opposite-load domain

This closes the entire physical two/two opposite-loaded-pair C4
alternative in the selected certificate. Combining it with
FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md at the canonical minimizer,
the remaining opposite-loaded-pair C4 can have only the mixed
physical mask: one loaded tip with one physical circle corner and
the other with two.

Every weight split of that remaining radial tip, every singleton
owner or retained free normal, all channel means, and all four
extras must still be handled. The all-three-loaded C4 and diamond
branches also remain open. No whole parent-cell or unrestricted
nine-square closure is asserted.

No numerical pose search, Lean compilation, CI, secondary-minimizer
assumption, or change of the strict point-normal convention is used
in the two/two exclusion above.
