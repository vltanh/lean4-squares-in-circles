# A hub-owned endpoint cannot oppose a radial free endpoint in a fan

**Status: complete hand physical-mask exclusion; root and separate independent
full hand audits passed.** Work in
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}
\tag{1}
\]
with the exact positive fan
\[
 Hu_i\quad(1\le i\le4),\qquad u_1u_2,\ u_2u_3,\ u_3u_4.
\tag{2}
\]
H is unloaded and physically circle-clear; all four path bodies are loaded.
The two endpoints have exact positive degree2. The internal bodies retain
all three of their positive forces.

**Theorem.** Suppose the H-to-u_1 normal is an H side axis, allowing a
positive-length shared side with any actual mean. The other endpoint
Hu_4 cannot be a genuine free vertex/vertex contact when u_4 has two
physical circle corners. Both individual circle weights, including either
zero endpoint, are retained. No extra square is moved or removed.

No new normal choice is needed. The proof uses the existing strict
point convention and the actual planar certificate. It does not give
a degree-two equation to either internal body.

## 1. The endpoint contact sets and the radial local routing

The whole-path theorem FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md makes
any two actual endpoint applications more than1 apart. Normalize the
hub, by a rigid coordinate change, as
\[
 H=[0,1]^2,\qquad P=(p,1)\in H\cap u_1,\qquad
 Q=(0,0)=H\cap u_4,\qquad 0<p\le1.
\tag{3}
\]
Here P is the actual u_1 application mean. Its normal is n_1=e_y.
The free endpoint's normal from H is
\[
                         n_4=(-a,-b),\qquad a,b>0.
\tag{4}
\]
Write O=(O_x,O_y) for the **true disk center in these hub coordinates**.
Translations of these displayed coordinates do not translate a force vector.

All actual u_1 contact points on the top side have positive first
coordinate, by the same >1 theorem. The physical boundary graph of the
four path bodies has no nonconsecutive contacts, by the connected loaded
noncontact theorem and the boundary-cycle exclusion. In particular
u_2 is disjoint from u_4 and u_3 is disjoint from u_1.

Put
\[
                 d=\sqrt{R^2-1/4}-1>9/10.
\tag{5}
\]
The local radial-free routing in BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md,
Section1, applies to the actual triangle H,u_3,u_4. It uses only the
radial endpoint's two forces, its zero circle moment, the unit support
span and the physical fact that u_3 touches the circle. No force or
degree condition at u_3 is needed. It gives the following whole local
conclusion: Hu_4 and u_3u_4 are singleton contacts at the two distinct
inner vertices of u_4, and both normals are strict in the corresponding
u_4 vertex cones. In particular u_3 does not contain Q. Neither internal
hub application can therefore coincide with Q.

## 2. The physical fan runs along the right hub arc

The selected physical plane embedding has all four boundary bodies on
its exterior face. Its outer face is H,u_1,u_2,u_3,u_4,H. Hence the two
inner hub spokes have the actual cyclic order between the two endpoint
spokes: their contact sets lie on the same arc of the hub boundary
between H intersect u_1 and Q. A shared-side mean stays on its actual
side of this arc. The endpoint Q is disjoint from both internal bodies
by Section1.

The complete corner-mean check in FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md,
Sections2--3, applies here. Its only use of tip ownership at Q was to
exclude the internal applications there; Section1 supplies exactly that
premise by radial routing. We recall the full exceptional case to make
clear that a coincident application at P is not silently discarded.

For0<p<1, the actual H normal at P is uniquely e_y. If p=1, the
retained strict point convention and the horizontal H axis imply a
positive-length shared Hu_1 side. The actual square is therefore
u_1=[s,s+1] times [1,2], with0<=s<1. Only u_2 can contain P; u_3
is physically disjoint from u_1. A horizontal rightward H normal at P
has a physical contact extending down H's right side, so belongs to
the right arc. For a normal with both components positive, if s>0,
u_1 occupies the upper half-plane locally and H the southwest quadrant.
The only remaining quadrant is southeast, which cannot have the required
positive vertical inward-normal component.

If s=0, H and u_1 fill the left half-plane locally. A u_2 side-interior
contact therefore has horizontal rightward normal, already handled.
An oblique vertex with both inward axes pointing strictly right has P
as its unique leftmost point. It then meets u_1 only at P, making the
two actual u_1 applications coincide. This is impossible for a loaded
degree-two endpoint with a boundary neighbor, by the full local lemma
in FAN_MIXED_TIP_ENDPOINT_EXCLUSION.md, Section2: positive concurrence
would give either a radial-S face-interior support with parallel forces,
or a radial-D inner point too close to the origin to be shared by two
boundary units. The remaining upward axis endpoint is the aligned
square u_2=[1,2] times [1,2]. Equality of the containing-circle radii
of u_1 and u_2 then gives O_x=1. The u_1 endpoint torque would make
its boundary-edge origin moment zero, contrary to the strict boundary
moment sign. The downward vertical endpoint cannot carry the positive
vertical normal. This exhausts the p=1 corner exception, including an
endpoint-valued Hu_1 mean.

Consequently, on a genuine left-arc port order every actual internal
normal has nonpositive first coordinate. The actual junction routing
and any shared-side mean preserve this conclusion.

If the inner spokes used the left arc from the top side through (0,1)
to Q, both of their actual normals would have nonpositive first
coordinate. Equations(3)--(4) would then make the first coordinate of
all four positive hub forces strictly negative. This contradicts H's
full unloaded translation balance. Therefore the inner spokes use the
right arc, through (1,1) and (1,0).

Extending the four noncrossing hub spokes through their boundary bodies
to their actual circle corners preserves the same cyclic order. Thus
u_1,u_2,u_3,u_4 run **clockwise** around the circle. Corner/center order
agrees with that order. Each boundary edge follows its consecutive minor
center arc; a contact cannot skip another boundary body.

For any actual contact between two clockwise consecutive boundary
squares, its directed origin moment is strictly negative. This is the
reflected form of FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Lemma1.1; its
proof uses the actual support lines and retains arbitrary shared means.
The genuine degree-two torque equation at u_1 consequently gives
\[
                       \det(P-O,e_y)=p-O_x<0.
\]
Hence
\[
                               O_x>p>0.
\tag{6}
\]

## 3. The common hub bounds the true origin

Normalize the positive physical circle-corner weights of the four path
bodies to sum to1. Their weighted position relative to O is0. Every
such corner z is within3/sqrt(2) of the hub center c_H=(1/2,1/2): use
an actual H contact, the neighbor's diameter sqrt(2), and H's half
diagonal1/sqrt(2). Therefore
\[
 R^2+|c_H-O|^2
       =\sum_z\lambda_z|z-c_H|^2\le\frac92.
\tag{7}
\]
Since R^2>7/2 in (1), equation(7) implies
\[
                         -\frac12<O_y<\frac32.
\tag{8}
\]
This uses the full four-load force balance, not an invented equilibrium
for a proper subpath.

## 4. The hub-owned endpoint center is northwest

The all-mask proper concurrence theorem applies to the degree-two
endpoint u_1 and its boundary neighbor u_2. Its concurrence is
\[
                          q_1=P+\ell e_y,\qquad \ell\ge0,
\tag{9}
\]
and q_1-O is a positive multiple of its nonzero circle resultant F_1.
Equation(6) therefore gives (F_1)_x<0.

We check the center quadrant without assuming that the circle resultant
and the square center have identical directions. Put
\[
                       X=p-O_x<0,\qquad Y=1-O_y>-1/2.
\tag{10}
\]
The square u_1 lies entirely above its support line y=Y, so its center
has strictly positive y-coordinate relative to O.

If its frame is horizontal, its far circle corners have x-coordinate
of the sign of its center's x-coordinate, except at the two-corner
transition where that center coordinate is0. Thus (F_1)_x<0 implies
(c_1-O)_x<=0, with every shared mean retained.

Otherwise the minimum-y support is the unique vertex (X,Y), with
inward axes
\[
                    u=(c,s),\qquad v=(-s,c),
               \qquad c,s>0,\quad c^2+s^2=1.
\tag{11}
\]
Suppose its center x-coordinate were nonnegative. Then c>s and
X>=-(c-s)/2. Its center projections onto both inward axes obey
\[
 \begin{split}
 cX+sY+\frac12
     &\ge s\left(Y+\frac{c+s}{2}\right)>0,\\
 -sX+cY+\frac12
     &>\frac{1-c}{2}>0.
 \end{split}
\tag{12}
\]
The unique physical far corner is consequently (X,Y)+u+v. Its first
coordinate is at least(c-s)/2>0, contradicting (F_1)_x<0. This excludes
the oblique alternative with nonnegative center x. In either frame,
write the actual center relative to O as
\[
                  c_1-O=(-r_1\sin\delta_1,r_1\cos\delta_1),
                        \qquad0\le\delta_1<\pi/2.
\tag{13}
\]
No equality of the two physical circle weights was used.

## 5. The radial free endpoint has an exact southwest coordinate formula

Let e be the outward radial axis of u_4 and f=Je. The clockwise
boundary-edge moment fixes the order of its two inner vertices:
\[
                      Q-O=d e-\frac12f,\qquad
                      T-O=d e+\frac12f.
\tag{14}
\]
For completeness, if these signs were reversed, the outward normal
from u_4 to u_3 at the lower vertex would have the form -A e-B f,
A,B>0. Its origin moment would be -dB-A/2<0, so the incoming
u_3-to-u_4 moment would be positive, contradicting Section2. The
signs in (14) instead give the required negative incoming moment.

Strictness at Q gives
\[
                    n_4=\cos\eta\,e+\sin\eta\,f,
                              \qquad0<\eta<\pi/2.
\tag{15}
\]
In the hub coordinates n_4 is strictly southwest by (4). A lift beta
of the e-direction can therefore be chosen in (pi/2,3pi/2). If
pi/2<beta<=pi, equation(14) gives
\[
                (Q-O)_y=d\sin\beta-\frac12\cos\beta\ge\frac12.
\]
Indeed its minimum on that quadrant is min(d,1/2)=1/2. This would
make O_y<=-1/2, contrary to (8). Thus e is strictly southwest.
Put beta=3pi/2-delta_4, where0<delta_4<pi/2. Equation(14) gives the
exact formula
\[
                         O_y=d\cos\delta_4-\frac12\sin\delta_4.
\tag{16}
\]
The center of u_4 is a positive radial multiple of e and has precisely
this southwest angle. Equation(16) uses its physical radial frame;
it does not impose equal or nonzero individual corner weights.

## 6. The three boundary links leave too little total endpoint angle

The centers in (13),(16) are respectively northwest and southwest.
Their actual clockwise path, fixed in Section2, follows the
complementary arc of length pi+delta_1+delta_4. Let
\[
                \theta=\arccos(9/25),\qquad\alpha=3\theta-\pi.
\tag{17}
\]
Each actual boundary contact has minor center angle less than theta.
The three links therefore imply
\[
                \delta_1+\delta_4<\alpha<\pi/6,
          \qquad\cos\alpha>89/100,\quad\sin\alpha<9/20.
\tag{18}
\]
These exact constants and their triple-angle checks are recorded in
FAN_TIP_OWNED_ENDPOINT_EXCLUSION.md, Section5.

Put sigma=1/sqrt(2) and rho=R-sigma>5/4. Containment and circle
contact give r_1>=rho. The actual application P is within sigma of
its endpoint center, including every shared mean. Hence (13) gives
\[
                         1-O_y\ge\rho\cos\delta_1-\sigma.
\tag{19}
\]
Add (16) and (19):
\[
 1\ge\rho\cos\delta_1+d\cos\delta_4
                     -\frac12\sin\delta_4-\sigma.
\tag{20}
\]
For a fixed sum S=delta_1+delta_4, the expression on the right is a
concave function of either angle on0<=S<=alpha. Both constituent
functions are positive and concave there, and both decrease as their
own angle increases. Its minimum is attained at an endpoint allocation.
Together with S<alpha, this gives the strict lower bound
\[
 \min\left\{\rho+d\cos\alpha-\frac12\sin\alpha-\sigma,
                      \rho\cos\alpha+d-\sigma\right\}.
\tag{21}
\]
Using rho>5/4, d>9/10, sigma<3/4 and (18), the two entries in (21)
are respectively strictly greater than
\[
 \frac54+\frac9{10}\frac{89}{100}-\frac12\frac9{20}-\frac34
       =\frac{269}{250}>1,
       \qquad
 \frac54\frac{89}{100}+\frac9{10}-\frac34
       =\frac{101}{80}>1.
\tag{22}
\]
Equations(20)--(22) contradict one another. This proves the theorem.

## 7. Exact whole-family scope

The endpoint owned by H may have either physical circle mask and any
actual shared-side mean. The free endpoint retains the complete radial
physical mask and both individual circle weights. Its inner neighbor's
three forces, every internal shared mean, all hub moments and all four
extra squares remain. The local no-coincidence at Q was proved from
radial routing; it was not inferred from a side-interior endpoint model.

There is no secondary minimizer, numerical pose assumption, change of
normal after stress extraction, Lean compilation or CI in this proof.
