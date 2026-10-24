# The D-leaf three-loaded C4 cannot use both left articulation vertices

**Status.** Complete hand exclusion of the entire stated contact-feature
branch; root and separate independent full hand audits passed. All three physical
circle masks, all BU/UC owners, every actual shared-side mean and all four
extras are retained. The remaining right-vertex, side and parallel-reaction
articulation branches are not excluded by this source. It does not close
the entire D-leaf or C1.4.b1 cell.

## 1. Full branch and necessary certificate

Let the selected positive graph be the cycle
\[
 A-B-U-C-A
\]
with a radial D leaf at the clear articulation `A`. Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[-v,H],\qquad H+v=1,
 \quad H,v>0.
\tag{1}
\]
The three other cycle bodies `B,U,C` are loaded and have exact positive
pair degree two. Suppose the actual A normals are strictly northwest
and southwest, respectively, at
\[
 P_B=(-s,H),\qquad P_C=(-s,-v).
\tag{2}
\]
Their inward directions into the tips are written
\[
 n_B=(-\cos\phi,\sin\phi),\qquad
 n_C=(-\cos\psi,-\sin\psi),\qquad 0<\phi,\psi<\frac\pi2.
\tag{3}
\]
This is the entire two-left-vertex branch, with no angle, owner or
circle-mask restriction beyond its stated feature.

Use the compatible selections already proved in
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md and
BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md. All such finite conditions
are imposed before multiplier extraction. In particular the first theorem
makes both fixed singleton A contacts side-owned. Since the normals in
(3) are not A axes, they are owned by `B,C`, respectively. The second
selection is used only for a singleton BU or UC edge; shared means are
never replaced by fixed points.

**Theorem.** No selected positive component satisfies (1)--(3).

## 2. The articulation concurrence is positive in this whole branch

Both points in (2) belong to boundary units, so
\[
 H^2,v^2\ge1-2s.
\]
As in D_DIAMOND_OBLIQUE_HUB_EXCLUSION.md, this gives
\[
 \frac38\le s<\frac49,
 \qquad \frac13<H,v<\frac23,
 \qquad |P_B|,|P_C|<\frac56.
\tag{4}
\]
A physical two-circle-corner square is radial S and every point of it
has norm greater than `9/10`. Hence `B,C` each have one physical circle
corner. The full original masks have therefore been exhausted.

The two-force concurrence theorem of
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies to each
of `B,U,C`: each has at least one boundary neighbor. It supplies a
positive radial concurrence `q_i`, and for every actual contact `p`
and outward unit normal `g` at that body,
\[
 p-q_i=\ell g,\qquad\ell\ge0.
\tag{5}
\]
For a unique-circle-corner body the concurrence belongs to the square.
The contacts of each such loaded tip are nonparallel. These statements
retain all shared means and all zero individual weights of a radial U.

Equation (5) at the A contacts places `q_B` northwest and `q_C`
southwest, since it writes them as `P_B+t n_B` and `P_C+t' n_C`
with nonnegative `t,t'`. Their unique circle corners have the same
quadrant signs. Every physical circle corner of `U` is acute to both,
because `U` touches both tips. Its first coordinate is therefore
strictly negative: a point with nonnegative first coordinate cannot
have positive scalar product with both a northwest and a southwest
vector.

The angular-neighbor contact theorem in
CIRCLE_CONTACT_ANGULAR_ORDER.md puts U's circle arc between B and C
on the western arc. Indeed BU and UC are both actual boundary contacts;
neither can skip the other boundary square. The D leaf supplies the
eastern circle port. Thus the counterclockwise order is `B,U,C` along
this western arc, for one or both physical U circle corners and for its
positive resultant direction. In particular
\[
                         \det(q_B,q_U)>0.
\]
If `g` is the actual B-to-U normal and `T` its actual application,
(5) gives
\[
 q_U-q_B=\ell g,\quad\ell>0,\qquad
 \det(T,g)=\frac{\det(q_B,q_U)}\ell>0.
\tag{6}
\]
The coefficient is positive because the boundary direction arcs are
distinct. This is the same boundary-edge moment calculation as in
C7_FORCE_POLYGON.md; no equation at A has yet been normalized.

Torque on B propagates the positive moment in (6) to its A edge.
Consequently
\[
 H\cos\phi-s\sin\phi>0.
\tag{7}
\]
The two A force lines intersect the horizontal leaf line at one point
`q_A=(q,0)`. Nonparallelness follows from (3). A's true force and torque
balance gives
\[
 L:=q+s=H\cot\phi=v\cot\psi>0,
 \qquad \tan\phi+\tan\psi=\frac1L.
\tag{8}
\]
Equation (7) proves `q>0` and hence `L>s`.

This establishes positivity for the full branch (1)--(3). It does not
assume a general positive-articulation-concurrence theorem for the other
C4 contact features.

## 3. The two left tips force L greater than one

Consider C; the upper argument is its reflection. Use its actual owned
A side frame
\[
 n=(-d,-c),\quad k=(c,-d),\quad
 c=\sin\psi,\ d=\cos\psi,
\]
\[
 C=P_C+[0,1]n+[-\rho,1-\rho]k,
 \qquad 0<\rho<1,\qquad V=1-\rho.
\tag{9}
\]
Its inner support point has own coordinates
\[
 X=sd+vc>0,\qquad Y=vd-sc>0,
\tag{10}
\]
where positivity of `Y` follows from `q>0` and (8).
The positive radial concurrence has the form `P_C+eta n`, `eta>=0`.
Its `k` coordinate is `Y>0`; consequently the unique physical circle
corner is
\[
 z_C=P_C+n+Vk=(X+1,Y+V)_{(n,k)}.
\tag{11}
\]
Comparing it with `P_C`, using (4), yields
\[
 \sqrt{1+V^2}=|z_C-P_C|\ge R-|P_C|>\frac{137}{120},
 \quad V>\frac{11}{20},\quad 0<\rho<\frac9{20}.
\tag{12}
\]
The radial concurrence equation is
\[
 \eta=\frac{Y-VX}{Y+V}\ge0,
 \qquad \frac YX\ge V>\frac{11}{20}.
\tag{13}
\]
Using `c/d=v/L` from (8),
\[
 \frac YX=\frac{v(L-s)}{sL+v^2}
 \le\frac{L-s}{2\sqrt{sL}}.
\]
If `L<=1`, the last expression increases with `L/s` and (4) gives
\[
 \frac YX\le\frac{5}{4\sqrt6}<\frac{11}{20},
\]
contradicting (13). Hence
\[
 L>1,\qquad \tan\phi+\tan\psi<1,
 \qquad \phi,\psi<\frac\pi4.
\tag{14}
\]
No restriction on the UC owner was used.

## 4. A complete small-contact screening lemma

We prove the geometric input needed for both tips. Keep the frame and
variables (9)--(13), and let `w` be the incoming force direction at C
from U. Its magnitude is positive. Since the A force has zero `k`
component while C's circle force has positive `k` component,
\[
                              w\cdot k>0.
\tag{15}
\]
We show that `w dot n` cannot be negative, and that every surviving
actual UC application satisfies
\[
                              |T_C|<\frac{39}{40}.
\tag{16}
\]
The statement covers every owner and every shared-side mean.

### 4.1 The far n vertex is screened from every unit neighbor

Suppose `w dot n<0`. The minimum of `w` on C is the vertex
\[
 T_C=P_C+n-\rho k.
\]
Write `x=X+1`, `y=Y+V`, so `x^2+y^2=R^2` and
`T_C=(x,y-1)` in this orthonormal frame. Its outward normal toward U
is parallel to `T_C-q_C`. By (13),
\[
 T_C-q_C=\left(\frac{Vx}{y},-\rho\right).
\]
Its unit-normal support value is therefore
\[
 h=\frac{VR^2+\rho y-y^2}
         {\sqrt{V^2R^2+(2\rho-1)y^2}}.
\tag{17}
\]
We will prove `h>R-1`. A unit neighbor beyond that support line has a
point of projection at least `h+1>R`, contradicting disk containment.
This width argument does not assume that U owns the contact or has a
unique physical circle corner.

Here `0<=rho<=9/20`, `V=1-rho`, and
`V<=y<=V+7/10<R`. For fixed `R,rho`, the derivative of (17) has numerator
\[
 R^2V(V\rho-y)+(1-2\rho)y^3<0.
\tag{18}
\]
Indeed `y-Vrho>=Vy` and `1-2rho<=V^2`, so this numerator is at most
`V^2 y(y^2-R^2)<0`. Thus it suffices to bound (17) at
`y=17/10-rho`.

Set
\[
 Z=R^2-\frac{289}{100}>0,\quad
 G(\rho)=\frac{221}{100}-2\rho,\quad
 F(\rho)=\frac{51}{50}-\frac{351}{100}\rho+2\rho^2.
\]
At that endpoint the numerator of (17) is
`N=VZ+rho G(rho)>0`. Direct expansion, with `D` denoting its denominator,
gives
\[
 N^2-ZD^2=\rho\bigl[ZF(\rho)+\rho G(\rho)^2\bigr]\ge0.
\tag{19}
\]
For an exact sign check, `F` decreases on `[0,9/20]`. On `[0,1/3]`,
`F>=F(1/3)=13/180>0`. On `[1/3,9/20]`,
\[
 F\ge-\frac{309}{2000}>-\frac16,\quad
 0<Z<\frac32,\quad G\ge\frac{131}{100}>1,
\]
so the bracket in (19) is greater than `-1/4+1/3>0`.
Consequently
\[
 h\ge\sqrt{R^2-\frac{289}{100}}>R-1,
\tag{20}
\]
since the last inequality is equivalent to `R>389/200`, which follows
from `R>=79/40`. This excludes the entire far-vertex alternative.

### 4.2 All remaining actual applications are uniformly deep

We have `w dot n>=0`. If it is positive, the actual point is
`T_C=P_C-rho k`, with own coordinates `(X,Y-rho)`.
If it is zero, the support is the full `k`-minimum side. The actual
mean is necessarily
\[
 T_C=P_C+\eta n-\rho k,
\]
where the same `eta` in (13) follows from the actual force and torque
at C. This is a consequence of the equations, not a selected replacement
for a mean.

In both cases its norm is at most that of the auxiliary point
\[
 T'_C=(X+\eta)n+(Y-\rho)k
      =\frac{Y}{Y+V}z_C-\rho k.
\]
Since `0<Y=vd-sc<v<7/10`, the exact scalar estimate of
D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md, Section 4, gives
\[
 |T_C|^2\le|T'_C|^2
 =R^2\left(\frac{Y}{Y+V}\right)^2-2\rho Y+\rho^2
 \le\frac{7409}{8000}<\left(\frac{39}{40}\right)^2.
\tag{21}
\]
It also proves that the incoming UC force is in the closed cone
spanned by the strictly southwest `n_C` and strictly southeast `k_C`,
with positive `k_C` component. Its vertical component is strictly
negative.

Apply the reflected result at B. Its actual BU application also has
norm below `39/40`; its incoming force `w_B` from U lies in the cone
spanned by `n_B` and
\[
                         k_B=(\sin\phi,\cos\phi),
\]
with positive `k_B` component, and is strictly upward. For C write
`w_C=w`; it is strictly downward. These are the actual outward normals
from U toward its two neighbors.

## 5. The middle boundary square has no surviving physical mask

Because each U application in (21) satisfies `|T|<39/40<=R-1`, it has distance strictly
greater than one from every physical U circle corner.

If U has two physical circle corners, its radial-S representation has
one inner side. Every point on either transverse side is within one of
its corresponding outer circle corner; the outer side is excluded as
well. Hence either actual application must be in the relative interior
of the inner side. Its normal is the radial inner normal. The
orientation-uniform inner-face exclusion in C7_FORCE_POLYGON.md,
Lemma 2.1, says its neighbor is strictly circle-clear, contrary to B or
C being loaded. This removes the entire two-corner U mask, including
all individual zero circle weights.

Thus U has one physical circle corner. Write it as
\[
 U=O+[0,1]u+[0,1]v,
 \qquad z_U=O+u+v.
\]
The two sides incident to `z_U` consist entirely of points at distance
at most one from `z_U`. Neither actual application lies on them.
Both applications consequently lie on the two inner sides, and every
actual outward U normal lies in the same closed right-angle cone
\[
                         K=\operatorname{cone}\{-u,-v\}.
\tag{22}
\]
This includes inner-side interiors, the opposite vertex, and all means.

The normals `w_B,w_C` have strict opposite vertical signs. They have
nonnegative scalar product because they belong to the right-angle cone
K. Their horizontal components must therefore be nonzero with the same
sign. Their positive weighted sum is the negative U circle force,
whose horizontal component is positive by Section 2. Thus both horizontal
components are positive. The two extreme axes of K can be written as
an upper northeast axis of angle `theta` and a lower southeast axis of
angle `theta-pi/2`, with
\[
                              0<\theta<\frac\pi2.
\tag{23}
\]

## 6. Every owner gives the same impossible angle inequality

Consider the entire BU owner cover. If B owns the contact, or it is a
shared side, its positive `k_B` force component and its side axes force
`w_B=k_B`. Since that vector of angle `pi/2-phi` belongs to K,
\[
                              \phi+\theta\ge\frac\pi2.
\tag{24}
\]
If U owns a singleton contact, its strictly upward normal is the upper
axis of K, of angle `theta`. The screening result proves
`n_B dot w_B>=0`; hence again (24). A remaining free singleton BU normal
is excluded by the compatible fixed-application unique-tip selection,
since AB is a fixed singleton and U is a boundary neighbor. All physical
shared means were already included in the first case.

The reflected exhaustive UC cover gives
\[
                              \psi\ge\theta.
\tag{25}
\]
For a C-owned/shared contact, its normal is `k_C` of angle
`-pi/2+psi`, which must lie above the lower axis of K. For a U-owned
singleton, its downward normal is that lower axis, and
`n_C dot w_C>=0` gives the same inequality. The fixed-tip theorem excludes
a remaining free singleton without freezing any shared mean.

Adding (24)--(25) yields `phi+psi>=pi/2`, contradicting (14), where
both angles are strictly below `pi/4`. This proves the whole theorem.

## 7. Exact scope of this completed implication

The source does not suppose that the middle U forces were absent or that
U shared either contact with A. U remains a loaded degree-two body.
Every pair force, physical circle mask and shared mean survives until its
explicit exclusion. The result is independent of the four additional
squares, which remain arbitrary.

For the full D-leaf all-three-loaded C4 one must still handle every A
contact pattern outside (2)--(3), including positive horizontal components,
pure A-axis normals, and parallel cycle reactions. No global q_A>0 premise
for those other branches has been asserted. No Lean compilation, CI or
numerical diagnostic is a premise of this hand proof.
