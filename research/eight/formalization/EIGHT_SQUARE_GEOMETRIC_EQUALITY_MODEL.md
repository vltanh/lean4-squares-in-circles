# A geometric model of every equality packing

The equality family consists of five fixed squares, two squares sliding
along fixed contact lines, and one central square with a free center and
angle. This note gives that model directly in physical coordinates. Its
definition uses neither a half-angle parameter nor an auxiliary central
disk. It is exactly equivalent to the complete parameter domain in
[the equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).

The fixed radius and the five fixed squares come from the unique
minimum of [the five-corner projected-distance model](EIGHT_SQUARE_FIVE_CORNER_MODEL.md).
They are geometric constants, not additional free parameters. Appendix A
supplies their equivalent stationary-coordinate adapter for the proofs.

## 1. One square, containment, and separation

For an angle alpha put
\[
 e_\alpha=(\cos\alpha,\sin\alpha),\qquad
 f_\alpha=(-\sin\alpha,\cos\alpha),
\]
and write the closed unit square with center p as
\[
 S(p,\alpha)=
 p+[-1/2,1/2]e_\alpha+[-1/2,1/2]f_\alpha.
\tag{1}
\]
An angle is naturally an element of the circle
\(\mathbb R/(\pi/2)\mathbb Z\), since a quarter turn does not
change this square. One may instead use the representative interval
\(-\pi/4\le\alpha<\pi/4\).

Two elementary functions describe all the geometric constraints. Define
\[
 \mathcal C(p,\alpha)=
 (|p\cdot e_\alpha|+1/2)^2+
 (|p\cdot f_\alpha|+1/2)^2.
\tag{2}
\]
This is the square's largest squared vertex norm. Thus containment in
the disk centered at zero with squared radius q is exactly
\(\mathcal C(p,\alpha)\le q\).

For a unit vector n, its half-width in direction n is the support function
\[
 h_\alpha(n)=
 \tfrac12\bigl(|n\cdot e_\alpha|+|n\cdot f_\alpha|\bigr).
\tag{3}
\]
Define the separation margin
\[
 \operatorname{Sep}_{\alpha,\beta}(d)=
 \max_{n\in\{e_\alpha,f_\alpha,e_\beta,f_\beta\}}
 \bigl\{|d\cdot n|-h_\alpha(n)-h_\beta(n)\bigr\}.
\tag{4}
\]
By the separating-axis theorem, two squares have disjoint open interiors
exactly when this margin is nonnegative for their center difference.
The maximum is explicit and contains no unchosen separating witness.
Equivalently, (4) is
\[
 \max\{|d\cdot e_\alpha|,|d\cdot f_\alpha|,
       |d\cdot e_\beta|,|d\cdot f_\beta|\}
 -\frac{1+|\cos(\alpha-\beta)|+|\sin(\alpha-\beta)|}{2}.
\tag{5}
\]
These definitions retain all weak contacts and simultaneous-axis ties.

## 2. The five-parameter model

Let \(P_1^*,\ldots,P_5^*,t_*\) be the unique minimizer of
[the five-corner model](EIGHT_SQUARE_FIVE_CORNER_MODEL.md), and let
\(R_*\) be its minimum radius. Put
\[
 q_*=R_*^2,\qquad e=e_{t_*},\qquad f=f_{t_*}.
\]
Turn the five minimizing corners into square centers by subtracting
their outward half-side offsets:
\[
 \begin{aligned}
 P_A&=P_1^*+(-1/2,1/2),&
 P_B&=P_2^*+(-1/2,-1/2),\\
 P_D&=P_3^*+(1/2,-1/2),&
 P_E&=P_4^*+(1/2,1/2),\\
 P_H&=P_5^*+(e+f)/2.
 \end{aligned}
\]
A,B,D,E have angle zero, and H has angle \(t_*\). These five
squares form the fixed anchor frame. Appendix A identifies this
geometric data with the older circle coordinates and records the
identities used below. No radius enclosure or stationary-root condition
is part of the model definition.

The free parameters are
\[
             (p,\theta,z,\eta)\in
 \mathbb R^2\times\bigl(\mathbb R/(\pi/2)\mathbb Z\bigr)
                    \times\mathbb R^2.
\tag{6}
\]
Here p and theta are the central square's actual center and angle. The
two exterior sliders have centers
\[
 P_T(z)=((P_B)_x-1,z),\qquad
 P_G(\eta)=P_H+e+\eta f,
\tag{7}
\]
and angles zero and \(t_*\), respectively. T slides vertically between
the left and right columns. G slides parallel to f while maintaining
its contact with H and its separating contact with A.

The admissible domain has three geometric requirements:

1. **Both sliders lie in the sharp disk.**
   \[
     \mathcal C(P_T(z),0)\le q_*,\qquad
     \mathcal C(P_G(\eta),t_*)\le q_*.
   \tag{8}
   \]
2. **T lies above the horizontal axis, and G lies below it.**
   These statements concern their whole squares:
   \[
       z\ge1/2,\qquad
       (P_G(\eta))_y+h_{t_*}((0,1))\le0.
   \tag{9}
   \]
3. **The central square contains the origin in its interior and
   separates from each exterior square.**
   \[
     \max\{|p\cdot e_\theta|,|p\cdot f_\theta|\}<1/2,
   \tag{10}
   \]
   \[
     \operatorname{Sep}_{\theta,\alpha_i}(P_i-p)\ge0
       \quad(i\in\{H,G,A,B,T,D,E\}),
   \tag{11}
   \]
   where \(\alpha_H=\alpha_G=t_*\) and all other exterior angles
   are zero.

**Geometric equality model.** Every parameter choice satisfying
(8)--(11) gives an eight-square packing whose least enclosing circle
has radius \(R_*\). Conversely, after an isometry and relabeling,
every equality packing has exactly this form. Its cyclic exterior order
is H,G,A,B,T,D,E. All 21 exterior pair separations are automatic from
the fixed anchors and slider conditions; only the seven central pairs
need to appear in the parameter domain.

The central square needs no separate containment inequality. Condition
(10) gives \(\mathcal C(p,\theta)<2\). The fixed B and D boundary
vertices differ horizontally by three, so \(R_*\ge3/2\) and
\(q_*\ge9/4>2\). Its containment is therefore automatic, without
a decimal radius bound.

## 3. All 21 exterior separations hold on these wider rails

For the calculations use the fixed constants in Appendix A, and put
\(c=\cos t_*\), \(s=\sin t_*\). The structural facts needed here
are
\[
 \frac12<u,v<1,\qquad \frac32<U<2,\qquad
 1<k_1<\frac32,\qquad k_2>1,\qquad 0<t_*<\frac\pi4.
\tag{12}
\]
They follow from Section 1 of
[the equality-family proof](HAND_EQUALITY_FAMILY_WITHOUT_BRACKET_TABLES.md).
Only these qualitative branch facts are used in the geometric argument
below; its statement needs no numerical radius enclosure.

### 3.1 Ten pairs among A,B,T,D,E

The five standard-frame squares form three columns: D,E on the left,
T in the middle, and A,B on the right. The exact circle identities give
\[
 r^2-U^2=4(1-u)>0,\qquad
 w^2-V^2=4(1-v)>0,
 \qquad U+V=3.
\tag{13}
\]
Thus A lies to the right of B, and E lies to the left of D. The adjacent
column gaps are exactly one for D,T and T,B, and at least one for every
other choice from adjacent columns. The gap between the two outer
columns is at least two. Within the right column, B is one unit above A;
within the left column, D is one unit above E. These horizontal and
vertical separators cover all ten pairs, independently of z.

### 3.2 Four fixed tilted contacts

Put \(W=(1+c+s)/2\), the support sum for a standard-frame square
and a square at angle \(t_*\). Direct substitution of Appendix A
and (7) gives
\[
 \begin{aligned}
 e\cdot(P_G-P_H)&=1,&
 e\cdot(P_A-P_G)&=W,\\
 e\cdot(P_A-P_H)&=W+1,&
 f\cdot(P_E-P_H)&=W.
 \end{aligned}
\tag{14}
\]
These separate HG, GA, HA and HE for every slider parameter eta.

### 3.3 The E,G pair

Write G's own-frame center as
\[
 P_G=\xi e+\zeta f,
 \qquad \xi=3/2-k_1,\qquad \zeta=1/2-k_2+\eta.
\]
Its top and left coordinates are
\[
 \operatorname{top}(G)=s(2-k_1)+c(\zeta+1/2),
 \qquad
 \operatorname{left}(G)=c(1-k_1)-s(\zeta+1/2).
\tag{15}
\]
The rail condition top(G)<=0 implies \(\zeta+1/2<0\).
Consequently, by (12),
\[
 \operatorname{left}(G)>c(1-k_1)>1-k_1>-1/2.
\tag{16}
\]
Also \(q_*=U^2+(2-u)^2>13/4\), and \(v<1\), so
\(w^2=q_*-v^2>9/4\). Hence the right edge of E is
\(1-w<-1/2\). The vertical line x=-1/2 strictly separates E and G.

### 3.4 Six pairs between H,G and B,T,D

The top of H is
\[
                   s(1-k_1)+c(1-k_2)<0.
\tag{17}
\]
The top of G is nonpositive by (9). The bottoms of B and D are
\(1-u>0\) and \(1-v>0\), respectively; the bottom of T is
\(z-1/2\ge0\). The horizontal axis therefore separates each of
H,G from each of B,T,D, including possible weak rail-endpoint contacts.

The count is \(10+4+1+6=21\). Every pair has an actual side-normal
separator, and no nonneighbor condition has been omitted.

## 4. The exact least enclosing circle

The five anchors are contained in the sharp disk. Their selected
farthest vertices are
\[
 (r,-u),\quad (U,2-u),\quad (-V,2-v),\quad (-w,-v),
                         \quad -k_1e-k_2f,
\tag{18}
\]
all of squared norm \(q_*\). Conditions (8) give slider containment;
(10) gives central containment as explained after the model statement.
Section 3 and (11) give all 28 pair separations. Thus every point of the
model domain is an actual packing at radius \(R_*\).

The least enclosing circle is exactly this circle, independently of
the unrestricted lower-bound theorem. The segment between the first
two points in (18) crosses the horizontal axis at a positive abscissa.
The segment between the next two crosses it at a negative abscissa.
Thus zero is a convex combination of these four boundary vertices.
If their convex weights are \(\lambda_j\), then for any proposed
circle center a,
\[
 \max_j|V_j-a|^2\ge\sum_j\lambda_j|V_j-a|^2
                         =q_*+|a|^2.
\tag{19}
\]
At a=0 the entire packing is contained at q*. At every a!=0 its required
squared radius is strictly larger. In the notation (2), the exact
minimum-circle formula is therefore
\[
 \boxed{\quad
   \min_{a\in\mathbb R^2}\ \max_{i\in\{0,H,G,A,B,T,D,E\}}
              \mathcal C(P_i-a,\alpha_i)=q_*.
 \quad}
\tag{20}
\]
Here \(P_0=p\) and \(\alpha_0=\theta\). The minimizing center is
uniquely zero, and the minimum radius is \(\sqrt{q_*}\).

## 5. Five genuine freedoms and the role of symmetry

The free geometric data are the central center's two coordinates, its
angle modulo a quarter turn, and the two slider positions. Replacing a
half-angle parameter by theta changes only coordinates, not the domain
or its dimension.

The full-dimensional box in Section 5 of the equality-family proof lies
strictly inside the admissible constraints after this angle change.
Its configurations are pairwise noncongruent. Thus all five freedoms
are genuine after Euclidean isometries and relabeling have been removed.
There is no further continuous symmetry that reduces the family to
four parameters. The common isometry fixes the disk center and the
standard-frame direction; choosing \(t_*>0\) accounts for reflection.
The remaining quarter-turn ambiguity belongs to each square's angle
coordinate and is already removed by using
\(\mathbb R/(\pi/2)\mathbb Z\).

Finite coincidences at special weak boundary configurations do not
change this dimension statement. No additional sign restriction on the
central angle is justified by the stationary anchor geometry.

## Appendix A. Exact fixed coordinates and explicit rail intervals

The [five-corner selection proof](HAND_FIVE_CORNER_MODEL_SELECTION.md)
identifies the geometric minimizer with the unique admissible stationary
triple \((q_*,u_*,t_*)\) of the existing stationary existence and
uniqueness theorem. This appendix is a compatibility description of the
already selected geometric constants, not their primary definition.
Write u=u*. The positive circle coordinates satisfy
\[
 \begin{gathered}
 r^2+u^2=U^2+(2-u)^2=V^2+(2-v)^2=w^2+v^2=q_*,
                         \qquad U+V=3,\\
 k_1=2-c(r-1)+su,\qquad
 k_2=1+cv-s(w-1),\qquad k_1^2+k_2^2=q_*.
 \end{gathered}
\tag{21}
\]
Equivalently, use the positive radicals of the existing stationary
definition, with \(v=2-Y\). The anchor coordinates are
\[
 \begin{array}{c|c|c}
 \text{square}&\text{center}&\text{angle}\\ \hline
 A&(r-1/2,\ 1/2-u)&0\\
 B&(U-1/2,\ 3/2-u)&0\\
 D&(1/2-V,\ 3/2-v)&0\\
 E&(1/2-w,\ 1/2-v)&0\\
 H&(1/2-k_1)e+(1/2-k_2)f&t_*.
 \end{array}
\tag{22}
\]
The circle equations, contact equations and branch inequalities (12)
describe fixed geometric data. They do not add variables to (6).

For readers wanting explicit endpoints, (8)--(9) are exactly
\[
 \boxed{\quad
  \frac12\le z\le\sqrt{q_*-(U-1)^2}-\frac12,
 \qquad
 k_2-\sqrt{q_*-(2-k_1)^2}
       \le\eta\le k_2-1-(2-k_1)\tan t_*.
 \quad}
\tag{23}
\]
Indeed T has \(0<(P_T)_x<1/2\) and z>=1/2, so its containment
cost is \((U-1)^2+(z+1/2)^2\). For G, (15) gives the upper eta
bound, while \(0<\xi<1/2\) and \(\zeta<-1/2\) give containment
cost \((2-k_1)^2+(k_2-\eta)^2\). The latter square root is taken
with its actual positive sign. Thus (23) is an algebraic version of
the two geometric rails, not an extra estimate.

## Appendix B. Exact equivalence to the earlier parameter domain

Only this equivalence proof uses the auxiliary central disk of the
earlier proof. No such disk occurs in the model definition (6)--(11).

### B.1 Every earlier parameter choice satisfies this model

The earlier domain has
\[
 7/12\le z\le\sqrt{q_*-(U-1)^2}-1/2,
\qquad
 k_2-\sqrt{q_*-(2-k_1)^2}\le\eta\le k_2-13/12.
\tag{24}
\]
Its core inequalities put zero in the central square's open interior,
and its seven support maxima are exactly (4)--(5) after replacing
\(\kappa\) by \(\theta=2\arctan\kappa\).

Both sliders satisfy (8). T lies strictly above the horizontal axis.
The already proved whole-interval comparison (21) in Section 3.2 of
the equality-family proof is
\[
                    (2-k_1)\tan t_*<1/12.
\tag{25}
\]
At the upper eta endpoint in (24), the top of G is
\(c\{(2-k_1)\tan t_*-1/12\}<0\); it is smaller at every other
allowed eta. This proves (9). Thus the earlier domain is contained in
the geometric model, with the actual angle in place of its rational
half-angle coordinate.

### B.2 Every geometric model point belongs to the earlier domain

Sections 3--4 already prove that every point of (6)--(11) is an actual
eight-square packing in the sharp disk, without using a central-core
theorem. Now apply the central-core input in Section 1 of
[the exterior-frame theorem](../HAND_EXTERIOR_FRAME_CONCENTRATION.md)
at that radius:
the unique central square contains the closed radius-1/12 disk in its
open interior. By (10), our named central square already contains zero
in its open interior. No other square can do so without violating
disjoint open interiors. Hence the theorem's central square is precisely
the one named by p and theta, and
\[
        |p\cdot e_\theta|<5/12,
          \qquad |p\cdot f_\theta|<5/12.
\tag{26}
\]

Every exterior square avoids the open radius-1/12 disk. For T, its own
first coordinate is in (0,1/2), and z>=1/2, so its distance from zero is
z-1/2. Consequently z>=7/12. For G, its own first coordinate is in
(0,1/2) and its second coordinate is \(\zeta<-1/2\), so its distance
from zero is \(-\zeta-1/2=k_2-1-\eta\). Consequently
\(\eta\le k_2-13/12\). Containment in (8) supplies the other
endpoints in (24). Finally, the seven conditions (11) are exactly the
seven separating-axis conditions in the earlier domain.

Choosing the representative \(-\pi/4\le\theta<\pi/4\), the inverse
coordinate change is \(\kappa=\tan(\theta/2)\), with
\(1-\sqrt2\le\kappa<\sqrt2-1\). This proves exact equivalence,
including every weak slider endpoint and every central contact.

The proof uses the central-core theorem only to compare two already
explicit parameter domains. The geometric model has no auxiliary core
radius or numerical radius bracket. Its geometric sufficiency and least
enclosing-circle arguments use the exact fixed frame and the qualitative
stationary branch facts (12).
