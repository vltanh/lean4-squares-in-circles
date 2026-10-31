# The entire radial-S-leaf opposite-load C4 is impossible

**Status: complete conditional hand exclusion; root and independent full
hand audits passed.** Work at the canonical radius minimizer in
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, in
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The positive component is A--B--U--D--A with a pendant **radial S
leaf at A**, with B,D loaded and U unloaded.

**Theorem.** This entire S-leaf opposite-loaded-pair C4 alternative
is impossible. Every physical circle mask, contact owner, U-parallel
endpoint, individual corner-weight split, channel mean and all four
completion squares are retained.

Combined with FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md, this closes the
whole opposite-loaded-pair C4 domain at the canonical minimizer.
The all-three-loaded C4 and the diamond domains remain open.

## 1. Complete mixed-mask and owner domain

The full unique/unique and two/two physical masks are already excluded
by FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md and
FOUR_CYCLE_TWO_RADIAL_TIPS_EXCLUSION.md. Reflect and relabel so B has
one physical circle corner and D has two.

The canonical reduction and the all-mask articulation normal selection
give
\[
 \begin{split}
 U&=[X-1,X]\times[Y,Y+1],\qquad P=(X,y_0),\quad Y<y_0<Y+1,\\
 A&=P+[0,1]v+[0,1]w,
       \qquad v=(a,b),\quad w=(b,-a),\quad a,b>0,\quad a^2+b^2=1,\\
 p&=(x,Y),\quad p+e_y=(x,Y+1),\qquad x\le X\le\varepsilon,\\
 B&\subseteq\{y\le Y\},\qquad D\subseteq\{y\ge Y+1\}.
 \end{split}
\tag{2}
\]
A is oblique to U. AB and AD are distinct singleton intersections,
and each is side-axis-owned. Their applications on an owning side
are in its relative interior. All BU/UD means remain actual means.

Use
\[
 h=\sqrt{R^2-1/4}-1,\qquad r=R-\sqrt2,
 \qquad \frac9{10}<h<\frac{61}{60},\quad r>\frac{14}{25},
 \qquad \varepsilon=\max(h-1,0)<\frac1{60}.
\tag{3}
\]
The S leaf's radial application p_L has norm h, and its outward
force direction is p_L/h. Every point of a circle-touching unit
square has norm at least r.

The upper two-corner body D is physically radial S with the same
parameter h. If oblique, it has inward axes
\[
 r_D=(c,d),\qquad t_D=(-d,c),\qquad c,d>0,
\]
and bottom vertex
\[
                         p+e_y=-r_D/2+h t_D.
\tag{4}
\]
The other radial position has x>1/2 and is impossible by (2).
If parallel to U, D=[-1/2,1/2] times [h,h+1]. These are the complete
physical alternatives proved in the two-radial-tip source.

## 2. Two contact facts retain every radial weight and mean

### 2.1. A-owned contact at the radial upper tip

If A owns AD, its normal is -w and
\[
                         q_D=P+\sigma v,\qquad 0<\sigma<1.
\tag{5}
\]
The point q_D is a vertex of D. It cannot be a physical circle
vertex, so it is an inner vertex and
\[
                              |q_D|^2=h^2+1/4.
\tag{6}
\]
There is also the strict projection fact
\[
                                  q_D\cdot v>0.
\tag{7}
\]
For an oblique D, its bottom vertex p+e_y cannot belong to A, by
(2). Thus q_D is its other inner vertex r_D/2+h t_D. The outward
D-to-A normal w at that vertex gives
\[
 K=bc-ad\ge0,\qquad C=ac+bd>0.
\]
Consequently q_D dot v=C/2+hK>0. For a parallel D the outward
normal w points down and right, so q_D=(1/2,h), whose v-projection
is a/2+hb>0. This proves (6)--(7) for the entire physical radial
mask without a weight assumption.

### 2.2. Tip-owned contact at the radial upper tip, when A owns AB

Suppose A owns AB while D owns AD. The unique-tip owner theorem
gives
\[
       n_{AB}=-v,\quad q_B=P+\tau w,\quad0<\tau<1,
       \qquad a\ge b.
\tag{8}
\]
The complete side-feature/A-vertex check in
FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md, Sections3.1--3.2, does not use
the D-leaf premise until its subsequent force equation. It gives
\[
 \begin{gathered}
 q_D=P+v=\kappa r_D+h t_D,\qquad0<\kappa<1/2,\\
 n_{AD}=t_D=Kv-Cw,\qquad
 C=ac+bd\ge1/\sqrt2,\quad 0\le K=bc-ad\le1/\sqrt2.
 \end{gathered}
\tag{9}
\]
For parallel D use c=1,d=0. Its genuine vertical-force torque
makes kappa>0, while its side-interior contact gives kappa<1/2.
For oblique D, positive concurrence gives its inner-face parameter
sigma>1/2 and kappa=sigma-1/2. Every channel mean and both radial
corner weights are retained in these deductions.

The bounds on C,K are purely geometric: the A support cone at P+v
gives K>=0, so the angle of r_D is at most the angle of v. The
latter is at most pi/4 because a>=b. Their difference is therefore
in [0,pi/4], whose cosine and sine are C and K. No D-leaf force
equation is used here.

The A force equation shows that the leaf direction has strictly
positive w-component. Its v-component can have either sign or be
zero; all three support features will be handled below.

## 3. A owns the unique-tip edge; the radial tip owns its edge

Assume (8)--(9). The radial tip's own coordinates give
\[
                   |q_D|^2=h^2+\kappa^2,
                   \qquad q_D\cdot w=\kappa K-hC
                    <\frac{1/2-h}{\sqrt2}<-1/4.
\tag{10}
\]
The last strict bound uses h>9/10 and sqrt(2)<8/5.
The leaf's three possible support features are exhaustive because
its w-component is positive.

### 3.1. The side feature is impossible

If the leaf direction is w, its radial application on A's maximum-w
side has coordinate h. The upper vertex q_D has w-coordinate h-1.
But h-1>-1/10, contradicting (10). This includes every possible
side endpoint or interior radial application.

### 3.2. The right vertex feature makes q_B too central

If the leaf direction has positive v-component, its application is
\[
                p_L=P+v+w=q_D+w=A_0v+B_0w,
                \qquad A_0,B_0>0,\quad A_0^2+B_0^2=h^2.
\]
Since |q_D|^2=h^2+kappa^2,
\[
                B_0=\frac{1-\kappa^2}{2},\qquad
                3/8<B_0<1/2,
                \qquad A_0>187/250,
                \qquad |A_0-1|<63/250.
\tag{11}
\]
Indeed A_0^2>81/100-1/4=14/25>(187/250)^2; its upper bound
A_0<h<61/60 supplies the other side of the last absolute value.

The actual vertical gap from q_B to q_D is b+tau a>=1. Since
0<b<=1/sqrt(2),
\[
                  \tau\ge\frac{1-b}{a}\ge\sqrt2-1.
\tag{12}
\]
Thus q_B=(A_0-1)v+(B_0-1+tau)w has its w-coordinate strictly
between -1/4 and1/2: the lower estimate is
sqrt(2)-13/8>-1/4. Consequently
\[
                    |q_B|^2
                <(63/250)^2+1/4
                 =19594/62500<19600/62500=(14/25)^2<r^2.
\tag{13}
\]
This is impossible for a point of the loaded B.

### 3.3. The lower vertex feature contradicts global force balance

If the leaf direction has negative v-component, write
\[
                       p_L=P+w=q_D-v+w=-A_0v+B_0w,
                       \qquad A_0,B_0>0.
\]
The two norm equations give
\[
                         A_0+B_0=1-\kappa^2/2<1.
\tag{14}
\]
The B circle force has negative global x-component, by its A-owned
normal -v and vertical channel force. The D circle force has
nonpositive x-component, by its tip-owned normal t_D and vertical
channel force. Hence global balance of the three circle-loaded
bodies makes the S-leaf direction have positive x-component.
Thus
\[
                        -aA_0+bB_0>0.
\]
Since a>=b, this implies B_0>A_0. Therefore
\[
                         h^2=A_0^2+B_0^2
                             <B_0(A_0+B_0)<B_0.
\tag{15}
\]
But (10) gives B_0=1+q_D dot w<3/4, while h^2>81/100.
This contradiction closes the last feature. The entire owner order
of Section3 is excluded.

## 4. The unique tip owns its edge; A owns the radial-tip edge

A unique tip owning its A edge is oblique to U. Its complete side
and A-vertex check gives the near-face contact at
\[
                         q_B=P+w,
\]
with inward lower-tip axes r_B=(c_B,-s_B), t_B=(-s_B,-c_B),
c_B<s_B, and n_AB=t_B. Its normal cone at P+w gives
\[
                  n_{AB}=-Cv+Kw,\qquad C>0,\quad K\ge0.
\]
Since n_AD=-w, the A force balance makes the leaf direction's
v-component strictly positive. Again its other component can have
any sign, giving three exhaustive features.

### 4.1. The side feature is impossible

If the leaf direction is v, A's own coordinate ranges are
\[
                  h-1\le z\cdot v\le h,
                  \qquad -t\le z\cdot w\le1-t,
                  \qquad0\le t\le1.
\]
Then
\[
             q_B=(h-1)v+(1-t)w,
             \qquad q_D=(h-1+\sigma)v-tw.
\]
Since 0<sigma<1 and h>1/2, the first coordinate of q_D has
absolute value strictly less than h. Equation (6) therefore forces
t^2>1/4, hence t>1/2. It follows that
\[
                            |q_B|^2<1/100+1/4=13/50<r^2,
\]
again impossible for a boundary neighbor. The side endpoint cases
were retained in t in [0,1].

### 4.2. The upper vertex feature has the wrong projection

If the leaf's w-component is negative, its application is
p_L=P+v. Put k=1-sigma in (0,1). Then q_D=p_L-kv.
Equation (6) and |p_L|=h give
\[
                         k^2-2k(p_L\cdot v)=1/4,
\]
so
\[
                         q_D\cdot v=-k/2-1/(8k)<0.
\]
This contradicts the physical projection (7).

### 4.3. The right vertex feature makes q_B too central

If the leaf's w-component is positive, write
\[
                      p_L=P+v+w=A_0v+B_0w,
                      \qquad A_0,B_0>0.
\]
With k=1-sigma, q_D=(A_0-k)v+(B_0-1)w. Equations (6)--(7) give
A_0-k>0 and
\[
                         1-2B_0=1/4+k(2A_0-k)>1/4.
\]
Consequently
\[
                   0<B_0<3/8,
                   \qquad A_0>4/5,
                   \qquad |A_0-1|<1/5.
\tag{16}
\]
The middle inequality follows from
A_0^2=h^2-B_0^2>81/100-9/64>16/25; the last also uses
A_0<h<61/60. Now q_B=p_L-v gives
\[
                         |q_B|^2<1/25+9/64=289/1600<r^2.
\tag{17}
\]
This excludes the entire other mixed owner order.

## 5. Both A-owned edges are impossible

Suppose A owns both AB and AD. Their normals are -v and -w.
The leaf direction has both own components positive, so its
application is the right vertex
\[
                     p_L=P+v+w=A_0v+B_0w,
                     \qquad A_0,B_0>0.
\]
The radial AD contact (5)--(7) gives exactly (16) again. Put
k=1-sigma and L=A_0-k=q_D dot v>0. The two norm equations yield
\[
              k(A_0+L)=3/4-2B_0.
\]
Since A_0+L<2h<5/2,
\[
                       k>3/10-(4/5)B_0,
                       \qquad \sigma<7/10+(4/5)B_0.
\tag{18}
\]

The unique lower tip has an A-owned contact, so Lemma2.1 of
FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md supplies a>=b, including its
parallel equality endpoint. Let q_B=P+tau w, 0<tau<1. The actual
channel levels give
\[
                              \tau a+\sigma b\ge1.
\tag{19}
\]
We prove the useful strict consequence
\[
                                  \tau>1/2-B_0.
\tag{20}
\]
If 0<B_0<=1/4, Cauchy's inequality and (18) give
\[
 a(1/2-B_0)+b\sigma
  <\sqrt{(1/2-B_0)^2+(7/10+(4/5)B_0)^2}<1.
\]
The expression under the final root is convex in B_0; its endpoint
values on [0,1/4] are 37/50 and349/400, both below one.
If 1/4<=B_0<3/8, use b<=1/sqrt(2) and sigma<1 instead:
\[
              a(1/2-B_0)+b\sigma<1/4+1/\sqrt2<1.
\]
Together with (19), these inequalities prove (20).

The coordinates of q_B are A_0-1 and B_0-1+tau. The first has
absolute value less than1/5 by (16). The second lies strictly
between -1/2 and B_0<3/8, by (20) and tau<1. Hence
\[
                             |q_B|^2<1/25+1/4=29/100<r^2.
\tag{21}
\]
This is the contradiction for the complete two-A-owned family.
No mean or endpoint of an unrelated shared side was restricted.

## 6. Complete S-leaf and opposite-load closure

Both tip-owned edges are excluded by
FOUR_CYCLE_MIXED_D_LEAF_EXCLUSION.md, Section2, whose proof expressly
retains the radial U-parallel endpoint and does not use a D-leaf
premise. Sections3--4 exclude the two mixed owner orders. Section5
excludes both A-owned edges. The all-mask articulation selection
makes this a complete owner cover.

Thus the entire S-leaf mixed physical mask is impossible. The
unique/unique and two/two physical masks were already closed, so
all S-leaf opposite-loaded-pair C4 components are excluded at the
canonical minimizer. With the separate full D-leaf theorem, **the
whole opposite-loaded-pair C4 branch is now excluded**.

The already completed adjacent-load exclusion leaves only the
all-three-loaded C4 alternative in this block type. The diamond
hub/tip domains remain distinct unresolved branches of C1.4.b1.
All four completion squares were retained throughout; no claim of
whole C1.4.b1 closure, an unrestricted radius theorem, or an equality
classification is made.

No numerical pose argument, Lean compilation, CI, changed normal
convention, or new secondary-minimizer premise is used.
