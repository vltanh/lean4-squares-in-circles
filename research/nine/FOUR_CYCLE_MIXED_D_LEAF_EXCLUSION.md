# The entire radial-D-leaf opposite-load C4 is impossible

**Status: complete conditional hand exclusion; root and independent full
hand audits passed.** Work at the canonical radius minimizer in
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, in
\[
                     79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The positive component is A--B--U--D--A with a pendant **radial D
leaf at A**, with B,D loaded and U unloaded.

**Theorem.** This entire D-leaf opposite-loaded-pair C4 alternative
is impossible, with every physical circle mask, side owner, U-parallel
endpoint, actual channel mean and all four completion squares retained.

The unique/unique and two/two physical masks are already excluded.
The new proof below covers the entire remaining mixed mask. The
S-leaf opposite-load family and the all-three-loaded C4 remain open.

## 1. Exact domain and constants

Use FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md and
FOUR_CYCLE_TWO_RADIAL_TIPS_EXCLUSION.md. Reflect across the horizontal
axis and relabel if necessary so that B has one physical circle
corner and D has two.

The canonical reduction and
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md give
\[
 \begin{split}
 U&=[X-1,X]\times[Y,Y+1],\qquad P=(X,y_0),\quad Y<y_0<Y+1,\\
 A&=P+[0,1]v+[0,1]w,\qquad
 v=(a,b),\quad w=(b,-a),\quad a,b>0,\quad a^2+b^2=1,\\
 p&=(x,Y),\qquad p+e_y=(x,Y+1),\qquad x\le X\le\varepsilon.
 \end{split}
\tag{2}
\]
Here p,p+e_y are the actual channel means, their magnitudes are the
same positive gamma, and
\[
 B\subseteq\{y\le Y\},\qquad D\subseteq\{y\ge Y+1\}.
\]
A is oblique to U; AB and AD are singleton contacts; each has an
actual side-axis owner. Neither channel endpoint belongs to A.

Set
\[
 h=\sqrt{R^2-1/4}-1,\qquad r=R-\sqrt2,\qquad s_0=1-r.
\tag{3}
\]
The elementary window bounds used throughout are
\[
 \frac9{10}<h<\frac{61}{60},\quad
 \frac{14}{25}<r<\frac7{10},\quad
 0<s_0<\frac9{20},\quad
 \varepsilon=\max(h-1,0)<\frac1{60}.
\tag{4}
\]
For example r>14/25 follows from sqrt(2)<283/200 and R>=395/200;
r<7/10 follows from R<21/10 and sqrt(2)>7/5. The other bounds are
immediate squared comparisons in (1).

The physical two-corner upper tip D is radial S with parameter h.
If it is oblique to U, its bottom vertex must be
\[
 p+e_y=-\tfrac12r_D+h t_D,
 \quad r_D=(c,d),\quad t_D=(-d,c),\quad c,d>0,\quad c^2+d^2=1.
\tag{5}
\]
The other radial possibility has x-coordinate hc+d/2>1/2,
contradicting x<=epsilon. If it is parallel to U, it is exactly
\[
                  D=[-1/2,1/2]\times[h,h+1],
                  \qquad Y+1=h,\quad |x|\le1/2.
\tag{6}
\]
The horizontal or downward radial alternatives would place B's
bottom below -R, exactly as in the two-radial-tip theorem.

## 2. Both tip-owned edges, including the parallel radial endpoint

A unique-circle-corner tip owning its A edge cannot be parallel to
U, by the complete axis check in FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md.
If D is oblique too, the complete theorem
FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md excludes both tip-owned
contacts.

It remains to retain (6). A D-owned horizontal AD normal is impossible:
a leftward normal exposes P, which is below D, and a rightward normal
places D beyond A's right support and away from U. A downward normal
also exposes a point below D. Hence the AD normal is upward vertical
and q_D=P+v is A's upper vertex.

Write the lower tip's inward axes at its top vertex p as
\[
             r_B=(c_B,-s_B),\quad t_B=(-s_B,-c_B),
             \qquad c_B,s_B>0,\quad c_B^2+s_B^2=1.
\]
The complete B-owned face list has either the near-face normal t_B
or the far-face normal -r_B. Both have negative x-component, so
A's application can only be its lowest vertex P+w. Its normal cone
has negative y-component. Therefore only the near face is possible.
The unique-circle torque consequence recalled in the unique-tips
source gives
\[
                   c_B<s_B,\qquad z_B=p+r_B+t_B.
\tag{7}
\]
Let S=c_B+s_B and T=s_B-c_B. With p=(x,h-1), |x|<=1/2,
\[
 \begin{split}
 |z_B|^2-R^2
 &\le(1/2+T)^2+(h-1-S)^2-[(h+1)^2+1/4]\\
 &=T+2+2S(1-h)-4h\\
 &<1+2+3/10-18/5=-3/10.
 \end{split}
\tag{8}
\]
Here S<3/2, T<1 and h>9/10. This contradicts z_B being a circle
corner. The complete both-tip-owned alternative is now excluded,
including D parallel to U, without any use of the leaf type in
this section.

## 3. A owns the unique-tip edge; the radial tip owns its edge

Assume A owns AB and D owns AD. The A-owned unique-tip theorem gives
\[
                  n_{AB}=-v,\quad q_B=P+\tau w,
                  \quad 0<\tau<1,\qquad a\ge b.
\tag{9}
\]
The same A-vertex/side-feature check as in Section2 puts the D
application at q_D=P+v. If D is oblique, it is on the relative
interior of its inner face, with normal t_D from (5). If D is
parallel, the normal is e_y; use c=1,d=0,r_D=e_x,t_D=e_y.
In both cases write
\[
              K=bc-ad,\qquad C=ac+bd,
              \qquad t_D=Kv-Cw,
              \qquad C^2+K^2=1.
\tag{10}
\]
The A support cone gives K>=0 and C>0.

### 3.1. Every radial mean and circle-weight split gives the same contact form

For an oblique D, write q_D=p+e_y+sigma r_D, 0<sigma<1.
Its contact concurrence has own coordinates
\((-1/2+\sigma,h+\sigma c/d)\).
The own radial coordinate of its force is positive, and its other
coordinate is gamma d>0. Positive proportionality therefore gives
sigma>1/2, exactly as in the two-radial-tip theorem. Thus
\[
                         q_D=\kappa r_D+h t_D,
                         \qquad 0<\kappa<1/2.
\tag{11}
\]

For a parallel D, q_D=(kappa,h) is in its bottom-side interior.
Its two forces are upward; its torque equation is
\(\nu\kappa+\gamma x=0\), where nu>0 is the AD magnitude.
Since x<=X<(q_D)_x, this forces kappa>0. Side-interiority gives
kappa<1/2. Hence (11) holds in this case too. No channel mean or
individual circle weight has been fixed.

### 3.2. The D leaf fixes the full A-side equations

The force balance at A is
\[
              \alpha e-\mu v+\nu(Kv-Cw)=0.
\]
The D leaf direction e is an A side axis. Its w-component must
be positive, so
\[
                   e=w,\qquad \mu=\nu K>0,\qquad \alpha=\nu C.
\tag{12}
\]
In particular K>0. The A support side in direction w has coordinate
r. Write the upper vertex as q_D=T v-s_0 w, where 0<T<1 because
the D-leaf application is side-interior. Equations (11) and A's
origin torque give
\[
 hC-\kappa K=s_0,\qquad
 T=\kappa C+hK,\qquad CT=K\tau,
 \qquad \tau=s_0+\frac\kappa K.
\tag{13}
\]
For the torque identity, q_B=(T-1)v+(tau-s_0)w and the two
A-edge magnitudes are nu K and nu; their total moment is
nu(CT-K tau). The radial leaf contributes zero.

Let theta be the angle of v above the horizontal, and theta_D the
angle of r_D. Then 0<=theta_D<theta<=pi/4, and
C=cos(theta-theta_D), K=sin(theta-theta_D). Since tau<1, (13) gives
\[
                          rC^2+hC<1.
\tag{14}
\]
If C>=4/5, the left side exceeds
\((1/2)(16/25)+(9/10)(4/5)=26/25\), impossible. Therefore
\[
 C<4/5,\quad K>3/5,\quad
 a<4/5,\quad b>3/5,\quad a\ge1/\sqrt2>7/10,
 \qquad d<\frac1{5\sqrt2}<\frac17.
\tag{15}
\]
The last bound follows from theta_D<=pi/4-(theta-theta_D):
sin(theta_D)<(4/5-3/5)/sqrt(2).

There is also a uniform lower bound on tau. Equation (13) gives
\[
 \tau=\frac{hC-s_0C^2}{1-C^2}
  >\frac9{20}\frac{C(2-C)}{1-C^2}
  \ge\frac9{20}(2\sqrt2-1)>\frac45.
\tag{16}
\]
The rational function is increasing on (0,1), and C>=1/sqrt(2).
The final strict comparison is 18sqrt(2)>25, whose square is
648>625.

### 3.3. The unique tip must be oblique and then is physically circle-clear

If B were parallel to U, its A-owned contact would be its upper-right
vertex at height Y. The difference q_D-q_B=v-tau w would give
\[
                         b+\tau a\le1+d<8/7.
\]
For oblique D the actual right side is 1+sigma d with sigma<1;
for parallel D it is1. But (15)--(16) make the left side exceed
29/25>8/7. Therefore B is oblique.

Its top vertex p satisfies, uniformly for (5) and (6),
\[
                       -2/3<p_x<1/60,\qquad |p_y|<1/5.
\tag{17}
\]
For (5), p=(-c/2-hd,hc-d/2-1). Use d<1/7, c>49/50,
and (4):
\[
 c/2+hd<1/2+61/420<2/3,
 \qquad hc-d/2-1>(9/10)(49/50)-1/14-1>-1/5.
\]
The upper y bound is h-1<1/60. For (6), use |p_x|<=1/2,
p_y=h-1, and p_x<=epsilon.

As in Lemma2.1 of FOUR_CYCLE_UNIQUE_TIPS_EXCLUSION.md, write
B=p+[0,1]r_B+[0,1]t_B with r_B=(c_B,-s_B),
t_B=(-s_B,-c_B), and q_B=p+r_B. Its A support condition is
ac_B>bs_B. Equation (15) consequently gives
\[
                       c_B>3/5,\qquad s_B<4/5,
                       \qquad c_B-s_B>-1/5.
\tag{18}
\]
From (17), |p|<7/10. Both adjacent B vertices therefore have norm
less than17/10<R. At the opposite vertex,
\[
 \begin{split}
 |p+r_B+t_B|^2
 &=|p|^2+2+2p_x(c_B-s_B)-2p_y(c_B+s_B)\\
 &<\frac{109}{225}+2+\frac4{15}+\frac35
   =\frac{754}{225}<\frac72<R^2.
 \end{split}
\tag{19}
\]
For the x-term use p_x in (-2/3,1/60) and c_B-s_B in (-1/5,1);
for the y-term use c_B+s_B<3/2. Thus every B corner lies strictly
inside the circle, contradicting its loaded unique-corner mask.
This excludes the entire owner order of Section3.

## 4. The unique tip owns its edge; A owns the radial-tip edge

Now B owns AB and A owns AD. The unique tip B is oblique to U.
The full side-feature and A-vertex check gives its near face and
\[
 q_B=P+w,\quad n_{AB}=t_B=(-s_B,-c_B),\quad c_B<s_B,
 \qquad n_{AD}=-w,\quad q_D=P+\sigma v,\quad0<\sigma<1.
\tag{20}
\]
Put C=a s_B+b c_B>0 and K=a c_B-b s_B>=0, so
n_AB=-C v+K w. The A force equation with a radial D leaf then
forces its direction to be e=v, with K>0: the positive leaf must
cancel the strictly negative v-component, and the remaining w
balance equates the positive AD magnitude with the AB magnitude
multiplied by K.

The radial D application is side-interior on A's maximum-v face.
Consequently A has own-coordinate ranges
\[
                  -s_0\le z\cdot v\le r,
                  \qquad -t\le z\cdot w\le1-t,
                  \qquad 0<t<1,
\]
and
\[
                         q_B=-s_0v+(1-t)w,
                         \qquad q_D=(\sigma-s_0)v-tw.
\tag{21}
\]
Since A owns AD, q_D is a vertex of the radial physical two-corner
body D. It cannot be either circle vertex, so it is an inner vertex.
Its norm is therefore exactly sqrt(h^2+1/4), for either orientation
(5) or (6). Since r>1/2 and 0<sigma<1,
\(|\sigma-s_0|<r\). Hence
\[
 t^2=h^2+1/4-(\sigma-s_0)^2
       >h^2+1/4-r^2
       >(9/10)^2+1/4-(7/10)^2
       =57/100>9/16.
\tag{22}
\]
Thus t>3/4. Equation (21) now gives
\[
                         |q_B|^2
                 <(9/20)^2+(1/4)^2
                  =53/200<(14/25)^2<r^2.
\tag{23}
\]
Every point of a circle-touching unit square has norm at least r.
But q_B belongs to the loaded B. This is the contradiction for the
entire other mixed owner order, including D parallel to U and every
radial circle-weight split.

## 5. Full D-leaf owner and physical-mask exhaustion

Both A-owned edges were excluded for every physical circle mask in
FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md, Section7. Both tip-owned
edges, including the radial U-parallel endpoint, are excluded in
Section2 above. Sections3--4 exclude both mixed owner orders.
The all-mask articulation selection makes these four alternatives
exhaustive, while retaining every channel mean.

The entire mixed physical mask is therefore impossible for a D leaf.
Together with the complete unique/unique and two/two physical-mask
theorems, this closes **every radial-D-leaf opposite-loaded-pair C4**
at the canonical minimizer, with all four extras present.

The remaining opposite-loaded-pair C4 has an S leaf and the mixed
physical mask. Its two A-tip contacts are axis-owned, all individual
radial-corner weight splits remain, and all four extras still require
completion control if the core cannot be excluded. The all-three-
loaded C4 and the diamond domains remain open. No whole C1.4.b1 or
unrestricted nine-square closure is claimed.

No numerical search, Lean compilation, CI, altered normal convention,
or additional secondary-minimizer premise is used in this proof.
