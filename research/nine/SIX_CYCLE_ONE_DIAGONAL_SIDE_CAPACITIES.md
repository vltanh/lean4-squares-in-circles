# Each side pocket of the unique-corner one-diagonal six-cycle holds at most one unit

**Status: complete whole-domain hand assembly; root and separate
independent full geometric, exact algebra and source-specific assembly
audits passed.**

Work throughout
\[
             79/40\le R\le\sqrt{1105}/16,\qquad \rho=5/4.
\tag{1}
\]
The entire selected positive component is
\[
                          B-W-C-U_C-T-U_B-B.
\tag{2}
\]
Its three loaded bodies B,C,T each have exactly one physical circle
corner. W is its only diagonal transmitter; the other two true
unloaded degree-two transmitters have width one. Retain all nine
physical squares, actual forces, original side means and three extras.

**Theorem.** Each of the two actual side pockets has capacity at most
one. The whole physical-unique, exactly-one-diagonal alternating C6
family is therefore impossible: its central region and diagonal
exterior pocket are already empty, leaving three extras for two
pockets of combined capacity at most two.

Physical radial loaded masks and the zero-diagonal family are outside
this theorem and remain separate obligations. No canonical motion or
change to any original contact mean occurs.

## 1. The complete actual shared-side normal form

Use SIX_CYCLE_ONE_DIAGONAL_INNER_CAPACITY.md and
SIX_CYCLE_ONE_DIAGONAL_CENTRAL_HOLE_EMPTY.md. In their global chart,
\[
 \begin{gathered}
 z_B=(-a,b),\quad z_C=(c,d),\qquad a+c=2+\sqrt2,\\
 p_B=(1-a,b-1),\qquad p_C=(c-1,d-1),\\
 \pi/4<\alpha,\beta<\pi/2,\qquad
                 \pi/2<\Sigma=\alpha+\beta\le3\pi/4,\\
 n_B=(\cos\alpha,-\sin\alpha),\qquad
 n_C=(-\cos\beta,-\sin\beta).
 \end{gathered}
\tag{3}
\]
The actual T applications are \(P=p_B+n_B\) and \(Q=p_C+n_C\).
The central-hole theorem proves that exactly one T interface is
genuinely shared, and that P,Q are distinct points of one actual
inner side. Reflect and relabel so that Q is the shared one.

Put
\[
 u=\cos\beta,\quad v=\sin\beta,\quad
 C_0=\cos\Sigma,\quad S_0=\sin\Sigma,\qquad
 e=(v,-u),\quad f=(-u,-v).
\tag{4}
\]
The orthonormal T chart (e,f) reverses orientation. The side points
from P to Q in direction e, and f points into T. Its unchanged
applications and their side-chord separation are
\[
 \begin{gathered}
 P=(A-1,B_0-1),\qquad Q=(A-1+\ell,B_0-1),\\
 \ell=\frac{\sqrt2-\cos\alpha-u}{v},\qquad0<\ell<1.
 \end{gathered}
\tag{5}
\]
Indeed the global horizontal component of Q-P is
\(\sqrt2-\cos\alpha-u\), and that of e is v. The actual strict
side-chord bounds are those of the central-hole theorem; neither
application is reselected.

The actual forces into T have directions \((S_0,-C_0)\) and
\((0,1)\). Their positive sum has positive own coordinates, so
T's unique circle corner is \(z_T=(A,B_0)\), with \(A,B_0>1/2\),
and its whole square is
\[
                           [A-1,A]\times[B_0-1,B_0].
\tag{6}
\]
Here B_0 is a coordinate and B is a physical body.

Define
\[
 \begin{array}{ll}
 p=1+u+v+S_0,&q_1=1+v-u-C_0,\\
 r_1=1+u-v-\ell,&s_1=2+u+v.
 \end{array}
\tag{7}
\]
Directly from the original applications,
\[
 z_B=(A-p,B_0-q_1),\qquad z_C=(A-r_1,B_0-s_1).
\tag{8}
\]
For example, the global vector \(z_B-P=(-1-\cos\alpha,1+\sin\alpha)\)
has own coordinates \((-u-v-S_0,u-v+C_0)\); likewise
\(z_C-Q=(1+u,1+v)\) has coordinates \((v-u,-1-u-v)\).
Thus (8) uses the actual circle corners.

The two equal-circle equations are linear:
\[
 pA+q_1B_0=(p^2+q_1^2)/2,\qquad
 r_1A+s_1B_0=(r_1^2+s_1^2)/2.
\tag{9}
\]
On the whole closed angular triangle
\[
                \alpha,\beta\ge\pi/4,\qquad
                         \alpha+\beta\le3\pi/4,
\tag{10}
\]
one has
\[
 p\ge2+1/\sqrt2,\quad s_1\ge3,\quad
 1\le q_1\le2+1/\sqrt2,\quad r_1\le1,\quad
                     D:=ps_1-q_1r_1\ge4+\sqrt2>0.
\tag{11}
\]
Here \(u+v\ge1,\ v\ge u,\ S_0\ge1/\sqrt2,\ -C_0\le1/\sqrt2\)
and \(\ell\ge0\). In particular \(D\ge3p-q_1\) gives the last
bound. There is no omitted pole or root choice. Therefore
\[
 \begin{split}
 A&=\frac{s_1(p^2+q_1^2)-q_1(r_1^2+s_1^2)}{2D},\\
 B_0&=\frac{p(r_1^2+s_1^2)-r_1(p^2+q_1^2)}{2D}.
 \end{split}
\tag{12}
\]

## 2. The original T torque and the four exact scalar certificates

Let \(m_B,m_C>0\) be the actual incoming magnitudes and let the
outward circle-resultant vector be \(\kappa(A,B_0)\), \(\kappa>0\). Force balance
gives
\[
 m_B=\kappa A/S_0,\qquad
 m_C=\kappa(B_0+A C_0/S_0).
\tag{13}
\]
Taking origin torque at the original P,Q gives
\[
 m_B[-C_0(A-1)-S_0(B_0-1)]
       +m_C(A-1+\ell)=0.
\]
Every determinant changes sign under the reversed chart, preserving
this zero equation. Substitution and multiplication by the positive
\(S_0\ge1/\sqrt2\) gives the exact normalized identity
\[
                  F:=S_0[A-(1-\ell)B_0]+\ell C_0A=0.
\tag{14}
\]
This is the S_0-multiplied torque. The coefficient 1/4 used below
belongs to exactly this F, not to F/S_0.

The actual outward channel heights are
\[
 h_B=C_0(A-1)+S_0(B_0-1),\qquad h_C=A-1+\ell.
\tag{15}
\]
Their outward normals in the T chart are \((C_0,S_0)\) and (1,0).
These are the actual occupied-crosscut heights, already positive by
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md.

The actual center vectors in this same origin-based chart are
\[
 \begin{split}
 t_*&=(A-1/2,B_0-1/2),\\
 b_*&=(A-p+(u+v)/2,\ B_0-q_1+(v-u)/2),\\
 c_*&=(A-r_1-(v-u)/2,\ B_0-s_1+(u+v)/2).
 \end{split}
\tag{16}
\]
Set
\[
 G_B=4t_*\cdot b_*+3\det(t_*,b_*),\qquad
 G_C=4c_*\cdot t_*+3\det(c_*,t_*).
\tag{17}
\]

C6_SHARED_T_SIDE_ARC_CERTIFICATES.md proves, on all of (10),
\[
 h_B-\frac{21}{50}+\frac F4>0,\qquad
 h_C-\frac{21}{50}>0,\qquad G_B>0,\qquad G_C>0.
\tag{18}
\]
Its variables A,B,C,S,p,q,r_0,s_0 correspond respectively to
A,B_0,C_0,S_0,p,q_1,r_1,s_1 here. We spell out the full scope and
exact sign evidence rather than treating numerical evaluations as proof.

Put \(k=\sqrt2-1\), \(x,y\in[0,1]\), and
\[
 \tau=kx,\quad H_0=1+k^2x,\quad j=k(1-x)y,\quad
 \omega=j/H_0,\qquad
 \alpha=\pi/4+2\arctan\tau,\quad\beta=\pi/4+2\arctan\omega.
\tag{19}
\]
For fixed alpha,
\(0\le\omega\le(k-\tau)/(1+k\tau)\), precisely its full allowed
range in (10). Conversely each point of (10) determines x and y,
except that x=1 collapses all y to the allowed endpoint. Thus one
whole rectangle covers every angular edge and interior point.

Sine and cosine are rational in these parameters over Q(sqrt(2)).
The positive polynomial factors are
\[
 D_a=1+\tau^2,\quad D_w=H_0^2+j^2,\quad
 V=(H_0^2-j^2+2H_0j)/\sqrt2=vD_w,\quad
 K=2D D_a^2D_wV>0.
\tag{20}
\]
The exact polynomial identity for K and all rational reductions
are given in the certificate source. In the data/checker, the
factor named "2D" denotes this polynomial numerator K.

Write \(L_1,L_2,L_3,L_4\) for the four expressions on the left
of (18). Multiplying by the following strictly positive factors
gives polynomials in x,y:
\[
 \begin{array}{c|c|c|c}
 i&Z_i&\deg P_i&\text{Bernstein coefficient count}\\ \hline
 1&D_a^2V^2KD_w&(18,10)&209\\
 2&D_aVK&(12,6)&91\\
 3&D_aV^2K^2D_w&(24,14)&375\\
 4&D_a^2V^2K^2D_w&(26,14)&405
 \end{array}
 \qquad P_i=Z_iL_i.
\tag{21}
\]
Every exact coefficient in the standard tensor Bernstein basis
is strictly positive. The respective exact minima are
\[
 \frac{10\sqrt2-9}{50}>\frac1{10},\qquad
 \frac{20-9\sqrt2}{50}>\frac17,\qquad
 \frac{762852688-539178072\sqrt2}{6279}>50,\qquad
 \frac{187+132\sqrt2}{2}>186.
\tag{22}
\]
The four rational comparison reserves after the justified
squarings are respectively4,162,39340299358276 and623.

C6_SIDE_ARC_CERTIFICATES.json records the exact power polynomials,
denominator factors and all1,080 indexed coefficients.
C6_SIDE_ARC_CERTIFICATES.js reconstructs every identity and
coefficient using exact rational and BigInt Q(sqrt(2)) arithmetic.
The exact power-to-Bernstein identity in the accompanying source
and the nonnegative basis weights, whose sum is one, prove all
four signs on the entire closed rectangle. There is no angle
subdivision or floating-point premise.

For the actual physical configuration, (14) turns the first
inequality of (18) into the required height bound. We have proved
\[
                 h_B,h_C>21/50,\qquad G_B,G_C>0.
\tag{23}
\]

## 3. Both actual center gaps have the required angular branch

We verify the angle branch before using (17). In B-side outward
coordinates the endpoint center heights are
\[
 \begin{split}
 t_*\cdot(C_0,S_0)&=h_B+(C_0+S_0)/2\ge h_B>0,\\
 b_*\cdot(C_0,S_0)&=h_B+(\sin\alpha-\cos\alpha)/2>h_B.
 \end{split}
\tag{24}
\]
The first increment is nonnegative because \(\Sigma\le3\pi/4\).
For the C-side normal e, whose own-chart coordinates are (1,0),
the corresponding identities are
\[
                 c_*\cdot(1,0)=h_C+(v-u)/2>h_C,\qquad
                 t_*\cdot(1,0)=A-1/2>0.
\tag{25}
\]
The last sign is the actual unique-circle-corner condition.

Normalize either actual side channel as
\[
 P_X=(l,h),\quad P_Y=(l+1,h),\qquad
 X\subset\{x\le l\},\quad Y\subset\{x\ge l+1\},
\tag{26}
\]
with outward direction upward. The two actual center horizontal
coordinates have separation at least two, because each unit has
halfwidth at least1/2. Every contained unit center has norm less
than \(M=91/60<2\): the farthest-corner inequality gives
\(|c|^2+|c|+1/2\le1105/256\), while
\[
                   M^2+M+1/2=1105/256+31/57600.
\]
Thus the centers in (26) have opposite strict horizontal signs.
Equations (24),(25) give positive vertical signs. Their angles obey
\[
                0<\phi_Y<\pi/2<\phi_X<\pi,\qquad
                          \gamma=\phi_X-\phi_Y\in(0,\pi).
\tag{27}
\]

The physical channel order identifies this upper arc as the actual
outward consecutive center gap. Globally the B-side outward arc
runs from B to T counterclockwise, and the C-side one runs from T
to C counterclockwise. The reversed T chart therefore gives the
positive determinant orders in (17). Consequently, for either side,
\[
                 G=|c_X||c_Y|(4\cos\gamma+3\sin\gamma).
\tag{28}
\]
On the proved branch \(0<\gamma<\pi\), positivity is equivalent to
\[
                            \gamma<\arccos(-3/5).
\tag{29}
\]
This is an actual center-gap conclusion, not an unqualified
inverse-cosine inference from a polynomial sign.

## 4. Full physical routing between the two endpoint center arcs

SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md supplies the facing actual
circle corners \(z_X,z_Y\) and the occupied simple crosscut
\[
                              z_X-P_X-P_Y-z_Y.
\tag{30}
\]
All its points have height at least h. Its upper outer-circle arc
completes a Jordan curve also wholly above h. Every extra E in
this actual exterior pocket satisfies
\[
                              E\subset D_R\cap\{y\ge h\}.
\tag{31}
\]
This statement uses the occupied original units, including the
actual transmitter; no concurrence polygon replaces their obstacle.

Both boundary center norms exceed \(\rho=5/4\), since their distance
to an actual circle corner is at most \(1/\sqrt2\) and
\(79/40-1/\sqrt2>5/4\). The connected-intersection theorem
ANNULAR_CENTER_ARC_AT_23_25.md applies to both endpoint units.
Its explicit closed-interval formulas show that the entire
intersection of each closed unit with the rho circle is one closed
arc whose relative interior lies in the open unit and contains
the radial-center point. Denote these arcs by \(I_X,I_Y\).

The radial-center points are in the open endpoint units, so (26)
gives
\[
               (\rho e_{\phi_X})_x<l,\qquad
               (\rho e_{\phi_Y})_x>l+1.
\tag{32}
\]
Cosine decreases on the upper semicircle. Every intersection of
the middle segment \(P_XP_Y\) with that semicircle therefore
has angle strictly between \(\phi_Y\) and \(\phi_X\).
The conclusion also holds if the segment never meets the circle.
The other two crosscut parts lie in X,Y and meet the rho circle
only in \(I_X,I_Y\).

We retain endpoint arcs that extend below the horizontal axis.
For every point p of a boundary unit with center c,
\[
                   c\cdot p\ge |c|^2-|c|/\sqrt2>0.
\]
Thus its entire inner-circle arc lies in the open angular
semicircle about its own center. Since (27) puts the two centers
in opposite upper quadrants, intersection of each arc with the
upper semicircle is still one closed interval containing its center
angle. Neither interval can pass across the other center angle:
that radial point is inside the other open unit, and a closed
unit cannot contain a point in the open interior of a physically
interior-disjoint unit.

Let p be a rho-circle point in the open interior of an extra E.
It is outside both closed endpoint units: otherwise a small open
ball in E would meet the other unit's open interior. Suppose its
angle is below \(\phi_Y\). The upper-circle path from that angle
down to zero avoids both closed endpoint arcs, because their
upper parts are the intervals just described. It avoids the
middle segment by (32), and the outer-circle arc because \(R>\rho\).
At angle zero it reaches height0<h; the positive horizontal ray
then escapes to infinity without crossing the Jordan curve.
This contradicts p being in the bounded pocket. An angle above
\(\phi_X\) is excluded by the symmetric path to pi and then the
negative horizontal ray.

Hence every inner-circle point in the extra's open interior lies
strictly between the two center angles. CENTERED_INNER_ARC.md
places the closed centered forty-degree arc of each endpoint
inside that unit's open interior. Avoiding both gives the full
routing statement
\[
 E^\circ\cap\{|p|=\rho\}
 \subset\{\rho e_\theta:
             \phi_Y+\pi/9<\theta<\phi_X-\pi/9\}.
\tag{33}
\]
No placement of the extra center in an unproved sector was assumed.

The weak-junction version follows from the actual cap theorem's
closure argument. Compact paths inside the extra's connected open
interior stay a positive distance from the occupied core; the
physical routings and their homotopies stay in that core. Their
pocket labels remain unchanged in the limit. Equations (30)--(33)
use the limiting actual closed crosscut and actual units. Additional
zero-weight contacts or extra circle contacts can subdivide this
pocket but cannot move an extra arc into a different free interval.

## 5. Exact interval budget and each whole side capacity

Equation (31), the minimum unit halfwidth1/2 and (23) imply
\[
                         |c_E|\ge(c_E)_y\ge h+1/2>23/25.
\tag{34}
\]
ANNULAR_CENTER_ARC_AT_23_25.md therefore gives a connected open
rho-circle arc in E of length strictly greater than
\(29\pi/120=43.5\) degrees. By (29),(33), its entire arc lies in
one interval of length
\[
                    \gamma-2\pi/9
                       <\arccos(-3/5)-2\pi/9<29\pi/60.
\tag{35}
\]

For completeness, the final comparison is exact. Polynomial division
and \(\arctan1=\pi/4\) give
\[
 0<\int_0^1\frac{x^4(1-x)^4}{1+x^2}\,dx=22/7-\pi.
\]
The quotient is \(x^6-4x^5+5x^4-4x^2+4\), with remainder -4,
so every term in this identity is explicit. Put \(z=583/630\);
then \(53\pi/180<z<\pi/2\). The signed cosine Taylor remainder gives
\[
 \begin{split}
 \cos(53\pi/180)&>\cos z>
          1-z^2/2+z^4/24-z^6/720\\
 &=3/5+\frac{67724343987694631}{45016921590480000000}>3/5.
 \end{split}
\tag{36}
\]
Therefore \(\arccos(-3/5)<127\pi/180\), and subtracting the two
twenty-degree endpoint arcs proves (35).

Two interior-disjoint extras in the same side pocket would have
disjoint open arcs with combined length strictly greater than
\(2\cdot43.5=87\) degrees, inside the single interval of length
strictly less than87 degrees in (35). This is impossible.
Each entire side pocket has capacity at most one.

## 6. Complete one-diagonal unique-mask exit and precise remaining scope

SIX_CYCLE_ONE_DIAGONAL_CENTRAL_HOLE_EMPTY.md excludes every central
extra, including the whole weak central free union.
SIX_CYCLE_ONE_DIAGONAL_OUTER_CAP_EMPTY.md excludes the diagonal
exterior pocket. The complete physical channel routing therefore
places all three extras into the two side pockets just bounded.

Both full allocations3+0 and2+1 are impossible, with either
assignment relative to T's uniquely shared side. The entire
alternating one-diagonal C6 with three physical unique corners is
excluded, with every original transmitter slider and shared mean.

The physical radial loaded masks, zero-diagonal width family,
other C6 load orbits and whole C1.6.b0 parent remain open.
The theorem does not alter any original force, assign a false
degree, use sampled angle boxes, classify original equality
packings, compile Lean or run CI. Its exact certificates prove
identities and signs over one full analytic rectangle; the geometric
routing and all actual physical hypotheses have been proved above.
