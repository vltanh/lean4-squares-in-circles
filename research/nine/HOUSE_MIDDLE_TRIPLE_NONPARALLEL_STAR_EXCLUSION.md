# The entire nonparallel-A star in the middle-triple house is excluded

**Status: complete hand whole-star exclusion; root and separate independent
full hand audits passed.** Work in the declared radius window, with exact
positive graph
\[
                         AD,AT,DT,AB,BC,CD.
\tag{1}
\]
The hubs A,D are unloaded of exact positive degree3. T,B,C are loaded;
every physical circle mask, individual corner weight and all four extra
squares remain. No degree-two equation is imposed on either hub.

The full shared/free-hub exclusions leave AD singleton and owned by
exactly one hub. Call that owner A. The complementary parallel-A star
was excluded in HOUSE_MIDDLE_TRIPLE_PARALLEL_STAR_EXCLUSION.md.

**Theorem.** The entire nonparallel-A alternative in
HOUSE_MIDDLE_TRIPLE_OWNED_HUB_DOMAIN.md is impossible under the same
compatible necessary-certificate selection.

## 1. Full coordinates, selections and a quantitative support span

Use the complete domain coordinates
\[
 A=[-1,0]\times[-t,H],\qquad t,H>0,\quad t+H=1,
 \qquad p_{AD}=0,\quad n_{AD}=e_x,
\]
\[
 D=[0,1]u+[0,1]v,\quad u=(a,b),\quad v=(b,-a),
 \qquad a,b>0,\quad a^2+b^2=1.
\tag{2}
\]
The true circle center O stays separate. Let alpha be the A-to-T normal,
beta the D-to-T normal, and zeta the D-to-C normal. Write gamma,mu,nu,kappa>0
for AD,AT,DT,DC magnitudes. The full domain gives
\[
 \alpha_x\ge0,\quad\alpha_y>0,\quad p_{AB}=(-1,-t),
 \quad F_{AB}=-\gamma e_x-\mu\alpha,
\]
\[
 p_{DT}=u,\qquad\beta=r u-s v,\quad r,s>0,
 \qquad\beta_y>0,
\]
\[
 p_{DC}=v\quad\hbox{or}\quad
 p_{DC}=v+\tau u,\quad\zeta=v,\quad0\le\tau<\frac a{1+b}.
\tag{3}
\]
The second DC alternative keeps every actual singleton or shared mean.
D's actual concurrence is
\[
 q_D=(k_D,0),\quad k_D=\frac{s}{\beta_y};
 \quad\text{if D owns DC,}\quad k_D=\frac\tau a<\frac1{1+b}.
\tag{4}
\]
HOUSE_MIDDLE_TRIPLE_FREE_EXTERNAL_SELECTION.md removes free DC.
HOUSE_MIDDLE_TRIPLE_NONPARALLEL_FREE_FEATURES.md removes free AT and
removes free DT whenever DC is singleton. Thus AT is A-owned vertical
or T-owned oblique. DT is T-owned or genuinely free opposite an actual
positive-length shared DC side. These finite choices precede the
multipliers, with the existing fixed-tip and matched-junction choices.

If a unit square S has minimum-n support point p, where n is unit and
n_x<0, then
\[
                  \max_{x\in S}(x_x-p_x)\le |n_y|.
\tag{5}
\]
At a vertex take its two orthonormal inward axes. At most one can have
positive horizontal component: otherwise their nonnegative n-coordinates
could not give n_x<0. For an inward axis w with w_x>0, n dot w>=0
implies w_x<=|n_y|; the other axis contributes no positive span. At a
side-interior p the inward normal axis has negative horizontal component;
the tangential interval has length at most1 and horizontal unit component
|n_y|. This proves (5), including endpoints and every actual side mean.
Reflection gives, when n_x>0,
\[
                  \min_{x\in S}(x_x-p_x)\ge-|n_y|.
\tag{6}
\]
In particular max_B x<0. When zeta_x>0, min_C x>=p_DC,x-|zeta_y|.

When C owns DC, its application is the singleton v. Write
\[
       \zeta=-l u+m v,\qquad l,m>0,\quad l^2+m^2=1.
\]
D's full force and torque give
\[
             \nu(r-s)=\gamma a>0,
                \qquad\kappa(m-l)=\gamma b>0.
\tag{7}
\]
These strict inequalities are only used in this C-owned singleton
alternative, never at an unknown shared-side mean.

## 2. Two T-owned perpendicular roof axes are impossible

Suppose AT is T-owned and oblique. Put alpha=(c,d), with c,d>0 and
c^2+d^2=1. Its A application is (0,H), and A's exact torque gives
\[
                         \mu(d-c)=t\gamma>0.
\tag{8}
\]
Thus d>c. Since gamma+mu*c-mu*d=H*gamma>0, the actual AB normal obeys
\[
          |n_{AB,y}|<1/\sqrt2,\qquad\max_B x<-1+1/\sqrt2.
\tag{9}
\]
If DT is T-owned too, its axis is alpha or the counterclockwise
perpendicular; the other two axes have negative vertical component.
In the perpendicular case beta=(-d,c), and r=beta dot u>0 gives
bc>ad. Hence b>a and b>1/sqrt(2). D's outward C vector
gamma*e_x-nu*beta has positive first coordinate. Equations(3),(6) give
\[
                   \min_C x\ge b-|\zeta_y|>b-1>-1+1/\sqrt2,
\tag{10}
\]
contrary to BC and (9). Every DC owner and mean was retained.

## 3. The entire parallel-roof radial-S mask is impossible

Suppose alpha=beta. Their two roof applications are distinct. The
complete domain theorem makes T radial S in their common direction,
with both circle weights equal and positive. Its actual positive weighted
application mean is the midpoint of its inner unit face. Neither
application is separately made a midpoint.

### 3.1. Oblique AT

Use alpha=(c,d) as in Section2 and p=c/d. Then
\[
 0<p<1,\qquad H=b+ap,\qquad
                  \ell=|u-(0,H)|=a/d\le1.
\tag{11}
\]
First b>=a is impossible. If D owns DC, (6) gives min_C x>=b-a>=0.
If C owns DC, (7) gives m>l, so zeta_x=mb-la>0 and min_C x>b-1.
Here b>=1/sqrt(2), and (9) again separates B,C. Therefore a>b.

D's C vector has nonpositive u-coordinate. Since r=dH, this gives
nu*dH>=gamma*a; with (8),
\[
                       \frac\mu\nu\le\frac{tH}{a(1-p)}.
\tag{12}
\]
The weighted midpoint is at distance nu*ell/(mu+nu) from (0,H).
An inner-face point is at most1/2 from that face's midpoint. Thus
\[
                       \frac\mu\nu\ge2\ell-1=2a/d-1.
\tag{13}
\]
But d=1/sqrt(1+p^2) and tH=(b+ap)(1-b-ap) give
\[
\begin{split}
 E&=a(1-p)(2a/d-1)-tH\\
  &\ge a(1-p)(2a-1)-(b+ap)(1-b-ap)\\
  &=[ap-(a-b)]^2+a^2+2ab-a-b>0,
\end{split}
\tag{14}
\]
where the final remainder is exactly
\[
 a^2+2ab-a-b
  =\frac{b\{a(1-b)+(a^2-b^2)\}}{1+a}>0
\tag{15}
\]
because a>b>0. Equations(12)--(13) contradict this strict inequality.

### 3.2. Vertical AT, including a shared roof side

Now alpha=beta=e_y. Write the actual A application (-xi,H),
0<=xi<=1. The common roof side contains it and u, so
H=b, t=1-b, a+xi<=1, and K=1-xi>=a. A torque gives gamma/mu=K/t.
Consequently (5) gives, with the true AT mean and AB possibly free,
\[
 \max_B x\le-1+\frac{t}{\sqrt{K^2+t^2}}
                \le-1+\sqrt{(1-b)/2}.
\tag{16}
\]
If D owns DC and b>=a, min_C x>=b-a>=0 is impossible. If D owns
DC and a>b, (4) gives k_D=a<1/(1+b), also impossible, since
\[
        a(1+b)-1=b\left(a-\frac b{1+a}\right)>0
                     \quad\text{when }a\ge b>0.
\tag{17}
\]
If C owns DC, (7) gives b>a, so zeta_x>0 and min_C x>b-1.
But b>1/sqrt(2)>1/2 implies sqrt((1-b)/2)<b, contradicting (16)
and BC. This exhausts the entire parallel roof.

## 4. Vertical AT and a nonparallel T-owned DT are impossible

Suppose alpha=e_y and DT is T-owned, nonparallel to AT. An aligned
T has only e_y as a side axis with positive vertical component, already
covered. Thus the A contact is T's unique bottom vertex P=(-xi,H),
0<=xi<=1. Label its inward axes j=(c,d), Jj=(-d,c), c,d>0.
The choice beta=j would put every minimum-beta point on P+[0,1]Jj,
with nonpositive horizontal coordinate. Since u_x=a>0, the complete
remaining feature is
\[
              \beta=Jj=(-d,c),\qquad u=P+L j,
                      \quad0<L\le1,
\]
\[
 K=1-\xi=1+a-Lc>0,\quad t=1-b+Ld,
 \qquad n_{AB}=(-K,-t)/\sqrt{K^2+t^2}.
\tag{18}
\]
Allowing L=1 only enlarges the strict relative-side-interior family.

If C owns DC, (7) gives r-s=c(b-a)-d(a+b)>0, hence b>a.
Then zeta_x>0 and min_C x>b-1. However
\[
 bK-at=b-a+2ab-L(bc+ad)
          \ge(b-a)-(b-a)^2>0.
\tag{19}
\]
Thus t/sqrt(K^2+t^2)<b and (5) gives max_B x<b-1, a contradiction.
If D owns DC and b>=a, min_C x>=b-a>=0 again separates C,B.
For a>b, (4),(18) instead give
\[
                       k_D=a+b(d/c)>a>1/(1+b),
\tag{20}
\]
contradicting (4),(17). No circle-mask restriction was needed.

## 5. A free DT opposite a shared DC side

The selected certificate leaves free DT only when DC is genuinely
shared. D then owns its normal v and, for some -1<delta<1, the whole
actual square is
\[
                             C=D+v+\delta u.
\tag{21}
\]
Its minimum horizontal coordinate is b+delta*a>b-a. Since C must
touch B with max_B x<0, necessarily a>b. Equation(4) retains the
actual shared DC mean.

### 5.1. Vertical AT

If alpha=e_y, the actual free DT normal has beta_x<0. For the complete
feature cover first let T be oblique. Its A contact is its bottom vertex
P=(-xi,H), and both inward axes have positive vertical component.
Since beta_y>0, a minimum-beta vertex cannot be the opposite vertex.
The left adjacent vertex has horizontal coordinate below P_x<=0.
Thus u is the right adjacent vertex. The strict inward normal there
has negative scalar product with its right/up axis, forcing beta_x<0.

If T is aligned, its minimum-y side contains the A contact, while u
is strictly to its right. The free minimum-beta vertex can only be the
bottom-right vertex, again with beta_x<0. This retains every shared
AT side and its actual mean. The line through u in direction beta
therefore meets y=0 at
\[
                   k_D=a-b\frac{\beta_x}{\beta_y}>a.
\]
As a>b, (17) contradicts the actual side-mean bound (4). The entire
vertical-AT/free-DT alternative is excluded geometrically.

### 5.2. Oblique T-owned AT: the complete physical mask cover

It remains that alpha=(c,d), c,d>0, d>c, and its A application is
P=(0,H), a fixed singleton in the relative interior of a T side. The
free DT application u is another fixed singleton. If T had one physical
circle corner, GENERAL_FIXED_TIP_NORMAL_SELECTION.md would exclude
the free DT normal. This is exactly its distinct-fixed-application
premise at the loaded degree-two T. Neither DC's mean nor a circle
weight is fixed. Those selections are already part of the same finite
compatible pre-certificate choice.

Thus T has two physical circle corners and is radial S. Put
\[
                       h=\sqrt{R^2-1/4}-1>9/10.
\tag{22}
\]
The shared vertex u cannot be a physical circle corner, so it is an
inner radial vertex. The triangle side-normal theorem at T gives
alpha dot beta>=0. Since beta is strict at a T vertex and alpha is
a T axis, this is strictly positive. Hence u lies on the same
alpha-support side as P. In particular
\[
 p:=c/d\in(0,1),\quad H=b+ap<1,
                   \quad\ell=a/d<1.
\tag{23}
\]
The strict last inequality uses P's relative-side-interior position.

The radial axis cannot be -alpha. That would make AT the outer
radial face at projection h+1 from O; any unit beyond it has width
at least1 in that direction and would reach projection h+2>R.
Thus AT is either the inner radial face or a tangential face. At a
tangential face P lies from the inner vertex u toward the outer
vertex. Since u_x>P_x, the radial axis must be Jalpha, not -Jalpha.
The following two cases are exhaustive.

### 5.3. AT is the inner radial face

Write e=alpha and f=Je. The actual positions and strict free normal
are
\[
 u-O=h e-\tfrac12f,\quad P=u+\ell f,
 \qquad\beta=\beta_e e+\beta_f f,
                       \quad\beta_e,\beta_f>0.
\tag{24}
\]
The true roof torque about O is
\[
             \mu(\ell-\tfrac12)
                      =\nu(h\beta_f+\tfrac12\beta_e).
\tag{25}
\]
Since ell<1, it implies mu>nu*beta_e.

The genuine shared DC side gives nu*r=gamma*a. In the displayed
frame,
\[
 e\cdot u=dH,\quad f\cdot u=-d(a-bp)<0,
                           \quad r<\beta_e dH.
\]
Combining this with (8),
\[
             \frac\mu\nu=\frac{tr}{ad(1-p)}
                    <\beta_e\frac{tH}{a(1-p)}.
\tag{26}
\]
But (23) gives p<b/a and p<(1-b)/a. Since a>b,
\[
 a(1-p)>\max(a-b,a+b-1)
                      \ge\frac{\sqrt3-1}{2}>\frac13.
\tag{27}
\]
For b<=1/2 use a-b; for1/2<=b<a use a+b-1, which increases
from (sqrt(3)-1)/2 on this interval. Also tH<=1/4. Thus (26)
implies mu<(3/4)*nu*beta_e, contradicting (25). Every actual DC
mean and every radial corner-weight split remain.

### 5.4. AT is a tangential radial face

Now e=Jalpha and the inner vertex u is on the tangential face with
inward normal alpha. The strict free normal has the form
\[
            \beta=\beta_e e+\beta_\alpha\alpha,
                      \quad\beta_e,\beta_\alpha>0.
\]
The actual outward circle force of T is
\[
                  F_T=\nu\beta_e e+(\mu+\nu\beta_\alpha)\alpha.
\]
Any positive combination of its two physical circle corners has
tangential/radial ratio at most1/[2(h+1)]<1/3. In contrast the
strict D coordinate beta dot u>0 gives
\[
 \frac{\beta_\alpha}{\beta_e}>\frac{a-bp}{H}
                     >\frac a{1+b}>\sqrt2-1>\frac25.
\tag{28}
\]
For the middle inequality use p<(1-b)/a and H<1; for the next
use a>b. The actual force ratio is strictly larger still, since
mu>0. This contradicts the physical circle-force cone. An individual
corner weight may be zero; the same closed cone bound holds.

Sections5.1--5.4 exclude every free-DT/shared-DC alternative.

## 6. Exhaustive whole-star conclusion

AT is A-owned vertical or T-owned oblique. When DT is owned, Section3
excludes the parallel roof, Section2 excludes two perpendicular T-owned
axes, and Section4 excludes the remaining vertical-AT/nonparallel roof.
When DT is free, its opposite DC side is actually shared, and Section5
covers every AT feature and every physical roof circle mask. Free DC
was already removed; both of its owned alternatives were retained.

All finite normal selections are the same compatible choices made
before extracting a certificate. The loaded fixed-tip selection in
Section5.2 is invoked only at two distinct fixed physical singleton
applications and one physical circle corner. No selection freezes a
shared mean or changes an extracted normal. Physical uncrossing and
thinning preserve the cited selections exactly as in their sources.

This is a core exclusion for the whole nonparallel-A middle-house
domain. The four arbitrary extra squares were never moved or discarded.
Together with the parallel-star, shared-hub and free-hub exits it closes
the whole middle-triple house orbit. Other house load orbits and larger
components require their own exits. No numerical sample, parameter
scan, secondary minimizer, Lean compilation or CI is a premise.

