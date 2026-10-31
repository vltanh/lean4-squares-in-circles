# A four-load fan cannot have both endpoint contacts owned by its tips

**Status: complete hand implication at the stated full physical scope;
root and separate independent full hand audits passed.** Work in
\[
 R_*:=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The selected positive component has exactly the fan edges
\[
 Hu_i\quad(1\le i\le4),\qquad
 u_1u_2,\ u_2u_3,\ u_3u_4.
\tag{2}
\]
The hub H is unloaded and physically circle-clear. All four path bodies
are loaded. In particular the two endpoints have positive degree2 and
the two internal path bodies have positive degree3.

**Theorem.** It is impossible that both physical endpoint intersections
\(H\cap u_1\) and \(H\cap u_4\) are singleton points in the relative
interiors of sides of their respective boundary tips. Every inner-spoke
owner, free normal, shared-side mean and physical circle-corner mask is
retained. The four arbitrary completion squares are also retained.

Only the two genuine degree-two endpoints receive a two-force
concurrence argument. The proof does not split either degree-three
internal body into artificial end triangles. No normal is changed after
a certificate is obtained.

## 1. Two geometric inputs, including the sign of a boundary-edge moment

We use the already audited whole-path theorem
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`: every actual endpoint
application pair on H is at distance strictly greater than1. In the
present owner family those applications are vertices of H. They are
therefore opposite vertices.

We also record the following boundary-contact sign, with its short
proof so that no force-polygon assumption is imposed on an internal
path body.

**Lemma 1.1.** Let two boundary unit squares S,T touch, in that positive
circular order. If p is any actual contact point and n is any common
unit normal directed S to T, then
\[
                              \det(p,n)>0.
\tag{3}
\]
The order is the consecutive minor-circle order of the touching pair.

To prove this, choose circle corners z_S,z_T. The strict45-degree cone
in `ACUTE_LOADED_CONTACT_GRAPH.md`, Section1, puts both corners within
45 degrees of the direction of p. They are in the same circular order,
by the corner/center order theorem. Rotate so that p lies on the
positive horizontal axis and write their angles as
\[
             -\pi/4<\alpha<\beta<\pi/4,
                  \qquad m=(\alpha+\beta)/2.
\]
Put \(h=n\cdot p\). Their separating inequalities imply
\(n\cdot(z_T-z_S)\ge0\). Thus a lift \(\nu\) of the normal direction
can be chosen in \([m,m+\pi]\).

Suppose \(n_y\le0\). If \(m\ge0\), its only possible directions in
this interval have \(\nu=\pi+\eta\), \(0\le\eta\le m\). Consequently
\[
 h\le n\cdot z_T=-R\cos(\beta-\eta)<-R/\sqrt2.
\]
If \(m\le0\), its only possible directions outside \((0,\pi)\) have
\(m\le\nu\le0\), and instead
\[
 h\ge n\cdot z_S=R\cos(\alpha-\nu)>R/\sqrt2.
\]
At m=0 the two endpoint directions give the respective contradictions.
But any two contained unit squares on opposite sides of a support line
have
\[
                         1-R\le h\le R-1,
\]
since each has width at least1 in direction n. This is incompatible
with the preceding inequalities because \(R/\sqrt2>R-1\) throughout
(1). Thus \(n_y>0\), proving (3). The proof keeps all side means and
all physical circle corners.

## 2. The actual hub port order and its two endpoint normal signs

Write \(\sigma=1/\sqrt2\). Rotate so the opposite endpoint vertices
are horizontally aligned, and write the true hub center as (x,h):
\[
 P_1=(x-\sigma,h),\qquad P_4=(x+\sigma,h).
\tag{4}
\]
The true circle origin is still0; no translation has been made.

Neither endpoint point belongs to a third packing square. Indeed H
occupies a right-angle tangent sector there, while its tip occupies a
half-plane. Since the contact is a singleton, the tip's supporting line
is strict in H's vertex cone. The complement of those two tangent
interiors is the union of two sectors each strictly smaller than90
degrees. A third square has tangent angle at least90 degrees and cannot
fit. This also shows that no inner-spoke mean can equal P_1 or P_4.

The selected physical embedding has all four boundary bodies on its
unbounded face. In the fan graph its outer-face boundary is necessarily
\(H,u_1,u_2,u_3,u_4,H\); otherwise at least one of the four path vertices
would be enclosed. Thus the two inner hub spokes lie on the same
boundary arc of H between its endpoint applications. Equivalently, the
actual center/contact spokes inside H have the cyclic order
\(u_1,u_2,u_3,u_4\). Their inner contact sets cannot cross either
endpoint point, by the preceding tangent-sector observation. After a
reflection, take their common H arc to be the lower one, through
\((x,h-\sigma)\).

This assertion concerns the actual application points. A shared-side
mean stays on its actual side of that lower arc. Coincidence of the two
inner spokes at the bottom vertex is allowed. The arbitrarily small
junction untangling from `PHYSICAL_BODY_GRAPH_UNCROSSING.md` preserves
the distinct endpoint sectors and this cyclic order.

Let n_1,n_4 be the unit normals from H to its two tips. The complete
zero-force and zero-torque equations at H imply
\[
 n_1=(-b_1,a_1),\qquad n_4=(b_4,a_4),\qquad
                   0\le a_i\le b_i,\quad a_i^2+b_i^2=1.
\tag{5}
\]
Here is the full moment argument, independent of all inner means. For
any lower-arc application X and any actual outward H normal n there,
\[
                 \det(X-P_1,n)\le0,
           \qquad\det(X-P_4,n)\ge0.
\tag{6}
\]
On either lower side this follows by parametrizing its unit length; at
the bottom vertex it follows from \(n_y\le-|n_x|\). For example on
the lower-left side
\(X=P_1+t(\sigma,-\sigma)\), \(0\le t\le1\), its unit normal is
\((-\sigma,-\sigma)\), and the two determinants are -t and1-t.
On the lower-right side, with its natural parameter t, they again are
-t and1-t. At the bottom vertex they are
\(\sigma(n_y+n_x)\) and \(\sigma(n_x-n_y)\).

Taking the full hub torque about P_1 and P_4 now gives respectively
\((n_4)_y\ge0\) and \((n_1)_y\ge0\). Their H vertex normal cones
already have \(|n_y|\le|n_x|\), with the appropriate horizontal signs,
which proves (5). Strict singleton ownership actually removes the side
axis endpoints of those cones, but the enlarged weak bounds in (5)
are sufficient.

The planar star obtained by extending each hub spoke through its
boundary body to a circle corner preserves the same circular port
order. Thus the boundary path u_1,u_2,u_3,u_4 is counterclockwise,
matching the lower H-arc order just chosen. This remains true at an
inner junction by the same compatible untangling; no circle spokes
intersect any other open body.

## 3. The true circle origin is below the endpoint chord

First we show
\[
                         -\sigma<x<\sigma.
\tag{7}
\]
Normalize the actual positive circle-corner weights of the four bodies
to have total1. They sum vectorially to0, and every one of these corners
z has distance at most \(3/\sqrt2\) from c_H: use an actual H contact,
the unit-square diameter \(\sqrt2\), and H's half-diagonal. Therefore
\[
 R^2+|c_H|^2
       =\sum_z\lambda_z|z-c_H|^2\le\frac92.
\tag{8}
\]
If x>=sigma, (4),(8) imply
\[
                       |P_1|^2\le4-R^2<(R-\sqrt2)^2.
\tag{9}
\]
The strict inequality is equivalent to \(R^2-\sqrt2 R-1>0\).
It holds throughout the window: replace sqrt(2) by10/7, note that
\(R^2-(10/7)R-1\) is increasing there, and evaluate it at79/40
to get \(887/11200>0\). But P_1 belongs to a boundary unit, so
\(|P_1|\ge R-\sqrt2\), contradicting (9). Reflection handles
x<=-sigma. This proves (7).

Let the actual u_1u_2 and u_3u_4 magnitudes and normals be positive
multiples of g_1,g_3 in the path direction. Lemma1.1 makes their origin
moments strictly positive. The two genuine endpoint torque equations,
with their radial circle moments zero, give
\[
                     \det(P_1,n_1)>0,
                 \qquad\det(P_4,n_4)<0.
\tag{10}
\]
Using (5),(7), the first inequality reads
\[
                      b_1h>a_1(\sigma-x)\ge0.
\]
Hence
\[
                                  h>0.
\tag{11}
\]
The reflected second inequality is
\(b_4h>a_4(\sigma+x)\). Both strict inequalities will be used below.
No moment equation from an internal degree-three body has been replaced
by an endpoint equation.

## 4. Both endpoint circle masks have the same exact own-frame chart

We give the left endpoint; reflection treats the right endpoint without
changing any force or weight. Write
\[
 X=\sigma-x>0,\quad P=(-X,h),\quad
 n=(-b,a),\quad k=Jn=(-a,-b),\quad
 a=\sin\phi,\ b=\cos\phi,\quad0\le\phi\le\pi/4.
\tag{12}
\]
Because the tip owns its H contact in a relative side interior, its
whole square is
\[
        S=P+[0,1]n+[-\rho,1-\rho]k,\qquad0<\rho<1.
\tag{13}
\]
The estimates also hold at the enlarged endpoints rho=0 or1.
Define
\[
 N=P\cdot n=bX+ah>0,\qquad
 K=-P\cdot k=bh-aX>0.
\tag{14}
\]
The strict second sign is exactly (10).

Apply the all-mask proper concurrence lemma from
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma2.1, to this endpoint.
Its other positive neighbor touches the circle. Its concurrence has
\[
                 q=P+\ell n,\qquad\ell\ge0,
\tag{15}
\]
and is a positive multiple of its nonzero circle resultant. Thus that
resultant has positive n-component and strictly negative k-component:
\(q\cdot n=N+\ell>0\), \(q\cdot k=-K<0\).

The square center's n-coordinate is N+1/2>0. Every physical circle
corner is therefore on its outer n-face. A negative k-component of the
circle resultant forces the center's k-coordinate to be nonpositive.
If it is strictly negative there is one physical far corner in that
sign; if it is zero there are two physical corners and the negative-k
corner carries positive weight. Accordingly put
\[
 Z=K+\rho\ge\frac12.
\]
In this entire physical-mask cover,
\[
 \begin{split}
 R^2&=(N+1)^2+Z^2,\\
 c_S&=(N+\tfrac12)n-(Z-\tfrac12)k,\\
 X&=bN-aK\ge bN-aZ.
 \end{split}
\tag{16}
\]
In particular the two-corner case is Z=1/2 and remains included even
with unequal or zero individual circle weights. The concurrence may
lie outside a radial square; only (15), which is valid in that case,
was used.

The actual center is in the upper-left quadrant. Its vertical coordinate
is \(a(N+1/2)+b(Z-1/2)\ge0\). Its horizontal coordinate is strictly
negative, since directly from (13)
\[
 (c_S)_x=-X-\tfrac12b-(\tfrac12-\rho)a
          \le-X-\tfrac12(b-a)<0.
\tag{17}
\]
Write its radius and upper-horizontal angle as
\[
                  c_S=(-r\cos\delta,r\sin\delta),
                          0\le\delta<\pi/2.
\]
Equation(16) gives
\[
 0\le\phi\le\delta,\qquad
 N+\tfrac12=r\cos(\delta-\phi),\qquad
 Z-\tfrac12=r\sin(\delta-\phi).
\tag{18}
\]
Also q in (15) is strictly upper-left. The corresponding right endpoint
has both center and resultant in the reflected upper quadrant.

## 5. The three boundary links bound the two endpoint angles jointly

Let the endpoint center angles be \(\delta_1,\delta_4\). Their upper
center arc has length \(\pi-\delta_1-\delta_4\). The actual ordered
boundary path follows the complementary lower arc. One can see this
either from the planar lower port order in Section2, or from the same
order of the two upper resultant quadrants: global balance places the
other two resultants on the complementary path arc of length greater
than pi. The center intervals are disjoint and preserve that choice
of cyclic arc.

Put
\[
 \theta=\arccos\frac9{25},\qquad \alpha=3\theta-\pi.
\tag{19}
\]
Each physical boundary contact has minor center gap less than theta,
by the radius and center-distance calculation in
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md`, Section3. Therefore
\[
                  \pi+\delta_1+\delta_4<3\theta,
                    \qquad\delta_1+\delta_4<\alpha.
\tag{20}
\]
Its exact triple-angle bounds are
\[
 0<\alpha<\pi/6,\qquad
 \cos\alpha=\frac{13959}{15625}>\frac{89}{100},
                  \qquad\sin\alpha<\frac9{20}.
\tag{21}
\]
The final sine comparison follows by squaring:
\(400\cdot13959^2-319\cdot15625^2=60613025>0\).
In particular every endpoint angle and every relative angle
\(\delta-\phi\) in (18) lies in [0,pi/6).

## 6. A uniform endpoint-coordinate inequality

Define
\[
 r_0=\sqrt{R^2-\tfrac14}-\tfrac12,\qquad
 d=r_0-\tfrac12=\sqrt{R^2-\tfrac14}-1>\frac9{10}.
\tag{22}
\]
The actual radius r in (18) has the circle equation
\[
 R^2=r^2+r\bigl(\cos(\delta-\phi)+\sin(\delta-\phi)\bigr)+\tfrac12.
\tag{23}
\]
Compare it with \(R^2=r_0^2+r_0+1/2\). With
\(u=\delta-\phi\in[0,\delta]\), subtraction gives
\[
 (r_0-r)(r_0+r+1)=r(\cos u+\sin u-1).
\]
Consequently
\[
                     r\ge r_0-\tfrac12\sin u.
\tag{24}
\]
This also includes u=0. For u>0 use \(r_0\ge r\),
\(r_0+r+1>2r\), and \(\cos u+\sin u-1\le\sin u\).

Combining the last line of (16) with (18),(24),
\[
 \begin{split}
 X&\ge r\cos\delta-\tfrac12(\cos\phi+\sin\phi)\\
  &\ge r_0\cos\delta
       -\tfrac12\bigl(\cos\delta\sin(\delta-\phi)
                                  +\cos\phi+\sin\phi\bigr).
 \end{split}
\tag{25}
\]
For \(s=\sin\delta\), \(c=\cos\delta\), the parenthesis is
\[
                   (1+sc)\cos\phi+s^2\sin\phi
                    \le\sqrt{1+2sc+s^2}
                    \le c+\frac65s.
\tag{26}
\]
The last comparison is exact: the difference of its two squared sides is
\[
 (c+\tfrac65s)^2-(1+2sc+s^2)
                    =\frac{2}{25}s(5c-7s)\ge0.
\]
Here \(0\le\delta<\pi/6\) implies \(\tan\delta<1/\sqrt3<5/7\),
and both compared quantities are nonnegative. Thus every endpoint in
the whole chart satisfies
\[
                        X\ge d\cos\delta-\frac35\sin\delta.
\tag{27}
\]
This is a coupled angle/radius estimate, not a fixed-frame assertion.

## 7. The exact hub diagonal is too short

Let \(g(t)=d\cos t-(3/5)\sin t\). On [0,alpha], it is positive,
strictly decreasing and concave: \(g''=-g<0\). Positivity follows,
for example, from d>9/10 and alpha<pi/6.

For a fixed sum of two arguments, concavity makes their g-sum smallest
at an endpoint pair. Strict decrease and (20) therefore imply
\[
 \begin{split}
 X_1+X_4
 &\ge g(\delta_1)+g(\delta_4)\\
 &>g(0)+g(\alpha)\\
 &=d(1+\cos\alpha)-\tfrac35\sin\alpha\\
 &>\frac9{10}\left(1+\frac{89}{100}\right)
                         -\frac35\frac9{20}
   =\frac{1431}{1000}>\frac{10}{7}>\sqrt2.
 \end{split}
\tag{28}
\]
But the actual horizontal endpoint coordinates in (4) give
\[
                         X_1+X_4=(\sigma-x)+(\sigma+x)=\sqrt2.
\]
This contradiction proves the theorem.

## 8. Scope and the exhaustive remaining endpoint alternatives

The argument covers both endpoint side owners simultaneously for every
physical one-/two-circle-corner mask, every circle-weight split, all
inner hub means and all inner boundary-edge owners. Only the endpoints
were treated as degree-two bodies. The extra four squares were never
removed or repositioned.

A surviving full fan must therefore have at least one endpoint contact
outside this family: a hub-owned side-axis contact (including a positive
shared side), or a genuinely free vertex/vertex endpoint contact.
The fixed-point unique-tip selection may remove some free cases, but a
shared endpoint/path side and a physical radial mask must remain until
separately handled. This source does not claim those alternatives or
the full fan closed. No numerical probe, Lean compilation or CI is used
as a premise.
