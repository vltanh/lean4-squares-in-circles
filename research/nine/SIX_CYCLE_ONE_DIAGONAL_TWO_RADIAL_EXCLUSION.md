# The exactly-one-diagonal alternating C6 cannot have two physical radial loads

**Status: complete whole-domain hand core exclusion; author, root and separate independent full source, prerequisite and exact audits passed.**
Work in \(79/40\le R\le\sqrt{1105}/16\), with the common selected physical certificate. The entire positive component is
\[
 B-W-C-U_C-T-U_B-B. \tag{1}
\]
W is its only diagonal transmitter; U_B,U_C are the actual unloaded degree-two side-normal transmitters. All three loaded bodies keep their physical circle masks, original individual nonnegative circle weights, actual pair forces, and original shared means. All three extras remain.

**Theorem.** At most one of B,C,T can have two physical circle corners. In particular the entire exactly-one-diagonal family with at least two physical radial loaded bodies is impossible.

This is a direct core exclusion. It does not use a unique-corner turn bound at a radial body or a limiting argument on circle weights.

The full all-mask proper concurrence, positive channel height and actual endpoint-center signs are supplied by SIMPLE_CYCLE_CONVEX_FORCE_POLYGON.md, Sections 1 and 5, using SIMPLE_CYCLE_LOADED_FORCES_NONPARALLEL.md. The compatible diagonal-endpoint side ownership is the same complete argument as SIX_CYCLE_ALTERNATING_DOUBLE_DIAGONAL_EXCLUSION.md, Section 2. None of these prerequisites bounds a radial concurrence inside its body.

## 1. Radial endpoints of a width-one channel use strict inner vertices

A radial loaded unit has actual form
\[
 S=[d,d+1]e+[-1/2,1/2]Je,\qquad
 K=d+1=\sqrt{R^2-1/4},\qquad9/10<d<61/60. \tag{2}
\]
If g is its outward normal into a side-normal transmitter, the next loaded application's position is p+g, with the original mean p.

The outer radial face cannot support a unit neighbor by width, and outer circle vertices are unshareable. For the inner radial axis g=-e, the next application is (d-1)e+yJe, |y|<=1/2. Its squared norm is less than13/50, while every point of a boundary unit has norm at least R-sqrt(2)>14/25, whose square exceeds13/50. Thus this axis is impossible.

A tangential radial axis g=+Je or -Je has support p.g=1/2. The next loaded unit would have minimum g-projection3/2 and width at least one, forcing maximum projection at least5/2>R. This is impossible as well.

Every remaining application is consequently a strict inner vertex. Its force normal is strict in that vertex cone, and the actual point is in the strict relative interior of the transmitter's side. An endpoint on the transmitter would be a vertex/vertex junction with a selected body-side-axis normal, forbidden by the existing strict point-normal convention.

At a radial body whose two channels have width one, the applications are distinct. Otherwise the two side-interior transmitter half-planes at that common vertex overlap unless their normals are opposite. Opposite normals are excluded by the nonparallel loaded-force theorem for the entire simple cycle. Thus both different inner vertices occur.

## 2. A radial endpoint of the diagonal forces R squared below17/4

Normalize the actual diagonal channel as
\[
 P_{BW}=(1-a,h),\qquad P_{WC}=(c-1,h),\qquad
 a+c=L:=2+\sqrt2,\quad h>0. \tag{3}
\]
The diagonal avoidance convention puts both applications in strict relative interiors of loaded sides. The two endpoint units have the same displayed square frame. The whole endpoint-center theorem gives strictly negative/positive horizontal center coordinates for B,C and nonnegative center heights.

If B is physically radial, those center signs force its radial direction to be leftward, rather than vertical or rightward. Its actual square is
\[
 B=[-K,1-K]\times[-1/2,1/2], \tag{4}
\]
so a=K and
\[
 0<h<1/2. \tag{5}
\]
The other endpoint has
\[
 C=[c-1,c]\times[b_C-1,b_C],\qquad
 c=L-K,\qquad c^2+b_C^2=K^2+1/4. \tag{6}
\]
Both diagonal endpoints cannot be radial: that would give c=K and 2K=L, whereas K>19/10 and L<7/2. Consequently C is physically unique, and b_C>1/2. Its strict side-interior application gives \(b_C-1<h\), hence \(b_C<3/2\).

Equation(6) gives the exact monotone identity
\[
 b_C^2=2LK-L^2+1/4. \tag{7}
\]
The right side equals9/4 at K=2. Since b_C<3/2 and L>0,
\[
 K<2,\qquad R^2<17/4. \tag{8}
\]
This conclusion uses the actual two-corner mask of B, with no assumption on how its original weights split.

For later simple estimates, the whole retained interval gives
\[
 9/10<d=K-1<1,\qquad
 1<c<31/20,\qquad 5/4<b_C<3/2. \tag{9}
\]
Here K>191/100 follows from the lower radius endpoint. Thus \(c<2+17/12-191/100<31/20\), while c>L-2=sqrt(2)>1. For the lower b_C bound, (7) and K>191/100 yield
\[
 b_C^2>189/100-(9/50)\sqrt2
 >25/16+29/400>25/16, \tag{10}
\]
using sqrt(2)<17/12.

## 3. The original B weights force its other normal downward

Assume now T is also physically radial. Section1 applies at both ends of the B-U_B-T channel and at T's other application.

The normalized original circle resultant of B has form \((-K,\omega)\), with -1/2<=omega<=1/2. Its proper concurrence is a positive multiple of that vector and lies on the actual W force line of height h. Equation(5) therefore gives omega>0; this is a consequence of the original weights, not a new equal-weight assignment.

Let g_B be the B-to-U_B normal. In B's exact force equation its incoming forces are \(-\mu_W e_x\) and \(-\mu_B g_B\), while the outward circle resultant has positive vertical component. Hence (g_B)_y<0. Section1 then fixes its actual application at the lower inner vertex
\[
 p_B=(-d,-1/2), \tag{11}
\]
and g_B has positive first component and negative second component.

## 4. Exact geometry of the two radial endpoints

Put
\[
 r_0=\sqrt{d^2+1/4},\qquad
 \phi=\arctan(1/(2d)). \tag{12}
\]
Both actual applications on B and T in this width-one channel have norm r_0, and their separation is exactly one. On this circle, the angle subtended by a unit chord is2phi, since sin(phi)=1/(2r_0).

The point p_B has polar angle pi+phi. The other application has angle pi+3phi. The alternative pi-phi would give a vertically upward channel, contrary to (g_B)_y<0. The radial direction of T is therefore either pi+2phi or pi+4phi. The first would make this channel a tangential side axis of T, excluded in Section1. Thus T's actual radial direction is exactly pi+4phi.

T's other original application must be its other inner vertex, by the distinctness statement in Section1. Denote it by Q. It is exactly
\[
 Q=r_0(\cos(\pi+5\phi),\sin(\pi+5\phi)),\qquad
 Q_x=-d\cos(4\phi)+\frac12\sin(4\phi). \tag{13}
\]
No T force-resultant direction or concurrence was substituted for its physical radial axis.

Throughout9/10<d<1 one has
\[
 \pi/8<\phi<\pi/6,\qquad
 \pi/6<\theta:=\pi-5\phi<3\pi/8. \tag{14}
\]
The lower phi bound uses1/(2d)>1/2>sqrt(2)-1; the upper uses1/(2d)<5/9<1/sqrt(3), since75<81. Thus \(Q_x=r_0\cos\theta\), and
\[
 \frac{dQ_x}{dd}
 =\frac{d\cos\theta-(5/2)\sin\theta}{r_0}<0, \tag{15}
\]
because tan(theta)>1/sqrt(3) and d<1<5/(2sqrt(3)). This is a whole-interval monotonicity calculation.

At d=1, tan(phi)=1/2 gives cos(4phi)=-7/25 and sin(4phi)=24/25, hence Q_x=19/25. Equation(15) and d<1 give the strict lower bound below. For its upper bound, r_0<sqrt(5)/2 and theta>pi/6 give \(Q_x<\sqrt{15}/4<1\). Therefore
\[
 19/25<Q_x<1. \tag{16}
\]

## 5. The complete C support fan contradicts its original concurrence

Equations(9),(16) put the actual Q strictly inside C's horizontal span:
\[
 c-1<Q_x<c. \tag{17}
\]
C has a unique physical circle corner (c,b_C) with b_C>0. Let g_C be its actual normal toward U_C and T. Its original force equation has outward circle resultant equal to \(\mu_W e_x-\mu_Cg_C\). Thus (g_C)_y<0.

If (g_C)_x<0, its actual application is the lower-left vertex \((c-1,b_C-1)\), and reserve one gives Q_x<c-1. If (g_C)_x>0, the application is the lower-right vertex \((c,b_C-1)\), and reserve one gives Q_x>c. Both contradict(17).

The only possible remaining normal is g_C=(0,-1), with its original mean on the bottom side. Its vertical force line has horizontal coordinate Q_x. Proper concurrence at the physically unique C is a positive multiple of (c,b_C), and also lies on the unchanged horizontal W force line y=h. Consequently
\[
 Q_x=\frac{ch}{b_C}
 <\frac{c}{2b_C}
 <\frac{31}{50}<\frac{19}{25}. \tag{18}
\]
Here(5),(9) were used, with no replacement of the mean. This contradicts(16), exhausting the full support fan.

Thus a radial diagonal endpoint B and radial opposite load T are impossible. Reflection covers a radial C and radial T. Two radial diagonal endpoints were already excluded in Section2, so every exactly-one-diagonal C6 with at least two physical radial loaded bodies is excluded.

The one-radial cases, with the radial body opposite or incident to W, retain their separate full completion obligations. No unit has moved, no force or corner weight has changed, no unique-mask turn bound has been imported by a limit, and no Lean compilation, CI or sampled angle box has been used.
