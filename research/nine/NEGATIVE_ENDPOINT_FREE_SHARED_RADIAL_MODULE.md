# A free negative endpoint of a boundary three-path forces an exact radial middle module

**Status: complete whole-feature hand reduction and source-dependency audit;
root and separate independent full hand audits passed.**
Work in
\[
                    79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Let H,A,B,C be actual contained interior-disjoint unit squares, with
positive edges HA,AB,BC and physical contact HC. A and B have exact
positive pair degree two and are positively circle-loaded. C physically
touches the circle and may retain arbitrary other positive forces.
H is physically clear and may retain arbitrary other positive forces.

Assume A has one physical circle corner z_A and
\[
                              c_H\cdot z_A<0.
\tag{2}
\]
All other physical packing units remain present. Suppose HA is a
genuinely free point-only vertex/vertex interface in the compatible
selected certificate.

**Theorem.** After an orthonormal coordinate choice about the true
circle origin, every such surviving free interface has the entire
module
\[
 \begin{gathered}
 N=\sqrt{R^2-9/4},\qquad T=\sqrt{R^2-1/4},\qquad d=T-1,\\
 A=[N-1,N]\times[1/2,3/2],\qquad
 B=[d,d+1]\times[-1/2,1/2],\\
 Q=H\cap A=(N-1,1/2),\qquad
 P=C\cap B=(d,-1/2).
 \end{gathered}
\tag{3}
\]
B has two physical circle corners and both of its original circle
weights are strictly positive. AB is a genuine shared side; BC is a
singleton. The actual H-to-A normal is (u,v), u>=v>0; the actual
C-to-B normal has both components positive. Every original AB mean
remains in its full actual overlap.

The theorem is uniform in all additional H and C forces. It needs
no HB chord, no triangle H-A-B, no fourth boundary-path body and no
three-force equation at H.

## 1. All geometric prerequisites hold in the actual four-body domain

If AB were a singleton, BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md
would remove the free HA at the true unique degree-two A with its
boundary neighbor B. Hence AB has positive length.

A and C are physically closed-disjoint. Indeed the physical boundary
path A-B-C cannot have a third contact AC: the complete boundary
angular-neighbor theorem in CIRCLE_CONTACT_ANGULAR_ORDER.md excludes
a physical boundary triangle. Its center-gap proof is geometric and
does not require C to have positive degree two.

By NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md, (2) gives
\[
                      |c_H|^2<9/2-R^2<3/5.
\]
Thus every actual point x of H satisfies
\[
                    |x|<\sqrt{3/5}+1/\sqrt2<3/2.
\tag{4}
\]
For the last exact comparison use
\(\sqrt{6/5}<23/20\), since \(6/5<(23/20)^2\).
This is a direct consequence of the same actual negative corner;
no stress reweighting or deleted outside force is involved.

These are precisely the geometric prerequisites used by the complete
module proof in HOUSE_LOWER_FREE_SHARED_PINNED_MODULE.md.
In that source's labels, its D,C,B become the present A,B,C.
The source's additional path endpoint is not used in the argument
once (4), actual HC and physical A/C disjointness are supplied.
The following sections give the complete scope audit and the
corresponding calculations.

## 2. A shared BC side is impossible in the entire incident-vertex case

Suppose the free A vertex Q is incident to the shared AB side.
Use common A/B axes to write
\[
 \begin{gathered}
 A=Q+[0,1]^2,\qquad
 B=Q+[t,t+1]e_x+[-1,0]e_y,\qquad -1<t<1,\\
 Q=(X,Y),\qquad n_{HA}=(u,v),\qquad u,v>0.
 \end{gathered}
\tag{5}
\]
The true A force coordinates identify
\(z_A=(X+1,Y+1)\), with X,Y>-1/2. If its actual AB
mean is \(Q+\tau e_x\), the full equations are
\[
 \lambda(X+1)=\mu u,\qquad
 \lambda(Y+1)=\mu v+\gamma,\qquad
 \lambda(Y-X)=\gamma\tau,
 \qquad \lambda,\mu,\gamma>0.
\tag{6}
\]
The complete tangent-sector argument excludes t<0: at Q the B
side-interior half-plane and A quadrant would force H to share
an A side. At t=0 the equal containing-circle equations give
Y=0 and X+1=sqrt(R²-1)>1, contradicting the last equation.
Thus
\[
                   0<t\le\tau\le1,\qquad Y>X,\qquad u\ge v.
\tag{7}
\]
Every original mean is retained.

The two physical circle equations give
\[
 Y=
 \begin{cases}
 (t/2)(X+1)+t^2/4,&Y\le1/2,\\
 t(X+1)+t^2/2-1/2,&Y\ge1/2.
 \end{cases}
\tag{8}
\]
Their complete comparison gives t>12/25. To recall the full
endpoint argument, t<=12/25 places the Y=1/2 transition at
X>=253/300>1/2, while Y>X and R²<9/2 imply X<1/2.
In the lower branch the crossing Y=X has
\(X+1=Y+1=(4+t^2)/(4-2t)\).
The actual positive coordinates are smaller than that crossing,
and this expression increases with t. It would imply
\[
 R^2<2(661/475)^2<(79/40)^2,
 \qquad (79/40)^2-2(661/475)^2=399137/14440000>0.
\]
Hence t>12/25 holds on the entire physical domain.

If BC also shared a side, the true B force equation and its
positive horizontal circle-force component force
\[
 C=Q+[t-1,t]e_x+[r-1,r]e_y,\qquad -1<r<1.
\tag{9}
\]
Physical A/C disjointness gives r<0. B's vertical force sign
gives Y<=1/2, including the radial weighted case. Then X>0,
and comparison of the actual B and C circle corners, with
k=-r in(0,1), gives
\[
       k^2+2k(1-Y)=2(X+t)+1<3-2Y,\qquad X+Y+t<1.
\tag{10}
\]
But X,Y>0 and the A circle equation imply X+Y>7/10:
otherwise R²<=389/100<(79/40)². This and t>12/25
contradict (10). BC is therefore a singleton in the entire
incident case. No equation at H or C was used.

## 3. The whole opposite-vertex/shared-BC case is also impossible

For completeness, before using any radial-middle conclusion, retain
the other full free-vertex type from the cited source: Q is on the
A side opposite AB. Suppose BC is shared. All three boundary units
are parallel.

Their two true B contact axes cannot be collinear. A radial S
inner-face neighbor is circle-clear and its outer-face neighbor
cannot fit; these exhaust both collinear signs. Normalize the two
perpendicular forces into B to point right and up:
\[
 \begin{split}
 B&=[x,x+1]\times[y,y+1],\\
 A&=[x-1,x]\times[y+s,y+s+1],\\
 C&=[x+t,x+t+1]\times[y-1,y],
             \qquad -1<s,t<1.
 \end{split}
\tag{11}
\]
Its northeast corner is on the circle,
\[
                          R^2=(x+1)^2+(y+1)^2.
\tag{12}
\]
The free H/A normal has positive first component at Q_x=x-1.
The complete support-span bound makes every H point's first
coordinate less than x. Since the actual H touches C, t<0.
Physical A/C disjointness then forces s>0.

Section3 of HOUSE_LOWER_FREE_SHARED_PINNED_MODULE.md now uses
only (11)--(12), circle containment and these signs to prove
\[
             -1/5<y<0,\qquad 7/10<x<1,\qquad
             Z:=\sqrt{R^2-x^2}>17/10.
\tag{13}
\]
Its comparison is complete: y>=0 makes every C corner strictly
inside the B circle in each x sign; then x>7/10. The A circle
corner is (x,Z), and s<1 gives Z<y+2 and x<y+1.
If y<=-1/5, this would give
\(R^2<(y+2)^2+(y+1)^2\le97/25<(79/40)^2\).

The upper free A vertex has height Z>17/10 and violates (4).
Thus Q=(x-1,Z-1). With its normal (u,v), the actual A equations
retain its AB mean \(Q+(1,\tau)\) and give
\[
                 \gamma\tau=\lambda(Z-x)>0,\qquad
                 0<\tau<1,\qquad
            \frac uv=\frac{x+(Z-x)/\tau}{Z}>1.
\tag{14}
\]
At a strict H support vertex with u>v>0 every H point advances
horizontally by less than1/sqrt(2) from Q.

The unchanged C circle equation in (11), on the other hand, gives
\[
 F=\sqrt{R^2-(y-1)^2}>3/2,\qquad
 x+1>17/10,\qquad
 t=\frac{4y}{F+x+1}>-1/4.
\]
The actual H/C contact needs horizontal advance at least
1+t>3/4>1/sqrt(2), a contradiction. This excludes the entire
opposite-vertex/shared-BC case, without any C force equation.

Thus BC is a singleton in both possible free-vertex classes.
No source argument has discarded its actual variable mean before
proving that physical conclusion.

## 4. The full two-body virtual-work selection forces both middle weights

Let P be the now-fixed BC point. The unique A circle corner and
its free HA vertex satisfy
\[
                              \det(Q,z_A)\ne0.
\tag{15}
\]
The complete argument in Section4 of the cited source uses only
A's true equations and its actual boundary neighbor B. If Q
were the radial-D inner vertex, torque about Q would force the
AB application onto a normal line through Q. The coincident
application is excluded by the boundary-neighbor coincidence
lemma. The other side-interior and vertex possibilities are
excluded by the full support-feature calculation in
GENERAL_FIXED_TIP_NORMAL_SELECTION.md, Section2; the remaining
outer vertex has support R/sqrt(2)>R-1. That calculation retains
every possible shared AB mean.

Suppose B uses at most one physical circle corner in its force.
This includes either zero-weight endpoint of its physical radial
mask. Choose its active corner z_B. In the common A/B axes take
the AB normal vertical, and define the two translation velocities
\[
                   w_A=Jz_A,\qquad
                   w_B=\frac{(z_A)_x}{(z_B)_x}Jz_B.
\tag{16}
\]
The denominator is nonzero: the absolute value of either own
coordinate of a physical circle corner is at least1/2.
These velocities kill the two actual circle forces and match
normal velocities across AB for every original mean. A common
rigid rotation of A+B about the true origin is a second virtual
motion killing the same internal rows.

Write n,m for the outward block normals at Q,P. Eliminating their
two positive magnitudes gives the necessary equality
\[
 \det(Q,n)(m\cdot w_B)-\det(P,m)(n\cdot w_A)=0.
\tag{17}
\]
The boundary-pair moment det(P,m) is nonzero. By (15), Q and z_A
are independent. The coefficient of the free n direction,
\[
                  (m\cdot w_B)JQ-\det(P,m)Jz_A,
\]
is therefore nonzero for every fixed genuine m.

Prelist every ordered physical H,A,B,C candidate, both free-vertex
classes and every possible active B corner before extraction.
The Q and P normal parameters are independent, including the
matched-junction convention, because A and C are physically
closed-disjoint. The finitely many nonzero analytic conditions
(17) can be avoided together with all earlier compatible strict
and generic choices. Uncrossing preserves surviving free normals
and adds only physical shared forces already covered in Sections2--3;
thinning deletes atoms. H, C and every other body have zero
velocity in this local argument, so all their additional forces
are retained and do not enter its work equations.

Thus B has two physical circle corners with both original weights
strictly positive. No weight is reset after certificate extraction.

## 5. The complete physical radial-middle module

Normalize this actual radial B as
\[
                         B=[d,d+1]\times[-1/2,1/2].
\]
A's shared AB cannot use either radial B side: the outer side
leaves insufficient disk width and the inner side makes A
circle-clear. Reflect so A is above B. Its actual overlap and
circle equation force
\[
                         A=[N-1,N]\times[1/2,3/2].
\tag{18}
\]
The uniform bounds
\[
 32/25<N\le23/16,\qquad T>191/100,\qquad
            1/2<T-N=2/(T+N)<200/319<2/3
\tag{19}
\]
are exact at the same full radius endpoints.

The lower-right A vertex is in a relative B-side interior, so
a third unit there would share an A side; it cannot give free HA.
The upper-right vertex is the unshareable circle corner.
The upper-left vertex has norm>3/2 and violates (4).
Consequently Q=(N-1,1/2), and (6)--(7) give the actual
H-to-A normal (u,v) with u>=v>0.

The true two-force equation at B gives a positive horizontal
component for the C-to-B normal g. A negative g_y would put
the BC contact at (d,1/2), in A's actual lower-side interior,
contradicting A/C disjointness. If g_y=0, its radial inner-face
neighbor C would be circle-clear. Thus g_y>0, and the actual
BC contact is P=(d,-1/2). It is a singleton by Sections2--3.
This proves every assertion of (3).

## 6. Exact source scope and remaining obligation

The source-dependency audit is complete:

| Original module argument | Premises supplied here |
| --- | --- |
| Small-root point bound | The actual negative corner gives (4), independently of H's degree |
| Both free-vertex/shared-next-side cases | True A/B degree two, physical boundary C, actual HC and A/C disjointness |
| Shared-block work and determinant | Only A/B are moved; all H/C and outside forces remain fixed |
| Independence and simultaneous preselection | Q and P cannot share a junction because A/C are physically disjoint |
| Radial-middle frame and final contacts | The actual B two-force equation, original AB mean, circle containment and (4) |

No equation at the extra house endpoint or the source's degree-three
third path body is used. The full four-body candidate family is
prelisted explicitly, so the change of graph labels does not presume
an unavailable earlier normal choice.

For the triangle-attached C4 with block loads ABC, the boundary
three-path cone and intact-petal pressure supply a negative unique
endpoint A. The theorem applies to every free HA, and therefore
excludes all such contacts when B is physically unique or has a
zero individual circle weight. Its remaining free family has the
exact module (3), both strictly positive B weights and the original
AB mean. C still has either physical mask. All H petal forces and
all three completion squares remain.

This is a complete physical-feature reduction, not an exclusion of
that radial-middle module or of the whole ABC orbit. The latter
still needs a full geometry, force or completion contradiction.
No actual HB contact, smaller root degree, changed mean, numerical
pose cover, Lean compilation or CI is used.
