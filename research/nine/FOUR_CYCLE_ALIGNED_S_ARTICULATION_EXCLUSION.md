# An all-three-boundary C4 cannot have an aligned S-leaf articulation

**Status: complete hand branch theorem; root and separate independent full hand
audits passed.**
Work in the declared radius window

\[
\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
h=\sqrt{R^2-\frac14}-1,
\qquad \sigma=\frac1{\sqrt2}.
\tag{1}
\]

Let the selected positive component have the cycle
\(A-B-U-C-A\) and a radial S leaf \(L\) attached to the clear
articulation \(A\). Suppose \(B,U,C\) physically touch the circle.
The leaf is normalized east, and the articulation is in the entire
aligned family

\[
L=[h,h+1]\times[-1/2,1/2],\qquad
A=[h-1,h]\times[t-1/2,t+1/2],
\qquad |t|\le1/2.
\tag{2}
\]

Its positive leaf force is horizontal and applied at \((h,0)\),
so it has zero origin moment. The two other positive A forces have
actual outward unit normals \(n_B,n_C\) and magnitudes
\(\mu,\nu>0\). Thus

\[
\kappa e_x+\mu n_B+\nu n_C=0,
\qquad \kappa>0.
\tag{3}
\]

**Theorem.** No such positive core exists. All frame orientations of
\(B,U,C\), all their physical circle-corner masks and individual
weights, all actual application means, and all four extra squares are
retained. Only A's force and moment equations are used. No positive
or zero multiplier on a possible additional physical \(AU\) contact
is assumed or introduced.

The tilted S-articulation family is a separate obligation; this source
does not claim the entire S-leaf C4 branch.

## 1. Uniform geometric constants and a rigid outer cap

The radius window gives

\[
\frac9{10}<h<\frac{11}{10},\qquad
r:=R-\sqrt2>\frac{11}{20},\qquad
R-\sigma>\frac{19}{15}>\frac54.
\tag{4}
\]

For the first bounds compare \(R^2-1/4\) with \((19/10)^2\)
and \((21/10)^2\). For the others use
\(\sqrt2<57/40\) and \(\sigma<17/24\).
Every point of a physical circle-touching unit has norm at least
\(r\), by comparison with one of its circle corners and the unit's
diameter \(\sqrt2\). Its center has norm at least
\(R-\sigma\), since a center is at distance \(\sigma\) from
each corner.

There is a useful exact rigidity statement:

**Cap lemma.** The only unit square contained in \(D_R\) and wholly
in \(x\ge h\) is \(L\).

Indeed, if its center is \(c=(c_x,c_y)\), its horizontal halfwidth
is at least \(1/2\), so \(c_x\ge h+1/2>0\). For any own
orthonormal axes \(u,v\), its maximum corner squared norm is

\[
|c|^2+\frac12+|c\cdot u|+|c\cdot v|
\ge |c|^2+|c|+\frac12
\ge(h+1/2)^2+(h+1/2)+1/2=R^2.
\]

Containment forces equality throughout. In particular
\(c_y=0\), \(c_x=h+1/2\), and the horizontal halfwidth equals
\(1/2\). The frame is therefore aligned, giving exactly \(L\).

Consequently neither \(n_B\) nor \(n_C\) can be \(+e_x\):
that would put the distinct corresponding unit wholly in this cap.

## 2. The complete A-normal cover forces one exact downward face

Reflect across the horizontal axis if necessary, so \(t\ge0\).
Put \(\ell=h-1\), so \(|\ell|<1/10\).
Every point on A's left side with nonpositive height has

\[
|p|^2<\frac1{100}+\frac14
=\frac{13}{50}<\left(\frac{11}{20}\right)^2<r^2.
\tag{5}
\]

Such a point cannot belong to any of \(B,U,C\).

The case \(t=0\) is already impossible. Equation (3) requires at
least one of \(n_B,n_C\) to have negative horizontal component.
Every support point for that normal is on A's left side, whose entire
height interval is then \([-1/2,1/2]\). Every point on that side
satisfies the same squared-norm bound (5), including its positive half,
and cannot belong to a boundary unit. Henceforth

\[
0<t\le1/2.
\tag{6}
\]

If both normals in (3) are horizontal, Section 1 makes them both
\(-e_x\). Their actual left-wall application means have positive
heights, by (5). The origin-moment equation on A would then be a
positive sum of these heights, because the leaf's moment is zero.
This is impossible.

Otherwise vertical force balance gives strict opposite signs. Relabel
so \((n_B)_y>0>(n_C)_y\). We claim

\[
\boxed{n_C=-e_y.}
\tag{7}
\]

If \((n_C)_x<0\), the actual A application is its lower-left
corner \((\ell,t-1/2)\), forbidden by (5).
If \((n_C)_x>0\), that application is
\(P=(h,t-1/2)\). By (6), this point lies in the relative interior
of L's left side. It is a minimum-\(n_C\) support point of C.
The elementary support-point fact in
`BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md`, Section 1, gives
\(P+\varepsilon n_C\in C\) for every sufficiently small
\(\varepsilon>0\). Because \((n_C)_x>0\) and P is in that
relative side interior, these points lie in \(\operatorname{int}L\).
A closed unit square cannot meet another square's open interior
without their open interiors overlapping. This is a contradiction.
Only the zero horizontal component remains, proving (7).

Equation (3) now gives

\[
(n_B)_x<0<(n_B)_y.
\]

Its A application is therefore the fixed upper-left vertex

\[
P_B=(\ell,t+1/2).
\tag{8}
\]

The whole lower unit C satisfies

\[
\max_C y=y_0:=t-1/2\in[-1/2,0],
\]

and its actual AC application is a point \((X,y_0)\) with
\(\ell\le X\le h\). Necessarily

\[
X>0:
\tag{9}
\]

if \(X\le0\), then \(|X|<1/10\) and (5) would again make
this boundary-unit point too central. The application may still be an
arbitrary mean on a horizontal shared side; nothing has fixed it to
an endpoint.

## 3. The lower unit's center is strictly to the right

We prove the following complete geometric fact, including aligned
endpoints.

**Lemma.** Let a unit square S have top support height
\(y_0\in[-1/2,0]\), with some point of that top support having
positive horizontal coordinate. If its center has horizontal
coordinate at most zero, every corner has squared norm at most
\(9/4+\sqrt2\).

Choose the unique top vertex when the frame is tilted, or the right
endpoint of the top side when it is aligned. Call it \(P=(x,y_0)\),
where \(x>0\). Write its inward axes as

\[
p=(-a,-b),\qquad q=(b,-a),
\quad a,b\ge0,\quad a^2+b^2=1.
\]

For an aligned frame take \((a,b)=(1,0)\). Put

\[
j=(a-b)/2,\qquad H=(a+b)/2.
\]

The center is \(c=(x-j,y_0-H)\); the assumed horizontal sign
forces \(0<x\le j\), in particular \(a>b\). Its own
coordinates obey

\[
c\cdot p=a(j-x)+b(H-y_0)\ge0,
\]

\[
c\cdot q=bx-bj+a(H-y_0)
\ge-bj+aH=\frac12>0.
\]

Hence the corner \(P+p+q=(x-2j,y_0-2H)\) is a farthest corner.
Since \(0<x\le j\) and \(-1/2\le y_0\le0\), its squared
norm is at most

\[
(2j)^2+(1/2+2H)^2
=(a-b)^2+(1/2+a+b)^2
=\frac94+a+b\le\frac94+\sqrt2.
\tag{10}
\]

This proves the lemma. Notice that
\(9/4+\sqrt2<15/4<(79/40)^2\).

Apply it to C using (9). Since C physically touches the radius-R
circle, (10) is impossible. Thus its center \(c_C\) satisfies

\[
(c_C)_x>0,
\qquad (c_C)_y<0,
\qquad -(c_C)_y\le1/2+\sigma<29/24.
\tag{11}
\]

Its center angle \(\gamma\), in \([0,2\pi)\), lies in the
fourth quadrant. In fact

\[
\boxed{\gamma>19\pi/12\quad(285\text{ degrees}).}
\tag{12}
\]

If its angle from the downward axis were at most \(\pi/12\),
then (4) would give

\[
-(c_C)_y\ge |c_C|\cos(\pi/12)
>\frac{19}{15}\frac{24}{25}
=\frac{152}{125}>\frac{29}{24},
\]

contradicting (11). Here \(\cos(\pi/12)>24/25\) follows from
\(\sqrt6>61/25\) and \(\sqrt2>7/5\) in the exact formula
\(\cos(\pi/12)=(\sqrt6+\sqrt2)/4\). The final rational
difference is \(23/3000>0\).

## 4. The upper unit's center angle is below 135 degrees

The actual point \(P_B\) in (8) belongs to B and is at distance
at most \(\sigma\) from its center \(c_B\). Since
\(|\ell|<1/10\) and \(1/2\le t+1/2\le1\),

\[
|(c_B)_x|<1/10+\sigma<17/20,
\qquad (c_B)_y>1/2-\sigma>-1/4.
\]

If \((c_B)_y\le0\), these bounds would imply

\[
|c_B|^2<\left(\frac{17}{20}\right)^2+
\left(\frac14\right)^2=\frac{157}{200}
<\left(\frac54\right)^2,
\]

contrary to (4). Thus \((c_B)_y>0\).

Let \(\beta\in(0,\pi)\) be its center angle. If
\(\beta\ge3\pi/4\), then

\[
(c_B)_x\le-\sigma|c_B|<-\frac54\sigma.
\]

The horizontal distance from \(P_B\) to \(c_B\) would then be
greater than

\[
\frac54\sigma-\frac1{10}>\sigma,
\]

where the final inequality uses \(\sigma>2/5\). This contradicts
\(|P_B-c_B|\le\sigma\). We have therefore proved

\[
\boxed{0<\beta<3\pi/4\quad(135\text{ degrees}).}
\tag{13}
\]

## 5. The two boundary contacts cannot span the required western arc

The centers of L, B, and C have directions \(0,\beta,\gamma\),
respectively. The physical boundary contacts \(BU\) and \(UC\)
join consecutive center directions along their corresponding minor
arcs, by `CIRCLE_CONTACT_ANGULAR_ORDER.md`. The arc from C to B
through angle zero contains L, so the boundary path B--U--C must use
the other, western arc. The center angle \(\delta\) of U therefore
satisfies

\[
\beta<\delta<\gamma.
\]

Each physical boundary contact spans strictly less than \(2\pi/5\)
(72 degrees), by that same theorem. Consequently

\[
\gamma-\beta=(\delta-\beta)+(\gamma-\delta)
<\frac{4\pi}{5}\quad(144\text{ degrees}).
\tag{14}
\]

But (12)--(13) give the incompatible strict lower bound

\[
\gamma-\beta>\frac{19\pi}{12}-\frac{3\pi}{4}
=\frac{5\pi}{6}\quad(150\text{ degrees}).
\]

This contradiction proves the theorem for the entire aligned family
(2), including both endpoint heights, every boundary-body frame and
all application means.

The argument excludes this core itself and does not move any other
square. It does not infer a positive multiplier from an unstressed
physical contact, invoke the diamond exclusion at a zero AU edge, or
apply a degree-two equation to U. The tilted S-articulation family
remains separate. No numerical scan, Lean compilation or CI is a
premise.
