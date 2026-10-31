# The entire oblique central-contact D-diamond chart is impossible

**Status.** Complete hand proof; root and separate independent full hand audits passed. Every owner of the lower boundary contact, every positive
shared-side mean, and the free articulation-contact endpoints are retained.
Only the degree-two lower tip's force and torque equations are used.
The central boundary square may have three or more contacts and arbitrary
additional forces. This source closes the oblique central-contact chart;
the central-horizontal and A/U-parallel charts are separate inputs to the
parent D-diamond cell.

## 1. Exact geometric and certificate domain

Throughout,
\[
 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 s=1+\sqrt2-R,
\]
\[
 A=[-s,1-s]\times[H-1,H],\qquad
 P=(-s,H-1),\qquad Q=(-s,H),\qquad 0<H<1.
\tag{1}
\]
The squares `U,C` are physical boundary squares, with actual contacts
`AU` at `Q`, `AC` at `P`, and `UC`. Their interiors and that of `A` are
pairwise disjoint. The selected inward normals are

- `m`, from `A` into `U` at `Q`, strictly northwest;
- `n`, from `A` into `C` at `P`, strictly southwest;
- `w`, from `U` into `C`, at the actual `UC` application `T`.

The lower tip `C` has exactly the two positive pair forces `AC,UC` and
positive circle load. No equation is assumed at `U`.

Use the compatible pre-certificate strict normal choices and the full
fixed-application unique-tip selection of
BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md. That selection is made
simultaneously for every candidate tip before extracting the physical
certificate. It permits no free point-contact normal at `C` when both
applications are singletons and `U` is a boundary neighbor. All shared
application means remain unrestricted.

**Theorem.** No such selected positive lower-tip star exists.

### 1.1 Uniform bounds and physical circle masks

As in D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md, both `P` and `Q` have
norm at least `R-sqrt(2)=1-s`. Hence
\[
 H^2,(1-H)^2\ge1-2s.
\]
Since `min(H,1-H)<=1/2`, and since `R>=79/40`,
\[
 \frac38\le s<\frac49<\frac9{20},\qquad
 \frac13<H<\frac23,
\tag{2}
\]
where the bound `s<4/9` follows from
`s<=sqrt(2)-39/40<4/9`: its last comparison is
`2<(511/360)^2`. We will also use the weaker convenient bounds
\[
 \frac3{10}<H<\frac7{10},\qquad
 |P|,|Q|<\frac56.
\tag{3}
\]
For (3), each squared norm is less than `277/400<25/36`.

By the physical adjacent-circle-corner classification in
RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md, a unit square with two physical
circle corners in this radius window is radial S; every point of it has
norm at least
\[
 \sqrt{R^2-\tfrac14}-1>\frac9{10}>\frac56.
\]
It cannot contain `P`. Thus `C` has exactly one physical circle corner.
This retains all initial physical masks rather than assuming uniqueness.
The proof never restricts the physical corner mask or force balance of
`U`.

We repeatedly use the radius-free triangle side-normal obstruction:
if one contact normal is a side axis of a square and its two neighbors
also touch, its two outward normals have nonnegative dot product.
Its complete statement, including shared-side means and side endpoints,
is UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md.

## 2. Singleton UC: the two exhaustive owners

When `UC` is a singleton, the fixed-application selection makes both
`AC` and `UC` side-owned. The strict southwest `AC` normal cannot be an
axis of `A`, so `AC` is owned by `C`. Write
\[
 n=(-d,-c),\qquad k=(c,-d),\qquad
 c,d>0,\quad c^2+d^2=1,
\]
\[
 C=P+[0,1]n+[-\rho,1-\rho]k,
 \qquad 0<\rho<1.
\tag{4}
\]
The `UC` side is owned either by `C` or by `U`. Coincident or endpoint
vertex/vertex cases do not create a third case: the selected common
normal there is strict in both vertex cones and is removed by the
fixed-application tip selection. A genuine side-owned singleton has its
application in the owning side's relative interior.

### 2.1 UC owned by C

This entire alternative, including the `U`-owned and free `AU` endpoints,
is excluded by D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md. Its proof uses
only `C`'s equations, not an equation at `U`.

### 2.2 Preliminary consequences when UC is owned by U

The side-normal obstruction applied at `C` and `U` gives
\[
 n\cdot w\ge0,\qquad (-m)\cdot w\ge0.
\tag{5}
\]
The first inequality is strict. If `n dot w=0`, `w` is also an axis of
`C`; a side of `C` meeting the relative interior of the owning side of
`U` creates a positive-length shared segment. That is outside the
singleton case. Thus
\[
 n\cdot w>0.
\tag{6}
\]
The minimizing `w` vertex of `C` is therefore on its `n`-minimum side
through `P`. It is one of
\[
 P-\rho k,\qquad P+(1-\rho)k.
\tag{7}
\]
We treat both possibilities through the full zero/positive split of the
second inequality in (5).

### 2.3 Positive dot product at U

Suppose `(-m) dot w>0`. Since `w` is an outward side axis of `U`, its
`AU` support point `Q` belongs to that same `w`-maximum side. Both `Q`
and `T` lie on one unit side, so `|Q-T|<=1`.

The second vertex in (7) cannot be `T`, since
\[
 |Q-P-(1-\rho)k|^2
 =1+(1-\rho)^2+2(1-\rho)d>1.
\]
Consequently
\[
 T=P-\rho k,\qquad
 Q-T=(\rho c,1-\rho d).
\tag{8}
\]
The normal pointing into `C` along this `U` side is
\[
 w=\frac{(1-\rho d,-\rho c)}{|Q-T|},\qquad
 w\cdot n=\frac{\rho-d}{|Q-T|}>0,
 \qquad w\cdot k=\frac{c}{|Q-T|}>0.
\tag{9}
\]
The sign is fixed by the positive `k` projection at the minimizing
vertex; its opposite would not support `C`. In particular `rho>d`.

Write
\[
 X=n\cdot P=sd+(1-H)c>0,\qquad
 Y=k\cdot P=(1-H)d-sc,\qquad V=1-\rho.
\]
The unique circle force has positive `n` and `k` components, so its
physical corner is
\[
 z_C=P+n+Vk.
\tag{10}
\]
Torque at `C` about `P`, with `T-P=-rho k`, gives
\[
 Y-VX>0.
\tag{11}
\]
In particular `Y>0`. Comparison of (10) with `P`, using `|P|<5/6`,
gives exactly as in the lower-tip-owned source
\[
 V>\frac{11}{20},\qquad \rho<\frac9{20}.
\tag{12}
\]
Equations (9) and (12) imply `d<9/20`, hence `c>7/8`. But (2)--(3)
then give the opposite strict bound
\[
 Y=(1-H)d-sc
 <\frac7{10}\frac9{20}-\frac38\frac78
 =-\frac{21}{1600}<0.
\tag{13}
\]
This excludes the whole positive-dot case.

### 2.4 Perpendicular endpoint at U

Suppose instead `(-m) dot w=0`. Because `w` is a side axis of `U`, so
is `m`; its northwest direction and (6) force
\[
 m=(-a,b),\qquad v=(b,a),\qquad w=-v,
 \qquad a,b>0,\quad a^2+b^2=1.
\]
There is an actual corner `O` of `U` such that
\[
 U=O+[0,1]m+[0,1]v,
 \quad Q=O+\lambda v,
 \quad T=O+\tau m,
 \quad 0<\lambda,\tau<1.
\tag{14}
\]
The strict intervals express the two owned singleton side contacts.
The `x` coordinate of `Q-T=lambda v-tau m` is positive. The only vertex
in (7) with `x` coordinate below that of `Q` is therefore
\[
 T=P-\rho k.
\]
Put
\[
 S=ac+bd>0,\qquad D=ad-bc.
\]
Since this is the minimizing `w` vertex, `D=w dot k>0`. Direct projection
of `Q-T=e_y+rho k` onto the axes in (14) yields
\[
 \lambda=a-\rho D,\qquad \tau=\rho S-b>0.
\tag{15}
\]
Again the circle corner is (10), and (12) holds. At `C`, force and torque
give the positive concurrence displacement
\[
 \eta=\frac{\rho S}{D}
      =\frac{Y-VX}{Y+V}>0.
\tag{16}
\]
Introduce the auxiliary point
\[
 T'=(X+\eta)n+(Y-\rho)k
    =\frac{Y}{Y+V}z_C-\rho k.
\tag{17}
\]
It is a geometric expression, not a replacement of any application or
force. The exact scalar estimate (14) of
D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md applies because `0<Y<7/10` and
`0<rho<9/20`. Therefore
\[
 |T|^2=X^2+(Y-\rho)^2
       <(X+\eta)^2+(Y-\rho)^2
       =|T'|^2\le\frac{7409}{8000}
       <\left(\frac{39}{40}\right)^2.
\tag{18}
\]

The positive `tau` in (15) also gives `b<rho S<=rho<9/20`, so `a>7/8`.
Since `D=ad-bc<a`,
\[
 \lambda>a(1-\rho)>
 \frac78\frac{11}{20}=\frac{77}{160}>\frac{12}{25}.
\tag{19}
\]
The vertices `O` and `O+v` are at distance at most one from `Q`, hence
have norm less than `5/6+1<79/40`. The vertex
`O+m=T+(1-tau)m` has norm less than `39/40+1=79/40`. Finally,
\[
 O+m+v=Q+m+(1-\lambda)v,
\]
\[
 |O+m+v|<\frac56+
 \sqrt{1+\left(\frac{13}{25}\right)^2}
 <\frac56+\frac{17}{15}
 =\frac{59}{30}<\frac{79}{40}.
\tag{20}
\]
Here `sqrt(794)/25<17/15` follows by squaring. All four vertices of
`U` are strictly circle-clear. This excludes the perpendicular endpoint
and completes every singleton `UC` alternative.

## 3. Positive-length shared UC: no application mean is fixed

Now allow `UC` to be a positive-length shared side. Its normal `w` is
an axis of both squares. The side-normal obstruction again gives
\[
 n\cdot w\ge0,\qquad (-m)\cdot w\ge0.
\tag{21}
\]
If both were positive, `P` would belong to the `w`-minimum face of `C`,
and `Q` to the `w`-maximum face of `U`. These faces lie on the same
physical contact line. Thus `w dot(Q-P)=w_y=0`. A horizontal `w`
cannot have positive dot product with both the southwest `n` and the
southeast `-m`. Hence at least one inequality in (21) is equality.
They cannot both be equality, since the strictly southwest and northwest
normals are not parallel. This is an exhaustive two-case division.

### 3.1 AC perpendicular to the shared normal

If `n dot w=0`, `n` is a side axis of `C`. The strict southwest normal
is not an axis of `A`, so `AC` is a singleton owned by `C`, with placement
(4). The only sign compatible with `(-m) dot w>=0` is `w=k`. The latter
dot product is in fact strictly positive: both vectors are southeast.
Thus `Q` is on the actual shared contact line, giving
\[
 k\cdot Q=k\cdot P-\rho,
 \qquad \rho=d.
\tag{22}
\]
The true shared application is
\[
 T=P+\eta n-\rho k,\qquad 0\le\eta\le1.
\]
The entire interval is retained. The circle corner is (10), and its
force/torque equations yield
\[
 \eta(Y+V)=Y-VX,
 \qquad Y\ge VX>0.
\]
The same circle-distance bound (12), now with `rho=d`, gives
`d<9/20,c>7/8`; (13) contradicts `Y>0`. This includes both endpoint
means and all positive circle-force magnitudes.

### 3.2 AU perpendicular to the shared normal: exact geometry

It remains that `(-m) dot w=0`. As in (14), write
\[
 m=(-a,b),\quad v=(b,a),\quad w=-v,\quad
 a,b>0,\quad a^2+b^2=1,
\]
\[
 U=O+[0,1]m+[0,1]v,\qquad Q=O+\lambda v,
 \quad 0<\lambda<1.
\]
A genuinely shared side has
\[
 C=O+[h,h+1]m+[-1,0]v,\qquad -1<h<1.
\tag{23}
\]
The positive dot product `n dot w` puts `P` on the `v`-maximum face of
`C`. The normal cannot be parallel to `w`, since then both forces at
`C` would be parallel to a square side axis, impossible for its unique
physical circle corner. Thus `P` is an endpoint of that face.

Projecting `Q-P=e_y` onto `v,m` gives
\[
 \lambda=a,\qquad P=O-bm.
\]
The endpoint choice `h+1=-b` would have `h<-1` and no shared segment.
Therefore the entire geometry is forced to be
\[
 \boxed{\quad
 U=O+[0,1]m+[0,1]v,\quad Q=O+av,\quad
 C=O+[-b,1-b]m+[-1,0]v,\quad P=O-bm.
 \quad}
\tag{24}
\]
The free `AC` normal has the full form
\[
 n=\alpha m-\beta v,\qquad \alpha,\beta>0,
 \qquad n_y<0.
\]
No value of that normal has been substituted or selected after the fact.

Set `h_0=1-H` and define
\[
 A_0=1+s a+H b>1,\qquad B_0=s b+h_0 a>0.
\tag{25}
\]
The unique physical circle corner of `C`, forced by its positive force
components, is
\[
 z_C=(A_0-b)m-(B_0+1)v,
 \qquad R^2=(A_0-b)^2+(B_0+1)^2.
\tag{26}
\]
The true shared application is
\[
 T=O+\xi m,\qquad 0\le\xi\le1-b.
\tag{27}
\]
In particular its entire mean interval, including both endpoints, is
still present.

### 3.3 Lower-tip force and torque force a tilt below 45 degrees

Write the actual balance as
\[
 \kappa z_C=\mu n+\gamma w,
 \qquad \kappa,\mu,\gamma>0.
\]
Torque about `P` gives the exact identity
\[
 \frac\gamma\kappa
 =\frac{B_0+1-(A_0-b)}{\xi+b}.
\tag{28}
\]
The numerator is positive. Since `xi+b<=1`,
\[
 \frac\gamma\kappa\ge B_0+1-(A_0-b).
\]
The strict southwest sign `n_y<0` in the vertical force equation gives
\[
 \frac\gamma\kappa
 <-\frac{(z_C)_y}{a}
 =B_0+1-(A_0-b)\frac ba.
\tag{29}
\]
As `A_0-b>0`, (28)--(29) imply
\[
 b<a,\qquad 0<b<\frac1{\sqrt2}.
\tag{30}
\]
This is a consequence of the actual force and the full shared mean,
not an imposed reflection or angle normalization.

### 3.4 Both possible far corners of U are too short

The `m` coordinates of the two `U` sides are `A_0-1` and `A_0`, both
positive. Consequently it suffices to compare the two vertices whose
`m` coordinate is `A_0`. Their squared norms are
\[
 A_0^2+B_0^2,\qquad A_0^2+(1-B_0)^2.
\tag{31}
\]
Subtracting the first from (26) gives
\[
 \Delta_-=1-2b-b^2+2h_0(a+b^2)+2s b(1-a).
\]
Using `h_0>1/3` and `s>=3/8` from (2),
\[
 \Delta_->
 f(b):=1-\frac54b-\frac13b^2
           +\sqrt{1-b^2}\left(\frac23-\frac34b\right).
\]
For `0<=b<=1/sqrt(2)`, every term in the derivative of `f` is
nonpositive and its constant term is strictly negative: the factor
`2/3-3b/4` is positive. Thus `f` is strictly decreasing, and
\[
 \Delta_-> f(1/\sqrt2)
 =\frac{11-7\sqrt2}{24}>0.
\tag{32}
\]
Subtracting the second expression in (31) from (26) gives
\[
 \Delta_+=-2b-b^2+2h_0b^2+2s b(2-a)+4h_0a
\]
\[
 >g(b):=-\frac12b-\frac13b^2
       +\sqrt{1-b^2}\left(\frac43-\frac34b\right).
\]
The same derivative argument shows `g` decreasing on this interval,
so
\[
 \Delta_+>g(1/\sqrt2)
 =\frac{10\sqrt2-13}{24}>0.
\tag{33}
\]
The final signs follow from `121>98` and `200>169`. Every vertex of
`U` therefore has norm strictly below the norm `R` of the actual `C`
circle corner. This contradicts the physical boundary contact of `U`.

## 4. Whole-chart conclusion and compatibility

The actual `UC` contact is either a singleton or a positive-length
segment. A singleton has exactly the two side-owner alternatives after
the already compatible fixed-tip selection. Section 2 excludes both,
including all parallel/perpendicular normal transitions. Section 3
handles every shared segment and every actual mean without that selection
hypothesis. These cases cover the entire declared oblique central chart.

No force at `U` was discarded, split, or assumed radial beyond its
physical circle contact. No application was frozen. No normal was changed
after certificate extraction. The theorem retains every other square in
the original packing, since it contradicts this physical three-square
subconfiguration with its actual selected lower-tip stress.

The parent D-diamond conclusion must still assemble this theorem with the
central-horizontal and A/U-parallel alternatives and their complete
contact-localization input. This source alone makes no claim about those
separate alternatives or the remaining global nine-square proof.
