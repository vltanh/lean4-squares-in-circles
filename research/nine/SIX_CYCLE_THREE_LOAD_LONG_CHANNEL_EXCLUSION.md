# A three-loaded six-cycle cannot have a two-body transmitter channel

**Status: complete hand whole-load-orbit exclusion; root and separate
independent full hand audits passed.** Work in
\[
                         79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Suppose the entire selected positive component is the six-cycle
\[
                         X-U-V-Y-W-Z-X,
\tag{2}
\]
with exactly X,Y,Z carrying positive total circle load. The three
other original packing squares remain arbitrary and in place.

**Theorem.** The component (2) is impossible. This excludes the
entire three-load orbit with cyclic gaps \(1,2,3\), including all
physical circle masks, every actual side mean and both possible
widths of W. No completion capacity or secondary minimizer is used.
The alternating three-load orbit and the four-/five-load six-cycle
families are not asserted closed here.

Use the existing strict point-normal convention and compatible
diagonal-transmitter avoidance, chosen before extraction. Every
statement below concerns the final full degree-two cycle, not a
cycle subgraph with further positive edges.

## 1. Exact reserves and the stronger radius floor

The normal-channel theorem
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md, Sections1--2, makes U,V
side-normal transmitters on one common line, with total reserve2.
The remaining transmitter W has reserve
\[
                              w\in\{1,\sqrt2\}.
\tag{3}
\]
Indeed the two-body channel cannot contain a diagonal transmitter:
its endpoint-center projection would be at least \(2+\sqrt2\),
exceeding the diameter bound for centers.

For every unit contained in the disk, its center c satisfies
\[
                R^2\ge |c|^2+|c|+\tfrac12.
\tag{4}
\]
This follows from the exact farthest-corner formula and
\(|c_1|+|c_2|\ge|c|\) in its own orthonormal frame. In particular
\[
                     |c|<M:=91/60,
\tag{5}
\]
because \(M^2+M+1/2=15541/3600>1105/256\).

Let n point along the long channel from X to Y. Its actual support
equations, including arbitrary transverse means, give
\[
                n\cdot(c_Y-c_X)=2+H_X(n)+H_Y(n)\ge3.
\tag{6}
\]
At least one endpoint center therefore has norm at least3/2.
Equation(4) proves the stronger floor
\[
                          R^2\ge17/4.
\tag{7}
\]
Consequently every boundary-square center has norm
\[
                         |c|>27/20.
\tag{8}
\]
For an exact comparison, \(R\ge\sqrt{17}/2>103/50\) and
\(1/\sqrt2<71/100\); then
\(|c|\ge R-1/\sqrt2>27/20\).

At a diagonal transmitter, the retained compatible convention
makes both actual endpoint contacts strict side-interior points
of the neighboring units. Those endpoint frames have the channel
direction as a side axis. Their center displacement is therefore
\[
                      (1+\sqrt2)n+\eta t,\qquad |\eta|<1,
\tag{9}
\]
where t is a unit vector perpendicular to n. No actual transverse
mean is prescribed.

## 2. The isolated load Y cannot have parallel pair forces

The direct physical boundary contact XZ gives a nonzero common
origin moment on the cycle, exactly as in
FIVE_CYCLE_THREE_LOAD_PARALLEL_EXCLUSION.md, Section1. That source's
Section2 applies to any loaded degree-two body whose pair forces
are parallel: its outward circle-resultant direction cannot support
a neighboring contained unit, so both pair forces point inward
on the same support face. Their true weighted application then
makes the body radial S or radial D.

The radial-D alternative has its two actual applications at the
one radial inner vertex and hence zero origin moment. It is
incompatible with the nonzero moment on XZ.

Suppose Y is radial S. Put
\[
 K=\sqrt{R^2-\tfrac14},\quad h=K-1,\qquad
 Y=[h,h+1]e+[-\tfrac12,\tfrac12]t.
\tag{10}
\]
Its two positive circle weights agree, but neither actual contact
on its inner side is required to be the midpoint. Equation(7)
gives \(K\ge2\), and (5) gives \(h<61/60\).

If W is side-normal, the actual point belonging to Z at its far
end is
\[
                         (h-1)e+y t,\qquad |y|\le1/2.
\]
Its squared norm is less than \(1/3600+1/4\). Every point of a
boundary unit has norm at least \(R-\sqrt2>14/25\), so this is
impossible.

If W is diagonal, Z has the same side axes e,t and (9) gives
\[
                  c_Z=(K-\tfrac32-\sqrt2)e+\eta t,
                         \qquad |\eta|<1.
\tag{11}
\]
The first displayed coordinate is negative throughout (1).
Its farthest corner therefore satisfies
\[
\begin{aligned}
 \max_{z\in Z}|z|^2
 &<(2+\sqrt2-K)^2+\tfrac94\\
 &\le K^2+\tfrac14=R^2.
\end{aligned}
\tag{12}
\]
The second difference, before applying \(K\ge2\), is exactly
\[
 (2+\sqrt2-K)^2+\tfrac94-(K^2+\tfrac14)
                  =(4+2\sqrt2)(2-K)\le0.
\]
Thus Z would be physically circle-clear. This excludes the
diagonal alternative as well.

Y has nonparallel forces. X and Z each have a boundary neighbor
and likewise have nonparallel forces. This complete argument
retains all physical two-corner weight limits at Y.

## 3. The proper concurrence triangle and its center half-planes

The nonparallel concurrence lemma
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Lemma1.1, now applies to all
three loads, including Y with two unloaded neighbors. At each
loaded body its concurrence q is a positive multiple of its circle
resultant and
\[
                       p-q=\alpha n,\qquad\alpha\ge0
\tag{13}
\]
for every actual outward pair normal n and application p.
For a physical one-corner body q lies inside its square. A
physical two-corner q is not assumed bounded.

Contracting U,V,W in the exact force equations gives the triangle
of loaded concurrences, with reserves \(2,w,0\). The proof of
FIVE_CYCLE_FORCE_POLYGON_DOMAIN.md, Sections2--3, applies unchanged:
reserve positivity gives strictly positive edge lengths; the direct
XZ moment fixes a nonzero common sign; all three positive angular
increments are less than pi and sum to2pi; force balance gives
positive turns. The triangle is strictly convex and contains the
origin strictly. Its vertices are distinct because the physical
circle-corner intervals, and hence their positive resultant rays,
are disjoint. No physical transmitter is removed from the packing.

Normalize the long channel horizontally, with X on the left, and
choose the vertical direction away from the origin across that
triangle edge. Its actual applications and concurrences lie on
one line of height \(h_0>0\). Write
\[
             c_X=(-x,y_X),\quad c_Y=(y,y_Y).
\tag{14}
\]
By (5)--(6),
\[
                       89/60<x,y<91/60.
\tag{15}
\]
Both endpoint centers satisfy
\[
                           y_X,y_Y\ge0.
\tag{16}
\]
Here the all-mask channel endpoint argument from
FIVE_CYCLE_FOUR_LOAD_EXCLUSION.md, Section2, uses only the proper
concurrences and the horizontal signs in (15), not reserve1.
For completeness, at an oblique left endpoint its rightmost
vertex is \(p=(l,h_0)\), with inward axes \((-a,b),(-b,-a)\).
If its center had nonpositive height, then a>b and
\(h_0\le(a-b)/2\). Its negative horizontal center coordinate makes
its projection onto \((-b,-a)\) strictly positive. Every farthest
corner therefore includes this step, and has negative height.
That contradicts its strictly positive vertical circle resultant
from \(q_y=h_0\). An aligned endpoint of negative center height
has the same contradiction; height zero is retained. Reflection
gives the right endpoint. Every radial weighted-corner limit and
every actual side mean is included.

Equations(5),(15)--(16) also give
\[
                       0\le y_X,y_Y<1/3,
\tag{17}
\]
since \(M^2-(89/60)^2=1/10<1/9\). Their center directions lie
within15 degrees of the west and east axes respectively: their
tangent deviations are less than \(20/89<1/4<\tan(\pi/12)\).

The third concurrence q_Z has negative height, because the origin
lies inside the triangle and both other concurrences have height
\(h_0>0\). Each positive circle-resultant direction lies within
20 degrees of its physical center direction, and distinct boundary
centers are separated by more than40 degrees. These are the actual
circle-center interval and centered-inner-arc theorems, with all
physical zero-weight corners retained.

If \(c_Z\) had nonnegative height, its direction would consequently
lie in the upper20-degree neighborhood of either the east or west
axis. It would be within35 degrees of \(c_Y\) or \(c_X\), contrary
to that strict boundary-center separation. Therefore
\[
                              (c_Z)_y<0.
\tag{18}
\]

## 4. The whole short side-normal alternative is impossible

If \(w=1\), the actual endpoint applications are one unit apart.
Each lies within \(1/\sqrt2\) of its body's center, so
\[
                 |c_Z-c_Y|\le1+\sqrt2,\qquad
                 |c_Z-c_X|\le\sqrt2.
\tag{19}
\]
The second inequality is the actual direct XZ contact.

Put \(c_Z=(z_x,z_y)\). Equations(15)--(18) imply
\[
 |(c_X+c_Y)_x|<1/30,\qquad
 (c_X+c_Y)_y\ge0,\qquad z_y<0.
\]
Thus
\[
\begin{aligned}
 |c_Z-c_X|^2+|c_Z-c_Y|^2
 &=2|c_Z|^2+|c_X|^2+|c_Y|^2
                       -2c_Z\cdot(c_X+c_Y)\\
 &>2(27/20)^2+\tfrac92-\frac{M}{15}\\
 &=\frac{14479}{1800}.
\end{aligned}
\tag{20}
\]
We used \(x^2+y^2\ge(x+y)^2/2\ge9/2\) from (6), with the
endpoint heights only increasing that sum. On the other hand
(19) gives at most \(5+2\sqrt2<47/6=14100/1800\).
This contradicts (20). No frame or transverse-mean choice was
made in this alternative.

## 5. The whole short diagonal alternative is impossible

Suppose \(w=\sqrt2\). The diagonal convention gives (9), with Y,Z
sharing side axes. The direct XZ contact and (15) imply
\[
 (c_Z)_x<(c_X)_x+\sqrt2
       <-89/60+17/12=-1/15.
\tag{21}
\]
In particular
\[
                    (c_Z-c_Y)_x<-31/20.
\tag{22}
\]

### 5.1. Complete frame and short-normal routing

The horizontal halfwidth of Y satisfies
\[
 H_Y(e_x)<2M-2-\tfrac12=8/15.
\tag{23}
\]
Choose its almost-horizontal and almost-vertical side axes with
absolute components \(a\ge b\ge0\). Equation(23) gives
\[
                  a+b<16/15,\qquad b<1/10,\quad a>99/100.
\tag{24}
\]
For the bound on b, the function
\(\sqrt{1-b^2}+b\) is increasing on \([0,1/\sqrt2]\), and at
b=1/10 its value is greater than109/100>16/15.

Every short-channel normal is an axis of Y. The center displacement
has longitudinal magnitude \(D:=1+\sqrt2<5/2\) and transverse
magnitude less than1. Normals along either near-vertical axis
would give horizontal displacement greater than \(-Db-a>-5/4\),
contrary to (22). The rightward near-horizontal axis also cannot
give (22). Thus its direction is the leftward near-horizontal axis.

If Y were aligned, that direction would be parallel to its
long-channel normal, contrary to Section2. Hence b>0. If its
leftmost vertex were the lower left support vertex, its height
would be
\[
              y_Y-\frac{a-b}{2}
                  <\frac13-\frac{89}{200}<0,
\]
contrary to its actual long application at height \(h_0>0\).
The only remaining frame and normal are therefore
\[
             u=(a,b),\quad v=(-b,a),\qquad n_{Y\to Z}=-u,
\tag{25}
\]
with long application
\[
                        p_Y=c_Y-\tfrac12u+\tfrac12v.
\tag{26}
\]
This covers both original tilt signs and every owner at the long
channel endpoint.

### 5.2. The physical radial Y mask

If Y has two physical circle corners, its center lies along one
of its own axes. Its large positive horizontal coordinate in (15)
and b<1/10 exclude both near-vertical radial axes and the negative
u axis. Thus Y is radial in direction +u:
\[
                       c_Y=(K-\tfrac12)u,
                       \qquad K=\sqrt{R^2-\tfrac14}\ge2.
\]
Equation(9) puts
\[
                      c_Z=(K-\tfrac32-\sqrt2)u+\eta v,
                                 \qquad|\eta|<1.
\]
Exactly (12) makes every Z corner strictly inside the circle.
This excludes the entire radial Y mask, irrespective of its
positive-corner weight split.

### 5.3. The physical unique Y mask

Now Y has one physical circle corner, so its proper concurrence
q_Y lies inside Y. From its long normal \(-e_x\) and (26), write
\[
                            q_Y=p_Y+\lambda e_x,\quad\lambda\ge0.
\]
The short contact belongs to the relative interior of Y's
minimum-u side. Its actual application is
\[
                       p'_Y=c_Y-\tfrac12u+\tau v,
                                      -1/2<\tau<1/2.
\]
Proper concurrence at this contact makes the v coordinates of
q_Y and \(p'_Y\) equal. Since \(e_x=au-bv\),
\[
                   \tau=\tfrac12-\lambda b.
\tag{27}
\]
The u coordinate of q_Y lies inside Y, so \(\lambda a\le1\).
Consequently \(\tau\ge1/2-b/a\).

The actual Z application has its own side parameter
\(-1/2<\tau_Z<1/2\). The exact diagonal reserve yields
\[
                c_Z-c_Y=-D u+(\tau-\tau_Z)v,
\]
so
\[
                         (c_Z)_y
                 \ge y_Y-Db-b>-\frac7{20},
\tag{28}
\]
using \(D+1=2+\sqrt2<7/2\), \(b<1/10\) and \(y_Y\ge0\).
This retains both actual strict side parameters; neither is
replaced by a midpoint.

Together with (8),(18),(21), equation(28) forces
\[
                 -7/20<(c_Z)_y<0,\qquad (c_Z)_x<-13/10.
\tag{29}
\]
Indeed its squared horizontal magnitude exceeds
\((27/20)^2-(7/20)^2=17/10>(13/10)^2\).
The negative sign is supplied by (21).

Using (5),(15),(17),(29), the two center differences satisfy
\[
 |(c_Z-c_X)_x|<13/60,\qquad
 |(c_Z-c_X)_y|<41/60.
\]
It follows that
\[
                        |c_Z-c_X|^2<37/72<1.
\tag{30}
\]
Every unit square contains the open disk of radius1/2 about its
center. Two interior-disjoint units have center distance at least1,
so (30) is impossible. This finishes the unique Y mask and the
complete short diagonal alternative.

## 6. Whole-orbit and certificate scope

The reserves \(2,w,0\), the full parallel/nonparallel alternative
at the isolated load Y, both values of w, both physical Y masks
and all long/short contact means have been exhausted. All three
extra squares remain untouched. No bound on an exterior region,
no movement of a square, and no secondary selection is needed.

Only existing compatible normal choices are used: strict point
normals and the diagonal-transmitter endpoint convention. The
proof never changes a selected normal or replaces an actual mean.
Physical circle contacts at unloaded bodies remain allowed.
Every force and torque equation belongs to the full exact
degree-two component (2).

The other simple-six-cycle load orbits and every positive chord
remain separate obligations. No argument here may be applied to
a six-cycle subgraph after deleting an additional positive force.
No numerical search, Lean compilation or CI is a premise.

