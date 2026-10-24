# A three-loaded five-cycle cannot have parallel forces at its isolated load

**Status: complete hand exclusion; root and independent full hand audits passed.**
Work in the declared window

\[
                 79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
Suppose the selected positive component is the simple five-cycle

\[
                         T-U-B-C-V-T,
\tag{2}
\]
where precisely T,B,C have positive circle load. Thus U,V are
unloaded degree-two transmission bodies, and B,C physically touch
each other and the containing circle. Every physical circle contact
with zero multiplier is retained.

**Theorem.** The two actual positive pair-force normals at T are
not parallel. This excludes the whole parallel alternative, including
both radial circle masks, both transmitter widths and every genuine
shared-side application mean, independently of all four extra squares.

The theorem is a complete necessary reduction of the three-load C5
branch. Its remaining nonparallel geometry and completion capacity,
the four-load C5 branch, and the parent C1.5.b0 remain open.

## 1. The cycle has a nonzero common origin moment

Orient the cycle (2) and let f_i be the positive directed pair force
at its actual application p_i. Each body's circle forces are radial,
so its origin torque balance gives

\[
                         \det(p_i,f_i)=H
\tag{3}
\]
with the same H on all five edges. This includes the unloaded bodies
and does not prescribe a shared-side mean.

The edge BC joins two physical boundary squares. By
CIRCLE_CONTACT_ANGULAR_ORDER.md, Section6, an actual common normal
between two such squares is not radial in (1). Its magnitude is
positive, so its origin moment is nonzero. Therefore

\[
                                  H\ne0.
\tag{4}
\]

## 2. Parallel pair forces would make T exactly radial S or D

Assume the two pair forces at T are parallel. Their nonzero sum is
opposite the positive circle resultant. Choose the unit vector e in
the outward circle-resultant direction. Every pair-force normal at T
would then be e or -e.

No pair force can point in direction e. For a unique physical circle
corner, that corner is strictly exposed by its radial direction and
cannot belong to another contained square. For two physical circle
corners write the square in its radial side frame as

\[
             [h,h+1]\times[-1/2,1/2],
             \qquad h=\sqrt{R^2-1/4}-1.
\]
Its normalized circle resultant is (h+1,eta), with |eta|<=1/2,
including a zero individual corner weight. If eta is nonzero, its
positive direction strictly exposes one of the two circle corners.
If eta=0, the positive direction exposes the outer face x=h+1;
a unit neighbor beyond that face has a point with x>=h+2>R,
since every unit square has width at least one. Each possibility is
impossible. Consequently both pair normals at T point in direction
-e and act on its same minimum-e support face.

Aggregate their actual applications with their positive magnitudes.
The weighted mean application p_bar lies on that face. Force and
origin torque make p_bar collinear with e. It is a positive multiple:
the normalized circle-corner average lies at distance at least
sqrt(R^2-1/4)>sqrt(2) in direction e, while both that average and
p_bar belong to the same unit square. A nonpositive multiple would
exceed the unit-square diameter.

For completeness, these facts give the full S/D classification
without a leaf-degree assumption. If just one circle corner has
positive weight, its opposite support is the opposite vertex; the
two vertices are radially collinear and differ by a diagonal of
length sqrt(2). This is radial D, with the sole inner application

\[
                           p_D=(R-\sqrt2)e.
\tag{5}
\]
If both adjacent circle weights are positive, use the displayed
radial side frame. For eta>0 the opposite support is (h,-1/2),
which is not a positive multiple of (h+1,eta); eta<0 is reflected.
Thus eta=0, the weights agree, and the aggregate application is
(h,0). This is radial S. Individual applications need not be the
midpoint: they retain their complete range along the inner face.

In the D alternative, both actual applications equal p_D and both
forces are parallel to e. Their origin moments are zero, contradicting
(3)--(4). Only S could remain.

## 3. A side-normal transmitter ends too close to the origin

Rotate about the containing-circle center so that e=e_x. Then

\[
                   T=[h,h+1]\times[-1/2,1/2].
\tag{6}
\]
Let its actual contacts with U and V be respectively

\[
                   p_U=(h,y_U),\qquad p_V=(h,y_V),
                   \qquad |y_U|,|y_V|\le1/2.
\tag{7}
\]
They remain actual weighted means if the physical intersections
are segments. No centering or opposite-height equality is imposed.

At an unloaded degree-two body, translation balance makes its two
forces opposite with equal magnitudes, and torque makes their
applications collinear along their common normal. If this normal is
a side axis, the application's displacement is exactly one unit. If
it is not a side axis, both supporting faces are opposite vertices,
and their connecting diagonal must be parallel to the normal, giving
width sqrt(2). These are the complete transmission alternatives.

Accordingly the actual contact with the boundary body B or C at
the far end of a transmitter is

\[
                  q_i=(h-w_i,y_i),\qquad w_i\in\{1,\sqrt2\}.
\tag{8}
\]
The window (1) gives the convenient strict bounds

\[
                  \frac9{10}<h<\frac{61}{60},
                  \qquad r:=R-\sqrt2>\frac{14}{25}.
\tag{9}
\]
For the last inequality, use R>=395/200 and sqrt(2)<283/200.
The h bounds follow by squaring their positive defining expressions.
In particular |h-1|<1/10.

If either transmitter is side-normal, its endpoint (8) satisfies

\[
                     |q_i|^2<\frac1{100}+\frac14
                              =\frac{13}{50}
                              <\left(\frac{14}{25}\right)^2<r^2.
\tag{10}
\]
But every point q of any circle-touching unit square has |q|>=r:
choose one of that square's circle corners z and use
|q|>=|z|-|z-q|>=R-sqrt(2). Since q_i belongs to the boundary
body B or C, (10) is impossible. Thus neither U nor V can be a
side-normal transmitter.

## 4. Two diagonal transmitters overlap

Both remaining transmitters have their same diagonal parallel to e_x.
Their rightmost vertices are p_U,p_V from (7). Their centers are
therefore

\[
              c_U=(h-1/\sqrt2,y_U),\qquad
              c_V=(h-1/\sqrt2,y_V).
\tag{11}
\]
Their square frames agree, with side axes at45 degrees to e_x.
On each of these two side axes, the absolute component of their
center difference equals |y_U-y_V|/sqrt(2), which is at most
1/sqrt(2)<1 by (7). Their two open unit projection intervals hence
overlap on both common square axes. Their open interiors overlap,
contrary to the physical packing.

This also covers y_U,y_V at opposite endpoints of the whole inner
face. No stricter application bound is needed.

The D alternative, every side/diagonal mixed alternative and the
last diagonal/diagonal alternative are all impossible. This proves
the theorem. No numerical pose search, Lean compilation, CI or
secondary-minimizer premise is used.
