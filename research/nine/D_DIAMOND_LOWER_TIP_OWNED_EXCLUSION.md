# The oblique D-diamond lower triangle: lower-tip-owned contact is impossible

**Status.** Complete hand proof of the entire lower-tip-owned `UC` contact
alternative in the oblique central-contact chart. Root and separate independent full hand audits passed. This source uses force and torque only at the
positive degree-two lower tip `C`; the central square `U` may have arbitrary
additional forces and contacts. It does **not** close the still separate
`U`-owned or shared `UC` alternatives, or the parent D-diamond cell.

## 1. Domain and conclusion

Write
\[
 R_0=\frac{79}{40},\qquad Q_0=\frac{1105}{256},\qquad
 R_0\le R\le\sqrt{Q_0},\qquad s=1+\sqrt2-R.
\tag{1}
\]
The circle is centered at the true origin. Consider the oblique central
D-diamond chart
\[
 A=[-s,1-s]\times[H-1,H],\qquad
 P=(-s,H-1),\qquad Q=(-s,H),\qquad 0<H<1.
\tag{2}
\]
The physical boundary squares `C` and `U` contain `P` and `Q`, respectively.
The `A`-to-`U` normal at `Q` is strictly northwest. The lower tip `C` has
exact positive degree two, and its actual positive contacts are `AC` at
`P` and `CU` at `T`. Its physical circle corner is unique.

In the lower-tip-owned alternative the side axes and placement of `C` are
\[
 n=(-d,-c),\qquad k=(c,-d),\qquad
 c,d>0,\quad c^2+d^2=1,
\]
\[
 C=P+[0,1]n+[-\rho,1-\rho]k,
 \qquad 0<\rho<1,
\tag{3}
\]
with `AC` owned by `C` at the relative interior point `P`, and `CU` owned
by `C` at the relative interior point
\[
 T=P+\eta n-\rho k,\qquad 0<\eta<1.
\tag{4}
\]
The sign and side in (4) exhaust the `C`-owned alternative. An incoming
`UC` force parallel to `n` would make the unique circle force parallel to
a side axis of `C`; a circle vertex on that axis has an adjacent vertex
strictly farther from the origin, contrary to containment. An incoming
`-k` force would put `U` beyond the maximum `k` face of `C`, at
`k` projection at least `k dot P+1-rho`, whereas its point
`Q=P+e_y` has projection `k dot P-d`. This is impossible. Thus the two
forces into `C` are positive multiples of `n` and `k`.
The selected circle corner is
\[
 z_C=P+n+(1-\rho)k.
\tag{5}
\]
The `UC` application is a vertex of `U`. The `AU` application `Q` lies
on an incident side of `U`, possibly at its other endpoint. Equivalently,
for some orthonormal axes `u,v`,
\[
 U=T+[0,1]u+[0,1]v,\qquad Q=T+\ell v,
 \qquad 0<\ell\le1,
\tag{6}
\]
where `u` points northwest and `v` northeast.

These are the actual contact features in the C-owned lower chart. For
completeness, the common-side assertion in (6) also follows directly from
the normals. The outward `U` normals toward `A` and `C` are both strictly
southeast: they are the negative of the strictly northwest `AU` normal,
and `k`, respectively. If `Q` is in a side interior, the positive
coefficient along that side's outward axis makes the maximizing `k`
vertex an endpoint of that same side. If `Q` is a vertex, the two
southeast normals cannot support opposite vertices; the vertices are
adjacent. Coincidence is excluded by (3)--(4), since the `n` coordinate of
`Q-T` is `-(eta+c)<0`. This proves (6) both when `AU` is `U`-owned and when
it is a free vertex contact.

**Theorem.** There is no such configuration in the disk `D_R`. In fact,
every vertex of `U` has norm strictly less than `79/40`.

No equation at `U`, and no assumption on its third neighbor, is used.

## 2. Uniform bounds at the two articulation vertices

Every point of a boundary unit square has distance at least
`R-sqrt(2)` from the origin: compare it with any physical circle corner
of that square. Since `P` and `Q` lie in physical boundary squares,
\[
 |P|,|Q|\ge R-\sqrt2=1-s.
\]
Also `0<s<9/20`; the upper bound follows already from `R>=79/40`.
Consequently
\[
 H^2\ge1-2s>\frac1{10},\qquad
 (1-H)^2\ge1-2s>\frac1{10}.
\]
Because `0<H<1`, this gives
\[
 \frac3{10}<H<\frac7{10},\qquad
 |P|^2,|Q|^2<\frac{81+196}{400}
 =\frac{277}{400}<\frac{25}{36}.
\tag{7}
\]
In particular `|P|,|Q|<5/6`.

Put `V=1-rho`. From (5),
\[
 \sqrt{1+V^2}=|z_C-P|
 \ge R-|P|>\frac{79}{40}-\frac56=\frac{137}{120}.
\]
It follows that
\[
 V^2>\frac{4369}{14400}>\frac{121}{400},
 \qquad V>\frac{11}{20},\qquad 0<\rho<\frac9{20}.
\tag{8}
\]

## 3. The exact lower-tip torque identity

In the orthonormal `(n,k)` coordinates write
\[
 X=n\cdot P=sd+(1-H)c>0,\qquad
 Y=k\cdot P=(1-H)d-sc.
\]
The unique physical circle corner has coordinates
\[
 z_C=(X+1,Y+V),\qquad (X+1)^2+(Y+V)^2=R^2.
\tag{9}
\]
The positive forces at `P,T` and the radial circle force give, by force
balance and torque about `P`,
\[
 \eta(Y+V)=Y-VX,
 \qquad
 \eta=\frac{Y-VX}{Y+V}.
\tag{10}
\]
Here no separate force or torque equation has been applied to `U`.
The positive `k` force gives `Y+V>0`; since `eta>0`, (10) and `X,V>0`
give `Y>0`. Moreover
\[
 0<Y=(1-H)d-sc<1-H<\frac7{10}.
\tag{11}
\]
Equation (10) is equivalently
\[
 X+\eta=\frac{Y(X+1)}{Y+V}.
\]
Since `T` has coordinates `(X+eta,Y-rho)`, we obtain the vector identity
\[
 T=\frac{Y}{Y+V}z_C-\rho k.
\tag{12}
\]
Thus
\[
 |T|^2
 =R^2\left(\frac{Y}{Y+1-\rho}\right)^2
   -2\rho Y+\rho^2.
\tag{13}
\]

## 4. An exact scalar estimate

For
\[
 \frac{15}{4}\le q\le\frac{1105}{256},\qquad
 0\le y\le\frac7{10},\qquad 0\le r\le\frac9{20},
\]
we claim
\[
 q\left(\frac{y}{y+1-r}\right)^2-2ry+r^2
 \le\frac{7409}{8000}<\left(\frac{39}{40}\right)^2.
\tag{14}
\]
For fixed `q,y`, the expression is convex in `r`: its second derivative
is
\[
 \frac{6qy^2}{(y+1-r)^4}+2>0.
\]
It suffices to check `r=0` and `r=9/20`.

At `r=0`, it is at most
\[
 \frac{1105}{256}\left(\frac7{17}\right)^2
 =\frac{3185}{4352}<\frac{7409}{8000}.
\tag{15}
\]
At `r=9/20`, write
\[
 f_q(y)=q\frac{y^2}{(y+11/20)^2}-\frac9{10}y+\frac{81}{400}.
\]
Its maximum on `[0,7/10]` is attained at `7/10`. Here is an exact
certificate, avoiding any numerical extremization. Set `a=7/10`,
`b=11/20`. Direct subtraction gives
\[
 f_q(a)-f_q(y)
 =\frac{(a-y)P_q(y)}{(a+b)^2(y+b)^2},
\]
\[
 P_q(y)=qb\bigl((2a+b)y+ab\bigr)
       -\frac9{10}(a+b)^2(y+b)^2.
\tag{16}
\]
The positive coefficient of `q` gives `P_q>=P_(15/4)`. The latter is a
concave quadratic, and its two endpoint values are
\[
 P_{15/4}(0)=\frac{4719}{12800}>0,
 \qquad
 P_{15/4}(7/10)=\frac{723}{512}>0.
\tag{17}
\]
It is therefore positive throughout the interval. Finally,
\[
 f_q(7/10)=\frac{196}{625}q-\frac{171}{400}
 \le\frac{7409}{8000}.
\]
The remaining margin is
\[
 \frac{1521}{1600}-\frac{7409}{8000}=\frac{49}{2000}>0,
\tag{18}
\]
which proves (14).

Apply (14) to (13), using (8), (11), and `R^2>15/4`. We have
\[
 |T|<\frac{39}{40}.
\tag{19}
\]
In particular `T`, `T+u`, and `T+v` all have norm strictly less than
`79/40`.

## 5. The opposite central corner

From (3)--(4),
\[
 Q-T=-(\eta+c)n-(d-\rho)k.
\]
As `Q,T` lie on one side of `U`, its length is
\[
 \ell^2=(\eta+c)^2+(d-\rho)^2
 \ge c^2+(d-\rho)^2
 =1-2d\rho+\rho^2\ge(1-\rho)^2=V^2.
\tag{20}
\]
Together with (6) and (8), this gives `11/20<ell<=1`.
The fourth vertex is
\[
 T+u+v=Q+u+(1-\ell)v.
\]
Because `u,v` are orthonormal,
\[
 |u+(1-\ell)v|
 =\sqrt{1+(1-\ell)^2}
 <\frac{\sqrt{481}}{20}<\frac{11}{10}.
\]
By (7),
\[
 |T+u+v|<\frac56+\frac{11}{10}
 =\frac{29}{15}<\frac{79}{40}.
\tag{21}
\]
Every vertex of `U` is therefore strictly inside `D_(79/40)`, and hence
strictly inside `D_R`. This contradicts the physical circle contact of
`U` and completes the entire stated owner alternative.

## 6. Scope

The proof retains the free `AU` endpoint `ell=1`, every allowed side
fraction and height, the whole radius window, and arbitrary third forces
at `U`. The scalar estimate is an elementary identity and convexity
argument; diagnostic optimization is not part of the proof.

The remaining lower-triangle alternatives are `UC` owned by `U`, and
positive-length shared `UC`. They require their own exact geometric
reduction or exclusion. No parent-cell closure follows from this source
alone.
