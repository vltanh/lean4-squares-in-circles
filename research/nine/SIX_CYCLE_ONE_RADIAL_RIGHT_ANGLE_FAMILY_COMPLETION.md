# The whole three-slider one-radial right-angle C6 family has completion capacity at most two

**Status: complete hand completion argument for the explicitly stated entire geometric family. Root and separate independent full saved-source and direct-prerequisite audits passed. The unrestricted one-radial C6 gate is still OPEN.**

This theorem extends the exact positive-core control in
SIX_CYCLE_ONE_RADIAL_POSITIVE_SATURATED_CONTROL.md to every actual
transverse position of all three side transmitters. It allows all
extra-square centers and orientations, genuine shared interfaces,
their endpoint means, physical zero-load circle contacts and every
additional physical contact.

## 1. Complete family and unchanged positive certificate

Retain

\[
r=\sqrt2,\quad s=1/\sqrt2,\quad d=r-1/2,\quad
R_0^2=5/2+r,
\]

and the three fixed physical loaded units \(S,B,C\), points
\(P,Q,T\), and unit vectors \(g,u\) of the control source:

\[
\begin{gathered}
S=[d,d+1]\times[-1/2,1/2],\qquad
P=(d,1/2),\quad Q=(s-1/2,s+1/2),\quad T=(-1/2,1/2),\\
g=(-s,s),\quad u=(-s,-s),\qquad
B=Q+[0,1]g+[0,1]u,
\end{gathered}
\]

with \(C\) the horizontal reflection of \(B\).

The actual three transmitters now have **arbitrary independent
transverse parameters**:

\[
\begin{split}
U_+(t_+)&=P+[0,1]g+[t_+-1/2,t_++1/2]u,\\
U_-(t_-)&=\text{the horizontal reflection of }U_+(t_-),\\
W(v)&=[v-1,v]\times[-1/2,1/2],
\end{split}
\]

where \(-1/2\le t_+,t_-,v\le1/2\). Require that all six actual
units are contained in \(D_{R_0}\) and have pairwise disjoint open
interiors. No independent product box is substituted for these
physical constraints.

**Theorem.** Every such six-body core admits at most **two** additional
interior-disjoint contained unit squares. In particular no original
nine-square packing can contain any member of this entire family.

For strict parameter interiors the same six-cycle, original contact
applications and positive force magnitudes in the control source
remain unchanged. The original mean on \(U_+-B\) is \(Q\), and on
\(B-W\) it is \(T\); reflect below. Moving a transmitter transversely
does not move either application or change their common force line.
Every force and torque equation therefore remains valid. The capacity
proof includes the closed parameter endpoints geometrically, by the
same occupied-path and compact-interior limit used in the ring and cap
sources. No selected normal is reset in applying the result to an
actual member of the family.

## 2. All extra squares are central or in the actual left pocket

Every contained-unit center has norm at most \(r\), by the exact
center bound in Section 3 of the control source. Distinct centers
have distance at least one.

The two radial-incident force channels have actual outward height

\[
(-u)\cdot P=1.
\]

The complete actual channel-cap theorem in
SIMPLE_CYCLE_CHANNEL_POCKET_CAPS.md puts every whole unit in either
of these exterior pockets beyond a support line of height one.
Its center would then have norm at least \(3/2>r\), a contradiction.
Thus both entire radial-incident exterior pockets are empty,
independently of both actual transmitter sliders.

The remaining channel, from \(T=(-1/2,1/2)\) to its reflection,
has outward normal \((-1,0)\) and height \(1/2\). Every whole extra
in its actual left exterior pocket satisfies \(x\le-1/2\), hence
its center satisfies \(c_x\le-1\).

The full physical region cover in the cited source now routes every
extra into the bounded central region or this left pocket. Additional
zero-weight contacts and additional physical boundary contacts only
subdivide these regions. They do not introduce a new place for an
extra square or invalidate the stated cap heights.

## 3. A uniform center box for every possible central extra

The six original applications, in ring order, are

\[
P,\ Q,\ T,\ \overline T,\ \overline Q,\ \overline P,
\]

where the bar is reflection in the horizontal axis. Their polygon is
the fixed convex hexagon

\[
\mathcal P=\{(x,y):-1/2\le x\le d,\quad
-1\le x+y\le r,\quad -1\le x-y\le r\}.
\]

The actual contact-polygon winding homotopy of
CONTACT_RING_HOLE_AREA.md, Section 1, puts every whole central
completion square inside \(\mathcal P\). This uses the six unchanged
applications, not a new choice of means or a claim that the entire
free region is convex.

Consequently a central extra center \((x,y)\), using the universal
projection halfwidth at least \(1/2\) in every unit direction,
satisfies

\[
0\le x\le r-1,\qquad -1+s\le x+y,x-y\le s.
\tag{1}
\]

In particular \(|y|\le1/2\). Suppose first \(y\ge0\), and use
the actual \(U_+(t_+)\). In its orthonormal coordinates \((g,u)\),
that transmitter is the rectangle

\[
g\cdot X\in[s-1,s],\qquad
u\cdot X\in[t_+-3/2,t_+-1/2].
\tag{2}
\]

The center's g-coordinate is in the **entire** first interval:

\[
g\cdot(x,y)=s(y-x)\ge-s(r-1)=s-1,
\qquad g\cdot(x,y)\le s/2<s.
\]

Also \(u\cdot(x,y)=-s(x+y)\ge-1/2\) by (1), whereas
\(t_+-3/2\le-1\). Thus the distance from this center to the
closed actual transmitter is exactly

\[
\max\{u\cdot(x,y)-(t_+-1/2),0\}.
\]

Its open inscribed radius-1/2 disk must avoid the transmitter's
interior. The distance is therefore at least \(1/2\), giving

\[
x+y\le-r t_+.
\tag{3}
\]

No separating axis between the two full units was presumed; this is
the actual point-to-rectangle distance in (2).

The physical transmitter corner \(Q+(t_+-1/2)u\) has squared
norm \((3/2-t_+)^2+1/2\). Its original circle containment forces

\[
t_+\ge3/2-\sqrt{2+r},\qquad
-r t_+\le M:=r\sqrt{2+r}-3r/2<1/2.
\tag{4}
\]

For the last exact comparison, square the positive sides of
\(r\sqrt{2+r}<(3r+1)/2\). It reduces to \(r<3/2\).

Combining (3) with \(x-y\ge-1+s\) from (1),

\[
2y\le M+1-s<1/2+3/10=4/5,
\]

where \(s>7/10\). Reflection, using the original independent
\(t_-\), proves the negative-y bound. Every central extra center
therefore lies in the single box

\[
\boxed{\ 0\le x\le r-1,\qquad |y|<2/5.\ }
\tag{5}
\]

This box has squared diameter less than
\(1/4+16/25=89/100<1\), since \(r-1<1/2\). Hence the whole
central region has capacity at most one.

## 4. Nonnegative v excludes every central extra

If \(v\ge0\), the center of the actual W is \((v-1/2,0)\), with
\(-1/2\le v-1/2\le0\). For every point in (5),

\[
|x-(v-1/2)|\le r-1/2=d.
\]

Its squared distance from the W center is consequently less than

\[
d^2+4/25=241/100-r<1.
\tag{6}
\]

The final strict comparison is \(r>141/100\), whose squared reserve
is \(119/10000>0\). This contradicts the necessary distance at
least one between centers of disjoint units. Thus for every
\(v\ge0\), the entire central region contains no additional unit.

## 5. Nonpositive v excludes every left-pocket extra

Section 4 of SIX_CYCLE_ONE_RADIAL_POSITIVE_SATURATED_CONTROL.md
proves that the entire left half of the radius-r center disk is
covered by the open unit disks centered at

\[
(-1/2,0),\qquad (-1/2,1/2+s),\qquad (-1/2,-1/2-s).
\]

The latter two are the unchanged physical centers of \(B,C\).
A left-pocket extra center satisfies \(x\le-1\). If \(v\le0\),
then \(-1\le v-1/2\le-1/2\), so moving the first displayed center
to the actual W center \((v-1/2,0)\) cannot increase its distance
to any such point. Thus the same complete cover remains valid on
the whole left-pocket center domain.

An extra center would be strictly less than one from at least one
of these three original physical centers, a contradiction. The
entire left pocket is empty for every \(v\le0\).

## 6. The left pocket always has capacity at most two

Let \((x,y)\) be any left-pocket extra center; then
\(x\le-1\), \(x^2+y^2\le2\). Assume \(y\ge0\). In the actual
orthonormal frame of B, use coordinates

\[
\xi=s(x+y),\qquad \eta=s(y-x).
\]

B is the rectangle \([0,1]\times[s,s+1]\) in these coordinates.
Here \(\xi\le0\), because \(y\le1\le-x\), and

\[
s\le\eta\le|(x,y)|\le r<s+1.
\]

The center's exact distance to B is therefore \(-\xi\).
Avoidance by its open inscribed half-radius disk gives

\[
x+y\le-s.
\]

If \(y\ge3/5\), this implies

\[
x^2+y^2\ge(s+y)^2+y^2\ge61/50+6s/5>2,
\]

since \(s>13/20\). This contradicts the center-radius bound.
Reflect for \(y\le0\). All left-pocket extra centers lie in

\[
[-r,-1]\times(-3/5,3/5).
\]

Split this rectangle at \(y=0\), assigning that line to just one
half. Each half has squared diameter less than
\(1/4+9/25=61/100<1\). Distinct extra centers have distance at
least one, so each half contains at most one. The left pocket has
capacity at most two, throughout every original slider domain.

## 7. Whole-family assembly and remaining scope

If \(v\le0\), the left pocket is empty and the central region has
capacity at most one. If \(v\ge0\), the central region is empty
and the left pocket has capacity at most two. Both radial-incident
exterior pockets are always empty. Thus the total extra capacity is
at most two for every original physical triple \((t_+,t_-,v)\),
including the join \(v=0\) and every circle-containment endpoint.

This excludes a nine-square completion of the whole displayed
right-angle core family. It is stronger than saturation of one
chosen member and does not require the three transmitters to be
physically circle-clear. Every extra square may rotate independently.

The orientations and positions of the three loaded bodies are explicit
hypotheses of this geometric theorem. The separate complete classification
in SIX_CYCLE_ONE_RADIAL_RIGHT_TURN_CLASSIFICATION.md proves that every
one-radial C6 with radial turn exactly pi/2 has precisely this geometry.
The strict obtuse radial-turn family remains in the existing unrestricted
one-radial gate, with its arbitrary loaded frames, force triangle and
original shared-interface features.
No new whole coarse-cell closure is claimed.

The proof is analytic and uses only the displayed elementary
radical comparisons and the actual physical cap/winding theorems.
No numerical search or finite certificate is a premise, and no Lean
compilation or CI was run.
