# A D-leaf diamond cannot have a nonparallel horizontal hub contact

**Status: complete hand proof; root and separate independent full hand audits passed.**
Work in the radius window
\[
                  79/40\le R\le\sqrt{1105}/16.
\tag{1}
\]
The selected positive graph has edges AL,AU,AB,AC,UB,UC: A,U are
its diamond hubs and L is a radial D leaf at A. U has exactly one
physical circle corner, and its frame is not parallel to A. The
physical radial mask of U is already excluded by
D_DIAMOND_RADIAL_HUB_EXCLUSION.md; the parallel-frame mask is excluded
by D_DIAMOND_PARALLEL_HUB_EXCLUSION.md.
Both tips B,C carry positive total circle load: each has exact positive
degree two and its two neighbors A,U physically touch, so the existing
triangle-transmitter obstruction excludes a zero-load tip.

**Theorem.** The actual outward AU normal from A cannot be horizontal.
This retains the entire physical circle mask and all forces of B,
every shared-side mean, and all four arbitrary extra squares. The proof
uses a degree-two force/torque equation only at the lower tip C, never
at the degree-three hub U.

## 1. A radius-free three-neighbor wall obstruction

Let three interior-disjoint unit squares have common right support
x=0. Suppose each contains an actual wall point (0,y_i), and the three
y_i lie in an interval of length at most one. Then all three frames
must be parallel to the wall.

Indeed, take their vertical sections at x=-2/3. For a tilted square,
write its inward axes at its rightmost vertex as (-a,b),(-b,-a),
where a,b>0 and a^2+b^2=1. The vertical section length at horizontal
depth t<=max(a,b) is
\[
 L(t)=
 \begin{cases}
 t/(ab),&t\le\min(a,b),\\
 1/\max(a,b),&\min(a,b)\le t\le\max(a,b).
 \end{cases}
\tag{2}
\]
Since 2/3<1/sqrt(2)<=max(a,b), either expression at t=2/3 is
strictly larger than one: the first is at least 4/3 and the second
is larger than one. An aligned unit has section length exactly one.

For every unit, the vertical distance from its wall point to either
vertical extreme is at most one. For a tilted frame these distances
are b and a; for a vertical wall side the arbitrary chosen wall point
lies on that unit side, with the same upper bound. Therefore all three
sections lie between min_i y_i-1 and max_i y_i+1, an interval of
length at most three. Their relative interiors are disjoint: the
section line is in the interior of each horizontal projection, so
an overlapping open section interval would give overlapping square
interiors. If any frame were tilted, their total length would exceed
three, a contradiction. This proves the claim, including arbitrary
wall application means.

The sampling depth 2/3 is intentional. At depth 1/2, a 45-degree
frame has section length exactly one and does not give this strict
argument.

## 2. A downward tip and the full physical-mask reduction

Use the D articulation coordinates
\[
 s=1+\sqrt2-R,\qquad
 A=[-s,1-s]\times[-v,1-v],\qquad 0<v<1.
\tag{3}
\]
The radial leaf contributes a positive horizontal force with zero
origin moment. Section 1 of D_DIAMOND_PARALLEL_HUB_EXCLUSION.md proves
the complete unique-U central-normal cover. After reflection in the
horizontal axis its circle corner z_U and a horizontal AU application
satisfy
\[
 (z_U)_x<0<(z_U)_y,\qquad n_0=-e_x,
 \qquad Q_0=(-s,y_0),\quad y_0>0.
\tag{4}
\]
Because U is tilted, Q_0 is its unique rightmost vertex. The selected
strict point-normal convention prevents Q_0 from being an A vertex:
the horizontal normal would not strictly expose that A vertex. Hence
\[
                       -v<y_0<1-v.
\tag{5}
\]

The actual A-tip normals n_B,n_C have nonpositive horizontal
components, by UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md applied to
the physical triangles AUB,AUC with the A-owned normal -e_x.
Vertical force balance on A gives either two horizontal leftward
normals, or vertical components of strict opposite sign. In the first
case U,B,C have a common right support and their actual applications
lie on A's left unit side. Section 1 contradicts U being tilted.

Thus label the downward tip C, so (n_C)_y<0. We exclude n_C=-e_y.
The geometric normal-cone argument in
BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md, Section 2, reflected to the
west and south A faces, makes the actual normal f from U to C satisfy
f_x>=0,f_y<=0. The degree-two force equation of C would then be
\[
                         F_C=-\mu e_y+\gamma f,
                         \qquad\mu,\gamma>0.
\]
It has nonnegative horizontal and strictly negative vertical
component. Its scalar product with the northwest vector z_U in (4)
is strictly negative. But U and C touch, so every physical circle
corner of C has strictly positive scalar product with z_U; summing
its positive total circle load gives z_U dot F_C>0. Contradiction.
Only the geometric part of the cited perpendicular-contact source
is used; no degree-two equation for U is imported.

Consequently the C normal is strictly southwest and its A application
is the fixed vertex
\[
                              P=(-s,-v).
\tag{6}
\]
Put
\[
                              \delta=y_0+v.
\tag{7}
\]
Both P and Q_0 belong to physical boundary unit squares. Comparing
each to one of its unit's circle corners yields
\[
 |P|,|Q_0|\ge R-\sqrt2=1-s,
 \qquad v^2,y_0^2\ge1-2s.
\]
Since 0<s<9/20 and 0<delta<1, it follows that
\[
 s>3/8,\qquad 3/10<v,y_0<7/10,
 \qquad 3/5<\delta<1,
\tag{8}
\]
\[
 |P|^2,|Q_0|^2<277/400<25/36,
 \qquad |P|,|Q_0|<5/6.
\tag{9}
\]
A two-physical-circle-corner unit is radial S and every point of it
has norm at least sqrt(R^2-1/4)-1>9/10. Thus C has exactly one
physical circle corner. No restriction on B's physical mask or its
upper A application is needed.

## 3. The complete lower-contact owner cover

The point P is not in U: U's only point on x=-s is Q_0, and
P!=Q_0. Thus the AC and UC applications on C are distinct.

If UC is a singleton, the two C applications are fixed. The
simultaneous selection of GENERAL_FIXED_TIP_NORMAL_SELECTION.md
removes every free vertex normal at either AC or UC. AC cannot be
A-owned, because its normal is strictly southwest; it is C-owned,
with P in the relative interior of a C side. UC must then be owned
by C or by U. A parallel-frame singleton with a vertex on a relative
side interior would actually have a positive-length shared side;
that alternative is treated separately in Section 6.

For the singleton alternatives write
\[
 n=(-d,-c),\quad k=(c,-d),\quad c,d>0,\quad c^2+d^2=1,
\]
\[
 C=P+[0,1]n+[-\rho,1-\rho]k,
 \qquad 0<\rho<1,\qquad V=1-\rho.
\tag{10}
\]
Here n is the incoming AC direction. Put
\[
                  X=sd+vc>0,\qquad Y=vd-sc.
\tag{11}
\]
Whenever the two positive incoming C forces have positive k
component, its unique circle corner is
\[
                z_C=P+n+Vk=(X+1,Y+V)_{(n,k)}.
\tag{12}
\]
The n coordinate is positive for every point of C, and the positive
circle k coordinate selects the endpoint +V. From (9) and (12),
\[
 \sqrt{1+V^2}=|z_C-P|\ge R-|P|>137/120,
 \qquad V>11/20,\quad\rho<9/20.
\tag{13}
\]
All normal choices here are pre-certificate choices; no extracted
force or shared-side mean is changed.

## 4. The C-owned UC singleton is impossible

An incoming UC direction parallel to n would make C's unique circle
force parallel to a side axis, impossible for a unique physical
circle vertex. Incoming -k would put U beyond C's maximum k
support, whereas its point Q_0=P+delta e_y has k projection
k dot P-delta d<k dot P+V. Thus the only C-owned alternative is
incoming +k at
\[
                       T=P+\eta n-\rho k,
                       \qquad0<\eta<1.
\tag{14}
\]
Its circle corner is (12). C force and torque give exactly
\[
 \eta(Y+V)=Y-VX,\qquad
 T=\frac{Y}{Y+V}z_C-\rho k,\qquad 0<Y<v<7/10.
\tag{15}
\]
The scalar estimate in D_DIAMOND_LOWER_TIP_OWNED_EXCLUSION.md,
Section 4, applies directly to
\[
 |T|^2=R^2\left(\frac{Y}{Y+1-\rho}\right)^2
               -2\rho Y+\rho^2
       \le7409/8000<(39/40)^2.
\tag{16}
\]
That estimate only uses the bounds in (13),(15) and the radius
window, not the distance between the two A applications.

The U applications Q_0 and T are vertices. Their outward U normals
are e_x and k, whose product c is positive. They cannot be opposite
vertices. They are distinct because (T-P)_x=-eta d-rho c<0 while
(Q_0-P)_x=0. Hence they are adjacent vertices. Write
U=T+[0,1]u+[0,1]w with Q_0=T+w. Its first three vertices have norm
less than 39/40+1=79/40 by (16); its fourth is Q_0+u and has norm
less than 5/6+1=11/6<79/40. This contradicts U's circle contact.

## 5. The U-owned UC singleton is impossible

Let f be the actual U-to-C normal, now a side axis of U. Because
that side normal is owned by U, the physical triangle UAC gives
f dot e_x>=0. U's tilted frame makes this inequality strict. The
support comparison at P and Q_0 gives
\[
                  f\cdot P\ge\max_{x\in U}f\cdot x
                                \ge f\cdot Q_0,
\]
so f_y<=0, again strict because U is tilted. Thus f is southeast.
The positive coefficient of e_x along f implies that Q_0 is one
endpoint of the U support side carrying T. The contact T is in its
relative interior: a U endpoint against a C vertex would be a
point-only vertex/vertex contact with a non-strict U-axis normal.

The C-owned AC normal also gives n dot f>=0 by the same physical
triangle side-normal theorem. Equality would make f a C side axis,
so U and C would have parallel frames and a positive-length shared
side. In this singleton alternative,
\[
                         n\cdot f>0,\qquad k\cdot f>0.
\tag{17}
\]
The second inequality holds because both k and f are southeast.
Therefore the C minimum of f is the vertex
\[
                              T=P-\rho k.
\tag{18}
\]
Its circle corner is again (12), so (13) holds.

The vector Q_0-T=(rho c,delta-rho d) lies along the actual U side,
with both components positive. If ell=|Q_0-T|, its outward southeast
unit normal is
\[
                    f=(\delta-\rho d,-\rho c)/\ell.
\tag{19}
\]
Consequently (17) gives
\[
                 0<n\cdot f=(\rho-\delta d)/\ell,
 \qquad d<\rho/\delta<3/4,\quad c>1/2.
\tag{20}
\]

Intersect the AC force line P+R n with the UC force line T+R f.
Writing beta=n dot f>0 and K=k dot f>0, their intersection is
P+eta n, where eta=rho beta/K>0. Moment balance of the unique
radial C force about this intersection gives
\[
                         Y-VX=\eta(Y+V)>0.
\tag{21}
\]
Here Y+V>0 follows directly from its positive k force.

This is incompatible with the full parameter bounds. Indeed
\[
                  Y-VX=v(d-Vc)-s(c+Vd).
\tag{22}
\]
If d-Vc<=0, this is negative immediately. Otherwise, (8),(13)
permit v<7/10, s>3/8 and V>11/20 to be substituted in their
respective directions, giving
\[
 \begin{aligned}
 Y-VX
 &<\frac7{10}(d-Vc)-\frac38(c+Vd)\\
 &<\frac{79}{160}d-\frac{19}{25}c\\
 &<\frac{79}{160}\frac34-\frac{19}{25}\frac12
   =-\frac{31}{3200}<0.
 \end{aligned}
\tag{23}
\]
This contradicts (21) and excludes every U-owned singleton.

## 6. The entire shared UC alternative is impossible

Here no fixed-tip selection at a variable mean is assumed. Write U
at its rightmost vertex as
\[
 p=(-a,b),\quad q=(-b,-a),\quad a,b>0,\quad a^2+b^2=1,
 \qquad U=Q_0+[0,1]p+[0,1]q.
\tag{24}
\]
A shared UC normal is an axis of this frame. The comparison at
P,Q_0 used in Section 5 forces its vertical component to be negative.
The only alternatives are q and -p.

If the normal were q, every point of C would have q coordinate at
least q dot Q_0+1. But P-Q_0=-delta e_y has q coordinate delta a<1,
a contradiction. Thus the normal is -p. Positive-length overlap
then writes C as
\[
 C=Q_0+[-1,0]p+[\sigma,\sigma+1]q,\qquad -1<\sigma<1.
\tag{25}
\]
The coordinates of P-Q_0 in this frame are (-delta b,delta a).
Its p coordinate is strictly between -1 and 0. Therefore P is in
the relative interior of one of the q support sides. Its incoming
AC normal is strictly southwest, so that side must be the minimum
q side, and
\[
                       \sigma=\delta a,\qquad n_C=q.
\tag{26}
\]
This proves geometrically that AC is C-owned; no free AC interface
or variable-mean exception has been omitted.

In the C coordinates n=q,k=-p, the parameters in (10)--(12) become
\[
 c=a,\quad d=b,\quad\rho=\delta b,\quad V=1-\rho,
 \qquad X=sb+va,\quad Y=vb-sa.
\tag{27}
\]
The actual shared application has the form
\[
 T=Q_0+\xi q,\qquad\delta a\le\xi\le1.
\tag{28}
\]
Both incoming C forces are positive multiples of n and k. Its unique
circle corner is therefore (12), and (13) applies. Equation (27)
and delta>3/5 give
\[
                     b<3/4,\qquad a>1/2.
\tag{29}
\]

The mean (28) is exactly
T=P+eta n-rho k, where eta=xi-delta a>=0. Its true force and torque
balance gives
\[
                       Y-VX=\eta(Y+V)\ge0.
\tag{30}
\]
But the argument (22)--(23), with c=a,d=b and (29), makes the
left side strictly less than -31/3200. This contradiction retains
both endpoints of the actual mean interval as well as its interior.
It excludes the entire shared-side alternative.

## 7. Complete scope

The horizontal A reactions were exhausted before selecting a lower
tip. In the opposite-sign alternative only that lower tip was made
physically unique; the upper tip retains its complete physical mask,
contact features and actual means. For the lower UC edge, a singleton
is either C-owned or U-owned after the legitimate distinct-fixed-tip
selection. A positive-length shared side was treated directly with
its full mean interval. Sections 4--6 exclude these three exhaustive
possibilities.

Thus no selected positive D-leaf diamond with a tilted, unique-circle
second hub can have horizontal AU. Together with the separate
parallel-hub theorem, this removes the entire horizontal-central
alternative. The oblique central alternative is treated in
D_DIAMOND_OBLIQUE_HUB_EXCLUSION.md; no unrestricted nine-square theorem
is asserted here, and no extra square or force at U was discarded.
