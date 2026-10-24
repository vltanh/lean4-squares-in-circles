# A triangle with a two-edge pendant chain is excluded throughout the window

**Status: complete hand argument; root and separate independent hand audits passed.** Consider
the entire chain-attachment alternative of C1.3.b2: a positive triangle
A,B,C and the positive pendant path A--U--L. In the declared radius
window this component cannot occur in a suitably selected physical
certificate. All contact types, both transmitter widths, all circle
corner masks, and the entire articulation orientation are included.
This excludes the core, independently of the other four physical
squares. The two other bridge-attachment layouts of C1.3.b2 are not
excluded by this manuscript.

The additional finite normal choices below are made before the physical
multiplier theorem, simultaneously with the preceding strict,
nonradial, planar-junction and generic choices. No obtained stress is
subsequently altered by choosing a new point normal.

## 1. The full load and radial-chain geometry

Throughout,

\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 T=\sqrt{R^2-\frac14},\qquad
 \varepsilon=\frac1{60},\qquad M=\frac{61}{40}.
 \tag{1}
\]

Every square center has norm strictly less than M, by the existing
farthest-corner bound. The leaf L is loaded. The central endpoint
theorem makes U physically circle-clear. It has degree two and thus
transmits equal opposite forces with projected width
\(w\in\{1,\sqrt2\}\). The two degree-two vertices B,C of the
positive triangle are loaded, since an unloaded transmitter cannot
have touching neighbors. A is physically circle-clear: if it touched
the circle, A,B,C would be three mutually touching boundary bodies,
contrary to the boundary-contact graph theorem.

Thus the only loaded bodies in this component are L,B,C. Rotate the
radial path so L points east. Its inward application radius is

\[
 r_L=R-\sqrt2\quad\hbox{in type D},\qquad
 r_L=T-1\quad\hbox{in type S}.
\]

The two true path application points are

\[
 p_{UL}=r_Le_x,\qquad p_{AU}=xe_x,
 \qquad x=r_L-w.
 \tag{2}
\]

The whole articulation A lies in the half-plane \(X\le x\),
and \((x,0)\) is its right support point. This is a consequence
of the actual normal channel; it is not an S/D assumption on A.

The combination D leaf/diagonal U is excluded by the selected
nonradial point-normal convention: the UL contact would be a
vertex/vertex radial contact at the nonzero point \((R-\sqrt2)e_x\).
All other combinations remain at this stage. They satisfy

\[
 x<\varepsilon,\qquad
 s:=1-x>\frac{59}{60},\qquad s<\frac85.
 \tag{3}
\]

Indeed \(T<121/60\), as follows by squaring at the upper endpoint
of (1), and \(x\le T-2<1/60\). For the upper bound on s,
the three remaining formulas are
\(2+\sqrt2-R\), \(3-T\), and \(2+\sqrt2-T\).
Use \(\sqrt2<3/2\) and \(R,T>19/10\).
The same three cases, now using \(\sqrt2<17/12\), give
\[
                    |x|<\frac{31}{60}<R-\sqrt2.
 \tag{3a}
\]
For the last comparison, \(R-\sqrt2>67/120\). Thus the
bridge application cannot belong to a circle-touching square.

Every positive circle corner of B or C has negative first coordinate.
For such a corner z, its scalar product with each positive circle
corner of either body is positive: within one body the corners are
adjacent, and across B,C this is the acute-contact theorem. But their
weighted sum is the negative horizontal leaf resultant. Hence
\(z_x<0\). Write the two circle-resultant vectors as \(m_B,m_C\).
Their vertical coordinates are opposite and nonzero; otherwise their
directions would coincide, which the disjoint inner-arc/resultant
theorem excludes. Label them so that

\[
 (m_B)_y>0>(m_C)_y,
 \qquad (m_B)_x,(m_C)_x<0.
 \tag{4}
\]

The connected loaded-noncontact theorem also gives closed
disjointness of L from both B and C. This will justify the simple
three-port order argument below.

## 2. A useful two-force boundary-body concurrence fact

**Lemma 2.1.** Let a loaded unit square have exactly two positive pair
forces, at least one of whose neighboring bodies touches the circle.
Their two force lines are nonparallel. They meet at a point q which
is a positive multiple of the square's circle-resultant vector m.
For each of its actual contact points p with outward unit normal n,

\[
                         p-q=\ell n,\qquad\ell\ge0.
 \tag{5}
\]

The point q need not be in the square when it has two circle corners;
equation (5), rather than an unjustified interior assertion, is the
conclusion needed here.

*Proof.* If the two forces were parallel with opposite signs, a
contact in the direction of the circle resultant would occur at an
outer circle corner, or at the outer radial S face. The first cannot
be shared and the second has support greater than R-1, so no unit
neighbor fits. If the forces are parallel with the same sign,
`PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md`, Lemma N.4, gives radial
S or D geometry. In D the application is the radial inner vertex,
which cannot be a contact with another circle-touching square. In S
the horizontal inner-face case of `C7_FORCE_POLYGON.md`, Lemma 2.1,
excludes such a circle-touching neighbor. Thus the lines are
nonparallel. Torque about their intersection makes q parallel to m.

Here are the precise parts of the rectangle normal-line calculation
from `C7_FORCE_POLYGON.md`, Sections 4--5, that apply without requiring
both neighbors to touch the circle. If the two application points
coincide, their nonparallel lines meet there. The point belongs to the
square, is a positive multiple of m by the acute cone theorem, and
(5) holds with zero coefficients. Suppose they are distinct.

For a square with one physical circle corner, use its own coordinates
\([a-1,a]\times[b-1,b]\), where
\(a\ge b\ge1/2\) and \(a^2+b^2=R^2\). The calculation in
Section 4 of that source excludes every concurrence outside the
rectangle using only distinctness of the two contacts, the impossibility
of sharing a circle point, and the unit-neighbor width bound. In
particular its outer-corner and inner-corner alternatives cannot give
two distinct contacts; its remaining lower-right-corner alternative
has outward support at least \(R/\sqrt2>R-1\). No hypothesis
that the other neighbor touches the circle is used in these steps.
Consequently q is in the square. It is a positive multiple of m,
and its supporting-half-plane position proves (5).

For two physical circle corners, write the square as
\([d,d+1]\times[-1/2,1/2]\), with
\(d=T-1>9/10\), and write
\(q=\tau(T,\eta)\), \(|\eta|\le1/2\). The first part of
Section 5 of the same source, again using only distinct contacts and
width, excludes \(\tau<d/T\). For \(d/T\le\tau\le1\),
q is inside the square. If \(\tau>1\), the elementary normal-line
check leaves no two distinct non-circle contacts when
\(|q_y|>1/2\). When \(|q_y|\le1/2\), every possible
non-circle contact is on the inner face or at one of its endpoints:
the outer horizontal face is excluded by width. Since \(q_x>T>d\),
each such contact has \(p-q\) pointing in its outward-normal
direction, so (5) holds with a positive coefficient. In all these
cases \(\tau\ge d/T>0\), proving the claim for every circle
weight mask. \(\square\)

## 3. The triangle has positive concurrence on the leaf axis

Apply Lemma 2.1 to B and C, since they touch each other. Let their
concurrence points be \(q_B,q_C\). These are positive multiples
of (4). If n is the BC unit normal directed B to C and p its actual
application point, (5) gives

\[
 q_C-q_B=\ell n,\qquad\ell>0,
 \qquad \det(p,n)=\frac{\det(q_B,q_C)}\ell>0.
 \tag{6}
\]

The coefficient cannot vanish because \((q_B)_y>0>(q_C)_y\).
The determinant is positive because both first coordinates are negative
and the second coordinates have these opposite signs. Orient the
triangle A to B to C to A. The zero moment of the bridge at A makes
the three contact moments equal. Write their common value as H;
equation (6) proves

\[
                                  H>0.
 \tag{7}
\]

The AB and AC applications on A are distinct. Otherwise call their
common point p. Their positive sum balances the horizontal bridge,
so \(-e_x\) belongs to A's normal cone at p, and torque gives
\(p_y=0\). Hence
\(p_x=x-\operatorname{width}_A(e_x)\le x-1<0\).
Lemma 2.1 at B says
\(q_B=p+\ell_B n_{AB}\), \(\ell_B\ge0\).
Its positive height forces \(\ell_B>0\) and
\((n_{AB})_y>0\), giving
\(H=\mu_{AB}p_x(n_{AB})_y<0\), a contradiction.

First consider nonparallel AB and AC normals. Delete the BC edge
and retain the paths from A through B and C to positive circle corners,
and from A through U,L to a circle corner of L. These three paths form
an embedded three-port tree. Their open strands are inside distinct
square interiors. The three applications at A are distinct: AB and
AC were just treated, and (3a) prevents either loaded body from
containing the AU application. A possible zero-stress boundary
contact elsewhere does not meet the open interior strands. Only this
simple three-branch tree is used, not a tree assertion about the full
physical touching graph.

Choose a positive upper circle corner of B and a positive lower circle
corner of C. The circular order of the three ports is L,B,C. The
crosscut argument for a tree with three boundary ports gives the same
order of its three branches at A. Outward normals of a convex square
occur in the boundary order of their supporting applications. Starting
from the bridge normal \(e_x\), the normals therefore have cyclic
order \(e_x,n_{AB},n_{AC}\). Positive equilibrium and
noncollinearity make each successive angular gap strictly less than
\(\pi\). In particular

\[
                         (n_{AB})_y>0>(n_{AC})_y.
 \tag{8}
\]

Their lines meet on the horizontal axis, by force and zero bridge
moment. Equations (7)--(8) show that their concurrence is

\[
                         q_A=(q,0),\qquad q>0.
 \tag{9}
\]

Since \(q_B-q_A\) is parallel to \(n_{AB}\), its positive
vertical component and (8) give a positive coefficient. Its horizontal
component is negative, because \((q_B)_x<0<q\).
Thus \((n_{AB})_x<0\). The same reasoning at C gives

\[
                         (n_{AB})_x,(n_{AC})_x<0.
 \tag{10}
\]

This is a full left-contact conclusion, independent of the earlier
small-s D-leaf localization.

## 4. Every tilted articulation is excluded

If A is not axis-aligned, its rightmost point is the unique vertex
\(p_0=(x,0)\). After reflecting vertically if needed, write its
inward orthonormal axes as

\[
 u=(-a,-b),\qquad v=(-b,a),\qquad a\ge b>0,
 \qquad a^2+b^2=1,
 \qquad A=p_0+[0,1]u+[0,1]v.
 \tag{11}
\]

The parallel-reaction alternative cannot occur here. Both reactions
would have to point left: opposite signs put B and C beyond opposite
support faces of A and separate them by A's positive width. Both
leftward reactions at a tilted square use its unique leftmost vertex,
contrary to the distinct applications just proved.

Use (9). If \(q>x\), q lies outside both coordinate-minimum sides
in the frame (11). A rectangle normal-line check leaves only the two
opposite vertices as support contacts with a line through q. The
rightmost one is \(p_0\), already used by the bridge, and cannot
also belong to either loaded neighbor. The other two contacts would
therefore coincide at the opposite vertex, again impossible. Thus

\[
             0<q\le x<\varepsilon,
             \qquad\delta=x-q\in[0,\varepsilon).
 \tag{12}
\]

In A's coordinates from \(p_0\), the concurrence has coordinates
\((a\delta,b\delta)\). A normal foot on either coordinate-minimum
side is within \(2\varepsilon=1/30\) of the origin, so it cannot
belong to a circle-touching unit square: every point of such a square
has norm at least \(R-\sqrt2>1/30\). The same excludes \(p_0\).
The opposite vertex cannot be used either. Its outward normal through
q has support at least

\[
 \sqrt2(1-\varepsilon)-\varepsilon>\frac43>R-1;
\]

a unit neighbor on its outward side would extend past the disk.

The only remaining contact classes are the side with u-coordinate 1
and its endpoint \(p_0+u\), or the side with v-coordinate 1 and
its endpoint \(p_0+v\). Their outward normals have respectively
the forms

\[
 n_u=\cos\alpha\,u-\sin\alpha\,v,
 \qquad
 n_v=\cos\beta\,v-\sin\beta\,u,
 \qquad \alpha,\beta\ge0,
 \tag{13}
\]

including zero angles for side contacts. Exactly one contact is in each
class: two u-class normals have nonpositive v-components and cannot
balance the strictly negative v-component of the bridge; the other
case is symmetric. In particular \(n_u\cdot n_v\le0\).

Each contact's support value is at least \(1-x\). For a side this
is immediate from \(p\cdot u=1-ax\) or
\(p\cdot v=1-bx\). For the endpoint \(p_0+u\),

\[
 p\cdot n=|p-q_A|+q_A\cdot n
       \ge1-\delta-q=1-x,
\]

and the other endpoint is identical. Therefore the centers of B,C
lie in the respective caps

\[
 |c|<M,
 \qquad n\cdot c>\frac32-\varepsilon=\frac{89}{60}=:D_0.
 \tag{14}
\]

These two caps have distance greater than \(\sqrt2\). Here is an
exact verification. Set \(t_0=\sqrt{M^2-D_0^2}\); then

\[
 t_0^2=\frac{1805}{14400},\qquad
 (D_0-1)^2-t_0^2=\frac{1559}{14400}>0.
 \tag{15}
\]

If the angle between their normals is \(\omega\ge\pi/2\),
project their difference on the unit bisector of \(n_u,-n_v\).
The projection gap is at least

\[
 2D_0\sin(\omega/2)-2t_0\cos(\omega/2)
 \ge\sqrt2(D_0-t_0)>\sqrt2.
\]

For the first inequality, decompose a cap point along its own normal;
its transverse magnitude is at most \(\sqrt{M^2-p^2}\) when its
normal projection is p, and the resulting lower expression increases
with \(p\ge D_0\). But centers of two touching unit squares are
at distance at most \(\sqrt2\), by their common contact point.
This contradiction excludes every tilted A.

## 5. Aligned articulations: parallel reactions and the finite selections

The remaining articulation has the complete aligned form

\[
             A=[-s,1-s]\times[h-1,h],\qquad0\le h\le1.
 \tag{16}
\]

If its two triangle normals are parallel, they must both point left;
opposite signs would separate B and C by A's positive width. Their
right support lines are both \(X=-s\), so both centers satisfy
\(c_x\le-s-1/2<-89/60\). The diameter of the corresponding
radius-M cap is at most \(2t_0<1\), by (15). This contradicts
the unit center-distance lower bound for interior-disjoint unit squares,
whose open inscribed radius-1/2 disks are disjoint.

Suppose the reactions are nonparallel. Equations (8)--(10) put them
at the two left corners, with

\[
 P=(-s,h),\quad n=(-b,a),\qquad
 Q=(-s,h-1),\quad m=(-d,-c),
 \tag{17}
\]

where \(a,b,c,d>0\), \(a^2+b^2=c^2+d^2=1\).
The positive concurrence (9) gives

\[
 K=ad+bc,
 \qquad h=\frac{ad}{K},\quad1-h=\frac{bc}{K},
 \qquad q=-s+\frac{bd}{K}>0.
 \tag{18}
\]

In particular \(0<h<1\). The same finite articulation determinant
argument as `D_LEAF_GENERIC_CONTACT_SELECTION.md` removes point-only
vertex/vertex AB or AC contacts before KKT. Its nonzero coefficient is
the product of the other normal's nonzero vertical component and the
present corner's nonzero height. Variable shared-side means do not
occur in this nonaxis alternative. Thus P,Q lie in the relative
interiors of B,C sides, and n,m are their actual side axes.

At least one of B,C has a unique physical circle corner. To prove
this, suppose both had two. Their facing-side normal coordinates
would both be \(D=T-1\), giving

\[
 sb+ah=D=sd+c(1-h).
\]

After substitution from (18), subtraction factors as
\((b-d)[sK-(1+bd)]=0\). The second factor cannot vanish,
because \(sK<bd\) by (18). Consequently
\(b=d,a=c,h=1/2\). Both bodies are now radial S squares
at directions symmetric about the west axis. Two such squares of the
same radius touch exactly when their half-angle \(\phi\) satisfies
\(\tan\phi=1/(2D)\): if it is smaller their interiors overlap
on the bisector, and if larger their angular shadows are disjoint.
The facing-side equation therefore gives

\[
 s=\sqrt{D^2+\frac14}-\frac1{4D}
 <\frac{23}{20}-\frac{15}{61}
 =\frac{1103}{1220}<\frac{59}{60},
\]

using \(D<61/60\) and
\(\sqrt{(61/60)^2+1/4}<23/20\). This contradicts (3).

If BC were point-only vertex/vertex, choose its endpoint body having
a unique physical circle corner. Its A-contact is side-interior with
fixed normal. If that normal and its circle direction are nonparallel,
their fixed force lines meet at a point different from the BC vertex:
no vertex is on the perpendicular line through a relative side-interior
point. Only finitely many BC normal directions can pass through that
intersection. If the two fixed directions are parallel, force balance
itself permits only the parallel BC directions. Exclude these finite
directions before KKT, for every physical candidate simultaneously.
The BC junction differs from both articulation contacts, so the matched
four-junction parameters and all previous choices remain compatible.

Every remaining BC contact has a side-axis owner. Reflect vertically
and exchange B,C if necessary so that B owns it. This retains both
possible owners and the full height range.

## 6. The complete owned-axis chart and the circle contradiction

The actual support-axis calculation of
`D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md`, Sections 2--3, applies to
(17) for every \(s>0\); its use here does not require s to be
small or the origin to be inside A. For clarity its full conclusion is
recorded. Put

\[
 v=Jn=(-a,-b),\quad k=Jm=(c,-d),\qquad
 L=bd-ac.
\]

A BC normal parallel to n is excluded by the radial-S/inner-face
circle-neighbor argument. The sign \(-v\) is excluded by projecting
its common support point on m: it would require a projection greater
than one across a unit square. The sign is therefore v. The contact
point is the minimum-m, minimum-k corner of C, and

\[
 T_{BC}=Q-rk,\quad0<r<1,
 \qquad w=b-Lr\in(0,1),\quad U_0=1-w=1-b+Lr.
 \tag{19}
\]

Here \(L>0\). One may obtain this from the same support argument,
or directly from (18):
\(a/b+c/d<1/s<60/59\), so
\((a/b)(c/d)<1\).

Force balance identifies actual positive-weight circle corners with
own-frame coordinates

\[
\begin{aligned}
 X_B&=1+sb+ah,& Z_B&=1-b+bh-sa+Lr\ge1/2,\\
 X_C&=1+sd+c(1-h),&Z_C&=1+d(1-h)-sc-r\ge1/2.
\end{aligned}
 \tag{20}
\]

Both satisfy \(X_i^2+Z_i^2=R^2\). In particular
\(X_B,X_C\le T<121/60\), with every physical circle-corner
mask retained.

Let \(P_0=a+c\), \(E_0=a^2+c^2\). From (18),

\[
 \frac ab+\frac cd<\frac1s<\frac{60}{59},
 \qquad b,d>\frac7{10}>\frac23,
 \qquad P_0<\frac65.
 \tag{21}
\]

The exact height-weighted inequality is

\[
 ah+c(1-h)=\frac{a^2d+c^2b}{K}
                   \ge\frac{E_0}{P_0}.
 \tag{22}
\]

After clearing positive denominators, its difference is
\(ac(a-c)(d-b)\ge0\). On the other hand (20), (3), and
\(1-b=a^2/(1+b)\), \(1-d=c^2/(1+d)\) give

\[
 ah+c(1-h)
 <\frac1{15}+\frac{59}{60}\bigl((1-b)+(1-d)\bigr)
 <\frac1{15}+\frac35E_0.
\]

Since \(E_0\ge P_0^2/2\) and \(1/P_0-3/5>0\),

\[
                  \frac{P_0}{2}-\frac3{10}P_0^2<\frac1{15}.
 \tag{23}
\]

The concave left side is at least \(3/40>1/15\) throughout
\([1/6,6/5]\): its endpoint values are \(3/40\) and
\(21/125\). Consequently

\[
                                a+c<\frac16.
 \tag{24}
\]

It follows that \(b,d>35/36\), hence both horizontal own-frame
coordinates in (20) satisfy

\[
             X_i>1+\frac{59}{60}\frac{35}{36}
                         >\frac{39}{20}.
 \tag{25}
\]

Meanwhile direct addition of (20) gives

\[
 Z_B+Z_C=2+(d-b)(1-h)-s(a+c)-(1-L)r.
\]

By (24), \(|d-b|<(a+c)^2<1/36\). Also
\(1-L=K^2/(1+L)\le(a+c)^2<1/36\). Using
\(s<8/5\) and \(0<r,h<1\),

\[
 Z_B+Z_C>2-\frac1{36}-\frac4{15}-\frac1{36}
             =\frac{151}{90}>\frac53.
 \tag{26}
\]

At least one of these genuine circle corners therefore has
\(Z_i>5/6\). Together with (25),

\[
 R^2=X_i^2+Z_i^2
   >\left(\frac{39}{20}\right)^2+\left(\frac56\right)^2
   =\frac{16189}{3600}>\frac{13}{3}>\frac{1105}{256},
\]

a contradiction. This excludes all aligned nonparallel charts.

## 7. Exact scope of the completed implication

The leaf/transmitter classification covers every chain A--U--L.
The right support of A is always less than \(1/60\); all its
aligned and tilted shapes are included. Lemma 2.1 and the three-port
order establish the positive concurrence without assuming a force
polygon point lies in every body. Tilted articulations are excluded by
the two center caps, parallel aligned reactions by one center cap, and
all remaining aligned reactions by the exact owned-axis circle
inequality. All finite exclusions are compatible pre-multiplier choices.

**Theorem 7.1.** The selected physical certificate can be chosen so
that its positive component is not a triangle with a pendant chain of
two edges, anywhere in (1). No assumption on the four remaining
physical squares was introduced or needed.

The full C1.3.b2 parent still requires the layouts with two leaves at
one triangle vertex, and with leaves at two different triangle vertices.
Neither is declared closed here. No Lean compilation or CI was run.
