# Two radial D leaves cannot share a triangle articulation

**Status: complete exact hand proof; root and independent full hand audits passed.**
Let a selected positive component consist of a triangle A,B,C and two
radial D leaves, both attached to A. This core is impossible throughout

\[
                  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

All physical contact types, shared-side means, circle-corner masks,
and both possible owners of the B--C contact are retained. The proof
excludes the core itself; its four additional packing squares are not
discarded or subjected to an independent pocket assumption.

## 1. Geometry, corner uniqueness, and constants

The two D leaf directions are distinct adjacent side normals of A:
equal directions repeat a square, and opposite directions would force
\(2(R-\sqrt2)=1\). Rotate and reflect so they point east and north.
Put

\[
 r=R-\sqrt2,\qquad s=1-r,\qquad
 d_S=\sqrt{R^2-\tfrac14}-1.
\]

Then the entire articulation is fixed:

\[
                         A=[-s,r]^2.
\tag{2}
\]

Its two leaf applications are \((r,0)\) and \((0,r)\), in the
relative interiors of the right and top sides. A is physically
circle-clear. B and C are loaded degree-two triangle vertices, since
a clear degree-two transmitter cannot have touching neighbors.

The inequality \(\sqrt2 r<d_S\), proved in
`SMALL_TREE_STRESS_CORES.md`, Section 3, implies that B and C each
have exactly one physical circle corner. Indeed every point of A has
norm at most \(\sqrt2 r\), whereas any unit square with two
physical circle corners is radial S and has minimum radius d_S.
Denote their unique circle corners by z_B and z_C. Both carry positive
weight. They are distinct and have positive scalar product, because
B and C touch. Force balance has the form

\[
                  m_B+m_C=-g,
                  \qquad g=(g_x,g_y),\quad g_x,g_y>0.
\tag{3}
\]

We use the degree-two boundary-body concurrence lemma from
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`, Lemma 2.1. Its hypotheses
require only one boundary neighbor. Each of B,C therefore has
nonparallel contact force lines, meeting at q_i inside that square,
where q_i is a positive multiple of z_i. At either contact p with
outward normal n,

\[
                            p-q_i=\ell n,\qquad\ell\ge0.
\tag{4}
\]

For the main argument below, R<2. In that range we have

\[
 \frac12<r<\frac35,\qquad
 \frac25<s<\frac9{20},\qquad
 R^2>\frac{39}{10},
\tag{5}
\]

and the useful strict radius budget

\[
 \begin{aligned}
 R^2-(s+1)^2
 &=(2+\sqrt2)(2R-2-\sqrt2)\\
 &\ge\frac{19}{10}-\frac{\sqrt2}{20}
  >\frac{73}{40}.
 \end{aligned}
\tag{6}
\]

Here \(r>67/120\), \(\sqrt2>7/5\), and
\(\sqrt2<17/12\) give (5)--(6). In particular all bounds remain
strict at the lower endpoint of (1).

## 2. The whole range R at least two

If R>2, then \(\sqrt2 s<r\). Every circle point z in the
closed southwest quadrant has distance greater than \(\sqrt2\)
from A: enlarge A to \([-s,\infty)^2\), whose nearest point v
to such z has \(|v|\le\sqrt2 s<r\), and use
\(|z-v|\ge R-|v|>R-r=\sqrt2\).
Thus no B,C circle corner is in that quadrant. But their positive
sum (3) points strictly into it. Two acute vectors cannot straddle
a forbidden closed 90-degree arc and have their sum inside the arc.
This is the acute-arc observation in
`TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md`.

At R=2 the only possible equality point in the southwest arc is

\[
             z_0=(-\sqrt2,-\sqrt2),\qquad P=(-s,-s),
             \qquad |P|=r.
\]

A circle-touching neighbor reaching z_0 must use the full square
diagonal from P to z_0. It is a radial D square with inner vertex P,
and its intersection with A is exactly P. It cannot be B or C in
the positive triangle. Indeed take its other positive contact q with
the boundary neighbor. A boundary/boundary contact has norm strictly
greater than r, so q differs from P. Torque about P, with the circle
corner collinear with P, forces

\[
                            \det(q-P,n_{BC})=0.
\tag{7}
\]

If q is side-interior, a perpendicular through the corner P cannot
reach that side interior. If q is an adjacent noncircle vertex, (7)
is an outer side axis with support R/\(\sqrt2\)>R-1, beyond which
no unit neighbor fits. The circle vertex cannot be shared. These are
all boundary features, including an actual shared-side mean. Thus
z_0 is also impossible for B or C. The same closed-arc contradiction
excludes R=2. Henceforth assume R<2.

## 3. Contact order reduces the articulation to two entire cases

Label B,C so that their acute circle-corner gap from B to C is
counterclockwise. Equation (3) and acuteness put both corners in the
open half-plane opposite g, hence strictly between the north and east
leaf ports in the long counterclockwise arc. Their circle-port order
is east, north, B, C.

Let T be the actual B--C application and n its normal from B to C.
Equation (4) gives

\[
             q_C-q_B=\ell n,\quad\ell>0,
             \qquad H:=\det(T,n)=\frac{\det(q_B,q_C)}\ell>0.
\tag{8}
\]

If P,Q are the A--B and A--C applications, and n_B,n_C the outward
normals from A, body torque therefore gives

\[
                 \det(P,n_B)>0,\qquad
                 \det(Q,n_C)<0.
\tag{9}
\]

### 3.1. Coincident applications are impossible

If P=Q, their positive normal sum is -g and its origin moment is
zero. Since g has positive coordinates, the common support point of A
must be its southwest vertex P=(-s,-s), and g is parallel to (1,1).
Both B,C contain P. If their intersection is only P, both of their
pair forces act at P, so torque about P makes both circle corners
collinear with P. They would be the same containing-circle point,
which two disjoint squares cannot share.

If B,C share a segment, P cannot be interior to that common segment:
their two local half-planes would leave no room for A. At its endpoint
there are two possibilities. If P is a vertex of both, their common
unit side starts at P and has full length one. Their union is

\[
                     P+[0,1]e+[-1,1]f,
\]

for orthonormal e,f. Distinct unique circle corners of the two halves
must be the two outer f endpoints. Their equal norms force P dot f=0.
If their e-coordinate were that of P, their norms would be at most
\(\sqrt{|P|^2+1}<R\). Thus their other e-coordinate is used, and

\[
          R^2=(\sqrt2 s+1)^2+1
              <\left(\frac{131}{80}\right)^2+1
              <\frac{39}{10},
\]

contrary to (5). If P is side-interior in one square, its local
half-plane and the two right-angle sectors of A and the other square
fill the plane. All frames are then parallel to A, and that other
square is the northwest or southeast unit neighbor at P. Every one
of its points has squared norm at most
\((1+s)^2+r^2<(29/20)^2+(3/5)^2<R^2\). It cannot touch the circle.
This exhausts coincident applications.

### 3.2. The distinct applications have the actual port order

Delete BC from the planar selected graph. The four branches at A end
at the four distinct circle ports just listed. The simultaneous
circle spokes and junction routing in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md` and
`UNIQUE_POSITIVE_COMPONENT.md` preserve their cyclic order. Neither
P nor Q is a leaf application: its radius r would force a neighbor
to share that D leaf's circle corner. Thus the four applications are
distinct and appear on A's boundary in the order

\[
                    (r,0),\ (0,r),\ P,\ Q.
\tag{10}
\]

Convexity gives the same weak order for their outward normals.
Together with (9), positive coordinate force balance, and the acute
circle-corner condition, this leaves, up to exchanging x and y, only:

* **Corner case:** P=(-s,r), Q=(-s,-s), with
  \(n_B=(-b,a)\), \(n_C=(-d,-c)\), all four letters positive.
* **Side case:** P=(-s,y), 0<y<=r, \(n_B=-e_x\),
  Q=(-s,-s), \(n_C=(-a,-b)\), a,b positive.

Here each normal has unit length. To verify this short exhaustion,
a top-side normal at P has the wrong moment sign, and a right-side
normal at Q does also. Two normals with nonnegative x or nonnegative
y cannot balance -g. A northwest normal at P makes z_B northwest
by (4); a southeast normal at Q, or a bottom normal with negative
moment, makes z_C southeast. Those two circle corners would have
negative scalar product. A left normal at P has y>0 by (9), and
has the same northwest consequence. The only remaining combinations
are northwest/southwest, left/southwest, and their diagonal
reflections; two southwest contacts would be coincident. This proves
the classification, including all axis endpoints and side means.

## 4. Select all remaining nonaxis A contacts to have the tip owner

We make one finite compatible pre-certificate choice, retaining every
actual shared-side mean. If BC is a point contact, the theorem in
`BOUNDARY_TIP_FIXED_APPLICATION_SELECTION.md` removes every free
vertex/vertex edge at a unique-corner tip whose other application is
fixed. In particular it removes each nonaxis A contact in the corner
case and the SW A contact in the side case, as well as every remaining
free BC point edge once those A contacts are fixed.

Here is the required extension when BC is a shared side. Its two
frames are parallel. Choose a common-axis normal e on that side and
put

\[
 w_B=Jz_B,\qquad
 w_C=\frac{e\cdot Jz_B}{e\cdot Jz_C}Jz_C.
\tag{11}
\]

The denominator is nonzero: both components of a unique farthest
circle corner in its square frame have absolute value greater than
1/2. These pure translations annihilate both circle forces and every
internal shared-side force, at any mean. Rigid rotation of B,C about
the origin is a second such virtual motion. Their two exterior
equations imply

\[
 D=\det(P,n_B)(n_C\cdot w_C)
       -\det(Q,n_C)(n_B\cdot w_B)=0.
\tag{12}
\]

For a free normal at a fixed vertex application, (12) is a nonzero
linear condition. The other moment is nonzero by (9). A zero
coefficient could therefore occur only if that application were
collinear with its tip's circle corner. A noncircle vertex of a
unique-corner boundary square is collinear with its circle corner
only at a radial D inner vertex, whose radius is r. But in R<2 both
possible free A applications have strictly larger norm:

\[
                   |(-s,r)|>r,
                   \qquad |(-s,-s)|=\sqrt2s>r.
\tag{13}
\]

Thus (12) excludes only a nowhere dense set of free-normal choices.
In the side case a tilted B gives a fixed vertex application P, with
fixed normal -e_x. If B is aligned and AB has a shared mean, a
simultaneous shared BC would make C aligned also. Its SW A contact
then places C entirely in [-s-1,-s]^2, whereas the upper circle
corner of B forces its bottom side above zero. They cannot touch.
So the variable-mean exception to (12) never occurs.

Prelist the finite physical candidates and avoid these determinant
zero sets together with the existing fixed-tip exclusions. Distinct
P,Q use distinct junction parameters, including the matched
four-junction convention. These are open dense restrictions inside
the already permitted open intervals. Uncrossing preserves surviving
point normals and adds only shared-side forces; thinning deletes
atoms. Every candidate and every physical shared block was prelisted.
The final selected certificate consequently has every nonaxis A
contact in the relative interior of a side of its tip, with that tip
owning the normal. Remaining BC point contacts have a side-axis owner.

In the corner case a shared BC is now impossible: the two facing
normals are nonparallel axes of the parallel frames, so any BC axis
is parallel to at least one facing normal. That tip would have two
parallel pair forces, contradicting (4). Thus BC is point-only there.

## 5. The corner case, with either B--C owner

Write the outer and inner normals as

\[
 n=(-b,a),\quad m=(-d,-c),\quad
 a^2+b^2=c^2+d^2=1,
 \quad a,b,c,d>0,
\]

\[
 v=Jn=(-a,-b),\quad k=Jm=(c,-d),\quad
 K=ad+bc>0,\quad L=bd-ac.
\tag{14}
\]

Let \(\phi,\psi\in(0,\pi/2)\) satisfy
\((a,b)=(\sin\phi,\cos\phi)\) and
\((c,d)=(\sin\psi,\cos\psi)\).

We recall the full side-owner chart from
`D_LEAF_NONPARALLEL_OWNER_EXCLUSION.md`, Sections 2--3 and 5.
Its geometric and tip-torque portions do not use that source's
horizontal-leaf height identity. For upper P=(-s,h), lower
Q=(-s,h-1), with the upper tip owning BC, the BC normal is exactly v,
and for some 0<rho<1,

\[
 T=Q-\rho k,\quad
 j=K\rho-a\in[0,1],\quad
 U=1-b+L\rho\in(0,1),\quad
                         0<K<L.
\tag{15}
\]

For clarity, the other B-axis sign would require an m-projection
greater than one from a vector \(j n-u v\) with 0<=j,u<=1.
The chosen sign forces L>0 by the facing-side support projection.
The unique lower tip's concurrence is
\(q_C=Q+(\rho K/L)m\), a positive proper multiple of
\(z_C=Q+m+(1-\rho)k\). Hence
\((z_C-T)\cdot n=L-K>0\), proving the final inequality in (15).
In particular \(\phi+\psi<\pi/4\).

The actual circle corners, with positive transverse coordinate, are

\[
 \begin{array}{ll}
 X_B=1+sb+ah,&Z_B=1-b+bh-sa+L\rho,\\
 X_C=1+sd+c(1-h),&Z_C=1+d(1-h)-sc-\rho,
 \end{array}
\tag{16}
\]

with \(Z_B,Z_C>1/2\) and \(X_B^2+Z_B^2=R^2=X_C^2+Z_C^2\).
In world coordinates they are

\[
 z_B=(-s-b+aU,\ h+a+bU),\quad
 z_C=(-s-d+c(1-\rho),\ h-1-c-d(1-\rho)).
\tag{17}
\]

### 5.1. The outer, northwest tip owns BC

Here h=r. Torque at A and its strictly negative cycle y-force give

\[
                    s ad<r bc,
       \qquad \tan\psi>\frac sr\tan\phi.
\tag{18}
\]

Indeed the moments are \(rb-sa>0\) and \(s(c-d)<0\).
Eliminating their positive force ratio from
\(\mu_B a-\mu_C c<0\) gives (18).

If \(\rho\ge s/d\), (17) gives

\[
 |(z_C)_x|\le s+d,\qquad |(z_C)_y|\le c+d,
\]

and therefore

\[
 R^2\le(s+d)^2+(c+d)^2
       \le(s+1)^2+\frac53,
\tag{19}
\]

contrary to (6). The last bound uses
\(d^2+2cd\le(5/3)d^2+(3/2)c^2\le5/3\).

Suppose instead \(\rho<s/d\). The lower tip's own-frame
coordinates of Q are \(S=s(c+d)\), \(D=s(d-c)>0\).
Its concurrence in (15) has m-coordinate strictly greater than S,
while its circle corner has coordinates \((S+1,D+1-\rho)\).
Positive radial collinearity implies

\[
                  \rho>1-\frac DS=\frac{2c}{c+d},
                  \qquad \frac{2cd}{c+d}<s.
\tag{20}
\]

Equations (18)--(20) force \(\tan\phi<2/5\). Here is an
exact uniform check. The function

\[
                    F(v)=\frac{2v}{(1+v)\sqrt{1+v^2}}
\]

increases for 0<v<1, since its derivative has the sign of 1-v^3.
If \(\tan\phi\ge2/5\), (18) would give
\(\tan\psi>2s/(5r)\). But throughout 1/2<=r<=3/5,

\[
                         F\left(\frac{2s}{5r}\right)>s.
\tag{21}
\]

After squaring positive quantities, (21) is precisely

\[
 P(r):=261r^4+276r^3-344r^2+16r+16<0.
\]

The polynomial is convex on that interval:
\(P''(r)=3132r^2+1656r-688>0\), and its endpoint values are
\(-179/16\), \(-2999/625\). Convexity bounds it above by their
negative chord. This contradicts (20), whose left side is
F(tan psi). Thus

\[
       a^2<\frac4{29},\qquad a+b<\frac7{\sqrt{29}}<\frac{13}{10}.
\tag{22}
\]

Evaluate (17) at the auxiliary parameter \(\rho_0=s/d\).
Then \(0<U_0=1-b+L\rho_0<1\), its x-coordinate is negative
with absolute value at most s+1, and its positive y-coordinate is

\[
 \begin{aligned}
 (z_B(\rho_0))_y
 &=a+b+r a^2-sab\frac cd\\
 &<a+b+\left(r-\frac{s^2}{r}\right)a^2\\
 &<\frac{13}{10}+\frac13\frac4{29}<\frac{27}{20}.
 \end{aligned}
\tag{23}
\]

The first strict bound uses (18); the next uses r<3/5. The actual
corner norm increases with rho on the interval in question, since
its positive transverse coordinate in (16) increases. Hence

\[
 R^2\le|z_B(\rho_0)|^2
       <(s+1)^2+\left(\frac{27}{20}\right)^2
       <(s+1)^2+\frac{73}{40},
\]

contradicting (6). This excludes every outer-owner pose.

### 5.2. The inner, southwest tip owns BC

Reflect vertically and interchange B,C. The same chart (14)--(17)
now has h=s, upper P=(-s,s), lower Q=(-s,-r), and the two leaf
directions east and south. The cycle y-force is strictly positive.
The same origin-moment elimination therefore gives

\[
                       r ad>sbc,
                 \qquad \tan\psi<\frac rs\tan\phi.
\tag{24}
\]

The upper concurrence is \(q_B=P+j n\), j>=0. In its own frame
put \(S=s(a+b)\), \(V=s(b-a)>0\). Its coordinates are
\((S+j,V)\), and its circle corner has coordinates
\((S+1,V+U)\). Positive collinearity gives

\[
 R\le\sqrt2\left(s+\frac1{a+b}\right),\qquad
 a+b\le\frac1{R/\sqrt2-s}<\frac{340}{321}<\frac{16}{15}.
\tag{25}
\]

For the rational bound, use
\(R/\sqrt2-s> (79/40)(12/17)-9/20=321/340\).
The increasing function a+sqrt(1-a^2) on 0<a<1/sqrt(2)
exceeds 16/15 already at a=1/10. Consequently

\[
          a<\frac1{10},\quad b>\frac{99}{100},\quad
          \tan\psi<\frac32\frac{10}{99}<\frac16,
          \quad c<\frac16.
\tag{26}
\]

Both normal circle coordinates in (16) are less than 8/5:
\(X_B<1+(9/20)(16/15)\) and
\(X_C<1+9/20+(3/5)(1/6)=31/20\).
Since R^2>39/10, both transverse coordinates exceed 11/10.
Their sum must therefore exceed 11/5. But (16) gives exactly

\[
 Z_B+Z_C=2+r(d-b)-s(a+c)-(1-L)\rho
       <2+\frac35\frac1{100}<\frac{11}{5}.
\tag{27}
\]

This contradiction excludes the inner-owner case as well. The corner
case is now completely closed without assuming which tip owns BC.

## 6. The side case, including all means and parallel frames

Write

\[
 P=(-s,y),\quad 0<y\le r,\quad Q=(-s,-s),\quad
 n=(-a,-b),\quad k=(b,-a),\quad a^2+b^2=1.
\]

Here C owns the normal n at Q. Torque at A gives

\[
                              a>b>0.
\tag{28}
\]

The circle corner of B has positive y-coordinate, since its normal
line at P is horizontal and its concurrence is a positive radial
multiple. C's corner is southwest. The B--C normal consequently has
negative y-coordinate by (4).

Write C in the exact form

\[
                   C=Q+[0,1]n+[-\tau,1-\tau]k,
                   \qquad0<\tau<1.
\tag{29}
\]

Whenever the BC normal has positive k-projection, C's actual unique
circle corner is

\[
                         z_C=Q+n+(1-\tau)k.
\tag{30}
\]

### 6.1. B is aligned with A

Its right side is x=-s and its unique upper circle corner is
\((-s-1,H)\), where
\(H=\sqrt{R^2-(s+1)^2}>1\). Its bottom side is y=H-1.
All actual A--B means are retained.

If C owns BC, the only nonparallel downward axis is k. B maximizes
k at its right bottom vertex, with x=-s. Every point on C's
minimum-k side has x=-s-aj-b tau<-s, a contradiction. If B owns BC,
its downward normal is -e_y. C then uses the vertex Q-tau k, so

\[
                   \tau a=H-r>s,
                   \qquad \tau>as.
\tag{31}
\]

Parallel B,C frames are incompatible with C's nonaxis facing normal.
Thus these are all possibilities. By (30), put L_*=1-tau<1-as.
The increasing squared corner norm is

\[
 \begin{aligned}
 F_C(L_*)&=2s^2+1+2s(a+b)+2s(a-b)L_*+L_*^2\\
 &<F_C(1-as)\\
 &=2+2sa+s^2(1+b^2+2ab)\\
 &\le2+2s+3s^2<\frac{1403}{400}<\frac{39}{10},
 \end{aligned}
\tag{32}
\]

contradicting |z_C|=R.

### 6.2. B is tilted

Its rightmost vertex is P. Write its inward unit axes as

\[
                    u_1=(-u,v),\quad u_2=(-v,-u),
                    \qquad u,v>0,\quad u^2+v^2=1.
\tag{33}
\]

The two vertices adjacent to P have norm at most |P|+1<7/4<R,
because \(|P|^2\le s^2+r^2<9/16\). Thus B's unique circle
corner is its opposite vertex

\[
                         z_B=(-s-u-v,\ y+v-u).
\tag{34}
\]

Its y-coordinate is positive. In fact v>u. Otherwise that height is
at most r<3/5 and its horizontal absolute value is less than
\(9/20+17/12=28/15\), giving
\(|z_B|^2<173/45<39/10\). Therefore

\[
                              v>1/\sqrt2>u.
\tag{35}
\]

#### Parallel B,C frames, including every shared BC

The only possible downward BC axis not parallel to n is k.
Parallel frames then give u=b,v=a. Put Delta=y+s, so Delta>s,
and \(X=1+s(a+b)<2\). The common support-line equation gives
\(\tau=a\Delta\). With H_*=sb+ay>0, the two circle corners
have frame coordinates

\[
                  (X-b\Delta,-1-H_*),\qquad (X,1-H_*).
\]

Equality of their squared norms therefore requires

\[
 G(\Delta):=2bX\Delta-b^2\Delta^2-4a\Delta+4s(a-b)=0.
\tag{36}
\]

But G is strictly decreasing for Delta>=0, because X<2 and a>b,
while

\[
                  G(s)=bs(2X-bs-4)<0.
\]

Thus Delta>s makes (36) impossible. No shared-side mean was fixed.
This argument also covers an endpoint-only contact of parallel
support faces. Henceforth the frames are nonparallel.

#### C owns BC

Its normal from B to C is k. Maximizing k on B forces
\(au-bv>0\) and the vertex T=P+u_2; the other sign would give
P itself, which is strictly outside C's facing half-plane.
The zero case is the parallel-frame case already excluded.

Let j be T's inward n-coordinate in C. Since Delta=y+s<=1,

\[
 j=av+bu-b\Delta
    \ge av-b(1-u)
    =(a-b)v+b(u+v-1)>\frac{a-b}{\sqrt2}.
\tag{37}
\]

The concurrence is Q+j n. Put S=s(a+b), D=s(a-b)>0.
Its positive collinearity with (30) gives circle coordinates

\[
             X_C=S+1,\qquad \frac{Z_C}{X_C}=\frac{D}{S+j}
                          <\sqrt2s<\frac{13}{20}.
\]

Also \(X_C<1+(9/20)(13/9)=33/20\), using
\(\sqrt2<13/9\). Consequently

\[
 R^2=X_C^2+Z_C^2
   <\left(\frac{33}{20}\right)^2
      \left(1+\left(\frac{13}{20}\right)^2\right)
   =\frac{619641}{160000}<\frac{39}{10},
\tag{38}
\]

a contradiction.

#### B owns BC with downward-left normal u_2

The normal has positive n-projection. If its k-projection
au-bv were negative, C's support point would have x>-s,
outside B. Equality makes the normal parallel to n, forbidden by
the degree-two concurrence lemma. Thus au-bv>0 and
T=Q-tau k. On B the same point is P+u_2+eta u_1 with 0<=eta<=1.
Its horizontal coordinate gives

\[
                        \tau b=v+\eta u\ge v>1/\sqrt2>b,
\]

contradicting tau<1.

#### B owns BC with downward-right normal -u_1

This normal has positive k-projection. If au-bv>0, C would use
T=Q+n-tau k, whereas B uses P+eta u_2. Horizontal coordinates
would give eta v=a+tau b>a, hence v>a and u<b; these imply
au<bv, a contradiction. Equality is the parallel-frame case.
Thus au-bv<0, C uses T=Q-tau k, and

\[
          \eta v=\tau b,\qquad
          \Delta=\tau\left(a+\frac{bu}{v}\right)<\frac\tau a.
\]

It follows that tau>a Delta>as. The circle corner is (30), so the
same exact bound (32) again contradicts |z_C|=R.

These are all downward axes of either square. Free point normals
were removed in Section 4, and parallel frames and variable means
were handled explicitly. The side case is fully excluded.

## 7. Whole-branch conclusion

The R>=2 argument, contact-order classification, simultaneous normal
selection, both corner owners, and every side case together exclude
the entire D/D same-articulation family in (1). Combined with
`TWO_S_LEAVES_ONE_TRIANGLE_ARTICULATION.md` and
`TWO_MIXED_LEAVES_ONE_TRIANGLE_ARTICULATION.md`, this closes the
whole two-leaves-at-one-triangle-vertex attachment layout.

The length-two-chain layout is separately closed by
`TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md`. The layout with leaves at
two distinct triangle vertices is not closed by this manuscript and
remains an obligation for the parent C1.3.b2 cell. No Lean compilation,
CI, numerical certificate, or omitted completion square is used here.
