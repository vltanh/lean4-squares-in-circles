# A complete pressure sign for tip-owned end-triangle contacts

**Status: complete hand implication; root and separate independent full hand audits passed.**
Work in
\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
Let A,B,C be an actual triangle of interior-disjoint unit squares.
The two bodies B,C are positive degree-two circle-loaded tips: their
only positive pair edges are AB, BC, AC. A may have further positive
edges. Suppose its AB and AC intersections are singleton points,
each lying in the relative interior of a side of the corresponding
tip B or C. All physical one-/two-circle-corner masks and all splits
of the two circle weights are retained.

Write c_A for the center of A and
\[
 M=2\sum_{z\text{ on }B\text{ or }C}\lambda_z z
\tag{2}
\]
for the total circle-force vector of the two tips. In the compatible
selected certificate,
\[
                              \boxed{c_A\cdot M>0.}
\tag{3}
\]

Consequently a bowtie whose four articulation contacts all satisfy
this tip-owned singleton premise is impossible: its two block
resultants are opposite, whereas (3) makes their scalar products
with the same c_A strictly positive.

This theorem does not yet cover an articulation-owned side axis
or a positive-length articulation contact. It is a whole owner
branch, with arbitrary poses and circle masks, rather than an angle
or radius slice of that branch.

## 1. The articulation applications are adjacent vertices

Each application is a vertex of A, since its other body supplies
a relative side-interior point. They cannot be the same vertex:
the tangent sector of A has angle90 degrees and each of the two
relative side-interior neighbors occupies a half-plane locally.
Three such interior sectors cannot be disjoint.

They cannot be opposite vertices either. Here is a radius-free
argument which also retains arbitrary actual supporting normals.
If P,Q are opposite A vertices, choose orthonormal inward axes
v,w at P, so Q=P+v+w. An outward normal n of A at P, strict in its
vertex cone, has n dot v,n dot w<0 and
\[
                        n\cdot(P-Q)\ge1.
\tag{4}
\]
A strict outward normal m at the opposite vertex has m dot n<0.
The support-span lemma in UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md
therefore gives
\[
                  \max_{x\in C}n\cdot(x-Q)<1.
\]
But B lies in n dot x>=n dot P. Equation (4) makes B and C
closed-disjoint, contrary to their contact.

The normals are indeed strict in the A vertex cones: if a
tip-owned normal were an A side axis, that A side and the tip side
would share a nondegenerate segment at their relative-side-interior
application, contrary to the singleton premise.

After a rigid rotation/reflection, write
\[
\begin{split}
 A&=[P_x,P_x+1]\times[P_y-1,P_y],\\
 Q&=P-e_y,\qquad c_A=P+(1/2,-1/2),\\
 n&=(-b,a),\quad v=Jn=(-a,-b),\\
 m&=(-d,-c),\quad k=Jm=(c,-d),\\
 a&=\sin\phi,\ b=\cos\phi,\quad
 c=\sin\psi,\ d=\cos\psi,\qquad0<\phi,\psi<\pi/2.
\end{split}
\tag{5}
\]
Here n,m point from A into B,C, respectively. Thus P is on the
minimum-n side of B and Q on the minimum-m side of C.

## 2. If at least one tip has one physical circle corner, BC is owned

If BC were a point-only vertex/vertex contact, use a tip with one
physical circle corner. Its application to A is a fixed relative
side-interior point. Its BC application is a different vertex.
GENERAL_FIXED_TIP_NORMAL_SELECTION.md removes the free BC normal
simultaneously before multiplier extraction. No side mean is fixed
by this argument.

Thus BC has a side-axis owner. Interchange B,C and reflect vertically
if necessary so that B owns that normal. Put
\[
 K=ad+bc=\sin(\phi+\psi)>0,\qquad
 L=bd-ac=\cos(\phi+\psi),
\]
so
\[
                      m=Ln+Kv,\qquad k=-Kn+Lv.
\tag{6}
\]

A BC normal parallel to n is impossible. The two positive pair
forces at B would then be parallel, and their nonzero circle
resultant would be parallel to a side axis. The parallel-force
classification gives radial S, with the contacts on its inner side:
an outer-side contact cannot fit a further unit in the disk.
The horizontal-inner-face lemma of C7_FORCE_POLYGON.md excludes
a circle-touching neighbor across that inner side. The same argument
excludes a BC normal parallel to m at C. This includes variable means
on a shared side and does not suppose that P dot n or Q dot m is
positive.

The remaining B-owned direction is v or -v. The choice -v is
impossible. It would give
\[
 T-P=j n-u v,\qquad0\le j,u\le1,
\]
while the outward normal v at C has positive m-component K.
Therefore T is on C's maximum-m side and
\[
             m\cdot(T-P)=1+c>1,
\]
contradicting Lj-Ku<=max(L,0)<=1.

Hence the BC normal is v. Its application minimizes m on C.
If L=0, C's two forces are parallel, already excluded. If L<0,
that application is Q+r k with 0<r<1, and
\[
                  n\cdot(T-P)=-a-Kr<0,
\]
contradicting B's minimum-n side at P. Thus L>0, and the complete
chart is
\[
\begin{split}
 T&=Q-rk,\qquad0<r<1,\\
 j&=Kr-a\in[0,1],\qquad
 U=1-b+Lr\in(0,1),\qquad V=1-r\in(0,1),\\
 B&=P+[0,1]n+[-U,1-U]v,\\
 C&=Q+[0,1]m+[-r,1-r]k.
\end{split}
\tag{7}
\]
In particular r>=a/K. Every actual endpoint allowed by this enlarged
chart is kept; endpoints which the original strict convention already
forbids only enlarge the domain of the estimates below.

Let mu,nu,gamma>0 be the AB,AC,BC magnitudes. The tip circle
resultants are
\[
                 F_B=\mu n-\gamma v,\qquad
                 F_C=\nu m+\gamma v.
\tag{8}
\]
Their component signs show that
\[
                  z_B=P+n-Uv,\qquad z_C=Q+m+Vk
\tag{9}
\]
are actual positive-weight circle corners. In a zero center-coordinate
tie, the specified extremal corner has positive weight because the
corresponding component of (8) is strict.

The two tip contact-line intersections are
\[
                 q_B=P+jn,\qquad q_C=Q+(Kr/L)m.
\tag{10}
\]
The general boundary-neighbor concurrence lemma in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma2.1, says each q is
a positive multiple of its tip's nonzero circle resultant. This
conclusion is valid also for two circle corners; no interior-location
claim for q in that case is needed.

## 3. A nonowner radial tip already gives the pressure sign

Suppose C has two physical circle corners. Put
\[
                     D=\sqrt{R^2-1/4}-1>\frac9{10}.
\tag{11}
\]
Its positive m- and k-circle components leave two possible radial
frames: radial direction m or radial direction k.

The tangential-facing possibility, radial direction k, would give
\[
                     Q\cdot m=-1/2,\qquad Q\cdot k=D+r.
\]
Using P=Q+e_y and j=Kr-a in (10),
\[
                        q_B\cdot n=-L/2-KD<0.
\]
This contradicts positive concurrence and F_B dot n=mu>0.
Therefore C is radial in direction m and
\[
                       Q\cdot m=D,\qquad Q\cdot k=r-1/2.
\tag{12}
\]

Immediately
\[
                c_A\cdot m=D-(c+d)/2>D-1/\sqrt2>0.
\tag{13}
\]
We prove c_A dot n>0 as well. Set
\[
\begin{split}
 X&=z_B\cdot n=1+a+LD-K(r-1/2),\\
 Z&=-z_B\cdot v=1+L/2-KD.
\end{split}
\tag{14}
\]
Both are at least1/2 and X^2+Z^2=R^2. If c_A dot n<=0, then
\[
 X\le1+(a+b)/2\le1+1/\sqrt2,\qquad
                     2LD\le K+b-a\le K+1.
\tag{15}
\]

For fixed D>9/10, write K=sin sigma,L=cos sigma with
0<sigma<pi/2. The last inequality in (15) puts sigma at or above
the unique solution of 2D cos sigma=1+sin sigma, namely
\[
 K_0=\frac{4D^2-1}{4D^2+1},\qquad
 L_0=\frac{4D}{4D^2+1}.
\]
The function 1+L/2-KD decreases strictly in sigma, so
\[
 Z\le1-\frac{D(4D^2-3)}{4D^2+1}<\frac{19}{20}.
\tag{16}
\]
For the strict last inequality, the subtracted function increases
for D>=9/10: its derivative numerator is
16D^4+24D^2-3>0, and its value at9/10 is27/530>1/20.

But R^2=(D+1)^2+1/4>193/50. Therefore
\[
 X^2>193/50-(19/20)^2=\frac{1183}{400}
       >\left(1+\frac1{\sqrt2}\right)^2,
\tag{17}
\]
where the last comparison follows from sqrt(2)<17/12.
This contradicts (15). Equations (13) and c_A dot n>0 give
c_A dot M=c_A dot(mu n+nu m)>0.

This covers C's entire physical two-corner mask, independently of B's
mask and independently of either split of C's circle weights.

## 4. An owner radial tip also gives the sign

We may now suppose C has exactly one physical circle corner.
Take C's torque about that corner z_C in (9). Its two pair forces
give exactly
\[
                       \nu V=\gamma(L-K).
\tag{18}
\]
Thus
\[
                         L>K>0,\qquad\phi+\psi<\pi/4.
\tag{19}
\]

If B has two physical circle corners, its positive n- and negative
v-circle components allow radial direction n or -v.
In the tangential-facing alternative, radial direction -v,
\[
                     P\cdot n=-1/2,\qquad P\cdot v=U-(D+1).
\]
Positive concurrence in (10) and F_B dot n>0 imply j>1/2.
A direct projection of z_C then gives
\[
                    z_C\cdot k=1-LD+K(1/2-j)<1-LD<1/2.
\tag{20}
\]
The last inequality uses D>9/10>1/sqrt(2) and L>1/sqrt(2).
It contradicts the necessary absolute coordinate bound at a circle
corner. Thus B is radial in direction n, and
\[
                         P\cdot n=D,\qquad P\cdot v=U-1/2.
\]
Hence
\[
\begin{split}
 c_A\cdot n&=D-(a+b)/2>0,\\
 c_A\cdot(n+v)&=D+U-1/2-a\\
 &\ge D+1/2-b+a(L/K-1)>D-1/2>0.
\end{split}
\tag{21}
\]
Here U>=1-b+La/K follows from r>=a/K.

In B's frame M=(mu+nu L)n+nu K v, whose two coefficients are
positive and whose v coefficient is smaller than its n coefficient.
If c_A dot v>=0, (21) gives the sign directly. If it is negative,
the second line of (21), together with that coefficient comparison,
gives the same strict sign. All weights of B's radial mask remain.

## 5. The complete unique/unique weighted-corner estimate

It remains to consider one physical circle corner on each tip.
Torque at z_B and (18) yield
\[
                   \frac{\mu}{\gamma}=\frac{1-j}{U}=:\beta,
             \qquad\frac{\nu}{\gamma}=\frac{L-K}{V}=:\chi.
\tag{22}
\]
Let
\[
 w_B=\sqrt{\beta^2+1},\qquad
 w_C=\sqrt{\chi^2+2K\chi+1}
     =\sqrt{L^2+\frac{(L-Kr)^2}{V^2}}.
\tag{23}
\]
Since the two corner norms equal R, their positive circle multipliers
are proportional to w_B,w_C.

Relative to c_A, their squared distances are
\[
\begin{split}
 G_B&=|z_B-c_A|^2
       =\frac32+a+b+(b-a)U+U^2,\\
 G_C&=|z_C-c_A|^2
       =\frac32+c+d+(d-c)V+V^2.
\end{split}
\tag{24}
\]
We prove the uniform, deliberately nonsharp bound
\[
                 w_B G_B+w_C G_C
                  <\frac{39}{10}(w_B+w_C).
\tag{25}
\]
It uses the whole domain (7),(19), without solving a circle equality
or choosing a pose interval.

For 0<=t<=1 put
\[
                   f(t)=\frac32+t^2+\sqrt{2+2t^2}.
\]
Cauchy gives G_B<=f(U), G_C<=f(V). The function is increasing and
convex, f(1)=9/2, and f(3/4)<77/20<39/10. Its chord on
[3/4,1] consequently gives
\[
                f(t)\le\frac{19}{10}+\frac{13}{5}t.
\tag{26}
\]
Also
\[
                  U\le1-bV,\qquad b>1/\sqrt2.
\tag{27}
\]
Thus G_B and G_C cannot both exceed39/10.

If neither exceeds39/10, their weighted sum is strictly below the
target: equality of both would require U,V>3/4, contradicting (27).
Consider the two remaining cases.

### 5.1. If G_B>39/10

Then U>3/4, V<sqrt(2)(1-U), and w_C>=1.
Since K/L>=a/b,
\[
 \beta
 =\frac{1+a-(K/L)(U+b-1)}U
 \le\frac{1+(a/b)(1-U)}U
 \le\frac{2-U}U.
\tag{28}
\]
For U>=10/13 the function
\[
             \frac{13U-10}{5}\sqrt{1+(2/U-1)^2}
\]
increases. Its derivative has the positive sign of
13U^3-13U^2-10U+20, which is at least
10-13/4>0 on this interval. Equation (26) bounds
w_B(G_B-39/10) by this function.

If U<=9/10, the bound is at most17 sqrt(202)/450<17/30.
Meanwhile V<sqrt(2)/4 gives
\[
                 G_C< f(\sqrt2/4)=25/8,
\]
so 39/10-G_C>31/40>17/30.
If U>=9/10, the same increasing function is at most
3sqrt(2)/5<9/10, whereas V<sqrt(2)/10 gives G_C<3.
Again the deficit of G_C is greater than9/10.
Together with w_C>=1, both intervals prove (25).

### 5.2. If G_C>39/10

Then V>3/4 and r<1/4. Since a<=Kr and K<1/sqrt(2),
\[
                  U=1-b+Lr\le r+r^2/2<3/10.
\tag{29}
\]
Thus G_B<f(3/10)<31/10 and w_B>=1. Equation (23) gives
\[
                            w_C\le\sqrt{1+1/V^2}.
\tag{30}
\]
If V<=9/10, equations (26),(30) give
w_C(G_C-39/10)<=17/30, less than the G_B deficit4/5.
If V>=9/10, (29) gives U<=21/200<11/100 and G_B<3,
while w_C<3/2 and G_C-39/10<=3/5. The weighted C surplus
is then less than9/10, again below the B deficit.
This completes (25).

Let Lambda be the sum of the two positive circle multipliers.
Expansion around c_A gives the exact identity
\[
 R^2=-|c_A|^2+\frac{c_A\cdot M}{\Lambda}
       +\frac{\lambda_B|z_B-c_A|^2+
                    \lambda_C|z_C-c_A|^2}{\Lambda}.
\tag{31}
\]
If c_A dot M<=0, equation (25) would imply R^2<39/10.
But (79/40)^2=39/10+1/1600. This proves (3) in the last
unique/unique case.

## 6. Two physical radial tips do not require a BC normal selection

The preceding generic BC selection only required one unique physical
circle corner. Complete the physical two/two case directly.

Every two-circle-corner unit is radial S, with inner radial coordinate
D>9/10 from (11). Its outer face admits no unit neighbor by width;
its inner face admits no circle-touching neighbor by
C7_FORCE_POLYGON.md, Lemma2.1. At a contact between two radial S
units, a SAT side owner must therefore be a tangential side.

In one unit's radial frame, a vertex of the other on that side cannot
be an outer circle vertex. The two radial directions have an acute
angle: each is proportional to the average of its two physical circle
corners, and all cross-body corner scalar products are positive.
Choose their positive angle theta after reflection. The upper inner
vertex would give D sin theta+(1/2)cos theta=1/2; its nonzero
half-angle root is tan(theta/2)=2D>1, outside the acute range.
The lower inner vertex instead gives
D sin theta-(1/2)cos theta=1/2. Its retained root has
tan(theta/2)=1/(2D), and the other coordinate is exactly D.
The additional parallel root theta=pi has other coordinate -D and
cannot lie on the tangential side whose radial coordinate is in
[D,D+1]; the coincident-direction endpoint supplies no distinct unit.
Thus the contact is an inner vertex of both units. After rotation
and reflection, the two radial directions and the
common point are
\[
 e_+=(c_0,s_0),\quad e_-=(c_0,-s_0),\quad
 c_0=D/\rho,\quad s_0=1/(2\rho),\quad
 \rho=\sqrt{D^2+1/4},\quad O=(\rho,0).
\tag{32}
\]
The squares have inward tangent directions
t_+=(-s_0,c_0), t_-=(-s_0,-c_0) and forms
\[
 B=O+[0,1]e_+ +[0,1]t_+,\qquad
 C=O+[0,1]e_- +[0,1]t_-.
\tag{33}
\]
Here c_0>s_0>0.

A relative-side-interior application of A to B cannot be on B's
outer radial face. It cannot be on the near tangential face
O+[0,1]e_+ either: the outside of that face is locally the exterior
pocket between the touching boundary pair B,C. A would lie in that
pocket, contrary to CONTACT_TRIANGLE_AND_BOUNDARY_POCKETS.md,
Theorem4.1.

Nor can it lie on the far tangential face
O+t_+ +[0,1]e_+. Every point of C has t_+-projection at most
t_+ dot O, with equality only at O, since
\[
                 t_+\cdot e_-=-2c_0s_0<0,\qquad
                 t_+\cdot t_-=s_0^2-c_0^2<0.
\]
The application to C is a relative side-interior point, hence not O.
Its distance from any point of that far B face is therefore strictly
greater than one. But the two A applications are adjacent A vertices,
at distance exactly one. This is impossible.

Only B's inner radial face remains. Reflection gives the same conclusion
for C. Their actual inward directions from A are consequently e_+,e_-,
and
\[
             c_A\cdot e_\pm
               =D-H_A(e_\pm)\ge D-\frac1{\sqrt2}>0.
\tag{34}
\]
Any positive combination has positive scalar product with c_A.
This proves (3) for all two/two weight splits, with the original free
BC normal untouched.

## 7. Exact scope and the remaining bowtie work

The three circle-mask cases in Sections3--6 exhaust every physical
mask under the tip-owned singleton articulation premise. No arbitrary
completion square was discarded, and none is needed for this owner
branch exclusion.

For a bowtie, sum the two tip force balances in each block. Their
interface resultants on A are M_1,M_2, their origin moments are zero,
and A is circle-clear, so M_1+M_2=0. Applying (3) to both blocks gives
a contradiction whenever all four articulation contacts have the
premise of this theorem.

The full bowtie C2.33.b0 remains open until the articulation-owned
and shared-side alternatives are either given the same pressure sign
or otherwise excluded/completed. The identity (31) is a possible
uniform exit for those alternatives; no unproved extension of (25)
to them is asserted. Extra positive pair forces at a tip are also
outside the degree-two premise.

No Lean compilation, CI, numerical certificate or post-extraction
normal adjustment is used.
