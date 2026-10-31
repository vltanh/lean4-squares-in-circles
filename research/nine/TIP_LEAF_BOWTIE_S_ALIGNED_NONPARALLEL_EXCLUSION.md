# An aligned S leaf at a bowtie tip: the entire nonparallel articulation is impossible

**Status: complete whole-interface hand exclusion; root and separate
independent full hand audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\qquad \delta=D-1<\frac1{60}.
\tag{1}
\]
The exact positive graph is H–A–B–H, H–C–E–H, and A–L.
The actual radial S leaf L points east, and A is aligned:
\[
                    A=[\delta,\delta+1]\times[h-1,h],
                         \qquad0\le h\le1.
\tag{2}
\]
A has exact degree three, H degree four, and B,C,E degree two.
All three additional physical squares remain in place.

**Theorem.** The two positive triangle forces at A cannot be
nonparallel. The proof retains every H/B frame, every circle
mask, every contact owner and all actual application means.
The parallel A interface is a separate whole branch.

## 1. The complete aligned-root feature and selection cover

The degree-two triangle tips B,C,E are loaded by the usual
unit-transmitter obstruction. H is physically clear, since H,C,E
cannot be a boundary triangle; A is clear by its actual leaf.

At A, a horizontal triangle normal would force the other normal
horizontal. A vertical A-owned normal makes the other vertical
component have the same sign by the unit-triangle side-normal
lemma, contradicting vertical balance. Thus both normals in
the present nonparallel branch strictly expose A vertices,
with opposite vertical signs.

They cannot use the same vertex or the same horizontal side.
Opposite vertices are excluded by the physical unit-triangle
support-span lemma. If both were right vertices, both horizontal
components and the leaf force would point east. Consequently
the actual ports are the two left vertices. Positive horizontal
and vertical balances together with torque then give 0<h<1.

The fixed A-star determinant from
D_LEAF_GENERIC_CONTACT_SELECTION.md applies without change.
Indeed, for actual vertices p_1,p_2 and normals n_1,n_2, its
necessary equation is
\[
 (n_1)_y\det(p_2,n_2)-(n_2)_y\det(p_1,n_1)=0.
\tag{3}
\]
The coefficient of a free first normal's x-component is
(n_2)_y(p_1)_y, which is nonzero here. The two physical vertices
are distinct junctions. Prelisting these aligned S stars along
with the existing D stars therefore removes every free A edge
compatibly before multiplier extraction. No neighbor load or
degree equation was used in that selection.

Thus both ports belong to relative interiors of sides owned
by their respective neighbors. Reflect vertically to put B at
the upper vertex. Write
\[
\begin{aligned}
 P&=(\delta,h),& n&=(-b,a),& v&=Jn=(-a,-b),\\
 Q&=(\delta,-w),& m&=(-d,-c),& k&=Jm=(c,-d),\\
 w&=1-h,& a,b,c,d&>0,&a^2+b^2&=c^2+d^2=1,\\
 K&=ad+bc>0,& L&=bd-ac.
\end{aligned}
\tag{4}
\]
Here n points A to B and m points A to H. Normalizing the
positive leaf magnitude to one, the true A equations give
\[
             \mu=\frac cK,\quad \nu=\frac aK,\quad
             h=\frac{ad}{K},\quad w=\frac{bc}{K}.
\tag{5}
\]
In the H frame,
\[
                  n=Lm-Kk,\qquad v=Km+Lk.
\tag{6}
\]
Let g be the B-to-H normal, T its actual application and
gamma>0 its magnitude. The actual B and H equations are
\[
               F_B=\mu n-\gamma g,\qquad
               M:=F_C+F_E=\nu m+\gamma g.
\tag{7}
\]
The H equation remains degree four throughout.

## 2. Every nonnegative AH support is already impossible

Put
\[
                  q_m=Q\cdot m=-\delta d+wc,\qquad
                  q_k=Q\cdot k=\delta c+wd.
\tag{8}
\]
Because H owns AH, the physical H–A–B triangle gives
m·g>=0. Hence
\[
                               M\cdot m>0.
\tag{9}
\]

Suppose first q_m>=0. For a nonparallel C/E interface at H,
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md gives its root
intersection q'=-tM, t>0, and the proper outward relations
at both actual ports. Thus q'·m<0.

A port on H's minimum-m side or one of its endpoints has
outward normal with nonpositive m-component. Its proper
relation could not reach the nonnegative coordinate q_m
from q'·m<0. A contact owned by a tangential H axis would
have m-coordinate exactly q'·m<0, outside H. Therefore
both actual C/E ports are on H's maximum-m side.

If the C/E root normals are parallel, their common direction
is M/|M|, whose m-component is positive by (9). Both ports
are again on the maximum-m side, including a coincident vertex.

That side has height 1+q_m>=1. The complete all-mask theorem
END_TRIANGLE_HIGH_FACE_EXCLUSION.md excludes the end triangle.
In particular every delta<=0 case has now been covered,
because w,c>0.

It remains only to consider
\[
                  0<\delta<1/60,\qquad -\delta<q_m<0.
\tag{10}
\]
Here R>sqrt(17)/2>103/50. Every point of B has norm at least
r=R-sqrt2, so
\[
          \sqrt{\delta^2+h^2}\ge r>\frac{129}{200},
                         \qquad h>\frac{16}{25}.
\tag{11}
\]
For the last inequality use delta<1/60 and
(129/200)^2-1/3600>(16/25)^2. The preceding r bound follows
from sqrt2<283/200.

## 3. The entire high-radius B mask and frame sum

In B's own frame define
\[
        p_n=-\delta b+ha,\quad B_0=\delta a+hb>0,\quad
                   X=1+p_n.
\tag{12}
\]
Its center has n-coordinate p_n+1/2>0. Since p_n<1<D,
B cannot be radial along n; the transverse and negative
radial axes are impossible as well. Thus B has one physical
circle corner.

The proper loaded-tip concurrence applies when B's pair
forces are nonparallel. A parallel B pair would force its
circle vector along n; a unique circle corner cannot be
parallel to its own side axis. Thus the pair is nonparallel,
and its proper line through P has constant v-coordinate
-B_0. Its unique corner therefore is
\[
              Z_B=Xn-Yv,\qquad Y>0,\qquad X^2+Y^2=R^2.
\tag{13}
\]
Write
\[
 B=P+[0,1]n+[-\rho,1-\rho]v,\quad0<\rho<1,\qquad
                         Y=B_0+\rho,\quad V=1-\rho.
\tag{14}
\]
Its proper advance is
\[
                    A_B=\frac{X B_0}{Y}-p_n\ge0.
\tag{15}
\]

We first prove L>0. Otherwise (5) is equivalent to a^2>=h.
Then
\[
 p_n\ge h\sqrt h-\delta\sqrt{1-h},\qquad
 |P|=\sqrt{h^2+\delta^2}\le h+\frac1{4608}.
\tag{16}
\]
Equation (15), after squaring positive quantities, requires
\[
                         p_n(R-|P|)\le |P|.
\tag{17}
\]
The function sqrt(h)(103/50-h) is concave on [16/25,1]
and is at least53/50 there. Using (16), the left side minus
the right side of (17) is strictly greater than
\[
 \frac{24}{625}-\frac{71}{5000}-\frac1{2304}
                      =\frac{34223}{1440000}>0.
\tag{18}
\]
Indeed the three terms respectively bound
h[sqrt(h)(103/50-h)-1],
delta sqrt(1-h)(103/50-h), and (1+p_n,lower)/4608;
the lower expression for p_n in (16) is at most1.
This contradiction proves
\[
                                L>0,\qquad a^2<h.
\tag{19}
\]

We also need the uniform bound a<19/20. If a>=19/20,
then h>a^2>=361/400, b<5/16, and
\[
        p_n>\frac{19h}{20}-\frac1{192},\qquad
                     |P|<h+\frac1{6400}.
\]
The resulting lower bound for the left side minus the right
side of (17) is the concave quadratic
\[
 \left(\frac{19h}{20}-\frac1{192}\right)
       \left(\frac{103}{50}-h-\frac1{6400}\right)
                        -h-\frac1{6400}.
\]
Its two endpoint values at h=361/400 and h=1 are respectively
1069997/12800000 and 2407/2048000, both positive. Therefore
\[
                                  a<19/20.
\tag{20}
\]

## 4. Exactly two transverse contact owners remain

The side-normal triangle lemma at B,H gives
\[
                           n\cdot g\le0,\qquad m\cdot g\ge0.
\tag{21}
\]
With K,L>0, a B-owned axis can only be g=v, and an H-owned
axis can only be g=k. This includes shared-side alternatives;
no opposite owner sign survives (21).

A free BH normal is removed by
GENERAL_FIXED_TIP_NORMAL_SELECTION.md. B is unique, P lies
in a relative side interior of B, and a free BH point is a
different B vertex. The two actual applications are fixed
distinct points, so the full fixed-tip selection applies.
It is compatible with the A-star selection of Section 1.

Consequently g=v or g=k exhausts the entire surviving domain.

The H square has the full actual representation
\[
                   H=Q+[0,1]m+[-\sigma,1-\sigma]k,
                                  \qquad0<\sigma<1.
\tag{22}
\]

### 4.1. The B-owned transverse contact

For g=v, its actual point satisfies
\[
             T=P+t n+Vv=Q-\sigma k,\qquad0\le t\le1.
\]
Equating the two H coordinates gives
\[
                         t=\frac{c-KV}{L},\qquad
                         \sigma=\frac{b-V}{L}.
\tag{23}
\]
Thus these are actual contact identities, including t=0,1.

### 4.2. The H-owned transverse contact

For g=k, B's maximum-k point is its minimum-n/maximum-v
vertex. Therefore
\[
             T=P+Vv=Q+j m-\sigma k,\qquad0\le j\le1,
\]
and
\[
                            j=KV-c,\qquad \sigma=d-LV.
\tag{24}
\]
Again every possible H-side mean endpoint is retained.

## 5. One exact corner bound covers both owners

Write the actual B circle corner in the H frame as
\[
                         Z_B=Zm-Wk,\qquad W>0.
\tag{25}
\]
The strict negative k-coordinate follows from (7),(6) for both
g=v and g=k. We claim
\[
                                  |Z|<1.
\tag{26}
\]

For g=k, (24) and Z_B=T+n-v give
\[
                Z=L-K(1-V)-hc-\delta d<L<1.
\]
Also F_B·m=mu L>0, so Z>0. This proves (26).

For g=v, Z_B=T+(1-t)n-v gives
\[
                         Z=q_m+(1-t)L-K.
\tag{27}
\]
Its upper bound is
\[
 Z\le q_m+L-K
   =d(b-a-\delta)+c(w-a-b)<1.
\tag{28}
\]
For the lower bound we prove K-q_m<1.

Put
\[
                 S=\sqrt{h^2b^2+w^2a^2}.
\]
Equations (5) give
\[
 K=\frac{ab}{S},\quad c=\frac{wa}{S},\quad d=\frac{hb}{S},
 \qquad
 K-q_m=\frac{ab-aw^2+\delta hb}{S}.
\tag{29}
\]
If a<=1/2, then K<=a/h<4/5, so K-q_m<K+delta<49/60.

If 1/2<=a<19/20, (19) gives w<b^2 and S<=b. Hence
\[
\begin{aligned}
 S-ab+aw^2-\delta hb
 &\ge\frac{(w-b^2)^2}{2b}+aw^2-\delta b\\
 &\ge\frac{ab^4}{1+2ab}-\delta b.
\end{aligned}
\tag{30}
\]
The last inequality is the exact minimum of that quadratic in w.
For b=sqrt(1-a^2), the function
\[
                              \frac{ab^3}{1+2ab}
\]
is strictly decreasing on [1/2,19/20]: its derivative has the
sign of 1-4a^2-4a^3b<0. At a=19/20 it is greater than1/60,
because
\[
                 1463\sqrt{39}>8000,\qquad
                 1463^2\cdot39-8000^2=19474391>0.
\]
Thus (30) is strictly positive. Equation (29) proves
K-q_m<1, and (27) proves Z>-1. This completes (26).

By (13),(25),(26),
\[
                               W>\sqrt{R^2-1}\ge\sqrt{13}/2.
\tag{31}
\]
Let p_k=q_k+1-sigma be H's maximum k-coordinate. In (24),
\[
                         p_k=1+K+L-W,
\]
whereas in (23),
\[
                         p_k=1+(1-t)K+L-W.
\]
Since q_k=delta c+wd>0 and sigma<1, both formulas yield
\[
       0<p_k<1+\sqrt2-\sqrt{13}/2<\frac{367}{600}.
\tag{32}
\]
For the last strict comparison, use
sqrt2<577/408, sqrt13>137/38, and
367/600-[1+577/408-137/76]=2/24225>0.

The lower-inner H vertex has coordinates (q_m,p_k).
By (10),(32), its norm is less than
\[
       \sqrt{(1/60)^2+(367/600)^2}
                         <129/200<r.
\tag{33}
\]
It therefore belongs to no boundary unit.

## 6. The opposite petal is forced onto one high H side

In both transverse-owner cases, (7),(6) put M strictly in
the positive m,k quadrant. Its unique maximizing H vertex is
\[
                           F=(q_m+1,p_k).
\tag{34}
\]

If the C/E root normals are parallel, both actual applications
are F and hence lie on H's maximum-m side.

Otherwise the end-triangle theorem supplies the negative
concurrence q'=-tM. The both-H-owned perpendicular C/E alternative
is already excluded by BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md;
for every other nonparallel alternative, Section 4 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md supplies an actual
maximizing port, necessarily F.
Its other application is exhaustively as follows.

* The same vertex would make q'=F, impossible because q'·m<0
  and F·m>0.
* The opposite strict vertex is forbidden by the unit-triangle
  support-span lemma.
* The adjacent lower-inner vertex is impossible by (33).
* The other adjacent vertex belongs to the maximum-m side.
* An H-owned normal -m or -k has negative dot product with M,
  contrary to the unit-triangle nonobtuse-normal consequence.
* An H-owned +k side application has m-coordinate q'·m<0.
  If it belongs to H at all, that coordinate lies in [q_m,0).
  Equation (33) therefore excludes it as a boundary contact.
* An H-owned +m application belongs to the maximum-m side.

These statements retain every shared-side mean, including all
endpoints. Thus both actual C/E applications lie on the single
side
\[
                         m\cdot x=1+q_m>1-\delta>59/60.
\]
END_TRIANGLE_HIGH_FACE_EXCLUSION.md excludes the whole petal.

Sections 1--6 exhaust the aligned S articulation with nonparallel
A forces. H has retained its true four-force equation, B its
actual degree-two equation, and C,E their complete end-triangle
equations. No extra square, side mean or circle-weight endpoint
has been dropped. The parallel A wall remains a separate branch.
No numerical pose sampling, Lean compilation or CI is used.

