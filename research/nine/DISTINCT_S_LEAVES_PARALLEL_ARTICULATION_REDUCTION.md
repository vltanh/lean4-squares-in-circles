# Every remaining distinct-S/S triangle has a parallel articulation

**Status: complete hand reduction; root and separate independent full hand audits passed.**

Consider the entire remaining C1.3.b2 family: a positive triangle
A,B,C, with radial S leaves at A and B, in
\[
             \frac{\sqrt{17}}2<R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]
The audited domain, port-order and corner-mask theorems give:

* A,B are physically circle-clear and each meets \(D_\delta\), where
  \(d=\sqrt{R^2-1/4}-1=1+\delta\) and \(0<\delta<1/60\).
* C is loaded with exactly one physical circle corner.
* The common triangle moment is nonzero. C's pair forces are
  nonparallel, with concurrence a positive multiple of its circle corner.
* At either nonparallel articulation its concurrence is a positive
  multiple of its radial leaf direction.
* At each articulation its two cycle applications and leaf application
  are distinct. All genuine side means remain.

These are TRIANGLE_DISTINCT_LEAVES_DOMAIN.md,
TRIANGLE_DISTINCT_LEAVES_PORT_ORIENTATION.md, and
DISTINCT_S_LEAF_CORE_AND_CORNER_MASK.md.

**Theorem.** A compatible necessary certificate can be selected so
that every such S/S core has at least one articulation with parallel
cycle forces. Its leaf is aligned with its frame. After rotation
and labeling the whole surviving domain has
\[
 A=[\delta,d]\times[t-1,t],\quad 0<t<1,\qquad
 n_{AB}=n_{AC}=-e_x,
\tag{2}
\]
with actual wall mean heights \(y_B>0>y_C\).

All four completion squares remain. The nonempty wall chart (2) is
classified in DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md; its universal
capacity of at most three is proved in the upper/lower capacity sources
and assembled in TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md. The audited exact
positive control belongs to (2).

## 1. Two force-only choices retain every shared mean

The external vectors are positive multiples of the two leaf directions
and C's unique circle corner. These three directions are distinct and
noncollinear. Normalize one leaf magnitude. Global force balance fixes
the other two magnitudes, hence three physical vectors \(G_A,G_B,G_C\)
whose sum is zero, independently of pair normals and side means.

For the directed AB force f, the other pair vectors are
\[
                  F_{AC}=-G_A-f,\qquad F_{BC}=f-G_B.
\tag{3}
\]
Nonparallel actual AC and BC normals determine f uniquely. A zero f
cannot give a positive AB edge; otherwise a free AB normal must be
parallel to one fixed vector. Its finitely many directions can be
avoided before multiplier extraction. If AC or BC is free too, fix
nonparallel values of those normals and vary the AB parameter:
the necessary determinant is nonzero on the product of the open
normal intervals. The parallel-C alternative is already impossible.

The AB parameter is independent of every other free parameter used
here. A singleton AC or BC contact at the AB point would give
coincident cycle applications at A or B, excluded by the port theorem.
A shared AC/BC side has a fixed normal regardless of its mean.
Matched opposite-pair parameters at a four-square junction do not
identify two triangle-edge parameters: the two opposite pairs are
disjoint, whereas triangle edges share a body.

Thus AB may be selected to have an actual side-axis owner, including
a positive-length shared side. We also use this immediate special
case of (3): if AB and AC have fixed nonparallel side-axis normals,
then the BC force is fixed up to scale, so a free BC vertex normal
can be avoided independently of all shared means.

Prelist the finitely many physical five-body assignments, radial
leaf directions, unique C corners, fixed axes and point-normal
variables. The stated nonzero determinant conditions have open
dense complements in the allowed intervals. Impose them together
with the previous strict, nonradial, matched-junction and finite
generic choices. Uncrossing preserves surviving point normals and
adds only shared-side forces; thinning only deletes atoms. No
choice uses extracted weights or an unknown mean.

For two distinct singleton C applications we also use the existing
GENERAL_FIXED_TIP_NORMAL_SELECTION.md: a unique-circle-corner
degree-two body has no free incident point normal, without a
boundary-neighbor premise.

## 2. An owned AB edge with neither articulation parallel

Suppose neither articulation has parallel cycle forces. By Section1
exchange A,B so A owns AB. The side-normal triangle theorem
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md says
\(n_{AB}\cdot n_{AC}\ge0\), and force balance puts the radial
leaf support on A's opposite face. Rotate and reflect to write
\[
 A=[h,h+1]\times[u-1,u],\quad n_{AB}=-e_x,\qquad
 p_A=(h+1,u),\quad |p_A|=d,\quad u>0.
\tag{4}
\]
Indeed a zero leaf y-component would make both cycle forces
horizontal, already the desired parallel case; a positive component
puts the radial support at the upper-right vertex.

Both articulations meet \(D_\delta\), on opposite sides of the AB
support line. Therefore
\[
 |h|\le\delta,\qquad u^2=d^2-(h+1)^2\le4\delta<1/15,
                  \qquad 0<u<13/50.
\tag{5}
\]
The AC normal has negative y-component and nonpositive x-component.
Every AC application is on A's bottom face; unless that normal is
vertical, the application is \((h,u-1)\).

Write the actual AB mean as \(P=(h,y)\). Positive radial concurrence
at A, and the nonzero triangle moment, give
\[
          0<y\le u,\qquad q_A=((h+1)y/u,y).
\tag{6}
\]
If B is oblique to A, AB is a singleton in the relative interior of
A's side. A side-axis normal at an A vertex would violate the strict
point-only vertex/vertex convention. Thus \(y<u\) in that case.

## 3. Every oblique-B leaf and BC feature

For an oblique B its unique rightmost vertex is P. Write its inward
axes and other vertices as
\[
 \begin{split}
 v&=(-a,b),\quad w=(-b,-a),\quad a,b>0,\quad a^2+b^2=1,\\
 V&=P+v,\qquad W=P+w,\qquad O=P+v+w.
 \end{split}
\tag{7}
\]
Exactly two S-leaf features remain:

1. the upper adjacent vertex \(V=(h-a,y+b)\);
2. the far-v side, with
   \[
      p_B=dv,\quad P\cdot v=\delta,\quad
      t:=-P\cdot w=bh+ay\in[0,1].
   \tag{8}
   \]

Here is the complete feature check. P is excluded by the port theorem.
Equations (5)--(6) give \(|P|<4/15\), so
\[
 |O|\ge\sqrt2-|P|>17/15>61/60>d.
\]
If W were the radial support, its outward \(-v\) component would
require \(ah-by\ge0\), hence h>0. But
\[
 |W|^2=1+h^2+y^2-2bh-2ay
       \le d^2-2h-2bh-2ay<d^2.
\]
For the minimum-v side the application \(-dv=(da,-db)\) would force
\(a<1/60\) from B's right support h, then have height below
\(-59/60\), although B's minimum height is \(y-a>-1/60\).
For the minimum-w side the same reasoning forces \(b<1/60\),
but its application height \(da>59/60\) exceeds
\(y+b<13/50+1/60\). The far-w side would require
\(-bh-ay=\delta\), impossible since \(h\ge-\delta\), y>0,
and b<1. The far-v side is (8). Endpoints are included throughout.

Both remaining leaf types have positive y-component and nonpositive
w-component. For V this is exactly its outward-support condition
\(bh+ay\ge0\); in (8) the w-component is zero. B's force balance
therefore makes its BC normal k satisfy
\[
                         k\cdot w>0.
\tag{9}
\]
If \(k\cdot v>0\), its application is O and \(k_x<0\).
The support-span lemma puts every point of C strictly to the left of
\(O_x+1=h-a-b+1<h\), so C cannot touch A.

If \(k\cdot v=0\), then k=w and its application Q is anywhere on
B's far-w face. For every actual AC application \(P_A\),
\[
 \begin{split}
 (-w)\cdot(P_A-Q)
 &\ge bh+a(u-1)-(bh+ay-1)\\
 &=1-a(1-u+y)>0.
 \end{split}
\tag{10}
\]
This contradicts Q being C's maximum \(-w\) support. The inequality
is strict at all endpoints too. Consequently
\[
              Q=W=(h-b,y-a),\qquad
              k\cdot v<0,\quad k\cdot w>0.
\tag{11}
\]
The two C applications are distinct, since \(W_x<h\) whereas
every AC application has x-coordinate at least h.

If AC is a singleton, the fixed-tip selection makes both C contacts
side-owned. BC must be C-owned, because (11) is a strict B vertex.
If AC is shared, it has vertical normal; AB and AC are fixed
perpendicular axes, so Section1 removes a free BC normal. Again
BC must be C-owned, since (10) excluded the B-owned feature.
But shared AC makes C parallel to A. Its owned BC normal would
then be vertical (its y-component is negative), making C's two
pair forces parallel. This is impossible.

Thus AC is a singleton, either owned by A's bottom face or by C.
These are the two exhaustive alternatives.

## 4. A complete vertical-transition obstruction

Suppose AC is A-owned with normal \(-e_y\). Its application is
C's unique top vertex
\[
            T=(x_A,u-1),\qquad x_A=(h+1)y/u>0,\quad x_A>h.
\tag{12}
\]
The strict last inequality follows because the point lies in the
relative interior of A's bottom side. We prove a transition lemma
whenever the C-side-owned second contact Q satisfies
\[
                  Q_x\le h,\qquad 0\le T_y-Q_y\le u,
\tag{13}
\]
and the BC direction into C has negative y-component.

Its x-component is positive: otherwise its scalar product with
\(T-Q\) would be negative (a vertical direction would give parallel
C forces). Write it \(k=(c,-s)\), c,s>0, \(c^2+s^2=1\).
C's other inward axis from its top vertex is \(\ell=(-s,-c)\).
Since Q has minimum-k support and is side-interior,
\[
 C=T+[0,1]k+[0,1]\ell,\qquad Q=T+\tau\ell,\quad 0<\tau<1.
\tag{14}
\]

If the contact magnitudes are \(\kappa,\nu>0\), C's circle vector
is \(\kappa k-\nu e_y\). Its coordinates in the (k,\(\ell\))
frame are \(\kappa+\nu s>0\), \(\nu c>0\).
Thus its unique physical circle corner is the opposite vertex
\[
                 Z=T+k+\ell=(x_A+c-s,u-1-c-s).
\tag{15}
\]
In particular \(Z_x>0\). The force lines concur at
\(q_C=(x_A,u-1-\tau/c)\), a positive multiple of Z.
Its \(\ell\) coordinate is \(T\cdot\ell+\tau\), strictly
less than \(Z\cdot\ell=T\cdot\ell+1>1/2\).
The proportionality is therefore less than one. Comparing positive
x-coordinates gives c>s. Put \(\rho=s/c\in(0,1)\).

The determinant equation \(\det(q_C,Z)=0\) is exactly
\[
 \frac{\tau}{c}Z_x=x_A(c+s)-(c-s)(1-u)>0.
\tag{16}
\]
Consequently
\[
 x_A>\frac{1-\rho}{1+\rho}(1-u),\qquad
 x_A=Q_x+\rho(T_y-Q_y)\le\delta+\rho u.
\tag{17}
\]
If \(\rho\le1/2\), these give
\(x_A>37/150\) and \(x_A<1/60+13/100=11/75\),
a contradiction. Thus \(\rho>1/2\), whence
\[
 c+s\ge3/\sqrt5>67/50,\qquad
                Z_y<u-1-67/50<-52/25.
\tag{18}
\]
But \(R<52/25\), by squaring, so containment fails.

In the oblique-B chart Q=W has \(Q_x<h\), and its location below
C's top gives
\(0\le T_y-Q_y=u-y-(1-a)<u\).
Thus this excludes the whole A-owned alternative, for both B-leaf
features and every mean.

## 5. Two C-owned contacts and B's vertex leaf

Suppose instead both contacts are C-owned. Their outward directions
from A and B into C are respectively
\[
                 m=(-s,-c),\qquad k=(c,-s),
       \qquad c,s>0,\quad c^2+s^2=1.
\]
The other perpendicular sign for k would have positive y-component,
contrary to B's force balance. The AC application is
\(P_A=(h,u-1)\). Its line through q_A from (6) gives
\[
 \rho:=s/c=\frac{(h+1)y-hu}{u(1-u+y)},\qquad 0<\rho<1.
\tag{19}
\]
Indeed denominator minus numerator is
\((h+1-u)(u-y)>0\).

If B's radial application is V, its positive concurrence is
\(q_B=((h-a)y/(y+b),y)\). The line from q_B to W has direction k,
so
\[
            \rho=\frac{a(y+b)}{(a-b)y+bh-b^2}>1.
\tag{20}
\]
The denominator is positive because the direction is downward and
rightward. Numerator minus denominator is
\(b(y+a+b-h)>0\). This contradicts (19), including every endpoint
radial direction at V.

## 6. Two C-owned contacts and B's side leaf

Now use (8). The coordinates and B concurrence give
\[
 h=bt-a\delta,\quad y=at+b\delta,\qquad
 \rho=\frac{ab}{t-b^2},\quad t=b^2+\frac{ab}{\rho}.
\tag{21}
\]
The denominator is positive. Equation (9) gives \(\rho>b/a\),
so (19) implies a>b and hence y>h. Rearranging (19),
\[
 \frac yu-\rho=\frac{(1-\rho)(h-\rho u)}{1+h-\rho u},
       \qquad \rho u-h=\frac{y-h}{1-u+y}>0.
\tag{22}
\]
The denominator is positive by (5), so \(y<\rho u\).

Let the outward C normals be \(S=(s,c)\), \(T_0=(-c,s)\), with
common support vertex \(V_C\). The actual applications are
\[
 P_A=V_C-\lambda T_0,\quad W=V_C-\eta S,\quad
                0<\lambda,\eta<1.
\]
Writing \(K=a-1+u-y\), their difference \((b,K)\) gives
\[
                     \lambda=cb-sK,\qquad \eta=sb+cK.
\tag{23}
\]

### 6.1. Exact compact parameter bounds

The inequality \(\lambda>0\), with (21), says
\(a(u-y)<t-1+a\). Since \(y>at\),
\[
                  u<(1+a^{-2})y,\qquad
                  \rho>y/u>\frac{a^2}{1+a^2}.
\tag{24}
\]
Also h<=delta and (21) give
\(b^2(a+b)\le bt\le\delta(1+a)\le2\delta\).
Therefore
\[
              b^2<1/30,\quad a^2>29/30,\quad
              a>49/50,\quad \rho>29/59.
\tag{25}
\]
Finally
\[
 \begin{split}
 u^2&=(\delta-h)(2+\delta+h)\\
 &\le\frac{61}{30}\left[\delta(1+a)-b^3-\frac{ab^2}{\rho}\right],
 \end{split}
\]
so
\[
                     u^2+\frac{19}{10\rho}b^2<\frac{61}{900}.
\tag{26}
\]
These bounds include the whole leaf mean interval; positivity of its
interior parameter is a consequence of (21), not an extra premise.

### 6.2. The actual opposite C corner lies outside the disk

For \(Z=V_C-S-T_0\), an actual corner whether or not it is C's circle
corner,
\[
                     Z_y=u-1+\lambda s-c-s.
\]
Equations (22)--(23) give
\[
 u+\lambda s=c^2u+s^2y+scb+s^2(1-a)
       <A(\rho)u+B(\rho)b+s^2(1-a),
\tag{27}
\]
where \(A(\rho)=(1+\rho^3)/(1+\rho^2)\) and
\(B(\rho)=\rho/(1+\rho^2)\). Also
\[
             s^2(1-a)<\frac12\frac{1/30}{1+49/50}
                      =\frac5{594}<\frac{17}{2000}.
\tag{28}
\]

For \(29/59<\rho\le3/4\), one has \(A(\rho)\le91/100\),
\(B(\rho)\le1/2\). The derivative of A has the sign of the
strictly increasing \(\rho^3+3\rho-2\), so its maximum here is
at an endpoint; those values are \(114884/127499<91/100\) and
\(91/100\). Cauchy's inequality and (26) give
\[
 \begin{split}
 A(\rho)u+B(\rho)b
 &<\sqrt{\frac{61}{900}
      \left[\left(\frac{91}{100}\right)^2+\frac{15}{152}\right]}\\
 &=\sqrt{\frac{10741429}{171000000}}<\frac{251}{1000}.
 \end{split}
\tag{29}
\]
Meanwhile
\[
 c+s=\frac{1+\rho}{\sqrt{1+\rho^2}}>
       \frac{88}{\sqrt{4322}}>\frac{2677}{2000}.
\tag{30}
\]
The last squared comparison has integer difference
\(88^2\,2000^2-2677^2\,4322=3126062>0\).
Thus (27)--(30) imply \(-Z_y>2079/1000\).

For \(3/4\le\rho<1\), use \(c+s\ge7/5\), \(A(\rho)\le1\),
\(B(\rho)\le1/2\), and
\[
 A(\rho)u+B(\rho)b
      <\sqrt{\frac{61}{900}\frac{43}{38}}
       =\sqrt{\frac{2623}{34200}}<\frac{277}{1000}.
\]
Then
\[
 -Z_y>1+\frac75-\frac{277}{1000}-\frac{17}{2000}
                                  >\frac{2079}{1000}.
\]
In both intervals this is outside the disk, because
\[
 (2079/1000)^2-\frac{1105}{256}=\frac{23339}{4000000}>0.
\]
This excludes the last oblique-B feature.

## 7. Every parallel-B and shared-AB case

For B parallel to A, AB has positive shared length: an axis force at
a point-only aligned vertex pair violates the strict convention.
The side-normal triangle theorem at B puts its leaf application at
\[
             p_B=(h-1,v),\quad
             v^2=d^2-(h-1)^2,\quad 0<|v|<13/50.
\tag{31}
\]
The nonzero condition follows because a horizontal leaf would already
make B's cycle forces parallel.

If v<0, B is \([h-1,h]\times[v,v+1]\).
Force balance puts AC on height u-1 and BC on height v+1.
Their height gap is greater than \(37/25>\sqrt2\), impossible for
two points of C. Thus v>0 and
\[
                        B=[h-1,h]\times[v-1,v].
\tag{32}
\]
Both normals into C have negative y-components. AC has nonpositive
x-component and BC nonnegative x-component.

If both x-components are strict, the applications are
\((h,u-1)\), \((h,v-1)\). If u differs from v, their vertical
joining segment violates one of C's two upward supporting normals.
If u=v, then h=0 and the applications coincide at (0,u-1).
The coincident unique-circle-corner star is radial D, with that
point its inner vertex. Its norm would be \(r=R-\sqrt2<7/10\),
whereas \(1-u>37/50>7/10\). This is impossible.

If both x-components vanish, C has parallel pair forces, already
excluded. With exactly one zero component, reflect across the vertical axis
and exchange A,B so AC is vertical and BC has positive x-component.
Write its applications as
\[
        T=(x_A,u-1),\quad x_A=(h+1)y/u>0,\qquad Q=(h,v-1).
\]
C's top support gives v<=u. Since \(u^2-v^2=-4h\), h<=0 and
\(x_A>h\); the applications are distinct.

If AC is a singleton, the fixed-tip selection makes BC C-owned
(the normal has both x,y components strict, so cannot be B-owned).
If AC is shared, its vertical normal and AB's horizontal normal let
Section1 remove a free BC normal. C is parallel to A in that case,
so a fixed BC axis cannot have both required strict components.
The shared case is impossible.

Therefore AC is a point contact at C's unique top vertex, and BC
is C-side-owned. The transition hypotheses (12)--(13) hold:
\(Q_x=h\), \(0\le T_y-Q_y=u-v<u\). Section4 excludes it.
All parallel frames and all genuine AB means have been covered.

## 8. Whole-family conclusion and remaining obligation

If neither articulation were parallel, Section1 would give an AB
owner. Sections2--6 exclude every oblique frame of the other
articulation; Section7 excludes every parallel frame. At least one
articulation therefore has parallel cycle forces.

Choose it as A and call its leaf direction e. Its two cycle forces
cannot point in opposite directions. Force balance would then make
their line parallel to e, so one cycle contact supports A in the
same +e direction as its leaf. If that support is a unique vertex,
the leaf and cycle applications coincide, contrary to the port
theorem. If it is a side, e is an A side axis, and the two opposite
cycle normals contradict UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md.
Thus both cycle forces point opposite e.

Their two distinct applications belong to one minimum-e support
face. A unique vertex would make them coincide, so the face is a
genuine side. Hence the leaf direction is an A side axis. Rotating
it east gives its radial far support x=d and its cycle wall
x=d-1=delta, exactly (2). Origin torque and positive magnitudes put
the two distinct wall means on opposite sides of zero. Label them
in the port order to obtain \(y_B>0>y_C\), and their containing
unit-height interval has \(0<t<1\).

All B/C owned/shared transitions, all actual means, and all four
completion squares remain in this wall chart. The audited exact
positive core shows that it cannot simply be declared empty.
That exit is now completed: DISTINCT_S_LEAVES_WALL_CLASSIFICATION.md
gives the whole exact slider family, and DISTINCT_S_LEAF_WALL_UPPER_CAPACITY.md
plus DISTINCT_S_LEAF_WALL_LOWER_EMPTY.md prove capacities three and zero
for its genuinely routed regions. TRIANGLE_TWO_BRIDGES_CELL_CLOSED.md
assembles the entire parent cell.

No numerical pose search, radius subdivision, Lean compilation or
CI is a premise of this reduction.
