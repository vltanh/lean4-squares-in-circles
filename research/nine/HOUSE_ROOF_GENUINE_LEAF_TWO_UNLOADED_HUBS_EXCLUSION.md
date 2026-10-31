# A genuine roof leaf excludes the house with two unloaded hubs

**Status: complete hand whole-family exclusion, saved for full independent
review. Root review is separate. No shared gate or cover metadata is changed.**

Work with nine actual interior-disjoint unit squares in the disk of radius

\[
  \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
  \qquad d=\sqrt{R^2-\frac14}-1<\frac{61}{60}.
\tag{1}
\]

The actual positive edges on the six named bodies are

\[
                    AD,\ AT,\ DT,\ AB,\ BC,\ CD,\ TL.
\tag{2}
\]

The entire positive neighborhoods of the unloaded hubs \(A,D\) are
\(\{D,T,B\}\) and \(\{A,T,C\}\). The roof \(T\) has exactly the three
positive neighbors \(A,D,L\), and \(L\) is a genuine circle-loaded leaf.
The roof has zero circle load, as also follows from the genuine-leaf
reduction. In the original house-roof \(BC\) row, \(B,C\) are the two
loaded degree-two bodies. The proof below requires only their actual
containment and physical \(BC\) contact, beyond the positive \(AB,DC\)
forces already in the full hub equations.

**Theorem.** A compatible simultaneous necessary certificate cannot
contain (2). This excludes the entire original
\(\mathrm{HOUSE.ROOF.LBC.S}\) and \(\mathrm{HOUSE.ROOF.LBC.D}\) families,
for all radii in (1), all physical circle masks, all individual zero
corner weights, every original contact mean, and the same three
arbitrary completion squares.

The two new steps are the genuine-roof three-force selection in
Section 8 and the actual support contradiction in Section 6. The roof's
third force is retained in both steps. No loaded degree-two roof
equation, radial-roof midpoint, replacement square, or completion
assumption is used.

## 1. Literal local imports and the one simultaneous selection

The following complete sources were read at the exact commit
\(3ab01d0c60aca0125e7700f7c8575be81828a09b\). Their SHA-256 pins are:

| Source | SHA-256 |
|---|---|
| HOUSE_MIDDLE_TRIPLE_SHARED_HUB_EXCLUSION.md | 22ab112afd60370a220a0aa8a2e64b77a280b4c22015416975db7818b5fc29b2 |
| HOUSE_MIDDLE_TRIPLE_FREE_HUB_SELECTION.md | 74e414f8f5afe4428ae0eb2068887be3f01342a8dd64267868faf96bfbd33ad6 |
| HOUSE_MIDDLE_TRIPLE_OWNED_HUB_DOMAIN.md | 008d0a71ef4030b5f5c55e045a354c2cf0b150005a53c8d0f0f8fe76a433848d |
| HOUSE_MIDDLE_TRIPLE_FREE_EXTERNAL_SELECTION.md | db8d9ce225af44417fb6338eabaeb65ccfea389fa3dd210dbe0cd7663d6bf34c |
| HOUSE_MIDDLE_TRIPLE_PARALLEL_STAR_EXCLUSION.md | fbc732dc4d86fe70626bb935ef7f3e2c12b9a5b8f135aa8dbc79927117079c30 |
| HOUSE_MIDDLE_TRIPLE_NONPARALLEL_FREE_FEATURES.md | 1c3837998a156080995617211a596e3e468a2ebeba41555b6a5cb5fcaae43186 |
| HOUSE_MIDDLE_TRIPLE_NONPARALLEL_STAR_EXCLUSION.md | 3c2c843fc85298e9b6309779feadd6518de72c2f1ab855e672ac5a922ff44bd8 |

The enlarged scopes used here are established by the following exact
proof inventory, not by importing the complete middle-house theorem
with a changed roof degree.

* The shared-hub source already states its theorem with no degree,
  load or circle-mask condition on \(T,B,C\).
* Sections 1--4 of the free-hub source use only physical unit geometry,
  the complete unloaded \(A,D\) equations, and physical \(BC\).
  They first exclude all shared \(AT/DT\) alternatives with free \(AD\),
  coincident roof applications at \(AD\), and simultaneous shared
  \(AB,DC\). Sections 5--6 then use one unloaded hub's fixed three
  applications. No equation or circle contact of \(T\) occurs.
* Sections 1--6 of the owned-hub domain use only those same physical
  facts and full unloaded \(A,D\) stars. Its Section 7, which assigns
  a loaded degree-two radial equation to the roof, is not imported.
* The free-external source and the nonparallel-free-feature source
  use only the full \(A,D\) stars at the displayed fixed singletons.
  Each genuinely shared mean is expressly retained.
* The entire parallel-\(A\) source uses only physical roof support
  geometry and the full \(A,D\) equations; it never uses a roof load.
* From the nonparallel-star source we use the quantitative support
  span of Section 1 and the physical/full-hub arguments of Sections
  2, 3.2, 4 and 5.1. They are also reproduced below. Its loaded-roof
  midpoint argument in Section 3.1 and loaded-roof mask arguments
  in Sections 5.2--5.4 are replaced by Sections 6 and 8 here.

For the finite selections, prelist all ordered physical tuples
\((A,D,T,B,C,L)\) of the present form as well as the old tuples,
before extracting multipliers. The old local determinants have
exactly the same coefficients and independent point parameters,
since they use only \(A,D\). Their nonzero-coefficient proofs do not
depend on the number of forces at \(T\). Section 8 adds one further
finite nonzero determinant at the actual genuine-leaf roof.

All exclusions are imposed together inside the existing strict,
nonradial and matched-junction open normal domains. Physical
uncrossing preserves a surviving free point normal and adds only
actual shared-side forces; thinning only removes atoms. Thus no
selected direction is changed after the positive certificate is
known. Nothing in this proof chooses an application mean.

For later use, a contained unit with center \(z\) satisfies

\[
 |z|\le \sqrt{R^2-\frac14}-\frac12=d+\frac12.
\tag{3}
\]

Indeed its farthest corner has squared norm at least
\(|z|^2+|z|+\tfrac12\). Its half-width in any unit direction is at
least \(1/2\). Consequently every minimum support height, measured
from the actual circle center, is at most \(d\). This is precisely
the force-free statement of END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md,
Section 1. The strict bound in (1) follows from

\[
 \left(\frac{121}{60}\right)^2-\frac{1041}{256}
                         =\frac{31}{57600}>0.
\tag{4}
\]

## 2. Complete hub-interface and owned-domain reduction

A side-axis \(AD\) owned by both hubs is impossible: with the common
axis horizontal, the triangle \(A,T,D\) forces the \(AT\) horizontal
component nonnegative and the \(DT\) component nonpositive. The full
unloaded balances force the actual \(AB\) component strictly left and
the actual \(DC\) component strictly right. The support-span lemma
puts \(B,C\) strictly on opposite sides of the hub interface, contrary
to their physical contact.

A genuinely free \(AD\) is excluded by the complete free-hub geometry
and determinant described in Section 1. Explicitly, the geometry
first makes \(AT,DT\) fixed singletons distinct from the \(AD\)
junction, and makes at least one of \(AB,DC\) a singleton. At that
unloaded hub, take the \(AD\) junction as \(p\), the two other fixed
applications as \(q,r\), and their normals as \(n_T,n_B\). If

\[
 t_T=\det(q-p,n_T),\qquad t_B=\det(r-p,n_B),
\]

then \(t_T\ne0\); a positive star also needs \(t_B\ne0\). The full
force and moment equations require

\[
 \det(n_{AD},\,t_B n_T-t_T n_B)=0.
\tag{5}
\]

A zero coefficient vector already rules out a positive star. Otherwise
(5) excludes finitely many directions in the independent free \(AD\)
interval. In particular a shared mean was not frozen to obtain (5).

Thus \(AD\) is a singleton owned by exactly one hub. The graph
symmetry exchanges \(A,D\) and \(B,C\), while fixing \(T,L\); call
the owner \(A\). Translate and rotate for geometry, but retain the
actual circle center \(O\) as a separate point:

\[
 p_{AD}=0,\quad n_{AD}=E=(1,0),\qquad
 A=[-1,0]\times[-t,H],\qquad t,H>0,\quad t+H=1,
\tag{6}
\]

\[
 D=[0,1]u+[0,1]v,\quad
 u=(a,b),\quad v=(b,-a),\quad
 a,b>0,\quad a^2+b^2=1.
\tag{7}
\]

Let \(\alpha\) be the \(A\)-to-\(T\) normal and \(\beta\) the
\(D\)-to-\(T\) normal. Write \(\gamma,\mu,\nu>0\) for the respective
\(AD,AT,DT\) magnitudes. The physical triangle gives
\(\alpha_x\ge0\). The entire actual \(AB\) vector is

\[
                       F_{AB}=-\gamma E-\mu\alpha.
\tag{8}
\]

Thus its first coordinate is strictly negative, every actual \(AB\)
application has \(x=-1\), and the strict support span gives

\[
                               \max_B x<0.
\tag{9}
\]

The complete roof feature cover at \(D\) is as follows. An owned
\(D\) axis would, by the physical triangle and full \(D\) balance,
put \(DC\) at \(u+v\), separating \(C\) from \(B\). The roof cannot
contain \(0\): the local half-plane of \(A\) and the strictly tilted
quadrant of \(D\) leave only sectors of angle less than a right
angle. Nor can it contact at \(u+v\), since its minimum horizontal
coordinate would be strictly positive while it must touch \(A\).
After reflection and interchange of the two \(D\) axes, exactly

\[
 p_{DT}=u,\qquad
 \beta=r u-s v,\qquad r,s>0,\quad r^2+s^2=1,\quad
 \beta_y=rb+sa>0
\tag{10}
\]

remains. Both \(T\)-owned and free \(\beta\) are retained.

If an \(AT\) point has \(x=0\) and height \(h\), the fact that
\(u\) minimizes \(\beta\) on \(T\) gives \(\beta_yh\ge r>0\).
A downward \(A\)-owned normal is also impossible, since \(T\)
contains \(u\) above \(A\). Hence

\[
               \alpha_x\ge0,\quad \alpha_y\ge0,\quad p_{AT,y}>0.
\tag{11}
\]

The full actual \(DC\) vector is

\[
                           F_{DC}=\gamma E-\nu\beta.
\tag{12}
\]

Its \(v\)-coordinate is strictly positive and its \(u\)-coordinate
is nonpositive. A positive \(u\)-coordinate would again separate
\(C\) from \(B\) at \(u+v\). Therefore its actual application is

\[
 p_{DC}=v
 \quad\hbox{or}\quad
 p_{DC}=v+\tau u,\quad n_{DC}=v,\quad
                 0\le\tau<\frac{a}{1+b}.
\tag{13}
\]

The strict upper bound follows from actual \(BC\): the support-span
bound at \(C\) gives \(\min_Cx>b+\tau a-1\), so \(b+\tau a<1\).
In particular every \(DC\) application has strictly negative height.

The full nonparallel \(D\) star has concurrence

\[
 q_D=(k_D,0),\qquad k_D=\frac{s}{\beta_y}>0,
 \qquad k_D<\min(1/a,1/b).
\tag{14}
\]

When \(D\) owns \(DC\), the unchanged actual side mean gives

\[
                    k_D=\frac{\tau}{a}<\frac1{1+b}.
\tag{15}
\]

These are full three-force equations, not degree-two substitutions.

## 3. Fixed-star owners and the entire parallel-\(A\) exit

A free \(DC\) would be applied at the fixed vertex \(v\). The other
two \(D\) applications are the distinct fixed points \(0,u\).
Eliminating its two other positive magnitudes from full \(D\) force
and torque gives, for its free unit normal \(\zeta\),

\[
 a\beta_y\zeta_x+(b\beta_y-s)\zeta_y=0.
\tag{16}
\]

Its first coefficient is positive. The parameter at \(v\) is
independent of those at \(0,u\), even with the matched opposite pair
at any of those junctions. Thus the simultaneous selection excludes
free \(DC\). It is owned by \(D\) or \(C\).

If \(C\) owns \(DC\), write its actual normal

\[
              \zeta=-l u+m v,\qquad l,m>0,\quad l^2+m^2=1.
\]

The full \(D\) force and torque at its actual vertex \(v\) give

\[
                  \nu(r-s)=\gamma a>0,\qquad
                  \kappa(m-l)=\gamma b>0,
\tag{17}
\]

where \(\kappa>0\) is the actual \(DC\) magnitude. Hence \(r>s\)
and \(m>l\). Equations (17) are not used at a variable \(D\)-side
mean.

Suppose first that \(\alpha=E\), so the full \(A\) star is parallel.
With actual \(AT=(0,h)\) and actual \(AB=(-1,y_B)\), its torque is

\[
          y_B=\frac{\mu}{\gamma+\mu}h,\qquad
                    0<y_B<h\le H<1.
\tag{18}
\]

Thus all of \(B\) lies in \(x\le-1\), and all of \(T\) lies in
\(x\ge0\). A \(D\)-owned \(DC\) gives
\(\min_Cx>b-1>-1\), impossible. Hence \(C\) owns it. To reach \(B\)
its \(\zeta_x\) must be negative, including exclusion of the vertical
axis by the actual width-one \(C\) frame. Equations (17) then force
\(a>b\), and \(\beta\) is strictly northeast.

The actual support inequality at \(u\) gives
\(h\ge r/\beta_y>1/(a+b)\). Meanwhile the whole \(T\) support cover
makes its unique left vertex \((0,h)\) and puts \(u\) on the lower
adjacent side or endpoint, so \(a^2+(b-h)^2\le1\) and \(h\le2b\).
Consequently \(b>1/3\). The \(C\)-owned axis has exact horizontal width

\[
 \operatorname{width}_x(C)
   =a(l+m)+b(l-m)<\sqrt2\,a.
\]

It must span from its real point \(v_x=b\) to a real \(BC\) point
with \(x\le-1\), requiring width at least \(1+b\). But

\[
            (1+b)^2-2a^2=(3b-1)(b+1)>0.
\]

This closes the entire parallel-\(A\) star, with both means in (18)
retained.

Henceforth \(\alpha_y>0\). The actual \(AB\) application is
\((-1,-t)\), and the true \(A\) concurrence satisfies

\[
 q_A=(k_A,0),\qquad
 k_A=p_{AT,x}-H\frac{\alpha_x}{\alpha_y}
     =-1+t\frac{\gamma+\mu\alpha_x}{\mu\alpha_y},
 \qquad -1<k_A\le0.
\tag{19}
\]

The fixed-star selections give:

* \(AT\) is not free: it is \(A\)-owned vertical or \(T\)-owned oblique.
* If \(AB\) is free, \(AT\) is an actual positive-length shared side.
* If \(DT\) is free, \(DC\) is an actual positive-length shared side.

For completeness the respective necessary free-normal determinants
have strictly nonzero coefficients

\[
\begin{array}{ll}
 AT:&
 -H\eta_y\alpha_x-\det((-1,-t),\eta)\alpha_y=0,
                \quad -H\eta_y>0,\\
 AB:&
 t\alpha_y\eta_x+
 [-\alpha_y-\det(p_{AT},\alpha)]\eta_y=0,
                \quad t\alpha_y>0,\\
 DT:&
 -b\zeta_y\beta_x+
 [a\zeta_y-\det(p_{DC},\zeta)]\beta_y=0,
                \quad-b\zeta_y>0.
\end{array}
\tag{20}
\]

The \(AB\) and \(DT\) conditions in (20) are invoked only when their
other application is a physical singleton. The heights of the three
applications at each hub are distinct, so the free parameter is
independent at matched junctions. All true shared alternatives remain.

We shall use the quantitative support span: if a contained unit has
minimum-\(n\) point \(P\) and \(n_x<0\), then

\[
              \max_{X\in S}(X_x-P_x)\le |n_y|.
\tag{21}
\]

For \(n_x>0\) reflection gives
\(\min_{X\in S}(X_x-P_x)\ge-|n_y|\). The unit-square proof, including
all side means, is in the nonparallel-star source Section 1.

## 4. Oblique \(AT\) and two perpendicular roof-owned axes

Suppose \(T\) owns \(AT\) and it is oblique. Write

\[
                    \alpha=(c,z),\qquad c,z>0,\quad c^2+z^2=1.
\]

Its actual \(A\) point is \(P=(0,H)\). Full \(A\) torque gives

\[
                       \mu(z-c)=t\gamma>0,
\tag{22}
\]

so \(z>c\). Also
\(\gamma+\mu c-\mu z=H\gamma>0\). Thus

\[
                |n_{AB,y}|<1/\sqrt2,\qquad
                  \max_Bx<-1+1/\sqrt2.
\tag{23}
\]

If \(T\) owns \(DT\) too, its positive vertical component permits only
\(\beta=\alpha\) or \(\beta=(-z,c)\). In the perpendicular case
\(r=\beta\cdot u=bc-az>0\), giving \(b>a\) and \(b>1/\sqrt2\).
The actual \(DC\) vector (12) has positive horizontal component.
Using its application (13) and (21),

\[
                   \min_Cx\ge b-|\zeta_y|>b-1>-1+1/\sqrt2.
\]

This contradicts \(BC\) and (23). No equation of \(T,B,C\) has been
used in this perpendicular case.

## 5. All vertical-\(AT\) alternatives

Let \(\alpha=e_y\), with its actual point \(P=(-\xi,H)\),
\(0\le\xi\le1\). This retains a shared \(AT\) mean and a possibly
free \(AB\) normal.

### 5.1. Parallel roof pair

If \(\beta=e_y\), both actual roof points lie on one roof side, so

\[
 H=b,\quad t=1-b,\quad a+\xi\le1,\quad K=1-\xi\ge a.
\]

The original \(A\) force and torque give
\(n_{AB}=(-K,-t)/\sqrt{K^2+t^2}\). Therefore

\[
          \max_Bx\le-1+\sqrt{(1-b)/2}.
\tag{24}
\]

For \(D\)-owned \(DC\), \(b\ge a\) gives
\(\min_Cx\ge b-a\ge0\). If \(a>b\), (14) gives \(k_D=a\),
contrary to (15), since

\[
      a(1+b)-1=b\left(a-\frac{b}{1+a}\right)>0
                        \quad(a\ge b>0).
\tag{25}
\]

For \(C\)-owned \(DC\), (17) gives \(b>a\), hence
\(\zeta_x=mb-la>0\) and \(\min_Cx>b-1\).
Since \(\sqrt{(1-b)/2}<b\) for \(b>1/\sqrt2\), (24) again
contradicts \(BC\). This proof never assigns a midpoint to the roof.

### 5.2. Nonparallel roof-owned \(DT\)

An aligned \(T\) would have only the parallel positive vertical axis,
already excluded. Otherwise \(P\) is its bottom vertex, with inward
axes \(j=(c,z)\), \(Jj=(-z,c)\), \(c,z>0\). The choice
\(\beta=j\) cannot reach \(u_x=a>0\) on the minimum-\(\beta\) side.
Thus the entire remaining roof-owned feature is

\[
        \beta=Jj,\qquad u=P+L j,\quad 0<L\le1,
\]
\[
        K=1-\xi=1+a-Lc>0,\qquad t=1-b+Lz.
\tag{26}
\]

The endpoint \(L=1\) only enlarges the actual side-interior domain.
If \(C\) owns \(DC\), (17) gives \(b>a\) and \(\min_Cx>b-1\), while

\[
 bK-at=b-a+2ab-L(bc+az)
      \ge (b-a)-(b-a)^2>0.
\tag{27}
\]

It follows that \(|n_{AB,y}|<b\), contradicting \(BC\) by (21).
If \(D\) owns \(DC\), \(b\ge a\) again separates \(B,C\). For \(a>b\),

\[
                       k_D=a+b\,z/c>a>1/(1+b),
\]

contrary to the actual mean bound (15).

### 5.3. Free \(DT\) opposite an actual shared \(DC\)

The physical shared side means

\[
                         C=D+v+\delta u,\qquad -1<\delta<1.
\tag{28}
\]

Its minimum \(x\) exceeds \(b-a\). Actual \(BC\) and (9) imply
\(a>b\). We have \(\beta_x<0\), without choosing a roof frame:
for oblique \(T\), the minimum-\(e_y\) point \(P\) is its bottom
vertex, and the strict minimum-\(\beta\) vertex \(u\), with
\(\beta_y>0\) and \(u_x>0\), can only be its right adjacent vertex.
Its strict inward normal has negative horizontal component.
For aligned \(T\), \(P\) can be any point of its bottom side, and
the only possible free minimum-\(\beta\) vertex is its bottom-right
vertex, giving the same sign. This covers every actual shared
\(AT\) mean.

Thus \(k_D=a-b\beta_x/\beta_y>a\), again contradicting
(15) and (25). All vertical-\(AT\) alternatives are closed.

## 6. Oblique parallel roof: the actual leaf forces excessive \(B\) support

It remains to treat \(\alpha=\beta=(c,z)\), \(c,z>0,z>c\), with
\(T\) owning this axis. Put

\[
        p=c/z\in(0,1),\qquad H=b+ap,\qquad
        \ell=|u-P|=a/z\le1,\qquad P=(0,H).
\tag{29}
\]

The equality of the two roof support heights gives \(H=b+ap\);
their actual side length gives \(\ell\le1\).
First \(b\ge a\) is impossible. If \(D\) owns \(DC\), then
\(\min_Cx\ge b-a\ge0\). If \(C\) owns it, (17) makes
\(\zeta_x=mb-la>0\), so \(\min_Cx>b-1\), and (23) separates
\(B,C\) because \(b\ge1/\sqrt2\). Consequently

\[
                             a>b>0.
\tag{30}
\]

From (29), \(H<1\), and \(a^2+b^2=1\),

\[
             p\le b/a,\qquad p<(1-b)/a,\qquad
             p\le1/\sqrt3<3/5,\qquad a>1/\sqrt2>7/10.
\tag{31}
\]

For the middle estimate, when \(b\le1/2\) use
\(b/a\le1/\sqrt3\); when \(b\ge1/2\) use
\((1-b)/a=\sqrt{(1-b)/(1+b)}\le1/\sqrt3\).

The nonpositive \(u\)-coordinate of (12) says \(\nu r\ge\gamma a\).
Here \(r=\alpha\cdot u=zH\). Combine this with the full \(A\)
torque (22):

\[
 w:=\frac{\mu}{\nu}
       \le\frac{tH}{a(1-p)}
       <\frac{1/4}{(7/10)(2/5)}
       =\frac{25}{28}.
\tag{32}
\]

Define the actual weighted roof application and its horizontal
coordinate by

\[
 Q=\frac{\mu P+\nu u}{\mu+\nu}
      =(q,H-pq),\qquad
 q=\frac{a}{1+w}>\frac{98}{265}>\frac13.
\tag{33}
\]

These are identities for the unchanged positive force magnitudes.
No roof application or transverse mean is reassigned.

The full true \(T3\) force equation is

\[
                         \lambda e=\mu\alpha+\nu\beta,
                    \qquad\lambda>0,
\tag{34}
\]

where \(e\) is the original genuine-leaf direction. Hence \(e=\alpha\).
The genuine leaf application is \(O+r_L\alpha\), with \(r_L=d\)
for an S leaf and \(r_L=R-\sqrt2\) for a D leaf. In either case
\(r_L\le d\), also directly because the leaf is a contained unit
on the outer side of that support.

The roof's width in this owned direction is one. Thus the opposite
roof support side containing both \(P,u\) has height
\(\eta=r_L-1<1/60\) relative to \(O\). The original roof torque,
including its zero-moment radial leaf force, gives

\[
                       Q=O+\eta\alpha,\qquad
                       O=(q,H-pq)-\eta(c,z).
\tag{35}
\]

Equation (35) retains the actual genuine-leaf transverse slider. It
does not assert that \(Q\) is a midpoint of any roof side.

Put \(K=1-pH\). The full \(A\) equation (22) makes its actual
\(AB\) normal

\[
 n_{AB}=\frac{(-K,-t)}{\sqrt{K^2+t^2}},
 \qquad K,t\in(0,1).
\tag{36}
\]

At the real \(AB\) point \((-1,-t)\), equations (35)--(36) give
the actual minimum support of \(B\), relative to the actual \(O\):

\[
\begin{split}
 h_B
 &=n_{AB}\cdot\bigl((-1,-t)-O\bigr)\\
 &=\frac{K+t+q(1-p)-\eta(Kc+tz)}
          {\sqrt{K^2+t^2}}.
\end{split}
\tag{37}
\]

Both \(K,t\) are positive, so their sum divided by their Euclidean
norm exceeds one. Also
\(0<Kc+tz\le\sqrt{K^2+t^2}\). These inequalities hold even if
\(\eta<0\), which includes the D case. Using (31),(33) and
\(\sqrt{K^2+t^2}<\sqrt2<3/2\) in (37),

\[
 h_B>
   1+\frac{(1/3)(2/5)}{3/2}-\frac1{60}
   =\frac{193}{180}
   >\frac{61}{60}>d.
\tag{38}
\]

The exact middle reserve is \(1/18\). This violates the universal
contained-unit support bound (3). Thus the entire oblique parallel
roof is excluded for both genuine leaf types. No equation at \(B\)
or \(C\), physical corner mask, or secondary minimizer was needed.

## 7. The sole remaining feature before the genuine-leaf selection

Sections 4--6 close every \(T\)-owned \(DT\) feature. Section 5.3
closes the free-\(DT\) case with vertical \(AT\). Therefore the
only feature still to consider is

* \(AT\) is oblique and \(T\)-owned, at its fixed singleton
  \(P=(0,H)\), in the relative interior of a roof side;
* \(DT\) is free, at the distinct fixed singleton \(u=(a,b)\),
  a strict vertex of \(T\);
* \(DC\) is actually shared, retaining its original mean.

The roof \(T\) has its full three forces throughout. No condition
on a hypothetical roof circle resultant is available or imposed.

The physical triangle at \(T\), using its owned \(TA\) axis,
gives \(\alpha\cdot\beta\ge0\). Since \(\beta\) is strict at a
\(T\) vertex and \(\alpha\) is an own axis, this is strict. Hence
the minimum-\(\beta\) vertex \(u\) lies on the same minimum-\(\alpha\)
side as \(P\). Set

\[
             P=u+\ell j,\qquad 0<\ell<1,\qquad
             \alpha\cdot j=0,\quad |j|=1.
\tag{39}
\]

Here \(j\) points from that endpoint toward the side interior.
Strict support gives

\[
                     \beta\cdot\alpha>0,\qquad
                     \beta\cdot j>0.
\tag{40}
\]

The actual \(AT,DT\) intersections are singleton points, even though
the distinct \(DC\) side has a variable mean.

## 8. Full genuine-roof three-force determinant excludes this free vertex

We record the precise local selection so neither a loaded \(T2\)
theorem nor an unwarranted noncollinearity premise is imported.

The physical genuine leaf fixes its radial unit direction \(e\)
and radial application \(O+r_L e\), by
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md, Section 6, for both S/D types.
The roof has exactly the two other forces at \(P,u\), with incoming
directions \(\alpha,\beta\). Equations (34),(40) imply

\[
             e\cdot\alpha>0,\qquad e\cdot j>0,
                   \qquad \det(\alpha,e)\ne0.
\tag{41}
\]

In particular its genuine leaf support is not \(u\), the endpoint
minimizing both displayed inward coordinates. The parameters at
the two roof contacts are distinct from any free leaf parameter;
the genuine-leaf direction itself is fixed by its physical S/D form.

The complete roof force and moment equations are

\[
 \lambda e=\mu\alpha+\nu\beta,\qquad
 \mu\det(P-O,\alpha)+\nu\det(u-O,\beta)=0.
\tag{42}
\]

The leaf has zero origin moment. Taking a determinant of the first
equation with \(e\), and using \(\det(\alpha,e)\ne0\), eliminates
\(\mu/\nu\). The necessary identity is

\[
                         \det(W,\beta)=0,
\tag{43}
\]

\[
 W=\det(P-O,\alpha)e+\det(\alpha,e)(u-O).
\tag{44}
\]

Every coefficient in (44) is fixed by the physical packing and the
actual side owner \(\alpha\). No \(DC\) mean or unknown circle
weight occurs.

The coefficient vector is nonzero. If \(W=0\), then
\(\det(\alpha,e)\ne0\) would make \(u-O=k e\) for some real \(k\).
Substitution of \(P-O=k e+\ell j\) from (39) gives instead

\[
                             W=\ell\det(j,\alpha)e\ne0.
\tag{45}
\]

This also covers the collinear \(u-O\) possibility; no separate
claim that the free vertex is nonradial was needed for (45).

For a fixed physical candidate, (43) therefore excludes at most two
unit directions in the open strict \(DT\) interval. If a candidate
has \(\det(\alpha,e)=0\), the positive force equation and (40)
already make it impossible, since its \(j\)-component cannot vanish.
Thus every candidate that could have a positive star has the
nonzero determinant just proved.

Before multiplier extraction, include all such ordered physical
genuine-leaf assignments, side-owned singleton \(P\), distinct
vertex singleton \(u\), and their side orientation in the finite
prelist of Section 1. The free \(DT\) parameter is at \(u\);
\(AT\) is owned and applied at \(P\ne u\). Matching opposite
pairs at one junction does not couple these distinct applications.
The fixed physical radial direction \(e\) adds no unknown normal
parameter. Hence (43) is a nontrivial analytic condition on the
permitted independent free interval and can be avoided along with
all earlier finite conditions.

This uses the same physical prelisting mechanism as
RADIAL_LEAF_ARTICULATION_FIXED_POINT_SELECTION.md, Sections 3--4.
Its boundary-neighbor theorem is not imported: the nonvanishing
needed here is the explicit proof (39)--(45), with no boundary
premise on \(A,D\). Uncrossing/thinning preserve the selected
free direction exactly as described in Section 1. A surviving
positive star (42) would therefore violate the selection. The
whole last free-\(DT\)/shared-\(DC\) feature is excluded.

## 9. Exhaustive original-family join

The actual \(AD\) normal is shared-axis, free, or owned by exactly
one hub. Section 2 excludes the first two and provides the complete
one-owner domain. In that domain Section 3 excludes the entire
parallel-\(A\) star and removes the exact free singleton features
without freezing any shared mean.

For the nonparallel \(A\) star, \(AT\) is either vertical \(A\)-owned
or oblique \(T\)-owned. Every vertical feature closes in Section 5,
including the genuinely shared \(AT\) mean and the opposite shared
\(DC\) mean. For oblique \(AT\), \(DT\) is either one of the two
permitted \(T\) axes or free: Section 4 closes the perpendicular
axis, Section 6 the parallel axis, and Sections 7--8 the complete
free feature. There is no further contact owner or side endpoint.

For \(\mathrm{HOUSE.ROOF.LBC.S}\) and
\(\mathrm{HOUSE.ROOF.LBC.D}\), the original graph has precisely
the true stars used above: \(A3,D3,T3,B2,C2,L1\), with the sole
genuine leaf at \(T\) and positive boundary loads at \(B,C,L\).
The same proof covers both physical leaf forms in (34)--(45) and
every radius in (1). Both loaded boundary stars, all of their
physical corner masks and individual weights, and all three
completion squares were retained.

Thus both whole original fine families are excluded under one
compatible initial normal selection. This proof is local to the
stated two-unloaded-hub/genuine-roof configuration; it does not
claim any house row with a loaded hub. No numerical pose sample,
parameter cover, Lean compilation, CI or remote metadata update
is a premise.

