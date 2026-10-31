# The entire mixed-corner opposite-load C4 attachment is excluded

**Status: complete whole physical-mask hand exclusion; root and separate
independent full hand audits passed.** Work at the common canonical
radius/center-norm minimizer in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\qquad \frac{91}{100}<D<\frac{61}{60}.
\tag{1}
\]
The entire positive component is
\[
                     H-A-U-C-H,\qquad H-X-Y-H,
\tag{2}
\]
with exact block loads A,C. Up to the true reflection, A has one
physical circle corner z_A, and C has two physical circle corners.
The true degrees are four at H and two at A,U,C,X,Y. All three
arbitrary completion units remain present. Every original shared-side
mean and every nonnegative split of C's positive total circle load is
retained, including a zero individual corner weight.

**Theorem.** This entire mixed physical mask is impossible in a
compatible selected certificate at the canonical minimizer.

## 1. The intact end triangle and the full canonical domain

The actual triangle resultant M=F_X+F_Y satisfies c_H.M>0. Each
actual physical circle corner of the radial neighbor C has positive
dot product with c_H, by RADIAL_BOUNDARY_NEIGHBOR_PRESSURE.md.
The genuine whole-component force sum therefore gives
\[
                  M+F_A+F_C=0,\qquad c_H\cdot z_A<0.
\tag{3}
\]
This is the complete mixed-mask statement of
END_TRIANGLE_RADIAL_NEIGHBOR_OBSTRUCTION.md. No resultant direction
has been substituted for a radial leaf at H.

TRIANGLE_C4_OPPOSITE_LOAD_CANONICAL_CONTACT.md gives actual HU
contact, H oblique to U, and singleton HA and HC intersections. Use
its complete coordinates
\[
 \begin{split}
 U&=[X_0-1,X_0]\times[Y_0,Y_0+1],\\
 P&=(X_0,y_0),\qquad Y_0<y_0<Y_0+1,\\
 v_H&=(a,b),\quad w_H=(b,-a),\quad a,b>0,\quad a^2+b^2=1,\\
 H&=P+[0,1]v_H+[0,1]w_H.
 \end{split}
\tag{4}
\]
The unchanged channel applications are
\[
                   p_A=(x,Y_0),\qquad p_C=(x,Y_0+1),\qquad x\le X_0,
\tag{5}
\]
with common positive magnitude gamma. A lies below Y_0 and C above
Y_0+1. Neither application in (5) belongs to H. H's leftmost and rightmost
vertices are strictly within the channel height interval, so
its only vertex below or on Y_0 is P+w_H, and its only vertex above
or on Y_0+1 is P+v_H.

The physical HUA/HUC triangles give the complete owned-normal signs:
an H-owned root normal has nonpositive x-coordinate; an A-owned HA
normal has nonpositive y-coordinate; a C-owned HC normal has
nonnegative y-coordinate. All normals point out of H.

For use in Section 6, (3) also gives a purely physical inner-face
restriction. If q belongs to H intersect A, then
\[
                      q\cdot z_A<R/\sqrt2.
\tag{6}
\]
In the outward corner frame z_A=(A_0,B_0), A_0,B_0>=1/2, every
point on an outer A face meeting z_A has dot product at least
R^2-max(A_0,B_0)>=R^2-R>R/sqrt(2). Thus q lies on one of the two
inner A faces. In particular, if q is an A vertex, it is exactly
the vertex opposite z_A. This is the full face restriction of
NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md, Section 1; no quantitative
corner approximation or higher-radius premise is used here.

## 2. The entire radial-C parallel frame is impossible

Suppose C is parallel to U. Its physical radial S axis is one of the
four channel coordinate directions. If it is horizontal, C's bottom
height is -1/2, so A's top is -3/2 and its minimum height is at most
-5/2<-R. If its radial axis is downward, that contradiction is still
stronger. The only remaining physical mask is
\[
                  C=[-1/2,1/2]\times[D,D+1].
\]
Then Y_0=D-1 and the genuine p_A in (5) satisfies
\[
                  |p_A|^2\le\frac14+(D-1)^2
                         <\frac{13}{50}
                         <\left(\frac{11}{20}\right)^2.
\tag{7}
\]
But every point of a circle-touching unit has norm at least
R-sqrt(2)>11/20. Thus p_A cannot belong to loaded A. This excludes
every parallel C mask independently of its two corner weights and
of A's frame or owners.

Hence C is oblique to U. Its fixed bottom vertex is p_C.

## 3. The unique HA contact has an actual side owner

If A is oblique to U, its other application p_A is a fixed vertex
distinct from its HA application. GENERAL_FIXED_TIP_NORMAL_SELECTION.md
therefore removes a free HA normal at this exact degree-two unique
body. The coincident radial-D exception is absent by Section 1.

If A is parallel to U and HA is free, its application Q_A is A's
upper-right vertex and H's bottom vertex P+w_H. In particular
(Q_A)_x=X_0+b>x. The free normal out of H is strictly southwest,
so A's unique circle corner is z_A=Q_A-e_x-e_y with (z_A)_x<0.
Give A and U the same virtual rigid motion
\[
             V(r)=t+\omega Jr,\qquad
             t=xJz_A,\quad \omega=-(z_A)_x.
\tag{8}
\]
The A circle row, every internal AU row and the fixed external UC
vertical row at p_C have zero work. At Q_A the remaining velocity is
\[
                    J\{xz_A-(z_A)_xQ_A\}\ne0,
\tag{9}
\]
because its pre-J first coordinate is (z_A)_x(x-(Q_A)_x). Thus the
positive HA row would impose a nonzero linear condition on its free
strict normal. Choose that normal away from this condition before
the multiplier theorem. The full shared-block argument is also
TRIANGLE_C4_OPPOSITE_UNIQUE_TIPS_EXCLUSION.md, Section 3; it uses
no circle-mask or load equation at the fixed oblique C.

These are virtual wrench identities only, not physical movements.
The original AU mean cancels internally and is never frozen. Both
arguments can be prelisted for every radial C mask and weight split.
Thus HA is H-owned or A-owned. Its actual singleton still has its
application in the relative interior of the owner's side.

## 4. The full radial-C contact face and its owner alternatives

An H-owned HA normal is -v_H. If A owns HA, it cannot be parallel
to U: the complete coordinate-axis check either exposes H's middle
left vertex, prevents the AU contact, or makes A's unique circle
force vertical along an axis, impossible for its parallel frame.
For an oblique A, the complete near/far side cover in
FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md, Section 1, together with
the nonpositive y owner sign, leaves only the near-side normal.
In either case the unique A force has strictly negative x-component.
Its two pair forces are nonparallel, so the full nonparallel proper
concurrence lemma, TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md,
Lemma 2.1, applies without a boundary-neighbor premise. Its concurrence
is a positive multiple of F_A on the vertical line through p_A.
Consequently
\[
                                  x<0.
\tag{10}
\]

Write C's inward bottom-vertex frame as
\[
               r_C=(c,d),\qquad t_C=(-d,c),\qquad c,d>0,\quad c^2+d^2=1.
\]
Its bottom vertex cannot be a circle vertex. The two radial-S
possibilities are D r_C-t_C/2 and -r_C/2+D t_C. The first has positive
x-coordinate and is excluded by (10). Thus the entire C pose is
\[
                  p_C=-\frac12r_C+D t_C,\qquad
                  C=p_C+[0,1]r_C+[0,1]t_C.
\tag{11}
\]

Every HC application lies on the inner radial face
\[
                         q_C=p_C+\sigma r_C,\qquad 0<\sigma\le1.
\tag{12}
\]
Here is its full feature cover. The two outer vertices are physical
circle corners and cannot be shared with H. The inner vertex p_C
cannot be in H by Section 1. Thus every vertex application is the
other inner vertex p_C+r_C. For a C-side-owned application, its
minimum-r_C side has first coordinate below x except at the already
excluded p_C. Its maximum-r_C side has outward H-to-C normal -r_C,
of negative y-coordinate, forbidden by the physical HUC owner sign.
The outer radial face has the same wrong sign (-t_C); equivalently
no contained unit can lie beyond its height D+1>R-1. Only the inner
radial side remains. Positive-length HC overlap was already excluded.

If C owns HC, then 0<sigma<1, its actual normal out of H is t_C,
and q_C is H's upper vertex P+v_H. The true C force is
F_C=nu t_C+gamma e_y. Its positive radial concurrence on the
channel line is
\[
                         p_C+\frac{\sigma}{d}e_y.
\]
Its r_C-coordinate is sigma-1/2, whereas F_C has r_C-coordinate
gamma d>0. Therefore
\[
                   C\text{ owns }HC\quad\Longrightarrow\quad \sigma>1/2.
\tag{13}
\]
The concurrence may be outside C; only its positive radial factor is
used. All radial corner weights remain arbitrary. If H owns HC or
HC is free, the C application is a vertex and sigma=1.

## 5. The entire A-owned HA branch

Write A's inward top-vertex frame as
\[
             r_A=(u,-v),\qquad t_A=(-v,-u),\qquad u,v>0,\quad u^2+v^2=1.
\]
The complete near-side owner chart gives
\[
             q_A=p_A+\tau r_A,\quad 0<\tau<1,\qquad n_{HA}=t_A.
\tag{14}
\]
The true force F_A=mu t_A-gamma e_y has positive coordinates on
both inward axes. Its unique physical circle corner is therefore
z_A=p_A+r_A+t_A. Its positive concurrence is
p_A-(tau/v)e_y. Comparing its r_A-coordinate with that of z_A
shows that its radial scale kappa is strictly less than one: the
increments from p_A are respectively tau<1 and 1. Since its global
x-coordinate is x<0, equation
\[
                          x=\kappa(x+u-v)
\]
forces
\[
                                  u<v.
\tag{15}
\]

If C owns HC, both oblique tips own their root contacts. The complete
leaf-independent FOUR_CYCLE_OBLIQUE_TIP_OWNER_EXCLUSION.md excludes
this whole case, retaining the radial mask and all means.

Otherwise sigma=1 in (12), and the two actual points of H differ by
\[
                  q_C-q_A=(c-\tau u,\ 1+d+\tau v).
\]
Their squared distance is
\[
         2+2d+\tau^2+2\tau\{v(1+d)-uc\}>2,
\tag{16}
\]
since v>u and c<=1. This exceeds H's squared diameter. Thus the
entire A-owned branch is impossible, with no restriction on the
remaining HC normal owner or radial weights.

## 6. H owns HA and A is oblique to U

The actual HA normal is -v_H. A's fixed top vertex is p_A, with
inward frame r_A=(u,-v), t_A=(-v,-u), u,v>0. The complete vertex
check gives
\[
                 q_A=p_A+r_A,\qquad au-bv>0.
\tag{17}
\]
It is not p_A or p_A+t_A, which are outside H's allowed x/height
domain. At p_A+r_A+t_A the outward A-to-H normal v_H has negative
t_A-coordinate, inconsistent with that vertex. The strict inequality
in (17) retains the absence of a shared HA interval.

By (6), the actual A vertex q_A is opposite its unique circle corner.
Thus
\[
                    z_A=p_A+t_A=-A_0r_A+B_0t_A,\qquad A_0,B_0>1/2.
\tag{18}
\]
Put rho=b/a and eta=v+rho u. The positive A concurrence is
p_A-eta e_y=kappa z_A, so
\[
                (1-\kappa)A_0=\eta v>0,\qquad
                (1-\kappa)B_0=1-\eta u>0.
\tag{19}
\]
If rho>=1, (17) gives u>rho v>=v, whereas
eta u=uv+rho u^2>=uv+u^2>1, contradicting (19). Hence
\[
                                  a>b.
\tag{20}
\]
No inequality A_0>B_0 is asserted or needed.

Let p=(p_C)_y. From |p_C|^2=D^2+1/4, p_A=p_C-e_y,
z_A=p_A+t_A and |z_A|^2=(D+1)^2+1/4, one obtains exactly
\[
                             B_0=D+\frac12+p.
\tag{21}
\]
Since A_0>1/2, (18) and the circle equation give B_0<D+1. Thus
p<1/2. As p=Dc-d/2, this forces
\[
                                  d>1/2.
\tag{22}
\]
Indeed d<=1/2 would give c>=sqrt(3)/2 and
p>(9/10)sqrt(3)/2-1/4>1/2, using sqrt(3)>5/3.

If sigma=1 in (12), the two H contacts have squared distance
\[
        |q_C-q_A|^2
          =3+2v+2d(1+v)-2cu>2,
\tag{23}
\]
by d>1/2 and cu<1. So H-owned and free HC are both excluded.

It remains that C owns HC, with 1/2<sigma<1 by (13). Now
\[
             |q_C-q_A|^2=(\sigma c-u)^2+(1+\sigma d+v)^2.
\tag{24}
\]
This expression strictly increases with sigma>=1/2, since its
derivative is 2[sigma+d(1+v)-cu]>0. At sigma=1/2 it exceeds
\[
                         \frac74+\frac52v.
\]
H's diameter therefore forces v<1/10, hence u>99/100.

The C-owned application is H's actual upper vertex. If
q_A=P+tau w_H with 0<tau<1, taking the v_H-projection of
q_C-q_A=v_H-tau w_H gives
\[
                 \sigma(ac+bd)=1+au-b(1+v).
\tag{25}
\]
By (20), b<1/sqrt(2), and
\[
 au-b(1+v)=(a-b)u+b(u-1-v)
                      >-\frac{11}{100\sqrt2}>-\frac1{10}.
\]
Since ac+bd<=1, (25) forces sigma>9/10. But then the actual
vertical contact difference is
\[
                      1+\sigma d+v>1+\frac9{20}
                                  =\frac{29}{20}>\sqrt2,
\tag{26}
\]
again impossible for two points of H. This excludes the entire
H-owned/oblique-A branch, including every original C mean and
all its side/free owner limits.

## 7. H owns HA and A is parallel to U: exact scalar routing

The actual A application is its upper-right vertex q_A. Write
\[
          z_A=(-V,-W),\quad V,W>1/2,\quad
          q_A=(1-V,1-W)=P+\tau w_H,\quad 0<\tau<1.
\tag{27}
\]
The force has both coordinates negative. Put p=(p_C)_y,
Z=-(p_C)_x. The geometry and circle equations give
\[
 \begin{gathered}
 p=Dc-d/2,\quad Z=Dd+c/2,\quad
 W=2-p,\quad V=\sqrt{R^2-W^2},\\
 \ell=(q_A)_x-x=1+Z-V,\qquad 0<\ell\le1.
 \end{gathered}
\tag{28}
\]
The last interval is the actual AU shared-side mean interval; it has
not been chosen. If F_A=k z_A, the true force and moment equations
give, with rho=b/a,
\[
             \mu a=kV,\qquad \gamma=k(W-\rho V)>0,\qquad
             \gamma\ell=k(W-V).
\tag{29}
\]
Hence W>V and
\[
           \rho=\frac{W-(W-V)/\ell}{V}\in(0,1],\qquad a\ge b.
\tag{30}
\]

Every remaining HC normal implies
\[
                              K:=bc-ad\ge0,\qquad c\ge d.
\tag{31}
\]
For a C-owned inner face, its H upper-vertex normal t_C has
t_C.v_H=K>=0. For an H-owned contact, the C outward normal w_H
at p_C+r_C has w_H.r_C=K>=0. For a free contact, its outward-H
normal has the form -lambda r_C+nu t_C, lambda,nu>0, and positive
v_H-coordinate forces nu K-lambda(ac+bd)>0. These exhaust the
whole actual HC owner cover; no radial mask was converted to a
unique corner.

In (12), the H application also has the form P+lambda v_H with
0<lambda<=1. Taking the w_H-projection of the two actual applications
gives
\[
                        \tau=a+b\ell-\sigma K.
\]
Since tau<1 and sigma<=1, equation (31) implies
\[
                        a+b\ell-(bc-ad)-1\le0.
\tag{32}
\]
All hypotheses of C4_MIXED_PARALLEL_TIP_SCALAR_BOUND.md are now
proved from the actual frame, weights and application means. Its
complete analytic theorem gives
\[
        F:=R^2-V-W-\frac12\{a(V+W)+b(W-V)\}>0.
\tag{33}
\]
Finally z_A.w_H=aW-bV=a(W-rho V)>0 by (29), and
c_H=q_A+v_H/2+(1/2-tau)w_H. Thus
\[
                             c_H\cdot z_A>F>0,
\tag{34}
\]
contradicting (3). This excludes the whole last branch, retaining
the closed mean endpoint ell=1 and all actual C owner alternatives.

## 8. Complete compatible cover and precise scope

The canonical packing and the actual HU contact are obtained with
all six core units and all three other units retained. Before stress
extraction, prelist every physical mixed assignment, both reflected
roles, every transmitter axis, the unique A corner and all radial C
masks. Impose the finite unique-tip and shared A+U virtual-work
exclusions of Section 3 together with the earlier strict, nonradial,
matched-junction and generic choices. No determinant there depends
on an adjustable radial corner weight or an actual shared mean.
Uncrossing preserves surviving point normals and adds only genuine
shared interfaces; every possible final case is already covered.
Thinning only deletes atoms.

Section 2 covers every parallel C frame. Section 3 removes every
free unique HA interface with its actual fixed/shared neighbor.
Section 5 covers the entire A-owned HA case. Sections 6--7 cover
both complete A frames when H owns HA, and retain every C side,
H side and free HC normal. Thus the mixed physical mask is wholly
excluded. The only use of an individual negative pressure was the
actual consequence (3) of the intact end triangle and the full
radial-neighbor theorem.

The result is canonical lower-bound exclusion, not a claim about
every noncanonical stressed core or about the original equality
packings. No degree-two equation was assigned to H, no petal force
or actual unit was deleted, and no numerical premise, Lean compilation
or CI enters the proof.
