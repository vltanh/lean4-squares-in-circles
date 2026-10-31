# The full tilted S-leaf bowtie domain has positive upstream concurrences and three exact interfaces

**Status: complete hand domain reduction; root and separate independent
full audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 D=\sqrt{R^2-\frac14}-1,\qquad
 \frac{91}{100}<D<\frac{61}{60}.
\tag{1}
\]
The exact positive graph is H--A--B--H, H--C--E--H, with the leaf
A--L. L is radial S. A has degree three, H degree four, and B,C,E
degree two. All three arbitrary completion squares remain fixed.

A is physically circle-clear. B,C,E are loaded, because an unloaded
degree-two transmitter cannot have touching neighbors. H is physically
clear, since otherwise H,C,E form a forbidden boundary triangle.
Write M=F_C+F_E for the whole opposite-petal resultant. We retain
\[
                    M\ne0,\qquad h_H(M/|M|)<D.
\tag{2}
\]
These are the full end-triangle conclusions at the actual degree-four
root; C,E are never replaced by an abstract leaf.

Reflect in the leaf axis if necessary. The entire tilted articulation is
\[
 A=R_0+[0,1]u+[0,1]v,\qquad R_0=D e_x,
 \qquad u=(-a,-b),\quad v=(-b,a),
\]
\[
                 a\ge b>0,\qquad a^2+b^2=1.
\tag{3}
\]
The four A vertices, in its coordinates based at R_0, are 0,
P=(1,0), Q=(0,1), W=(1,1). Their original coordinates are
R_0, R_0+u, R_0+v, R_0+u+v. In this source u,v coordinates
are used only for ordinary vector components and supports; any
determinant equation uses a consistently oriented frame.

## 1. The A contacts are distinct and its two normals independent

No third unit can contain R_0. L occupies a half-plane locally there,
and the tilted A occupies a strictly internal ninety-degree sector of
the opposite half-plane. Each remaining sector is strictly narrower
than ninety degrees, whereas a unit through that point needs a local
sector of at least ninety degrees.

Let n point A to B and m point A to H, with magnitudes mu,nu>0.
Normalize the leaf magnitude to one. The true A force equation is
\[
                          \mu n+\nu m=-e_x.
\tag{4}
\]
If the two applications coincided at p, the vector -e_x would be an
outward normal of A at p. Thus p is its unique leftmost vertex W.
The zero origin torque of the leaf gives p_y=0, hence a=b. But then
\[
 |p|=\sqrt2-D<R-\sqrt2,
\]
contrary to p belonging to the boundary square B. The strict comparison
follows already from R>=79/40, D>91/100 and sqrt(2)<10/7.

Opposite parallel n,m would separate B,H beyond opposite A supports,
preventing their physical contact. Equal parallel directions would both
be -e_x by (4), and would give the coincident W applications just
excluded. Hence n,m are independent. Their normal lines intersect at
q_A. A's true torque makes q_A parallel to e_x.

Let g point B to H, with magnitude gamma>0 and actual application T.
The genuine B and H equations are
\[
                F_B=\mu n-\gamma g,\qquad
                M=\nu m+\gamma g.
\tag{5}
\]
The incoming H torque is zero about the circle origin, after summing
the actual C,E torque equations. Thus, when its two incoming lines
are independent, their intersection q_H is parallel to M.

## 2. The full positive-concurrence cover, including parallel H inputs

The purely geometric behind-ports statement in
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md, Section 2, applies to
every root of the physical triangle A,B,H. It needs no circle load
or degree-two equation at that root.

### 2.1. Parallel incoming H forces

If g=-m, A and B lie beyond opposite H supports and could not touch.
Thus the only parallel-H alternative is g=m, for which
\[
                              M=(\nu+\gamma)m.
\tag{6a}
\]
B's forces are nonparallel because n,m are independent. Its proper
concurrence has the form q_B=q_A+U n with U>=0. Write
q_A=tau(mu n+nu m) and q_B=kappa(mu n-gamma m), kappa>0.
Comparison of m-coordinates gives tau nu=-kappa gamma<0. Thus
q_A=q e_x with q>0 in this entire alternative too. No finite H
concurrence is asserted for parallel incoming lines.

If the AH application is a strict minimum-m vertex of H, the BH
application must be that same vertex, since g=m. Then q_B=q_A,
and comparison of n-coordinates would give tau=kappa>0, a contradiction.
Consequently the parallel-H alternative can only occur when the
minimum-m support of H is a side. Its full axis resultant (6a) is
retained in the subsequent interface arguments.

### 2.2. Nonparallel B and H forces

The conditional nonparallel part of the proper loaded-tip theorem in
TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies to B.
Its boundary-neighbor hypothesis was used only to establish
nonparallelism; here that premise is supplied by this case. Its
concurrence q_B is a positive multiple of F_B, behind both actual
applications, for every physical B mask and corner-weight split.

Combining the three behind-port statements gives
\[
 q_B=q_A+U n,\qquad q_H=q_A+V m,\qquad
 q_H-q_B=W_0 g,\qquad U,V,W_0\ge0.
\tag{6}
\]
Here W_0 cannot vanish: independence of n,m would then give U=V=0,
and all three actual applications would coincide, contrary to Section 1.
Also V>0, since otherwise g would be parallel to n, contrary to this
case. Write q_A=tau(mu n+nu m). From (5)--(6),
\[
 F_B=\left(\mu+\frac{\gamma U}{W_0}\right)n
                -\frac{\gamma V}{W_0}m,
 \qquad q_B=(\tau\mu+U)n+\tau\nu m.
\]
The positive proportionality q_B to F_B gives tau<0 by comparing
m-coordinates. The n-coordinate of q_H is then tau mu<0.
Its proportionality to M forces U>0 and makes that proportionality
positive. In particular the H input lines are independent: if g were
parallel to m, (6) would force U=0. We have proved
\[
                         q_A=q e_x,\quad q>0,
                    \qquad q_H\in(0,\infty)M.
\tag{7}
\]

### 2.3. Parallel B forces, with every actual mean retained

Opposite-sign parallel forces at a loaded unit would require a neighbor
beyond an actual circle corner or beyond its outer radial-S face.
Neither fits in the disk. This is the neighbor-free width argument in
the first paragraph of the same proper-concurrence proof.
The remaining case is g=-n, so F_B=(mu+gamma)n. Lemma N.4 of
PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md gives physical radial S or D
geometry and a weighted-mean application r_B n, where
\[
                  r_B=D\quad\hbox{or}\quad r_B=R-\sqrt2.
\]
Both real B applications belong to its inner support. Their original
means need not individually be radial.

The pure A,H behind-port statements give
\[
 p_{AB}=q_A+\alpha n,\quad p_{AH}=q_A+\beta m
          =q_H-\delta m,\quad
 p_{BH}=q_H+\epsilon n,
\]
with alpha,beta,delta,epsilon>=0. Put s=beta+delta, so
q_H=q_A+s m. Taking the weighted average of the two B applications
and comparing its m-coordinate gives
\[
       \tau\nu(\mu+\gamma)+\gamma s=0.
\tag{8}
\]
If s>0, then tau<0 and
\[
             q_H=\frac{s\mu}{\nu(\mu+\gamma)}
                          (\nu m-\gamma n).
\tag{9}
\]
This proves (7), including its strict H sign, in the entire parallel
case as well.

If s=0, (8) gives q_A=q_H=p_AH=0. The two B applications coincide
at p=r_B n. They cannot equal the AH application, by Section 1.
Consequently A,H share the nondegenerate segment from0 to p. Their
common frames own n and m, with n perpendicular to m. A occupies
\[
                    [r_B-1,r_B]n+[-1,0]m.
\tag{10}
\]
For radial D, p is a vertex of B and A; their positive normal n is
an A-side axis at a singleton vertex/vertex contact, forbidden by the
selected strict point-normal convention. For radial S, the leaf
direction in (4) strictly exposes the A vertex (D-1)n-m. Its norm
must be D, giving (D-1)^2+1=D^2 and hence D=1. That vertex would
then be -m, making the leaf direction -m and contradicting mu>0
in (4). Thus s=0 is impossible. This completes (7) without discarding
parallel B forces or replacing any shared mean.

## 3. A whole-frame support estimate removes the high A interfaces

Set sigma=D-q. In A coordinates q_A=(sigma a,sigma b).
We have sigma>=0. Indeed an A-owned normal on either near face
would contradict (4), by the unit-triangle owned-normal lemma. If
sigma<0, the normal line from q_A to either adjacent vertex has
the wrong strict sign for that vertex. The only remaining non-leaf
vertex is W. Positive owned +u or +v contacts are unavailable too:
their actual transverse means would be sigma b or sigma a, respectively,
which are negative and outside the A side. Thus the two applications
would coincide at W. Therefore
\[
                            0\le\sigma<D.
\tag{11}
\]

We use the whole-frame estimate proved in
TIP_LEAF_BOWTIE_D_PARALLEL_EXCLUSION.md, Section 4. In rotated form:
if a unit S has a minimum-m support point p, rho=p·m>0, and a positive
ray e meets p+[0,infinity)m, then
\[
                              h_S(e)\ge2\sqrt\rho.
\tag{12}
\]
The proof includes a strict supporting vertex, a full side, and every
side-mean endpoint. The support increment in direction e is at least
its component along m; minimizing over the ray sector gives endpoint
values 1+rho and |p|+rho/|p|, both at least2sqrt(rho).

An H contact at W has its outward A-normal in the own-coordinate
sector between the diagonal and +v, because a>=b and (11).
Its original support height is at least
\[
                              1-\frac{D}{\sqrt2}.
\tag{13}
\]
For completeness, the support as the normal angle theta varies from
pi/4 to pi/2 is
(1-Da)cos(theta)+(1-Db)sin(theta). If 1-Da is negative this is
increasing; otherwise it is concave. Its endpoint minimum is at least
1-D/sqrt(2). The diagonal endpoint uses a+b<=sqrt(2) and D<sqrt(2).
An A-owned +v contact has the same lower bound directly.

Both heights are greater than D^2/4. One exact coarse comparison is
\[
 1-\frac{D}{\sqrt2}>\frac{23}{84}
       >\frac{3721}{14400}>\frac{D^2}{4}.
\tag{14}
\]
For nonparallel H inputs, (7) puts their concurrence on the positive
M ray, and the behind-port statement makes it p_AH+t m with t>=0.
Equations (12)--(14) contradict (2). For parallel H inputs, (6a)
makes M a positive multiple of m, and the whole-unit width gives
h_H(M/|M|)>=rho+1>D directly. Thus H uses neither W nor an A-owned +v
contact. If a=b, the +u support has the same bound too; all remaining
cases below then disappear. Hence a>b in any surviving interface.
Explicitly, at a=b the strict P/W pair would have positive
unnormalized P-normal coefficient
lambda_P=(a-b)/(1-sigma a)=0, which is impossible; the +u/W
pair has the same zero-coefficient obstruction. The two owned axes
are excluded by their high +u or +v support just proved.

## 4. Exhaustive A-feature routing

Near A-owned axes -u,-v are impossible: their nonnegative dot product
with the other triangle normal would contradict the corresponding
negative component of (4). The leaf vertex is unavailable by Section 1.
For a strict vertex contact the vector from q_A to that vertex is a
positive multiple of its outward normal.

Opposite strict vertices P,Q cannot both be used by a physical unit
triangle. The upper vertex Q cannot pair with an A-owned +u normal,
by the owned-normal nonobtuse lemma; it cannot pair with +v because
the resulting u-component is negative. Pairing Q with W is impossible
as well: writing the two positive normal coefficients before
normalization, their v-equation is
\[
             (1-\sigma b)(\lambda_Q+\lambda_W)=b,
\]
and their u-equation forces
\[
                  \lambda_Q=\frac{b-a}{1-\sigma b}<0.
\]
The alternative +v together with W similarly gives a negative +v
coefficient. The pair +u with P has negative v-component, and +v
with P contradicts the owned-normal lemma. Coincident vertices were
already excluded.

After the high-H exclusions of Section 3, the full remaining cover is
therefore exactly:

1. H uses P and B uses W, both strict A-vertex contacts;
2. H has actual normal +u and B uses W;
3. H has actual normal +u and B has actual normal +v.

In the last two cases H is either parallel to A or has a strict
minimum-u vertex at its actual AH application. Those are the two
geometric subfamilies of the A-owned-H interface; neither is omitted.

## 5. The strict P/W interface has both neighbor-owned normals

In case1, both A applications are fixed distinct vertices. Their
original heights are -b and a-b, both nonzero; their normal vertical
components have the corresponding strict signs. Eliminating the A
magnitudes from vertical balance and origin torque gives
\[
 n_y\det(p_{AH},m)-m_y\det(p_{AB},n)=0.
\tag{15}
\]
If AB is free, the coefficient of n_x in (15) is
m_y(p_AB)_y, which is nonzero. If AH is free, the coefficient of m_x
is -n_y(p_AH)_y, again nonzero. The simultaneous finite open-dense
selection used in the D-leaf articulation source therefore leaves
no free A edge. It requires no load or degree-two equation at H.

Prelist every such physical tilted-S A-star, with arbitrary positive
degrees and physical masks at its two triangle neighbors, before
the multiplier theorem. The two A vertices are distinct physical
junctions, so matched four-junction choices do not couple their
parameters. Impose (15)'s avoidance with the earlier finite exclusions.
Uncrossing preserves surviving point normals and adds only genuine
shared-side forces; thinning only deletes atoms. Every eventual
strict P/W star was in the prelist, and any added A-side alternative
is already retained in cases2--3.

Thus in case1 AB is owned by B and AH by H, with the A vertex in the
relative interior of the corresponding neighbor side. An axis endpoint
at a singleton vertex/vertex contact would violate the same strict
point-normal convention. All mutual BH owner, free-normal and side-mean
possibilities remain for the subsequent whole case proof.

## 6. Exact scope

The reduction retains all physical B masks, including the parallel
radial-S weighted-mean case. It proves the positive A concurrence,
and either the positive H concurrence or the explicitly retained
parallel-H axis alternative, before using those conclusions.
Its three actual interface alternatives are
exhaustive for the entire tilted S articulation. It supplies a domain
for the subsequent full exclusions; it is not itself a capacity claim.
No extra square is moved, no H force is discarded, and no extracted
normal is reselected after multipliers are known.
