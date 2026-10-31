# A shared side at a negative endpoint cannot be followed by a free boundary interface

**Status: complete whole-domain hand selection and geometric exclusion; root and separate independent full source, selection-compatibility, geometry and scope audits passed.**

Work in the actual triangle-attached component H--A--B--C--H with its intact HXY petal, all true degrees H4 and A2,B2,C2, positive circle loads at A,B,C, and all three original completion squares. A and B have one physical circle corner each. C retains either physical circle mask and every original individual weight. Suppose
\[
 79/40\le R\le\sqrt{1105}/16,\qquad q=R^2,\qquad
 c_H\cdot z_A<0.
\tag{1}
\]
HA is genuinely shared and its normal is A-owned. AB is a genuinely free point-only vertex/vertex contact.

**Theorem.** This whole family is impossible. The proof retains every original HA and BC shared mean, every HC owner, all additional H forces, and every individual radial-C zero-weight endpoint.

The finite two-body block exclusions in Section 3 are imposed together with the common strict and fixed-tip choices before multiplier extraction. Their compatibility and full scope are proved there. No selected normal or extracted force is changed afterward.

## 1. The actual endpoint and shared H side

NEGATIVE_UNIQUE_ENDPOINT_OWNED_CONTACT_DOMAIN.md gives the full-window frame
\[
 \begin{gathered}
 A=[a-1,a]\times[b-1,b],\quad z_A=(a,b),\quad a^2+b^2=q,\\
 1<a<2,\quad 3/5<b<5/3,\qquad
 T=A\cap B=(a-1,b),\\
 g_{A\to B}=(-u,v),\quad u,v>0.
 \end{gathered}
\tag{2}
\]
It also supplies the unchanged proper concurrence and HA mean
\[
 q_A=\kappa(a,b)\in A,\qquad
 Q=(\kappa a,b-1),\qquad0<\kappa b<2/3.
\tag{3}
\]
No shared mean in (3) is assigned an endpoint.

Since HA has positive length, H has the same side axes and lies below A. For an original geometric overlap parameter ell,
\[
 H=[a-2+\ell,a-1+\ell]\times[b-2,b-1],\qquad0<\ell<2.
\tag{4}
\]
In fact
\[
                              0<\ell<1.
\tag{5}
\]
If \(\ell\ge1\), then \(c_H{}_x\ge a-1/2\), so
\[
 c_H\cdot z_A
 \ge q-\frac a2-\frac{3b}{2}
 >q-1-\frac52>0,
\]
contrary to (1). Here \(q\ge6241/1600>7/2\), and the strict coordinate bounds are (2).

Thus the entire actual H lies below \(y=b-1\), whereas the free AB point T has height b. In particular no HC singleton application can equal T.

## 2. The actual BC contact must be genuinely shared

Suppose BC were a singleton. Then the physically unique true degree-two B would have two fixed singleton applications, one of which is the free AB vertex T.

The coincident-point possibility is impossible. In B's own corner frame, a non-circle vertex collinear with its unique corner can only be the radial-D inner vertex, with norm \(R-\sqrt2\). Two interior-disjoint boundary units cannot share such a point: equality in
\[
 R\le |T|+|z-T|\le(R-\sqrt2)+\sqrt2=R
\]
forces both units to have the same containing-circle corner, which is unshareable. Therefore \(\det(T,z_B)\ne0\). If both B applications were T, its actual torque about T and positive circle load would instead force \(\det(T,z_B)=0\).

For distinct fixed applications, GENERAL_FIXED_TIP_NORMAL_SELECTION.md excludes a free AB in the common selected certificate. This is a contradiction as well. Hence BC has positive length. B and C are parallel, and its original mean remains anywhere in their actual shared segment.

## 3. Unique C with singleton HC: a complete compatible two-body block selection

Suppose C has one physical circle corner and HC is a singleton. Let p=T be the free AB vertex on B and let r be the fixed HC point on C. They are distinct, since \(p_y=b\) while \(r_y\le b-1\) by (4). The two external normal parameters therefore belong to distinct physical junctions.

Let e be the actual common BC side normal, and let \(z_B,z_C\) be the unique physical circle corners. In their common orthonormal side frame every corner coordinate has nonzero absolute value greater than \(1/2\). Define
\[
 w_B=Jz_B,\qquad
 w_C=\frac{e\cdot Jz_B}{e\cdot Jz_C}\,Jz_C.
\tag{6}
\]
Both scalar factors are nonzero. These pure translations annihilate the two radial circle forces and satisfy
\[
                       e\cdot(w_C-w_B)=0.
\]
They consequently annihilate the actual internal BC work for every value of its original mean and magnitude. A common rigid rotation of B+C about the true origin is a second virtual motion annihilating the same circle and internal contact forces.

Write n for the outward normal from B into A and m for the outward normal from C into H, with original positive magnitudes mu,nu. The two exact work equations are
\[
 \begin{split}
 \mu\det(p,n)+\nu\det(r,m)&=0,\\
 \mu(n\cdot w_B)+\nu(m\cdot w_C)&=0.
 \end{split}
\]
Eliminating mu,nu gives the necessary relation
\[
 D(n,m)=\det(p,n)(m\cdot w_C)
                 -\det(r,m)(n\cdot Jz_B)=0.
\tag{7}
\]

For any positive candidate, m cannot be parallel to \(z_C\). If it were, C's circle force and its HC force would both be parallel to \(z_C\), while its remaining positive BC force is along a side axis, which is not parallel to a unique circle corner with two nonzero own coordinates. C's true two-force equation could not hold. Therefore
\[
                              m\cdot w_C\ne0.
\tag{8}
\]
Section 2 already proved that p and \(z_B\) are linearly independent. As a linear function of the free n, (7) has coefficient
\[
                    W=(m\cdot w_C)Jp-\det(r,m)Jz_B.
\]
Equations (8) and that independence give \(W\ne0\). This argument does not assume that the H/C contact has nonzero origin moment or that H touches the circle.

For fixed genuine m, a nonzero linear condition excludes at most two unit directions from the open free interval for n. If m is also free, choose it nonparallel to \(z_C\); the same calculation shows that D is not identically zero on the product of the two independent open normal intervals. Its analytic zero set has empty interior. The parallel-m exception has no positive candidate and needs no avoidance condition.

For completeness, make this selection simultaneously before extracting multipliers. Prelist every ordered physical H,A,B,C candidate in the standing family, with A physically boundary, HA genuinely shared, unique B,C, physical shared BC, and singleton external AB,HC points. Include every possible actual shared pair that uncrossing could leave, and all external owner possibilities. For each candidate with free AB and with the geometric endpoint separation in (4), avoid the nontrivial condition (7), together with the previous finite strict and fixed-tip exclusions. There are finitely many physical squares, contact points and corner choices. The matched opposite-pair convention at a four-square junction does not couple p and r, because these are distinct points. Thus the allowed choices retain a nonempty open dense set.

Uncrossing does not change a surviving free normal and only adds physical shared contacts already in the prelist. Thinning deletes atoms. All internal means were retained in deriving (7), and the motions give zero velocity to A,H and every other square; none of their forces is removed. The final positive B/C block would violate its prelisted exclusion. This rules out the entire unique-C/singleton-HC family.

## 4. Unique C with shared HC: the entire parallel geometry is impossible

Now suppose C is unique and HC has positive length. HA, BC and HC make all four square frames parallel. Since the actual AB normal in (2) is strictly northwest, the B vertex at T is its lower right vertex. Thus
\[
                   B=[a-2,a-1]\times[b,b+1].
\tag{9}
\]
Its farthest vertical coordinate is b+1.

If \(a\le3/2\), its farthest horizontal absolute value is \(2-a\). Equality of the two physical circle radii gives
\[
                 (2-a)^2+(b+1)^2=a^2+b^2,
                 \qquad b=2a-\frac52\le\frac12,
\]
contradicting \(b>3/5\). Therefore \(a>3/2\). The far horizontal coordinate of B is now a-1, and the circle equality gives
\[
                              b=a-1,\qquad1/2<b<1.
\tag{10}
\]

B lies in \(y\ge b\), and H lies in \(y\le b-1\). Any parallel unit C touching both must therefore have exactly the vertical interval
\[
                              [b-1,b].
\tag{11}
\]
Its interior is disjoint from A's interior, which has the same vertical interval. Hence either C lies horizontally left of A or right of A. The latter is impossible because H's right endpoint \(a-1+\ell<a\) by (5). Writing w for C's right endpoint, we have
\[
                         a-2<w\le a-1.
\tag{12}
\]
The strict lower bound follows from its physical H contact and H's left endpoint \(a-2+\ell>a-2\); positive shared length only strengthens it.

In (11), the largest absolute vertical coordinate is b. Circle containment therefore puts C's horizontal interval in \([-a,a]\), and physical circle contact requires either right endpoint a or left endpoint -a. Equation (12) excludes the first. The second gives \(w=1-a\). But (12) would then imply
\[
                         1-a>a-2,\qquad a<3/2,
\]
contradicting (10). This exhausts all unique-C HC types.

## 5. Radial C: the complete shared B/C pose and free AB vertex

Suppose instead that C has two physical circle corners. Use its actual radial frame, and reflect if necessary, so
\[
 \begin{gathered}
 C=[d,d+1]\times[-1/2,1/2],\\
 d=\sqrt{q-1/4}-1>91/100,\qquad
 N=\sqrt{q-9/4},\qquad 5/4<N\le23/16<3/2.
 \end{gathered}
\tag{13}
\]
Its shared BC side cannot be an outer radial face, by the width bound, or an inner radial face, by the complete radial-inner-face boundary-neighbor theorem in C7_FORCE_POLYGON.md, Lemma 2.1. Thus BC is tangential; choose B above C.

Their actual parallel frames and B's physical circle equality force
\[
                  B=[N-1,N]\times[1/2,3/2],
                  \qquad z_B=(N,3/2).
\tag{14}
\]
Indeed the other possible horizontal interval \([-N,1-N]\) cannot overlap C's positive interval. The unchanged BC mean has x coordinate in \([d,N]\), since \(d<N<d+1\).

The true B equation is
\[
                    \lambda z_B=\mu n+\gamma e_y,
                    \qquad\lambda,\mu,\gamma>0,
\]
where n points from A into B. Its first component gives \(n_x>0\). Since AB is free at a B vertex, its only possible points are the lower left and upper left vertices of (14).

The lower left point \(P_-=(N-1,1/2)\) is impossible for a boundary/boundary contact. The universal theorem in C7_PINNED_VERTEX_CONTACT_TYPES.md, Section 3, gives
\[
                         |P_-|\ge\sqrt{q-1}-1.
\]
Its proof has no C7 premise and holds for every \(R>\sqrt2\). Here, however,
\[
 |P_-|^2=q-2N-1<q-2\sqrt{q-1}
                   =(\sqrt{q-1}-1)^2,
\tag{15}
\]
because \(N+1/2>\sqrt{q-1}\), whose squared comparison is exactly \(N-1>0\). Thus the actual free point is
\[
                               P=(N-1,3/2).
\tag{16}
\]

## 6. The actual H is strictly separated from radial C

The same free point has squared norm \(q-2a+1\) in A's frame (2), and \(q-2N+1\) in (16). Hence
\[
                               a=N,\qquad b=3/2.
\tag{17}
\]
Because HA is shared, H's second center coordinate in that A frame is \(b-3/2=0\). Its original first center coordinate, call it h_A, satisfies
\[
                         N-3/2<h_A<0.
\tag{18}
\]
The lower strict bound is the positive HA overlap. The upper strict bound is precisely \(c_H\cdot z_A=N h_A<0\).

We now identify A's frame in the fixed radial-C coordinates, without moving any square. Put \(w=N-1\), so \(1/4<w<1/2\), and let e_A be A's first positive side direction. Its circle corner is \(z_A=P+e_A\). The two circle equations give
\[
                         P\cdot e_A=w,\qquad |e_A|=1.
\]
There are exactly two unit solutions. One is \(e_A=(1,0)\), which would give \(z_A=z_B\), an unshareable circle point. The other is
\[
 e_A=(-C_0,S_0),\qquad
 C_0=\frac{9/4-w^2}{9/4+w^2}>0,\qquad
 S_0=\frac{3w}{9/4+w^2}>0.
\tag{19}
\]
The second positive A side direction is \(f_A=(S_0,C_0)\), determined by \(P\cdot f_A=b=3/2\). These are orthonormal; the corner frame is allowed to reverse orientation.

The original H center is therefore \(h_Ae_A\). Its maximum first coordinate in the radial-C frame is
\[
 \begin{split}
 \max_{X\in H}X_x
 &=-h_A C_0+\frac{C_0+S_0}{2}\\
 &<(2-N)C_0+\frac{S_0}{2}
   =\frac{9/4-(3/4)w-w^2+w^3}{9/4+w^2}.
 \end{split}
\tag{20}
\]
This full support bound retains the original h_A and hence every HA mean. On the entire interval \(1/4<w<1/2\),
\[
 \begin{split}
 &9/4-(3/4)w-w^2+w^3
       -\frac9{10}(9/4+w^2)\\
 &=\frac9{40}-\frac34w-\frac{19}{10}w^2+w^3\\
 &<\frac9{40}-\frac34w-\frac75w^2
 <-\frac1{20}.
 \end{split}
\tag{21}
\]
The first strict inequality uses \(w^3<w^2/2\); the decreasing quadratic in the next line equals \(-1/20\) at \(w=1/4\). Consequently
\[
                         \max_{X\in H}X_x<9/10<d
                                  =\min_{Y\in C}Y_x.
\tag{22}
\]
H and C are strictly separated, contradicting their actual physical contact. This excludes the entire radial-C case, with no C force equation or assumption that both radial weights are positive.

## 7. Exhaustion and retained data

AB free forces BC genuinely shared at the true unique B. A unique C is excluded whether HC is singleton or shared. A radial C has the exact full shared pose (14), and its only remaining free AB vertex yields the strict physical separator (22). These are every C mask and every HC contact type.

The proof is uniform throughout the original radius window. It leaves every original shared application free until an actual equation determines it, and never uses a degree-two equation at H. All H4/petal forces, C's two physical corner weights including their zero endpoints, and all three arbitrary completion squares remain. The virtual-work calculation only moves B,C infinitesimally as a test of their unchanged equations; it is not a physical motion or a new certificate. No HB chord, post-extraction normal choice, force deletion, sampled angle domain, Lean compilation or CI is used.
