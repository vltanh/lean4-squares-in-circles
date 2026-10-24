# An end triangle cannot attach to one high root side

**Status: complete uniform hand exclusion at the strengthened 39/40
threshold; root and separate independent full hand audits passed.** Work in
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1<\frac{61}{60}.
\tag{1}
\]
Let H,C,E be a physical positive triangle, with C,E exact positive
degree-two loaded tips. H may have arbitrary additional positive
neighbors. Use the common selected certificate of
BOWTIE_CELL_CLOSED.md, Section 1.

**Theorem.** The two actual HC,HE applications cannot both belong
to one side of H whose outward unit normal N and support height P
satisfy
\[
                              N\cdot x=P,\qquad P\ge39/40.
\tag{2}
\]
The applications are the actual aggregate means on shared sides.
The conclusion includes their endpoints, all tip circle masks, and
all root/tip/free contact owners. No equation at H is reduced to
degree two.

## 1. Nonparallel root forces and their complete signs

Write n_C,n_E for the outward root normals and M=F_C+F_E for
the whole two-tip circle resultant. The end-triangle theorem gives
M nonzero. When the root normals are nonparallel, their intersection
q satisfies
\[
               q=-tM,\qquad t>0,\qquad
               p_i=q+a_i n_i,\quad a_i\ge0.
\tag{3}
\]
These are Sections 2--3 of
END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md; they use the actual
degree-two equations only at C,E.

Because both p_i lie on the side (2), every outward root normal
there has nonnegative N-component. Thus M has nonnegative
N-component, q has nonpositive N-component, and (3) implies
\[
                         a_i(n_i\cdot N)=P-q\cdot N>0.
\tag{4}
\]
Both a_i and both normal N-components are strictly positive.
In particular a root-owned side axis must be N, not one of the
two tangential axes.

If neither normal equals N, their applications must be the two
different endpoints of the side. A coincident endpoint would put
q at that endpoint, contradicting q·N<=0<P. The two normals have
opposite nonzero tangential components. If one normal is N, the
other application is an endpoint with its corresponding strict
tangential sign.

Let n be one strict endpoint normal. Choose its own perpendicular
unit direction v so that
\[
 N=c n-bv,\qquad c>0,\quad b>0.
\]
The other root normal lies strictly on the other side of n from v,
so the positive sum M lies strictly between the two directions.
Equation (3) therefore gives
\[
               p_n:=p\cdot n>0,\qquad p_v:=p\cdot v>0,
               \qquad P=c p_n-bp_v.
\tag{5}
\]
Explicitly, for the upper endpoint take v=Jn: then
p_v=det(n,p)=-t det(n,M)>0. For the lower endpoint take v=-Jn.
This includes the case in which the other root normal is N.

The contained tip beyond the support n·x=p_n gives the sharp bound
\[
                                  P\le p_n\le d.
\tag{6}
\]
The first inequality follows from (5), since c<=1.

## 2. Every side-owned interface puts both tip centers in one narrow cap

A root-owned N contact puts its whole tip in N·x>=P. Therefore
its center z satisfies
\[
                                 z\cdot N\ge P+\frac12.
\tag{7}
\]
This does not assume that the tip frame is parallel to H.

Consider instead a contact owned by its tip, with n strict at a
root endpoint. In the frame n,v of (5), its center has n-coordinate
p_n+1/2. The proper loaded-tip concurrence lies at
\[
                          q_T=p+\ell n,\qquad \ell\ge0,
\tag{8}
\]
on a positive multiple of the actual circle resultant.

First suppose the tip has one physical circle corner. Its far
n-coordinate is p_n+1>0, and (8) makes its far v-coordinate
positive. Write that unique corner and its center as
\[
                 Z=(p_n+1,Y),\qquad
                 z=(p_n+\tfrac12,Y-\tfrac12),\qquad Y>0.
\tag{9}
\]
No other corner can maximize the n-contribution because
p_n>0. The proper concurrence is a positive multiple of Z.
Comparing its v-coordinate and then its n-coordinate gives
\[
                         Y\le\frac{p_n+1}{p_n}\,p_v.
\tag{10}
\]
Consequently
\[
\begin{aligned}
 z\cdot N
 &=c(p_n+\tfrac12)-b(Y-\tfrac12)\\
 &\ge P+\frac12(c+b)-\frac{bp_v}{p_n}\\
 &=P+\frac{P}{p_n}-\frac c2+\frac b2\\
 &\ge P+\frac Pd-\frac12.
\end{aligned}
\tag{11}
\]
The identity uses bp_v=c p_n-P. All inequalities are uniform
up to the genuine side-mean endpoints.

If the tip has two physical circle corners, its center is radial
along one of its side axes. Its strictly positive n-coordinate
p_n+1/2 rules out a transverse radial axis and the negative n-axis.
It is therefore radial S along n, with p_n=d and center
z=(d+1/2)n. Equation (5) gives c>=P/d, so
\[
                 z\cdot N\ge P+\frac{P}{2d}
                    \ge P+\frac Pd-\frac12.
\tag{12}
\]
The last step uses P<=d. No equality of the two corner weights
was assumed.

The common lower bound in (11)--(12), also implied by (7), is
\[
             P+\frac Pd-\frac12
             \ge\frac{39}{40}+\frac{117}{122}-\frac12
             =\frac{3499}{2440}=:c_*.
\tag{13}
\]
Every unit center has norm strictly less than 91/60. Two centers
in the cap z·N>=c_* consequently have squared distance less than
\[
             4\left[\left(\frac{91}{60}\right)^2
                       -\left(\frac{3499}{2440}\right)^2\right]
                    =1-\frac{65641}{2679120}<1.
\tag{14}
\]
For completeness, the cap diameter is its transverse boundary chord:
the two endpoint angles have absolute value below
arccos(c_*/(91/60))<pi/2, and the maximal chord joins the two
extreme angles. This contradicts the unit-center separation of
interior-disjoint unit squares.

Thus every nonparallel interface with no free root edge is excluded.

## 3. The entire parallel root interface

Parallel root normals cannot be opposite, because their two tips
would lie beyond opposite root supports and could not touch.
If their common normal is N, (7) puts both centers in the cap
(14), irrespective of means and tip frames.

Otherwise both actual applications coincide at one endpoint p
of the side (2). If the common normal is tangent to that side,
the total origin torque is a nonzero multiple of det(p,n), whose
absolute value is P>0, impossible.

For a strict endpoint normal n, its N-component is positive.
The total tip torque gives det(p,n)=0, and p·N=P>0 therefore
makes p a positive multiple of n. The two loaded tips have
nonparallel pair forces: each has the other as a boundary neighbor,
so the full proper-concurrence theorem applies. Their respective
concurrences lie at p+ell_C n and p+ell_E n, with both ell
nonnegative. Both true circle resultants would thus have the same
radial direction n. That is impossible for distinct boundary
squares: their center directions differ by more than40 degrees,
whereas each full circle-resultant direction differs from its
center direction by less than15 degrees.

This excludes every parallel alternative and coincident mean.

## 4. A free root edge with two radial tips is impossible

Suppose HC is free and C,E both have two physical circle corners.
The complete local routing in
BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md, Section 1, applies
without a unique-mask premise at the other boundary tip.
Rotate so
\[
 C=[d,d+1]\times[-\tfrac12,\tfrac12],\qquad
 Q=(d,\tfrac12)=H\cap C,\qquad T=(d,-\tfrac12)=C\cap E.
\tag{15}
\]
In particular CE is a singleton at the other inner C vertex.
The point T has norm sqrt(d^2+1/4).

On the radial square E, T cannot belong to an outer side or
outer corner, nor to its inner side's relative interior.
The former alternatives are excluded by the outer-face screen
and the latter by the boundary-inner-face theorem. If T lies on
a tangential side, its norm equals that side's minimum possible
norm only at the inner vertex. Thus T is an inner vertex of E.

The two radial orientations determined by T give C itself and
one distinct reflected radial square E. In E's own frame, T=(d,1/2)
and Q has coordinates
\[
 Q=\left(d-\frac{d}{d^2+1/4},\
       \frac12+\frac{d^2-1/4}{d^2+1/4}\right).
\tag{16}
\]
Here Q_n<d and Q_v>1/2; the two positive distances to those
support lines have squared sum1. Hence Q is strictly beyond both the inner and upper
supporting lines of E, and T is its unique nearest point, at
distance1.

The elementary free-vertex application lemma gives
|Q-P_E|<=1 for the actual HE application P_E; see
BOWTIE_SHARED_SIDE_FREE_INTERFACE.md, Section 1.1.
Therefore P_E=T. The whole segment QT belongs to H and to C,
contradicting that HC is a free singleton. This disposes of the
complete two-radial free mask.

## 5. Every remaining free root interface

Name a free root edge HC.

If C is unique and CE is a singleton, the compatible fixed-tip
selection removes HC. Its coincident radial-D exception cannot
touch the boundary neighbor E. If C and E are both unique and
CE is shared, the compatible two-tip block selection removes HC,
retaining the entire shared mean. These are precisely the
prelisted selections of BOWTIE_CELL_CLOSED.md, Section 1.

The two remaining physical-mask patterns have complete explicit
charts in the existing free-interface sources.

### 5.1. C is radial, E unique

If HE is a singleton, the whole singleton-root-interface theorem
in BOWTIE_RADIAL_FREE_INTERFACE_PRESSURE.md, Sections 2--4,
already excludes the case. It uses only the true degree-two
equations at C,E.

If HE is a shared side, Section 5 of that source gives, in the
common H,E frame,
\[
 H=Q+[-1,0]^2,\qquad
 Q=(d j-f/2,\ d f+j/2),\qquad
 f,j>0,\quad f^2+j^2=1.
\tag{17}
\]
The common root side containing both applications is its right
side, so its height in (2) is P=Q_x. The unique E circle corner is
\[
                            Z_E=(Q_x+1,\ Q_y-j-1).
\tag{18}
\]
If P>=39/40, (17) and d<61/60 imply f<1/12 and j>11/12.
It follows that
\[
                 Q_y-j-1=d f-j/2-1<-1,
                 \qquad Q_x+1\ge79/40.
\]
Thus
\[
                  |Z_E|^2>(79/40)^2+1>1105/256,
\]
contradicting containment. All shared HE means were retained in
the cited chart.

### 5.2. C is unique, E radial, and CE is shared

The complete chart in BOWTIE_SHARED_SIDE_FREE_INTERFACE.md,
Section 4, is
\[
\begin{gathered}
 Q=(Z-1,-1/2)=H\cap C,\qquad
 5/4<Z\le23/16,\\
 H=Q+[0,1]u+[0,1]v,\qquad
 u=(a,b),\quad v=(-b,a),\quad a,b>0,\quad a^2+b^2=1.
\end{gathered}
\tag{19}
\]
That source proves HE is owned by the radial E inner face,
with its actual application in that face's relative interior.
It is therefore a vertex of H.

The application cannot be Q, whose x-coordinate is less than
the radial inner-face coordinate d, and it cannot be Q+v,
whose x-coordinate is still smaller. The opposite vertex
Q+u+v is farther than1 from the free application Q, forbidden
by the free-vertex distance lemma. Hence the other root
application is Q+u. Their common root side has outward normal
-v=(b,-a), and its height is
\[
               P=b(Z-1)+a/2
                  \le\sqrt{(Z-1)^2+\tfrac14}
                  \le\frac{\sqrt{113}}{16}
                  <\frac34<\frac{39}{40}.
\tag{20}
\]
This contradicts (2).

Sections 4--5 exhaust every free root contact with all physical
circle masks and actual mean limits. Together with Sections 1--3,
they prove the theorem.

The result is a whole end-triangle implication at an arbitrary
root degree. It does not by itself classify a larger component
unless both of its actual root applications satisfy (2).
No additional normal is chosen after certificate extraction, no
other physical square is moved, and no numerical pose sampling,
Lean compilation or CI is used.

