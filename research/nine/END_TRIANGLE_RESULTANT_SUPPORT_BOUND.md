# A loaded end triangle has a strict support bound in its resultant direction

**Status: complete hand implication; root and separate independent full
hand audits passed.** Work in the declared radius window
\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
       \qquad d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]
Let A,B,C be three actual interior-disjoint unit squares with all
three positive pair edges. The tips B,C have exact positive degree
two and positive circle load. A may have arbitrary further positive
neighbors. Put
\[
       F_B=2\sum_{z\text{ on }B}\lambda_z z,\qquad
       F_C=2\sum_{z\text{ on }C}\lambda_z z,\qquad M=F_B+F_C.
\tag{2}
\]
All physical circle masks, individual zero corner weights, contact
owners and actual shared-side application means are retained.

**Theorem.** The vector M is nonzero, and
\[
                 \boxed{\ h_A\!\left(\frac M{|M|}\right)<d.\ }
\tag{3}
\]
Here \(h_A(e)=\max_{x\in A}e\cdot x\) uses the original circle origin.
This is a whole end-triangle theorem; it does not replace the two
tips by a physical radial leaf or remove their occupied geometry.

## 1. The sharp support height available to any contained unit

Every contained unit has center c with
\[
             |c|\le\sqrt{R^2-\frac14}-\frac12=d+\frac12.
\tag{4}
\]
Indeed its farthest-corner squared norm is at least
\(|c|^2+|c|+1/2\). Thus a contained unit lying in
\(n\cdot x\ge h\), for a unit vector n, satisfies \(h\le d\).
If \(h=d\), equality in both the center bound and the half-width
bound forces the unique radial S square with center
\((d+1/2)n\) and inner side \(n\cdot x=d\).
This is the complete equality statement of
OUTER_BRIDGED_TRIANGLE_EXCLUSION.md, Section 1.

## 2. Root force lines in any physical unit-square triangle

Let n,m be the outward A-to-B and A-to-C unit normals, with actual
applications P,Q on A. Suppose n,m are nonparallel. Their lines
meet at q. We claim
\[
                         P=q+a n,\qquad Q=q+b m,
                         \qquad a,b\ge0.
\tag{5}
\]
This claim is purely geometric and retains every actual side mean.

If n is an A side axis, UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md
gives \(n\cdot m\ge0\). Normalize \(A=[0,1]^2\), \(n=e_x\),
and \(P=(1,p)\), \(0\le p\le1\).
If m is an A side axis too, nonparallelism makes it \(e_y\) or
\(-e_y\). The two normal lines then meet inside A, proving (5).
Otherwise m strictly exposes a right-hand A vertex. If
\(m_x>0,m_y>0\), then \(Q=(1,1)\) and
\[
             b=\frac{1-p}{m_y}\ge0,\qquad a=bm_x\ge0.
\]
The lower-right case has
\(b=-p/m_y\ge0\), \(a=bm_x\ge0\).
This proves (5) when at least one actual normal has an A-side owner.

Otherwise P,Q are vertices strictly exposed by their respective
normals. Opposite vertices are impossible. To see this, let u,v
be the inward orthonormal side vectors at P, so \(Q=P+u+v\).
Strict exposure gives \(n\cdot u,n\cdot v<0\) and
\[
                  n\cdot(P-Q)=|n\cdot u|+|n\cdot v|\ge1.
\]
The opposite vertex normal m has \(n\cdot m<0\).
At Q, C minimizes m; the strict support-span lemma therefore gives
\(\max_{x\in C}n\cdot(x-Q)<1\). All of B has n-projection
at least \(n\cdot P\), so B and C could not touch.

If P=Q, take q=P and a=b=0. Otherwise the vertices are adjacent.
For example, write \(P=(0,1)\), \(Q=(0,0)\),
\[
                 n=(-u,v),\qquad m=(-w,-z),
                  \qquad u,v,w,z>0.
\]
The exact intersection parameters are
\[
                 a=\frac{w}{vw+uz}>0,\qquad
                 b=\frac{u}{vw+uz}>0.
\]
They satisfy (5). Rotation and reflection cover every adjacent pair.
Thus (5) holds throughout the full nonparallel root interface.

## 3. Its concurrence lies on the ray opposite the total circle force

Let the positive AB,AC,BC magnitudes be \(\mu,\nu,\gamma\), and let
g be the B-to-C unit normal. The exact tip force equations are
\[
                     F_B=\mu n-\gamma g,\qquad
                     F_C=\nu m+\gamma g,\qquad
                     M=\mu n+\nu m.
\tag{6}
\]
In particular M is nonzero when n,m are nonparallel. Their two
circle resultants are nonzero and have distinct radial directions.

The tips have each other as boundary neighbors. Hence the full proper
concurrence lemma in TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md,
Lemma 2.1, applies with every physical circle mask:
their force-line intersections \(q_B,q_C\) are positive multiples
of \(F_B,F_C\), and lie behind each actual outward application.
Together with (5), this gives
\[
             q_B=q+u n,\qquad q_C=q+v m,\qquad u,v\ge0,
             \qquad q_C-q_B=\ell g,\quad\ell>0.
\tag{7}
\]
The strict last inequality follows from the distinct positive radial
directions; it does not assert that a two-corner concurrence lies
inside its unit.

The circle forces have zero origin moment. Summing the two tip torque
equations cancels their mutual BC moment and gives
\[
                        \det(P,\mu n)+\det(Q,\nu m)=0.
\tag{8}
\]
Since both lines pass through q, \(\det(q,M)=0\).
Thus \(q=\tau M\) for a real scalar \(\tau\).
Using \(\ell g=v m-u n\), equations (6)--(7) become
\[
 \begin{split}
 q_B&=(\tau\mu+u)n+\tau\nu m,\\
 F_B&=\left(\mu+\frac{\gamma u}{\ell}\right)n
                         -\frac{\gamma v}{\ell}m.
 \end{split}
\tag{9}
\]
The vectors n,m are independent and \(q_B\) is a positive multiple
of \(F_B\). Comparing their m-coefficients gives \(\tau\le0\).
If \(\tau=0\), that comparison gives \(v=0\), and (7) then gives
\(q_C=q=0\), impossible for a positive proper concurrence.
Consequently
\[
                             q=-t e,\qquad
                       e=M/|M|,\quad t>0.
\tag{10}
\]
This sign uses only the genuine equations at the two degree-two tips.
It places no fictitious degree-two equation at A.

## 4. A maximizing root point is an actual port

If both n,m are side axes of A, the nonparallel alternative is
perpendicular. BOWTIE_PERPENDICULAR_CONTACT_EXCLUSION.md excludes
that whole case for two loaded tips, including every side mean.

In every other nonparallel case, at least one of P,Q maximizes
the linear functional \(e\cdot x\) on A.
For one root-owned axis, normalize as in Section 2. The other
strict right-vertex normal has nonzero vertical sign. The positive
sum \(\mu n+\nu m\) has the same vertical sign and positive
horizontal component, so its maximizing point is exactly that
other application Q.
For two strict vertex normals, the vertices are equal or adjacent.
In the adjacent example of Section 2, both normals have negative
horizontal component. Their positive sum therefore maximizes at P
or Q, or on the whole common left side, which includes both.
Rotation and reflection give the remaining cases.

Choose such an actual port p, with corresponding outward normal w.
By (5),(10),
\[
                         p+t e=a_0 w,\qquad a_0\ge0,
                    \qquad p\cdot e=h_A(e).
\tag{11}
\]
If \(h_A(e)\le0\), the desired strict bound is immediate because d>0.
Otherwise \(a_0>0\), since \(a_0=0\) would imply \(p=-t e\).
Now \(w=(p+t e)/|p+t e|\), and Cauchy's inequality gives
\[
 \begin{split}
 p\cdot w
   &=|p+t e|-t(e\cdot w)\\
   &\ge(p+t e)\cdot e-t(e\cdot w)\\
   &=h_A(e)+t(1-e\cdot w)>h_A(e).
 \end{split}
\tag{12}
\]
The last inequality is strict: w is n or m; e cannot equal either
one when they are independent and both coefficients in (6) are positive.
The actual tip beyond this port lies in \(w\cdot x\ge p\cdot w\).
Section 1 gives \(p\cdot w\le d\). Equation (12) proves (3) in the
whole nonparallel domain.

## 5. Parallel interfaces and strict equality

If n,m are parallel, they cannot be opposite: B,C would lie beyond
opposite A supports separated by the positive width of a unit.
Thus \(n=m=e\), \(M=(\mu+\nu)e\ne0\).
Both tips lie in \(e\cdot x\ge h_A(e)\), giving \(h_A(e)\le d\).
Equality would make both of them the same unique radial S square
from Section 1, contrary to interior disjointness.
Hence \(h_A(e)<d\) here too.

Sections 2--5 cover every actual interface and prove the theorem.
No side ownership has been silently imposed on a free point normal.

## 6. Exact scope

The result bounds the root's support in the direction of the *whole*
two-tip circle resultant. The two circle forces are not individually
replaced by radial leaves. Every unit remains physically present.
The argument permits extra positive forces at A and arbitrary zero-weight
physical contacts, but B,C must retain their exact degree-two equations.
It supplies a joint necessary inequality for larger attached components;
by itself it does not close the tip-attached bowtie-leaf family.

No sampled pose, numerical certificate, angle subdivision, changed
post-extraction normal, Lean compilation or CI is used.

