# Every D-leaf triangle reaction acts on the articulation's left side

**Status: complete hand geometric and torque implication; two independent
hand audits passed.** Consider the four-body positive component consisting of
a triangle \(A,B,C\) and a radial diagonal leaf \(L\) attached to
\(A\), in the radius window

\[
                 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
                                                               \tag{1}
\]

Write

\[
 s=1+\sqrt2-R,
 \qquad A=[-s,1-s]\times[t-\tfrac12,t+\tfrac12],
 \qquad |t|<\frac12.                                      \tag{2}
\]

The positive bridge normal from \(A\) to \(L\) is \(e_x\),
and its application point is \((1-s,0)\). The other two outward
normals of \(A\), toward \(B,C\), both have strictly negative
horizontal component. Consequently exactly one of the following holds:

1. both normals are \(-e_x\), and both application points lie on
   the left side of \(A\);
2. their vertical components have opposite nonzero signs, and their
   application points are exactly the upper-left and lower-left vertices
   of \(A\).

The proof covers every application point on a shared side, vertex/side
contacts, point-only vertex/vertex contacts, and every positive split
between two circle corners. It does not discard the freely chosen
vertex/vertex normal cases or claim the entire D branch impossible.

## 1. Circle-force directions and two elementary radius bounds

The standard radial bridge reduction gives that \(A\) is
circle-clear. Both \(B,C\) are loaded. Indeed, if either were
unloaded, its two positive forces would transmit through its opposite
supports, placing the other two triangle bodies on opposite sides of
its positive-width projection gap; those two bodies could not touch.

The loaded circle vertices of \(B\) and \(C\) are pairwise
acute. For vertices in different bodies this is
`ACUTE_LOADED_CONTACT_GRAPH.md`, using their physical contact and
\(R^2>2+\sqrt3\). For vertices in the same body it follows from
their distance at most \(\sqrt2\) and \(R^2>1\). Let
\(\mathcal Z\) denote all such vertices with positive weights.
Summing the component force equations gives

\[
             \sum_{z\in\mathcal Z}\lambda_z z=-F e_x,
             \qquad F>0,\quad\lambda_z>0.                \tag{3}
\]

Dotting (3) with each \(z\in\mathcal Z\), pairwise acuteness
therefore proves

\[
                              z_x<0.                    \tag{4}
\]

The radius window gives

\[
                         0<s<\frac9{20}<\frac12.         \tag{5}
\]

The lower inequality follows from \(R<1+\sqrt2\). For the upper,
\(s\le\sqrt2-39/40<9/20\), using \(\sqrt2<57/40\).
Also \(\sqrt2<29/20\), so

\[
\begin{aligned}
 s^2+(s+\sqrt2)^2
 &<\left(\frac9{20}\right)^2+\left(\frac{19}{10}\right)^2\\
 &=\frac{61}{16}
 <\left(\frac{79}{40}\right)^2\le R^2.                 \tag{6}
\end{aligned}
\]

Every circle corner \(z\) of a square touching \(A\) satisfies

\[
                              z_x\ge-s-\sqrt2.           \tag{7}
\]

To see this, choose any actual shared point \(p\in A\cap T\).
Then \(p_x\ge-s\) and \(|z-p|\le\sqrt2\), because both
points belong to the same unit square \(T\).

## 2. A support-point span lemma

**Lemma 2.1.** Let \(T\) be a unit square and let \(p\in T\)
minimize \(n\cdot x\) on \(T\). If \(n_y<0\), then

\[
                           \max_{x\in T}x_y-p_y<1.       \tag{8}
\]

By reflections and interchanging coordinates, if \(n_x>0\), then

\[
                           p_x-\min_{x\in T}x_x<1.       \tag{9}
\]

*Proof.* First suppose \(p\) is the unique minimizing vertex. Let
\(u,v\) be the two inward unit side vectors from that vertex.
Then \(u,v\) are orthonormal and
\(n\cdot u>0\), \(n\cdot v>0\). They cannot both have
nonnegative vertical component: otherwise

\[
                 n_y=u_y(n\cdot u)+v_y(n\cdot v)\ge0.
\]

Thus the upward span of the square from \(p\), namely
\(\max(u_y,0)+\max(v_y,0)\), is at most one of these positive
components. That component is strictly less than one. Equality would
make its side vector \(e_y\), contradicting
\(n\cdot e_y=n_y<0\).

If the minimum is attained along a side, write \(u=n/|n|\) for
its inward perpendicular unit side direction and \(v\) for its
tangent unit side direction. Here \(u_y<0\). The highest point of
the square is therefore on this minimizing side, and its height above
any point \(p\) of the side is at most \(|v_y|<1\), since
\(u_y\ne0\). This also covers a minimizing endpoint of that side.
It proves (8), including all nonunique support cases. Equation (9) is
the reflected version. \(\square\)

## 3. No triangle reaction at A can be vertical

Suppose, for example, that the outward normal from \(A\) to \(C\)
is \(e_y\). Put \(h=t+1/2\), so \(0<h<1\). Then

\[
                       C\subseteq\{y\ge h\}.            \tag{10}
\]

The bridge force has zero vertical component. Vertical force balance
at \(A\) forces the other triangle normal \(n_B\) to have
\((n_B)_y<0\). Its application point \(p_B\) is consequently
on the bottom supporting side of the aligned square \(A\), so
\((p_B)_y=h-1\). The same point minimizes \(n_B\cdot x\)
on \(B\). Lemma 2.1 gives

\[
                         \max_{x\in B}x_y<h,             \tag{11}
\]

contradicting the required physical contact between \(B\) and
\(C\). Horizontal reflection excludes the normal \(-e_y\).
This argument does not require that either contact application point
be fixed along a shared side.

## 4. No triangle reaction at A can point rightward

Suppose an outward normal \(n_B\) from \(A\) to \(B\)
has \((n_B)_x>0\). Its support point on \(A\) then has
horizontal coordinate \(1-s\). It minimizes \(n_B\cdot x\)
on \(B\), so the reflected span bound (9) gives

\[
                              q_x>-s\quad(q\in B).        \tag{12}
\]

Combining (12) with (4), every positive circle vertex of \(B\)
has horizontal coordinate strictly between \(-s\) and zero.
Its vertical coordinate is therefore nonzero, with absolute value
greater than \(\sqrt{R^2-s^2}\). All positive circle vertices of
\(B\) have the same vertical sign: if two had opposite signs,
their distance would exceed \(2\sqrt{R^2-s^2}>\sqrt2\), which
is impossible for points in one unit square. The last strict inequality
follows already from (1) and (5).

The vertical component of (3) is zero. Since \(B\) carries a
positive circle weight, at least one positive circle vertex \(w\)
of \(C\) has the opposite vertical sign. Choose any positive
circle vertex \(z\) of \(B\). Write

\[
 z=(-X,\varepsilon\sqrt{R^2-X^2}),\qquad
 w=(-Y,-\varepsilon\sqrt{R^2-Y^2}),
 \qquad X,Y>0.                                          \tag{13}
\]

By (12), (4), and (7),

\[
                           X<s,\qquad Y\le s+\sqrt2.     \tag{14}
\]

Their positive dot product requires

\[
 XY>\sqrt{(R^2-X^2)(R^2-Y^2)}.
\]

Both sides are nonnegative. Squaring and cancelling \(X^2Y^2\)
gives the equivalent necessary inequality

\[
                              X^2+Y^2>R^2.               \tag{15}
\]

But (14) and (6) give \(X^2+Y^2<R^2\), a contradiction.
No outward triangle normal of \(A\) has positive horizontal
component. Section 3 excludes zero horizontal component, so both have
strictly negative horizontal component.

## 5. Exhaustive contact locations and the exact height equation

Let \(\mu_B,\mu_C>0\) be the two aggregate contact magnitudes.
The bridge is horizontal, so

\[
                  \mu_B(n_B)_y+\mu_C(n_C)_y=0.            \tag{16}
\]

If one vertical component vanishes, both do. Their strictly negative
horizontal components then make both unit normals equal to \(-e_x\).
Both application points are on the left side \(x=-s\). Their heights
\(y_B,y_C\) obey the exact torque equation

\[
                          \mu_B y_B+\mu_C y_C=0,          \tag{17}
\]

because the bridge has zero origin moment. This statement permits
all admissible weighted means on positive-length shared sides.

Otherwise, after interchanging \(B,C\), the two normals can be
written

\[
 n_B=(-\cos\phi,\sin\phi),\qquad
 n_C=(-\cos\psi,-\sin\psi),
 \qquad 0<\phi,\psi<\frac\pi2.                          \tag{18}
\]

Their support points on \(A\) are uniquely

\[
                  p_B=(-s,h),\qquad p_C=(-s,h-1),
                  \qquad h=t+\frac12\in(0,1).            \tag{19}
\]

Equation (16) says \(\mu_B\sin\phi=\mu_C\sin\psi\).
The origin-torque equation cancels the terms involving \(s\) and
becomes

\[
                \mu_B h\cos\phi
                   =\mu_C(1-h)\cos\psi.
\]

Eliminating the two positive magnitudes yields

\[
 \boxed{\displaystyle
       h=\frac{\tan\phi}{\tan\phi+\tan\psi},
       \qquad
       t=\frac{\tan\phi-\tan\psi}
                    {2(\tan\phi+\tan\psi)}.}            \tag{20}
\]

Thus the full D articulation has precisely the parallel-left or the
opposite-left-corner contact pattern, with its height retained exactly.
No small-angle or small-height assumption has been made. The remaining
whole-branch task must still retain the actual supporting faces of
\(B,C\), their mutual contact, and their force/torque balances, or
prove the joint five-extra completion obstruction. In particular this
localization alone does not exclude positive D cores.
