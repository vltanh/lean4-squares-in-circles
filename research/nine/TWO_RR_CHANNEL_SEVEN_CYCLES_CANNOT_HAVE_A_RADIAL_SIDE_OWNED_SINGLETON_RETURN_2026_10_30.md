# Two-RR seven-cycles exclude a direct return owned by the radial body's side

Date: October 30, 2026 UTC. Author: joint-pockets continuation.

**Status: complete whole-owner hand exclusion, frozen for independent
review.** In the exact two-RR short-C7 family, the direct contact
between the radial body B and the unique-circle body D cannot be
a singleton at which B supplies the side and D the vertex.
The proof covers every remaining D-side or D-vertex application
of its other channel. In the latter case, a uniform critical-value
argument replaces a subdivision of the angle interval.

All original forces, means, masks and nine physical squares remain.
There is no Phi-minimum premise and no feasible-motion assertion.

## 1. Exact original family and whole conclusion

Keep the entire original positive component
\[
                   X-U_+-A-U_3-D-B-U_--X.
\tag{1.1}
\]
The four loaded bodies are \(X,A,B,D\). The first three have
two physical circle corners. D has one physical circle corner
and positive total circle load. Each U is an actual unloaded
full-positive-degree-two side transmitter. Retain both individual
circle coefficients at every radial body, including zero endpoints,
the unchanged pair normals and magnitudes, every original contact
application and whole shared-side mean.

All nine actual unit squares have disjoint open interiors and
remain in the original disk, with
\[
                         2<R\le\frac{\sqrt{1105}}{16}.
\tag{1.2}
\]
Every additional physical contact and both actual completion squares
remain present. In particular no circle-clear or zero-stress body
is deleted from the packing. The displayed cycle is the whole
positive component, so its loaded vertices have precisely their
two displayed positive pair forces.

**Theorem 1.1.** The actual B-D contact cannot be a singleton
vertex/side contact with B supplying the side and D the uniquely
exposed vertex.

This is the whole radial-side-owner alternative left after the
accepted free-VV and shared-segment exits in [S], Section 7.
The theorem also applies when (1.1) and this owner alternative
are assumed directly. Its contradiction does not use the positions
of the two completion squares.

## 2. Original radial frame and the fixed A application

Write
\[
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \phi=\arctan\frac1{2d},\qquad
 \rho=\sqrt{d^2+\tfrac14}=\frac1{2\sin\phi}.
\tag{2.1}
\]
The complete RR geometry and actual circle-spoke order give the
frame already established in [S], Section 2:
\[
 \begin{gathered}
 B=[d,d+1]\times[-\tfrac12,\tfrac12],\\
 A=[d,d+1]e_A+[-\tfrac12,\tfrac12]Je_A,\qquad
 e_A=(\cos\gamma,\sin\gamma),\\
 \gamma=2\pi-8\phi,\qquad 0<\arg c_D<\gamma,\\
 \frac{14}{15}<d<\frac{61}{60},\qquad
 \frac{\pi}{7}<\phi<\frac{\pi}{6},\qquad
 \frac{2\pi}{3}<\gamma<\frac{6\pi}{7}<\pi.
 \end{gathered}
\tag{2.2}
\]
Reflection here is of the whole original coordinate description.
The two RR gaps are the actual consecutive gaps through X;
their order is not selected independently.

By the full radial side-channel support cover [R], Section 1,
each of A's two actual positive applications is an inner vertex.
Its RR application toward X is
\[
                         d e_A+\tfrac12Je_A
\]
by the actual RR orientation in [R], Section 8. The two positive
applications cannot be the same inner vertex. Indeed the full
circle resultant of A is a positive multiple of
\[
                (d+1)e_A+\eta Je_A,\qquad |\eta|\le\tfrac12.
\]
At the upper inner vertex the determinant with this vector is
\[
                    d\eta-\tfrac12(d+1)\le-\tfrac12.
\]
If both pair forces acted there, their torque about that point
would vanish while the full circle torque would not. The same
calculation at the lower vertex has the opposite strict sign.
This uses the full original circle mean, including either zero
individual coefficient.

Consequently the unchanged A-U3 application is exactly
\[
 \begin{split}
 p_A&=d e_A-\tfrac12Je_A=(u_0,v_0),\\
 u_0&=d\cos\gamma+\tfrac12\sin\gamma,\\
 v_0&=d\sin\gamma-\tfrac12\cos\gamma.
 \end{split}
\tag{2.3}
\]
It is also A's unique maximum-x point. The complete exact
polynomial bound [S], Section 4, applies to these coordinates
without a shared-return premise and gives
\[
                        u_0<0,\qquad \tfrac12<v_0<\tfrac{21}{20}.
\tag{2.4}
\]
Its proof uses the identity
\[
 v_0=-\frac{\sin9\phi}{2\sin\phi}
\]
and a global completed-square bound, with all signs of
\(\sin^2\phi-1/5\) included.

We need one strengthened horizontal estimate. Put
\[
                    a_4=-\cos4\phi,\qquad s_4=\sin4\phi.
\]
Then
\[
                          0<a_4<\tfrac25,\qquad s_4>\tfrac9{10}.
\tag{2.5}
\]
For completeness, the rational form of \(a_4\) is
\[
 a_4=\frac{-16d^4+24d^2-1}{16d^4+8d^2+1}.
\]
Its comparison with \(2/5\) is equivalent to
\[
                       112d^4-104d^2+7>0.
\]
The polynomial \(112y^2-104y+7\) is increasing for
\(y\ge(14/15)^2\), and its value at that endpoint is exactly
\(70567/50625>0\). The strict lower d bound proves the claim.
The \(s_4\) bound follows from
\(s_4^2=1-a_4^2>21/25>81/100\) and \(s_4>0\).

Since
\(\cos\gamma=2a_4^2-1\) and \(\sin\gamma=2a_4s_4\),
\[
 \begin{split}
 d-u_0
 &=s_4(2ds_4-a_4)\\
 &>\frac9{10}\left(2\frac{14}{15}\frac9{10}-\frac25\right)
   =\frac{144}{125}>1.
 \end{split}
\tag{2.6}
\]
All estimates in this section cover the full interval (1.2).

## 3. The complete B-owned side cover

Suppose B supplies the side at the singleton B-D contact.
Its outer radial face cannot support a contained unit: a unit
beyond \(x=d+1\) has width at least one and hence a point
with x coordinate at least \(d+2>R\).

The inner radial face cannot support a physical boundary neighbor
either. Here is a force-free proof including all side limits.
If such a neighbor has a strict maximum-x vertex
\[
                  p=(d,y),\qquad |y|\le\tfrac12,
\]
write its inward orthonormal edges, up to reflection, as
\[
                    (-a,b),\quad(-b,-a),\qquad
             a,b>0,\quad a^2+b^2=1.
\]
The squared norm of p is at most \(d^2+1/4\). Each single-edge
corner has squared norm at most \(d^2+9/4\). For example
\[
 |p+(-a,b)|^2=d^2+y^2+1-2da+2yb
                         \le d^2+\tfrac94.
\]
The opposite corner has squared norm at most
\[
 d^2+\tfrac94-2d(a+b)+|b-a|
       \le d^2+\tfrac{13}{4}-2d
       \le d^2+\tfrac94,
\]
because \(a+b\ge1\), \(|b-a|\le1\), and \(d>1/2\).
All four corners are strictly within the containing circle since
\[
                     d^2+\tfrac94
                     <d^2+2d+\tfrac54=R^2.
\tag{3.1}
\]
Reflection changes neither estimate. If maximum x is a side
instead, the neighbor is aligned:
\[
             [d-1,d]\times[t-\tfrac12,t+\tfrac12].
\]
Meeting B's closed inner face requires \(|t|\le1\); also
\(|d-1|\le d\). Its maximum corner norm is again at most
\(d^2+9/4<R^2\). Thus every inner-face axis support would
make the neighbor physically circle-clear, contradicting D.

The negative tangential B side puts the whole D in \(y\le-1/2\),
whereas (2.2) gives \(c_{D,y}>0\). Hence the only remaining
original B-side normal is \(+f=(0,1)\), with application
\[
                       p=(t,\tfrac12),\qquad d\le t\le d+1.
\tag{3.2}
\]
The actual singleton uses a relative-side-interior point of B;
retaining the larger closed interval in (3.2) only includes its
possible limiting endpoints in the inequalities.

The normal \(-f\) strictly exposes this vertex on D. Therefore
its full original square has the unique chart
\[
 \begin{gathered}
 D=p+[0,1]u+[0,1]v,\\
 u=(a,b),\qquad v=(-b,a),\qquad
 a,b>0,\quad a^2+b^2=1.
 \end{gathered}
\tag{3.3}
\]
The labels choose u to have positive x coordinate. No D normal
or application has been reselected.

## 4. The circle corner and the entire parameter interval

Containment of \(p+u\), together with \(t\ge d\), gives
\[
 \begin{split}
 (t+a)^2+(\tfrac12+b)^2&\le R^2=d^2+2d+\tfrac54,\\
                              2da+b&\le2d.
 \end{split}
\tag{4.1}
\]
Because \(b>0\), the second inequality is equivalent to
\[
                     \frac{b}{1+a}\ge\frac1{2d}=\tan\phi.
\]
Thus, putting
\[
                      b_0=\sin2\phi,\qquad a_0=\cos2\phi,
\]
one has \(b\ge b_0\), \(a\le a_0\), and \(b>a\), since
\(2\phi>\pi/4\).

The own-coordinate center projections satisfy
\[
 \begin{split}
 c_D\cdot u&=ta+\tfrac12b+\tfrac12>0,\\
 c_D\cdot v&=-tb+\tfrac12a+\tfrac12\le0.
 \end{split}
\tag{4.2}
\]
Equality in the second would give two physical circle corners.
The actual D has a unique one, so its farthest corner is
\[
                          z=p+u=(t+a,\tfrac12+b).
\tag{4.3}
\]
It is on the containing circle. If \(b=b_0\), (4.1) forces
\(t=d\), and (4.2) is an equality, contrary to that mask.
Consequently the actual parameter lies strictly in
\[
                               b_0<b<1.
\tag{4.4}
\]

For the uniform comparison below define on the whole interval
\([b_0,1)\)
\[
 \begin{split}
 a(b)&=\sqrt{1-b^2},\\
 \zeta(b)&=\sqrt{R^2-(\tfrac12+b)^2},\\
 t(b)&=\zeta(b)-a(b).
 \end{split}
\tag{4.5}
\]
These are real and smooth there. The identity
\[
 \zeta(b)^2-(d+a(b))^2=2d(1-a(b))-b
\]
is nonnegative precisely when \(b/(1+a(b))\ge1/(2d)\).
Hence throughout this comparison interval
\[
                             t(b)\ge d.
\tag{4.6}
\]
At \(b_0\), equality holds. At the actual parameter these
formulas describe exactly the original D; they are not choices
of a replacement mean or mask.

## 5. Complete support cover for the original U3 application

Let g be the original unit A-to-D channel normal and let \(p_D\)
be its unchanged application on D. The full side-channel theorem
[L], Lemma N.1, and (2.3) give
\[
                         p_D-p_A=g,\qquad |g|=1.
\tag{5.1}
\]
Every D point has x coordinate at least \(t-b\ge d-1\),
while A's maximum x is \(u_0\). By (2.6),
\[
                      (p_D-p_A)_x\ge d-1-u_0>0.
\tag{5.2}
\]
Thus \(g_x>0\), and D's outward supporting normal toward U3
is \(-g\), with negative x component.

We cover all four D sides and all four vertex cones.

At p, the horizontal displacement from \(p_A\) is
\(t-u_0\ge d-u_0>1\), contradicting (5.1). The cone at
\(p+u\), and the two side normals \(u,-v\), have positive
x component and cannot equal \(-g\).

At the vertex \(p+u+v\), minimum-g support requires
\(g\cdot u\le0\). Since \(g_x>0\) and \(a,b>0\), this
forces \(g_y<0\). But that vertex has height
\[
                    \tfrac12+a+b>\tfrac32,
\]
whereas (5.1) would give height \(v_0+g_y<v_0<21/20\).
This is impossible, including cone boundaries.

On the side \(p+[0,1]v\), the outward normal is \(-u\),
so \(g=u\). Its height is at most \(1/2+a\), whereas
(5.1) would give
\[
                      v_0+b>\tfrac12+b>\tfrac12+a.
\]
This excludes that entire side, including its endpoints.

The only remaining support possibilities are therefore:

1. the vertex
   \[
                       P=p+v=(t-b,\tfrac12+a);
   \tag{5.3}
   \]
2. the side
   \[
                   p_D=p+v+\xi u,\qquad 0\le\xi\le1,
   \quad g=-v=(b,-a).
   \tag{5.4}
   \]

These alternatives deliberately overlap at their endpoints.
They retain the entire original D-side mean in (5.4).
No assumption that the U3-D contact is a singleton is made.

## 6. The full side-mean alternative is impossible

Assume (5.4), and put
\[
                            w=v_0-\tfrac12,
                       \qquad 0<w<\tfrac{11}{20}.
\]
Equation (5.1) gives \(p_A=p+2v+\xi u\), so
\[
                   \xi=\frac{w-2a}{b}\ge0,
                 \qquad 0<a\le\frac w2<\frac{11}{40}.
\tag{6.1}
\]

Write the actual circle force as \(\chi z\), \(\chi>0\).
The full original force equation at D is
\[
                         \mu v-\nu f+\chi z=0,
                         \qquad \mu,\nu>0.
\tag{6.2}
\]
Projecting on u and v gives
\[
                  \nu=\frac{\chi(z\cdot u)}b,\qquad
                  \mu=\frac{\chi(t+a)}b.
\tag{6.3}
\]
The original B force acts at p. Taking the complete torque about p,
using \(\det(u,v)=1\), yields
\[
                       \mu\xi+\chi(-tb+\tfrac12a)=0.
\tag{6.4}
\]
Equations (6.1)--(6.4) force the exact mean identity
\[
                   t(b^3-w+2a)
                         =a(w-2a+\tfrac12b^2).
\tag{6.5}
\]
Neither side application was chosen independently.

But \(b^3\ge b^4=(1-a^2)^2\ge1-2a^2\). Thus the left
side of (6.5) is at least
\[
 t(1-w+2a-2a^2)\ge t(1-w)
                     >\frac{14}{15}\frac9{20}
                      =\frac{21}{50}
                      =\frac{336}{800}.
\tag{6.6}
\]
Here \(0<a<1\). The right side is strictly below
\[
                a(w+\tfrac12)
                    <\frac{11}{40}\frac{21}{20}
                     =\frac{231}{800}.
\tag{6.7}
\]
This contradiction includes both mean endpoints. The whole
side-support alternative is excluded.

## 7. A uniform critical-value theorem excludes the vertex alternative

Assume the original application is the vertex (5.3). Define
\[
 \begin{split}
 P(b)&=(t(b)-b,\tfrac12+a(b)),\\
 F(b)&=|P(b)-p_A|^2,\qquad b\in[b_0,1).
 \end{split}
\tag{7.1}
\]
At the actual parameter, the unchanged channel equation gives
\[
                               F(b)=1.
\tag{7.2}
\]
The complete force and torque equations also force
\[
                               F'(b)=0.
\tag{7.3}
\]
To verify (7.3), differentiate the rigid square family (4.5).
The application p moves horizontally. The same physical corner
\(z=p+u=(\zeta,1/2+b)\) stays on the radius-R circle.
For this arbitrary infinitesimal rigid velocity, full equilibrium
makes the sum of the powers of the original forces zero.
The force \(-\nu f\) at p has zero power, and the circle force
\(\chi z\) has zero power because \(z\cdot z'=0\).
The remaining original force \(-\mu g\) acts at P, so
\(g\cdot P'=0\). By (5.1), this is exactly (7.3).

This is the linear virtual-work identity for the original complete
equilibrium star. The comparison family need not be feasible
against another square, and no new contact or circle multiplier
is assigned along it. All actual extra zero-stress contacts remain
in the packing and contribute their original zero coefficient.

We now prove that every stationary value of F in \((b_0,1)\)
is strictly below one. In the following derivatives a, t and
zeta mean the functions (4.5). Put
\[
                  C=t-b-u_0,\qquad S=\tfrac12+a-v_0.
\]
By (2.6) and (4.6), \(C>d-1-u_0>0\) throughout the interval.
Direct differentiation gives
\[
 \begin{split}
 P'&=\left(\frac ba-1-\frac{1/2+b}{\zeta},-\frac ba\right),\\
 P''&=\left(\frac1{a^3}-\frac{R^2}{\zeta^3},
                                      -\frac1{a^3}\right).
 \end{split}
\tag{7.4}
\]
At any stationary point of F,
\[
                  (C-S)\frac ba
                         =C\left(1+\frac{1/2+b}{\zeta}\right).
\tag{7.5}
\]
Consequently
\[
 \begin{split}
 \frac12F''
 &=|P'|^2+\frac{C-S}{a^3}-\frac{CR^2}{\zeta^3}\\
 &>|P'|^2+C\left(\frac1{a^2b}-\frac{R^2}{\zeta^3}\right)>0.
 \end{split}
\tag{7.6}
\]
For the final strict sign, \(\zeta=t+a\ge d+a\). The function
\((d+a)^3/a^2\) decreases on \(0<a\le1\), since its derivative
has the sign of \(a-2d<0\). Therefore
\[
 \frac{\zeta^3}{a^2}
       \ge\frac{(d+a)^3}{a^2}
       \ge(d+1)^3
       >R^2,
\]
where
\[
 (d+1)^3-R^2=d(d+1)^2-\tfrac14>0
\]
already follows from \(d>1/2\). Since \(b<1\), this proves
\(\zeta^3>R^2a^2b\), as required.

Thus every critical point is a strict local minimum. In
particular any such point \(b_*\) satisfies
\[
                              F(b_*)<F(b_0).
\tag{7.7}
\]
Indeed, otherwise a value immediately to the left of the strict
minimum \(b_*\) exceeds both endpoint values on \([b_0,b_*]\).
The maximum on this compact interval then occurs at an interior
point. There \(F'=0\) and \(F''\le0\), contradicting (7.6).
This argument requires no assumption on the number of critical
points or on the behavior at the open endpoint b=1.

At the left comparison endpoint, \(t(b_0)=d\), and
\[
 \begin{split}
 P(b_0)&=(d-\sin2\phi,\tfrac12+\cos2\phi)
                        =\rho(\cos3\phi,\sin3\phi),\\
 p_A&=\rho\bigl(\cos(2\pi-9\phi),\sin(2\pi-9\phi)\bigr).
 \end{split}
\tag{7.8}
\]
Their actual angular difference in this expression is
\(2\pi-12\phi\in(0,2\pi/7)\). Hence
\[
 \sqrt{F(b_0)}
      =2\rho\sin(\pi-6\phi)
      =\frac{\sin(\pi-6\phi)}{\sin\phi}<1.
\tag{7.9}
\]
The final inequality uses exactly
\(0<\pi-6\phi<\phi<\pi/6\).
The reference \(b=b_0\) is an algebraic endpoint in the comparison
function; its tied-circle geometry is never substituted for the
actual unique mask (4.4).

Equations (7.7)--(7.9) contradict the simultaneous original
requirements (7.2)--(7.3). This excludes the entire vertex
alternative. Together with Section 6 and the complete feature
cover, Theorem 1.1 follows.

## 8. Literal remaining scope and review boundary

The accepted shared-return source [S], including its separate
review, excludes every positive-length shared B-D segment.
Its final literal caller also imports the selected free-VV exit.
Combining those accepted results with Theorem 1.1 leaves only
the singleton alternative in which D supplies the side and B
the vertex. That alternative, the two actual extras and all
their physical constraints remain. This manuscript does not
declare the full two-RR mask, the mixed C7 parent or the sharp
nine-square theorem closed.

The new fixed-A-application argument, horizontal gap, complete
remaining feature cover and global critical-value proof were
derived by joint-pockets. Common-certificate independently
suggested the force-free inner-face cover of Section 3 and
the original side-mean identity in Section 6. The simple final
bounds (6.6)--(6.7) were independently derived here. Those
contributions must be disclosed in any reviewer record:
common-certificate's review alone is not the independent gate
for its own contributed inner-face and mean steps. A separate
noncontributor may check those sections, while the full-source
review checks every new composition and remaining argument.

The proof uses original equilibrium as virtual work, not a
deformation permitted by selected positive contacts alone.
Thus it requires no additional all-physical-contact screen and
does not ignore a possible zero-stress blocker.

## 9. Complete frozen operative inputs

| Label | Complete source or review | SHA-256 | Literal use |
| --- | --- | --- | --- |
| [R] | RADIAL_LOAD_SIDE_CHANNEL_POCKET_CAPACITY.md | 2d78bc2892c11e58007881ff84d57cc6606dce201bb46d412ef216c12577191e | Complete radial side-channel inner-vertex support cover and actual RR application orientation. |
| [L] | PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Original full unloaded side-channel displacement and support identity. |
| [S] | TWO_RR_CHANNEL_SEVEN_CYCLES_CANNOT_HAVE_A_SHARED_DIRECT_RETURN_2026_10_30.md | 3ddc7f2755c492b5cc8c1ea710b4534bfcc28e22e8d2e7c862209a6c4a9acf6a | Actual two-RR frame and whole-window bounds in Section 2; complete generic radial support-height calculation in Section 4; accepted shared/free-VV joins only in Section 8 above. |
| [SR] | REVIEW_TWO_RR_SHARED_DIRECT_RETURN_COMMON_CERTIFICATE_2026_10_30.md | 74f5ba44262bc259b0dee73c07c03505524e192ae1f59b465baabe946589fd68 | Complete separate accepted review of the frozen shared-return source, with its original contribution boundary retained. |

All four complete input records were read. The new theorem requires
its own independent hand review. No original flag, shared metadata,
normal, mean or physical square was changed. No numerical pose or
angle search, mesh, optimizer, computational packing certificate,
Lean/Lake execution, CI dispatch or remote edit was used.
