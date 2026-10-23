# A uniform center norm and the directions forced by the high tangent tails

## 1. The sharp axial bound controls every center norm

Let an actual unit square lie in a disk centered at the origin with
squared radius \(q\le Q=9789/2500\). In a sorted own frame its center
is \((a,-y)\), with \(a\ge|y|\ge0\), and its farthest corner gives
\[
(a+1/2)^2+(|y|+1/2)^2\le Q.                            \tag{1}
\]
Set \(r=\sqrt{a^2+y^2}\). Since \(a+|y|\ge r\),
\[
r^2+r+1/2\le r^2+a+|y|+1/2\le Q.
\]
Completing the square proves
\[
\boxed{|p|=r\le\sqrt{Q-1/4}-1/2<283/200=:U.}           \tag{2}
\]
The last strict comparison is the exact rational inequality
\[
(U+1/2)^2+1/4-Q=13/8000>0.
\]
This is a bound on the original center, with no radial-boundary or
axis-owner assumption. It is stronger than the frequently used
\(|p|<3/2\) amplitude bound.

## 2. All original aligned-axis nominal losses are at most their error

On any zero or quarter edge write its relative frame angle as
\(k\pi/2+d\), with \(k\in\{0,1\}\), and put \(e=|d|\).
Each of the four original forward SAT projections contains a rotated
projection of exactly one center. Thus (2) gives
\[
|P(d)-P(0)|\le Ue.                                   \tag{3}
\]
The square support width satisfies
\[
W(d)\ge1+e/2-e^2/4-e^3/12
\]
on \(0\le e\le3/10\). If the original witness is feasible, then
\[
\begin{aligned}
P(0)&\ge W(d)-Ue\\
&\ge1-\left(\frac{183}{200}+\frac e4+\frac{e^2}{12}\right)e
\ge1-\frac{399}{400}e
\ge1-e.                                              \tag{4}
\end{aligned}
\]
The coefficient is increasing in e, and its value at \(3/10\) is
\(399/400\). Therefore every originally feasible aligned witness
obeys the complete whole-interval necessary inequality
\[
\boxed{P^{\rm nominal}\ge1-|d|\qquad(|d|\le3/10).}     \tag{5}
\]
In particular, for any nonnegative weights on several actual aligned
witnesses, the nominal error is bounded by the weighted sum of their
actual absolute errors. An unweighted cancellation spends at most
their shared sum, not a fresh total budget on each edge.

For use at the coarse threshold, the same calculation gives the
slightly stronger simple coefficient
\[
\boxed{P^{\rm nominal}\ge1-\frac{99}{100}|d|
\qquad(|d|\le13/50).}                                \tag{6}
\]
The exact coefficient reserve at that endpoint is
\[
\frac{99}{100}-\frac{183}{200}-\frac{13}{200}
-\frac{169}{30000}=\frac{131}{30000}>0.
\]
These inequalities include zero error, both error signs, all original
axes and every original sign label. They introduce no tangent cut.

## 3. The entire high-G tail excludes GA axis 0 globally

Now assume the actual G0--G2 candidate geometry. Its core bound gives
\[
a_i>L:=447/800.
\]
Suppose
\[
u_G=y_G/a_G\le-4/5,
\qquad b_G=-y_G.
\]
Then
\[
b_G>447/1000,\qquad a_G<1.                            \tag{7}
\]
The first follows from \(b_G\ge(4/5)a_G>(4/5)L\). For the second,
\(a_G\ge1\) would imply
\((a_G+1/2)^2+(b_G+1/2)^2\ge197/50>Q\).

The original GA axis-0 projection has the form
\[
P_{G0}=-b_G+a_A\sin\phi_G-y_A\cos\phi_G.
\]
For **every real relative angle**, (2) and (7) give
\[
P_{G0}\le-b_G+\sqrt{a_A^2+y_A^2}
<U-447/1000=121/125<1\le W(\phi_G).                   \tag{8}
\]
Thus no original GA axis 0 is feasible on this high-G tail. This
conclusion needs neither an A sign nor a mismatch hypothesis.

## 4. If A is nonnegative, high G forces a negative A/G tilt

Assume in addition \(y_A\ge0\), and write \(b_A=y_A\).
Normalize \(\theta_A=0\), and set
\[
t=\theta_G-\theta_A,\qquad \phi_G=\pi/2-t.
\]
The actual concentrated frame has \(|t|<7/10\). We prove
\[
\boxed{t<0.}                                         \tag{9}
\]
Suppose instead \(t\ge0\), and set \(c=\cos t\),
\(s=\sin t\). Then \(c,s\ge0\), \(c+s\ge1\), and
\(W=(1+c+s)/2\). The four original GA projections are
\[
\begin{array}{ll}
0:&-b_G+a_Ac-b_As,\\
1:&a_A-a_Gs-b_Gc,\\
2:&a_Gc-b_Gs-b_A,\\
3:&a_G-a_As-b_Ac.
\end{array}                                          \tag{10}
\]
Axis 0 is already excluded by (8). For axis 1, (7) and the core
lower bound give
\[
\begin{aligned}
P_{G1}-W
&<\frac{183}{200}-\frac{847}{800}s-\frac{947}{1000}c\\
&\le\frac{183}{200}-\frac{947}{1000}(s+c)
\le-\frac4{125}<0.                                  \tag{11}
\end{aligned}
\]
Here \(847/800>947/1000\), so the first linear bound uses only
nonnegative s. Finally, both axes 2 and 3 have projection at most
\(a_G<1\le W\), by the assumed A sign. No originally feasible
witness remains, contradicting actual separation. This proves (9),
including exclusion of zero tilt and all owner ties.

The endpoint-sign theorem
`HAND_COARSE_AD_SIGN_RIGIDITY.md` proves \(y_A>0\) under
\(S\le13/50\), with no tangent cuts. Therefore (8)--(9) can be
used at that earlier coarse boundary without importing any later
owner, sign, H/D cone or tilt conclusion:
\[
\boxed{S\le13/50,\ u_G\le-4/5
\ \Longrightarrow\ t<0\text{ and every GA witness lies in }\{1,2,3\}.}
                                                               \tag{12}
\]
The negative tilt branch still requires its own complete exclusion.
In particular, (12) is not a proof of \(u_G>-4/5\).

## 5. The reflected local statement for a high positive target

There is an analogous exact pair statement on BT. Suppose
\(u_T\ge4/5\), and assume \(y_B\le0\). Then no original BT
axis 2 is feasible, for any angle: its projection is a rotated
projection of B minus \(y_T\), bounded exactly as in (8).
Moreover,
\[
\boxed{d_B>0.}                                       \tag{13}
\]
To check every original axis directly, suppose \(d_B\le0\),
put \(x=-d_B\), \(c=\cos x\), \(s=\sin x\), and write
\(b_B=-y_B\), \(b_T=y_T\). The four quarter projections are
\[
\begin{array}{ll}
0:&-b_B+a_Tc-b_Ts,\\
1:&a_T-a_Bs-b_Bc,\\
2:&a_Bc-b_Bs-b_T,\\
3:&a_B-a_Ts-b_Tc.
\end{array}
\]
Axes 0 and 1 are at most \(a_T<1\); axis 2 has the all-angle
exclusion just stated; axis 3 has precisely the negative margin in
(11), with T in place of G and B in place of A. This proves (13).
No reflection of the seven-cycle or of its charged index set was used.

## 6. Scope of the result

The new universally usable tools are the original-center norm (2)
and the all-axis nominal bounds (5)--(6). The high-tail statements are
complete implications on their stated continuous domains, including all
original witnesses and weak ties. They supply directions and owner
exclusions, not global tangent capture or a mismatch upper bound.

Every estimate is elementary circle support, a monotone degree-two
coefficient, or a displayed rational comparison. No numerical optimizer,
state or angle mesh, computed table, or external script is a proof
premise. No Lean source, compilation, or CI was changed or run.
