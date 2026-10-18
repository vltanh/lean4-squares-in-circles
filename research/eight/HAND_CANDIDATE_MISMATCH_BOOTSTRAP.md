# Hand implications for staged candidate capture

## Scope

This note proves continuous implications that can be applied after a
full-domain cyclic pair bound. It does not supply an unproved pair bound,
declare an unverified numerical fit valid, or close the remaining candidate
capture gate. The fixed comparisons in
`candidate_mismatch_bootstrap_arithmetic.json` verify the rational constants
below; all geometric and cyclic arguments are given here.

The roles are \((H,G,A,B,T,D,E)=(0,1,2,3,4,5,6)\), the quarter word is
\(k=(0,1,0,1,0,1,1)\), and

\[
\phi_i=k_i\pi/2+d_i,\quad d_i=\theta_{i+1}-\theta_i,\qquad
I=\{0,2,3,4,5\},\quad S=\sum_{i\in I}|d_i|.
\tag{1}
\]

The hand frame theorem gives \(|d_i|<7/10\) on every edge. A smaller
proved bound on S supplies that same smaller bound on each of the five
charged differences. Every later table using such a restriction is
conditional on the earlier theorem that supplied it.

## 1. A general cyclic contraction

Let \(0<L\le7/10\), suppose \(|d_i|\le L\) for \(i\in I\), and
let \(\beta>0\). Define

\[
h(x)=\frac{|\sin x|+|\cos x|-1}{2}.
\]

Suppose a fully covered pair theorem supplies labels \(L_i\) and constants
\(\gamma_i\), with

\[
\phi_i-\beta_i h(\phi_i)+L_i-L_{i+1}\ge\gamma_i
\quad\text{for every retained actual separator},
\qquad
\beta_i=\begin{cases}\beta&i\in I,\\0&i\notin I.\end{cases}
\tag{2}
\]

Put \(e_i=\phi_i-\beta_i h(\phi_i)+L_i-L_{i+1}-\gamma_i\ge0\).
The labels and actual frame differences telescope, so

\[
\sum_i e_i+\beta\sum_{i\in I}h(|d_i|)
=2\pi-\sum_i\gamma_i.
\tag{3}
\]

On \([0,7/10]\), \(h(x)=(\sin x+\cos x-1)/2\) is concave and
vanishes at zero. If a rational \(\kappa>0\) satisfies
\(h(L)>\kappa L\), its endpoint chord gives

\[
                 h(x)\ge\kappa x\qquad(0\le x\le L).
\tag{4}
\]

Thus, whenever \(\sum_i\gamma_i+\varepsilon>2\pi\),

\[
\boxed{\quad S<\frac{\varepsilon}{\beta\kappa}.\quad}
\tag{5}
\]

All signs in this implication matter: (2) covers every currently possible
axis before (3) is summed. A desired contact owner is not used as a
hypothesis of the bound that is intended to prove that owner.

The following fixed rational choices satisfy (4). Their verification uses
only the lower Taylor sums \(S_7(L)\le\sin L\) and
\(C_{10}(L)\le\cos L\).

| L | Admissible kappa |
|---|---|
| \(7/10\) | \(29/100\) |
| \(2/5\) | \(38/100\) |
| \(3/10\) | \(41/100\) |
| \(1/4\) | \(43/100\) |
| \(1/5\) | \(44/100\) |
| \(1/8\) | \(46/100\) |
| \(1/10\) | \(47/100\) |
| \(1/20\) | \(48/100\) |
| \(1/40\) | \(49/100\) |
| \(1/250\) | \(49/100\) |

For example, with the initial L=7/10 and beta=1/50, a complete theorem
with all seven \(\gamma_i=17947/20000=.89735\) would give S<3/10:

\[
7\frac{17947}{20000}+\frac1{50}\frac{29}{100}\frac3{10}
-\frac{710}{113}=\frac{47}{11300000}>0.
\tag{6}
\]

Equation (6) is an interface, not a claim that this particular pair theorem
has already been established. Each actual contraction stage must bind its
own exact table, domains and lower constants.

## 2. Containment bounds used to eliminate axes

Work at squared radius \(q\le Q=9789/2500\). A canonical exterior
square has center \((a,-u a)\), where \(|u|\le1\). Set \(b=|u|a\).
It avoids the open radius-1/12 central disk. Therefore

\[
\frac1{12}\le
\sqrt{(a-1/2)_+^2+(b-1/2)_+^2}
\le\sqrt2(a-1/2)_+.
\]

Since \(\sqrt2>141/100\),

\[
             a\ge\frac12+\frac{\sqrt2}{24}>\frac{447}{800}=.55875.
\tag{7}
\]

The farthest-corner containment equation yields

\[
(a+1/2)^2+(b+1/2)^2\le Q.
\tag{8}
\]

At \(a=283/200=1.415\), even the value b=0 makes the left side
larger than Q. Hence a<1.415. Also a>=b gives
\(2(b+1/2)^2\le Q<98/25=3.92\), hence b<9/10. We have proved

\[
                   .55875<a<1.415,\qquad0\le b<.9.
\tag{9}
\]

These bounds hold for original exterior squares and for their boundary
representatives; they do not require an outer radial kind.

## 3. At S <= 2/5, zero-quarter edges have only axes 1 and 3

Consider a zero-quarter edge, so \(\phi=d\), and put \(x=|d|\le2/5\).
For source \((a,-\sigma b)\) and target \(R_\phi(A,-\tau B)\), the
primary margins are

\[
M_2=A-a\cos\phi+\sigma b\sin\phi-W,\qquad
M_4=a-A\cos\phi-\tau B\sin\phi-W,
\quad W=\frac{1+\sin x+\cos x}{2}.
\]

Because b<=a, B<=A and cos x−sin x>0, either margin is bounded above by

\[
1.415-.55875(\cos x-\sin x)-W
=.915-1.05875\cos x+.05875\sin x.
\tag{10}
\]

The elementary inequalities
\(\cos x\ge1-x^2/2\ge.92\), \(\sin x\le x\le.4\) make (10)
at most

\[
             .915-1.05875(.92)+.05875(.4)=-\frac{711}{20000}<0.
\tag{11}
\]

Thus neither axis 2 nor axis 4 separates. In the candidate word this
applies to H→G, A→B and T→D whenever S<=2/5. Every selected separator
on these three edges is then axis 1 or axis 3, including all ties.

## 4. At S <= 1/10, the zero-quarter edges force strict signs

Let x<=1/10. Axes 2 and 4 are already excluded. The remaining margins are

\[
M_1=\sigma b+A\sin\phi-\tau B\cos\phi-W,\qquad
M_3=a\sin\phi+\sigma b\cos\phi-\tau B-W.
\tag{12}
\]

If the source signed coordinate \(\sigma b\le0\), then axis 1 is
bounded above by

\[
1.415\sin x+.9\cos x-W
\le .915(.1)+.4-.5=-.0085<0.
\tag{13}
\]

If the target signed coordinate \(\tau B\ge0\), axis 1 is instead
bounded above by

\[
.9+1.415\sin x-W
\le .4+.915(.1)-\tfrac12(1-.1^2/2)=-.006<0.
\tag{14}
\]

For axis 3 the same two bounds apply with their roles interchanged:
source \(\sigma b\le0\) gives (14), and target \(\tau B\ge0\)
gives (13). Therefore an actually separating zero-quarter pair requires

\[
                         u_{\rm source}>0>u_{\rm target}.
\tag{15}
\]

For the three candidate zero-quarter edges this gives

\[
                   u_H>0>u_G,\qquad
                   u_A>0>u_B,\qquad
                   u_T>0>u_D.
\tag{16}
\]

All zero tangents are explicitly excluded by the strict reserves. These
signs are consequences of a proved mismatch bound, so they can be used to
reduce a later pair table without circularity.

## 5. Conditional fixed-table implementation

`verify_conditional_affine_arc_hand.js` retains the exact support and
polynomial arithmetic of the independently audited affine-arc kernel.
It additionally accepts explicitly declared signed frame-difference
intervals and original-axis domains. They are printed as hypotheses in
its output. Its default is [-.7,.7] and all four axes on every edge.

Each declared interval must lie in [-.7,.7]. Required angle unions are
the intersection of the physical center-gap range with that declared
signed interval, separately for the positive and negative half branches.
An original-axis restriction changes only which chains must be covered;
it is an input hypothesis to be discharged by an earlier theorem such as
Section 3, or by an explicit complementary-case assumption.

The conditional kernel's default replay gives exactly the same 9,796 row
results and complete angle-cover report as the frozen upper-G proof. The
new conditional-domain interface now has its independent review in
`CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`; all signed-range,
original-axis and isolated-angle-endpoint checks pass. Each restricted
table must still supply its own complete domain cover. No completed G
proof has been altered by this extension.
