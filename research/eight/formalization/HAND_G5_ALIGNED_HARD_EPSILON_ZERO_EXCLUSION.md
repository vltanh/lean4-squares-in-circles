# The entire epsilon-zero aligned hard-quarter branch is excluded

## 1. Scope and statement

Put `Q=9789/2500`. Consider the original own-frame signs

\[
 (y_H,y_G,y_A,y_B,y_T,y_D,y_E)
 =(b_H,-b_G,b_A,-b_B,b_T,-b_D,-b_E),\qquad b_i\ge0,
\]

sorting `a_i>=b_i`, and corner bounds

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q.
\tag{1}
\]

Assume all three zero edges are aligned, retain either original
transverse witness on each, and retain original axes GA0, BT2, DE3,
EH1. Let

\[
 \theta_H=\theta_G=t,\quad\theta_A=\theta_B=0,
 \quad\theta_T=\theta_D=-u,
 \quad\theta_E=t,
\]
\[
 t,u\ge0,\qquad\alpha=t+u\le7/10.
\tag{2}
\]

Thus `epsilon=theta_H-theta_E=0` and `delta=alpha`. These are
explicit branch hypotheses, including the weak E sign.

**Theorem.** No such edge system exists. The proof covers every
nonnegative E transverse magnitude, not just the E-zero boundary.
It requires no core, nonneighbor, or mismatch-capture premise.

The theorem also excludes the weaker **five-anchor system**, in
which G and T are omitted entirely. Keep (1) for H, A, B, D and E,
the respective frames `t,0,0,-u,t`, and assume only

\[
\begin{split}
 b_H+a_A\cos t-b_A\sin t&\ge1+W(t),\\
 a_B\cos u-b_B\sin u+b_D&\ge1+W(u),\\
 b_A+b_B&\ge1,\\
 a_D+a_E\sin\alpha+b_E\cos\alpha&\ge W(\alpha),\\
 a_H-b_E&\ge1,
\end{split}
\qquad W(z)=\frac{1+\cos z+\sin z}{2}.
\tag{2a}
\]

The first two inequalities are the composites HG+GA and BT+TD;
the last two are exactly the original DE3 and EH1 projections in
these frames. The original seven-vertex hypotheses imply (2a) by
addition and elimination of the same shared G/T transverse
coordinates. Every subsequent step uses only (2a) and the five
retained circles, so existence of replacement G or T centers is
not needed. This is the formulation supplied by a preceding
three-zero necessary reduction.

For this exclusion, it is harmless to use Q as a common containing
circle throughout. The conclusion is a contradiction already at Q;
no radius-changing descendant is asserted in this note.

## 2. Elementary domain bounds and the necessary cap sum

The shared A/B-chain calculation in Section 2 of
`HAND_G4_E_INTERIOR_BOUNDARY_REDUCTION.md` uses exactly the
first three composite inequalities in (2a) and their circles.
It proves

\[
                         0\le\alpha<11/50=.22.
\tag{3}
\]

It is independent of E's sign magnitude and does not use its
interior-orientation reduction.

Write `b=b_E` and define

\[
 f(x)=\sqrt{Q-(x+1/2)^2}-\frac12,
 \qquad C_0=\sqrt{Q/2}-\frac12<.9,
\]
\[
 c=\cos\alpha,\quad s=\sin\alpha,
 \quad W=\frac{1+c+s}{2},
 \quad g(b)=W-f(b)s-bc.
\tag{4}
\]

The actual EH1 witness is `a_H-b>=1`. The first composite in
(2a), `W>=1` and `a_A<U=283/200` give
`b_H>=2-a_A>2-U=.585`. Thus the H circle
forces

\[
                               0\le b<31/200=.155.
\tag{5}
\]

Indeed `b>=.155` would give a squared corner value larger than Q,
because

\[
 (331/200)^2+(217/200)^2-Q=13/20000>0.
\]

The E circle gives `a_E<=f(b)`. Increasing this primary in the DE3
projection only weakens the necessary bound. Hence the same actual
H and D vertices satisfy

\[
 b_H\le B_H(b):=f(1+b),
 \qquad
 b_D\le B_D(b):=\min\{C_0,f(g(b))\}.
\tag{6}
\]

Here `g(b)` is positive on the entire relevant interval. In fact
`W>=1`, `f(b)<U`, (3),(5) give `g(b)>.5337>1/2`.
Also `b<1/2` and `f(b)>1/2` give the identity and inequality

\[
 g(b)=1-b+(b-1/2)(1-c)-(f(b)-1/2)s\le1-b\le1.
\tag{7}
\]

In particular every square root in (6) is real. The cap `B_D`
is nondecreasing in b, since `g'(b)<0`: on this interval
`-f'(b)<1` and `s<c`.

For an endpoint transverse bound B define the original hard cap

\[
 \mathcal L(\theta,B)
 =\cos\theta\sqrt{Q-(3/2-B+\cos\theta)^2}
        -\sin\theta(3/2-B+\cos\theta).
\tag{8}
\]

It increases with B. The actual HG--GA and BT--TD paths, followed
by their actual AB constraint, therefore give

\[
 2\le\mathcal L(t,B_H(b))+\mathcal L(u,B_D(b)).
\tag{9}
\]

It suffices to exclude the two endpoint splits `(t,u)=(0,alpha)`
and `(alpha,0)`. The full-feasible-cap convexity theorem in
`HAND_G5_HARD_SPLIT_CONVEXITY_FULL_FEASIBLE_CAP_RANGE.md`
applies to (9): each actual feasible cap supplies its own
`Q>=(D+1)^2+1/4` lower bound, and `D=1.5-B>=.6`.
Equivalently, one may use that note's construction preserving H,
D, E and their exact mixed contacts. No bad-mismatch condition is
needed for this complete branch exclusion.

## 3. The endpoint cap sum is concave in the E transverse coordinate

For a fixed angle theta, introduce

\[
 R(x)=\sqrt{Q-(x+1/2)^2},\qquad r_x=\frac{x+1/2}{R(x)},
\]
\[
 C_\theta(x)=2-R(x)+\cos\theta,
 \qquad w_\theta(x)=\sqrt{Q-C_\theta(x)^2},
\]
\[
 H_\theta(x)
 =\cos\theta\,w_\theta(x)-\sin\theta\,C_\theta(x)
 =\mathcal L(\theta,f(x)).
\tag{10}
\]

On the domains used below these are real and `C_theta,w_theta>0`.
Put

\[
 J_\theta(x)=\sin\theta+
              \cos\theta\frac{C_\theta(x)}{w_\theta(x)},
 \qquad K_\theta(x)=r_xJ_\theta(x)>0.
\]

Direct differentiation gives

\[
 H_\theta'(x)=-K_\theta(x),
\]
\[
 \partial_xK_\theta(x)
 =\frac{\cos\theta\,Q r_x^2}{w_\theta(x)^3}
             +\frac{J_\theta(x)Q}{R(x)^3}>0.
\tag{11}
\]

Thus H is decreasing and strictly concave in its primary argument.
The scalar g in (4) is convex in b, because f is concave and
`s>=0`. It follows that `H_u(g(b))` is concave in b.

For either endpoint split define

\[
 \Phi_{t,u}(b)
 =H_t(1+b)+
   \min\{\mathcal L(u,C_0),H_u(g(b))\}.
\tag{12}
\]

The minimum with a constant preserves concavity. For example, its
hypograph is the intersection of the two convex hypographs; one
may equivalently use the single clipping point as g decreases.
Consequently (12) is concave on `[0,b_actual]`.

All the functions are defined on this whole interval. For H, the
cap at the actual b is feasible, and reducing b increases its cap.
For D, (7) gives `f(g(b))>=f(1)>.79`, and so its radicand in
(10) is bounded below by `Q-1.71^2>.995^2` before clipping.

We will prove

\[
                         \Phi_{t,u}'(0+)\le0.
\tag{13}
\]

Concavity then gives `Phi_{t,u}(b)<=Phi_{t,u}(0)` for every
feasible b.

## 4. Only one short unclipped interval needs a derivative estimate

Write

\[
 R_0=\sqrt{Q-1/4},\qquad v=R_0-1,
 \qquad \eta=\frac1{2R_0},
\]
\[
 g_0(\alpha):=g(0)=\frac12+\frac c2-vs,
 \qquad -\partial_bg(0)=c-\eta s>0.
\tag{14}
\]

If `g_0<=C_0`, the D cap is already clipped at b=0 and stays
clipped for all larger b. The H cap decreases, so (13) is immediate.
This includes a weak tie at the clipping point.

Otherwise `g_0>C_0`, which forces

\[
                              0\le\alpha<11/100.
\tag{15}
\]

Indeed g_0 decreases. At `.11`, elementary alternating Taylor
bounds give `cos(.11)<.994`, `sin(.11)>.1097`, and `v>.914`.
Thus

\[
 g_0(.11)<\frac{4483671}{5000000}<.899<C_0.
\]

The final comparison follows by squaring, with
`Q-2(1399/1000)^2=599/500000>0`.

On the entire active rectangle

\[
 0\le\theta\le.11,\qquad C_0\le x\le1,
\]

we have the useful uniform bounds

\[
 \cos\theta>.99,\quad 1\le r_x<6/5,
 \quad R(x)<7/5,
 \quad C_\theta(x)>1.59,
 \quad w_\theta(x)<6/5.
\]

Consequently (11) gives

\[
 \partial_xK_\theta(x)
 >\frac{224939}{54880}
 =4+\frac{5419}{54880}>4.
\tag{16}
\]

For transparency, this bound substitutes
`cos>.99`, `Q>3.9`, `r_x>=1`, `w<1.2`, `R<1.4`, and
`J>.99(1.59)/1.2` into the two positive terms of (11).

There is also a simple angular bound

\[
                         \partial_\theta K_\theta(x)<6/5.
\tag{17}
\]

To see it, use the cap variables `L,X,w,C,k=w-sin(theta)` at
the fixed x. Then

\[
 \partial_\theta J
 =\frac{Lk}{w^2}-\frac{XC\sin\theta}{w^3}\le1.
\]

Here `L<=w` and `0<k<=w`. Multiplication by `r_x<6/5`
proves (17).

## 5. The endpoint with t=0

On the unclipped arc define

\[
 A(\alpha)
 =K_\alpha(g_0(\alpha))(\cos\alpha-\eta\sin\alpha).
\]

The factor in parentheses is positive and decreases. Also

\[
 g_0'(\alpha)=-\frac12\sin\alpha-v\cos\alpha
                         <-891/1000.
\]

Equations (16)--(17) therefore give

\[
 \frac{d}{d\alpha}K_\alpha(g_0(\alpha))
 <\frac65-4\frac{891}{1000}<0.
\]

Thus A decreases from `A(0)=K_0(1)`. For `(t,u)=(0,alpha)`,
the right derivative of (12) is

\[
 \Phi_{0,\alpha}'(0+)
 =-K_0(1)+A(\alpha)\le0.
\tag{18}
\]

This also includes alpha=0.

## 6. The endpoint with u=0

On `[0,.11]`,

\[
                            K_\theta(1)\ge K_0(1).
\tag{19}
\]

Here is a direct uniform proof. At x=1 one has
`f(1)>.79`, hence `C<1.71`, `w>.995`, and
`cos(theta)>1-.11^2/2=.99395`. Thus

\[
 L>\frac{3203521}{4000000}>.8,
 \quad k>.88,\quad w>.99,\quad X<2.
\]

The numerator in the angular derivative of J is therefore positive:

\[
 Lkw-XC\sin\theta
 >(.8)(.88)(.99)-(2)(1.71)(.11)
 =\frac{8019}{25000}>0.
\]

Thus K_theta(1) increases, proving (19). Since K_0 increases in
x, `g_0<=1` and `0<c-eta s<=1` imply

\[
\begin{split}
 \Phi_{\alpha,0}'(0+)
 &=-K_\alpha(1)+K_0(g_0)(c-\eta s)\\
 &\le-K_0(1)+K_0(1)=0.
\end{split}
\tag{20}
\]

Together with the clipped case, Sections 5--6 prove (13) for both
endpoints and every alpha in (3).

## 7. The explicit E-zero scalar reserve finishes both endpoints

At b=0 the two caps in (6) are exactly

\[
 B_H(0)=f(1)=B(0),\qquad
 B_D(0)=\min\{C_0,f(g_0(\alpha))\}=B(\alpha),
\]

where B is the explicit E-zero endpoint cap in
`HAND_G5_E_ZERO_HARD_QUARTER_SPLIT_EXCLUSION.md`.
Equations (18)--(19) of that note are scalar inequalities, not
existence assertions about comparison packings. They give

\[
 \Phi_{0,\alpha}(0)<2-\frac{149}{625000},\qquad
 \Phi_{\alpha,0}(0)<2-\frac{149}{625000}.
\tag{21}
\]

Concavity and (13) now prove the same strict upper bounds for all
feasible b. They contradict the necessary lower bound two in (9).
Full split convexity, or its endpoint construction preserving H,D,E,
therefore excludes every split in (2), completing the theorem.

This proof treats the same E transverse parameter through both
neighboring constraints, retains every original center when deriving
the inequalities, and uses a single concavity argument for its whole
range. No numeric minimizer, angle mesh, owner preference, or
generated state inventory is a premise. Other owner/sign classes and
nonzero zero-edge errors remain separate reduction obligations.
