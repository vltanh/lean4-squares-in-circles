# Positive D tilt: every surviving weak-link separator points upward and is shallow

Independent mathematical review on November 2, 2026 accepted the entire
continuous-domain proof, all owner/sign and diagonal boundary cases, and
the exact scalar checker. No C-bottom or unproved placement lemma is used.

This is a hand exclusion of complete original separator cells in the
`001/00` caller at `R^2<=Q=1105/256`. Normalize
`d=x_D-x_C>=v=y_D-y_C>=7/30`, retain the original strict weak bit
`d<h_C+h_D`, and suppose D has canonical nonnegative tilt

\[
u_D=(\alpha_D,\beta_D),\quad
w_D=(-\beta_D,\alpha_D),\quad
\alpha_D\ge\beta_D\ge0.
\]

The accepted G-order theorem and signed right cap apply in this caller.
All original squares remain present. The argument only needs the seven
selected originals and makes no claim that the remaining full-nine bulk
has closed.

**Conclusion.** Every usable original owned C,D separator must point
upward and have slope at most one. A C-owned separator of slope at least
one is impossible. Thus the only surviving signed original owner options
are the upward shallow axes of C or D; a D-owned slope-one boundary is
retained. In particular a negative C tilt cannot contribute its upward
steep axis as a usable separator.

## 1. Original consequences and the cap-transfer criterion

Write

\[
h_i=(\alpha_i+|\beta_i|)/2,\quad g_i=1/(4h_i),\quad
\eta_i=h_i+g_i-1\ge0.
\]

The two actual main links and the original center-radius/corner bounds
give

\[
d+h_C+h_D<2011/960.
\]

The original cone inset gives `d>=g_C+g_D`. Consequently

\[
\boxed{\eta_C+\eta_D<91/960.}                       \tag{1}
\]

These are the same original span inequalities used in the accepted
two-thirds transfer proofs. Set

\[
K=23/32,\qquad
\sigma_D/46=\alpha_D-1+K\beta_D.
\]

The signed right cap and ordinary left cap contradict any strict transfer

\[
                 d+h_C-h_D+\sigma_D/46>1.            \tag{2}
\]

Indeed the actual A,B and B,C links then make the adjusted main span,
including its signed toll, exceed two; the two actual short links make
the adjusted short span at least one. Their weighted sum exceeds
`2*46+27/2=211/2`, while the two original endpoint caps bound that same
quantity above by `211/2`.

The accepted strict-weak cone sign lemma gives `n_x>0` for every usable
owned separator, and `|n_y|<n_x` if `n_y<0`. A horizontal normal is
impossible by the original strict weak bit.

## 2. Downward normals are impossible

Suppose a usable separator is `n=(c,-s)`, with `c>0`, `s>0`, and
`t=s/c<1`. Put `h=(alpha_D+beta_D)/2`,
`j=(alpha_D-beta_D)/2`. The unchanged D frame has exact support
`H_D(n)=c*h+s*j`. The free-frame comparison for the unchanged C frame
therefore gives

\[
d+h_C-h_D\ge A(t)+t(j+v)>1,
\qquad
A(t)=\frac{\sqrt{1+t^2}}2+
     \frac{1+t}{2\sqrt{1+t^2}}.
\]

The strict inequality uses `A(0)=1` and
`A'(t)=(1+t^3)/(2(1+t^2)^(3/2))>0`. The signed toll is nonnegative:
writing `z_D=beta_D/(1+alpha_D)<=sqrt(2)-1<K` gives
`sigma_D/46=beta_D(K-z_D)>=0`. Thus (2) holds, a contradiction.

## 3. A complete scalar orientation-budget lemma

Define, for folded physical C and nonnegative D,

\[
r=\frac{|\beta_C|}{\alpha_C+|\beta_C|}\in[0,1/2],
\qquad
z=\frac{\beta_D}{1+\alpha_D}\in[0,\sqrt2-1].
\]

We prove from (1) that

\[
                         \boxed{r+z<K.}              \tag{3}
\]

In these variables the same original width excesses are

\[
E(r)=\frac{1+D(r)}{2\sqrt{D(r)}}-1,
\quad D(r)=1-2r+2r^2,
\]

and

\[
L(z)=\frac{2z^2(1-z)^2}
           {(1+z^2)(1+2z-z^2)}.
\]

Both functions increase over their stated folded ranges. For E this
follows because `D` decreases and the corresponding
`alpha_C+|beta_C|=1/sqrt(D)` increases. For L, the corresponding folded
width sum is

\[
q(z)=\frac{1+2z-z^2}{1+z^2},\qquad
q'(z)=\frac{2(1-2z-z^2)}{(1+z^2)^2}\ge0,
\]

and `L=(q+1/q)/2-1` increases for `q>=1`.

Suppose contrary to (3) that `r+z>=K`. Then

\[
r_0:=55/32-\sqrt2\le r\le1/2,
\qquad 7/32\le K-r\le\sqrt2-1,
\]

and monotonicity gives

\[
\eta_C+\eta_D=E(r)+L(z)\ge F(r):=E(r)+L(K-r).       \tag{4}
\]

We now check concavity on this *entire* interval. First, `r_0>3/10`
because `(227/160)^2-2=329/25600>0`. Direct differentiation gives

\[
E''(r)=\frac{5(1-2r)^2-1}{4D(r)^{5/2}}<0
\quad(3/10\le r\le1/2).
\]

Also `sqrt(2)-1<5/12`, since `(17/12)^2-2=1/144>0`.
Put `W(z)=(1+z^2)(1+2z-z^2)>0`. Direct rational differentiation gives

\[
L''(z)=4P(z)/W(z)^3,
\]

where the polynomial may be grouped as

\[
\begin{split}
P(z)={}&1-6z+6z^2(6z^2-1)\\
      &-6z^3(1-z^2)-3z^6(6-2z-z^2).
\end{split}
\]

For `7/32<=z<=5/12`, its last two grouped terms are nonpositive, while

\[
1-6z\le-5/16,
\qquad
6z^2(6z^2-1)\le z^2/4\le25/576.
\]

The middle comparison uses `6z^2<=25/24`. Thus
`P(z)<=-155/576<0`, proving strict concavity of L throughout the required
range. Consequently F in (4) is concave, so its minimum is at an endpoint.

At the right endpoint,

\[
F(1/2)=\frac{3\sqrt2}{4}-1+\frac{61250}{1526879}.
\]

Since `sqrt(2)>24/17`, its excess over `91/960` is greater than

\[
\frac1{17}+\frac{61250}{1526879}-\frac{91}{960}
 =\frac{103322027}{24918665280}>0.                  \tag{5}
\]

At the left endpoint, `L(K-r_0)=L(sqrt(2)-1)=3sqrt(2)/4-1>1/17`.
Moreover

\[
E(r_0)>E(3/10)=\frac{79}{10\sqrt{58}}-1>
\frac{11}{305},
\]

where the last step uses `(61/8)^2-58=9/64>0`. Therefore

\[
F(r_0)-91/960>
\frac1{17}+\frac{11}{305}-\frac{91}{960}
=\frac{97}{995520}>0.                              \tag{6}
\]

Both complete endpoint checks are strict. Concavity makes (4) greater
than `91/960` throughout the interval, contradicting (1). This proves (3).

## 4. An upward steep C-owned normal contradicts the signed cap

Suppose C owns an upward normal `n=(c,s)` with `0<c<=s`. For that original
owner, `h_C=(c+s)/2`, and its smaller coordinate ratio is
`r=c/(c+s)=|beta_C|/(alpha_C+|beta_C|)`. This includes either canonical
representation of a diagonal C frame.

The nonnegative D tilt has support `H_D(n)=c*j+s*h`, while C's owned
normal support is `1/2`. Since the original cone comparison is `v<=d`,

\[
(c+s)d\ge cd+sv\ge1/2+cj+sh.
\]

Divide by the positive `c+s`, noting `g_C=1/(2(c+s))`, to obtain

\[
d\ge g_C+h_D-\beta_D r.
\]

With `alpha_D-1=-beta_D z`, this yields

\[
\begin{split}
d+h_C-h_D+\sigma_D/46
&\ge1+\eta_C+\beta_D(K-r-z)\\
&>1.
\end{split}
\]

The last inequality follows from (3); even if beta_D is zero,
`c>0` makes `h_C>1/2` and hence `eta_C>0`. This proves (2), a
contradiction for every upward steep C-owned normal.

If D owns an upward normal with positive horizontal component, its
nonnegative canonical tilt already gives slope at most one. Its other
axis has nonpositive horizontal component and was excluded by the
strict-weak cone sign lemma. Together with Section 2, this proves the
stated complete reduction of the original owner/sign options.

## Exact arithmetic and scope

`computer_assisted/weak_outer_numeric_positive_separator_arithmetic.py`
reconstructs the rational derivative numerator, all square-root
comparisons, and both orientation-budget endpoint reserves. No numerical
optimization claim is used in this proof. The remaining upward shallow
original separator alternatives still require the full-nine bulk
argument; this reduction alone does not close `001/00` or `100/00`.
