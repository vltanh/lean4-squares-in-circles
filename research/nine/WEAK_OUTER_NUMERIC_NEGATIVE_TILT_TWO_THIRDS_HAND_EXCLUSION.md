# Negative D tilt: complete exclusion through transverse gap 2/3

This extends the accepted negative-tilt `5/8` theorem to `2/3`. It is a
complete hand argument with an exact arithmetic companion. Discovery of
the sharper constants was computer assisted; numerical values are not
premises. No Lean, Lake or CI is used.

## Statement

Retain the original nine-square `001/00` predicate at
`R^2<=Q=1105/256`, with actual A,B and B,C links, a strict weak original
C,D cone link, and actual E,F and F,G links. Reflect vertically so that

\[
d=x_D-x_C>0,\qquad 0\le v=y_D-y_C\le2/3.
\]

Suppose D's canonical original frame has nonpositive folded tilt:

\[
u_D=(\alpha,-\beta),\qquad w_D=(\beta,\alpha),\qquad
\alpha^2+\beta^2=1,\quad\alpha\ge\beta\ge0.
\]

**These hypotheses are impossible, including at closed Q.** All nine
originals remain present; the contradiction needs only the seven
selected originals. Simultaneous reversal gives the corresponding
`100/00` statement.

The accepted inputs are the original endpoint cap and universal
four-beta toll, the center-radius bound `|c_i|<91/60`, and the elementary
free-frame support comparison proved in
`WEAK_OUTER_NUMERIC_NEGATIVE_TILT_LOW_GAP_HAND_EXCLUSION.md`:

\[
H_S(n)+c h_S\ge\frac{1+c^2+cs}{2},
\qquad c=n_x>0,\quad s=|n_y|,\quad c^2+s^2=1.       \tag{1}
\]

It applies to the unchanged original S frame. On each interval between
projection-sign changes its left side is concave in that frame angle,
so the minimum occurs when an axis is parallel to the horizontal or to
n. The two endpoint values are `c+s/2` and `(1+c^2+cs)/2`; the latter is
smaller because their difference is `(1-c)(1-c-s)/2<=0`.

## Every usable original separator has slope magnitude below 13/40

The two actual main links imply
`x_C-x_A>=h_A+2h_B+h_C>=3/2+h_C`. Using original containment and the
center-radius bound therefore gives

\[
d+h_C+h_D<\frac{133}{64}+\frac{91}{60}-\frac32
          =\frac{2011}{960}.                       \tag{2}
\]

Every physical original owned separator n for C,D has `n_x>0`:
otherwise `n.(c_D-c_C)<=v<=2/3<1`, while the two physical unit-square
supports sum to at least one. Put `c=cos(phi)>0`, `s=sin(phi)>=0`.
For the original owner of n, its supports are exactly `1/2` and
`(c+s)/2`. Combining these with (1) for the other original square gives

\[
d+h_C+h_D\ge J(\phi)
 :=\sec\phi+\cos\phi+\sin\phi-\frac23\tan\phi.
\]

This function is strictly increasing on `[0,pi/2)`, since

\[
J'(\phi)=\frac{\sin^3\phi+\cos^3\phi-2/3}{\cos^2\phi}>0;
\]

the numerator is at least `1/sqrt(2)-2/3>0`. At `tan(phi)=13/40`,

\[
J(\phi)=\frac{3889}{40\sqrt{1769}}-\frac{13}{60}
        >\frac{2011}{960}.                         \tag{3}
\]

After positive-denominator multiplication and squaring, the comparison
in (3) is exactly

\[
93336>2219\sqrt{1769},\qquad
93336^2-2219^2\,1769=1121887>0.
\]

Consequently every usable original owned separator satisfies

\[
\boxed{\quad t:=|n_y|/n_x<13/40.\quad}             \tag{4}
\]

This restriction accounts for both owners and all original signs. It
does not assume that horizontal separation is available.

## The upward transfer

Write `h=(alpha+beta)/2`, `k=(alpha-beta)/2`, and

\[
A(t)=\frac{\sqrt{1+t^2}}2+
     \frac{1+t}{2\sqrt{1+t^2}},\qquad T=13/40.
\]

For an upward separator, (4) is below `alpha/beta` whenever beta is
positive, so the original D support is `c*h+s*k`. Equation (1) for the
original C frame and physical separation give

\[
d+h_C-h_D+\frac{2\beta}{23}
\ge A(t)+t(k-v)+\frac{2\beta}{23}
\ge F(t):=A(t)+t(k-2/3)+\frac{2\beta}{23}.          \tag{5}
\]

This last function is concave on `[0,T]`, because

\[
A''(t)=\frac{3t(t-1)}{2(1+t^2)^{5/2}}\le0.
\]

At zero, `F(0)=1+2beta/23>=1`. At the other endpoint,

\[
T k+\frac{2\beta}{23}
=\frac{13}{80}\alpha-\frac{139}{1840}\beta
\ge\frac{\sqrt2}{23}.                            \tag{6}
\]

Indeed, as beta increases from zero to `1/sqrt(2)`, the left side in
(6), with `alpha=sqrt(1-beta^2)`, is decreasing. Its minimum is its
displayed value at `alpha=beta=1/sqrt(2)`.

Therefore

\[
F(T)\ge\frac{3889}{80\sqrt{1769}}-\frac{13}{60}
                    +\frac{\sqrt2}{23}>1.          \tag{7}
\]

There is a short entirely rational check of (7). The squared reserves

\[
(673/16)^2-1769=65/256>0,\qquad
2-(24/17)^2=2/289>0
\]

give `sqrt(1769)<673/16` and `sqrt(2)>24/17`. Thus the excess in (7) is
strictly greater than

\[
\frac{3889}{3365}-\frac{13}{60}+\frac{24}{391}-1
=\frac{6869}{15788580}>0.
\]

Concavity and the two endpoint comparisons imply `F(t)>1` whenever
`0<t<=T`. The remaining value `t=0` would be a horizontal separator and
would imply `d>=h_C+h_D`, contrary to the original strict weak bit.
Consequently every upward separator proves the strict transfer

\[
\boxed{\quad d+h_C-h_D+\frac{4\beta_D}{46}>1.\quad} \tag{8}
\]

## Downward separators and the cap contradiction

The downward support argument is unchanged and has no upper bound on
v: replacing its favorable displacement `-v` by zero only weakens the
physical inequality. For completeness, put `t_D=beta/alpha`. The
adjusted original gap is bounded below by

\[
\begin{cases}
A(t)-t k,&0\le t\le t_D,\\
A(t)-\beta+t h,&t_D\le t\le1.
\end{cases}
\]

Each branch is concave. Its complete endpoint values at `0,t_D,1`
are `1`, `1/alpha`, and `sqrt(2)+k`, all at least one. Positive beta
makes (8) strict through its toll. If beta is zero, the downward
normal has `t>0` and gives `A(t)+t/2>1` directly. This accounts for all
negative-tilt boundary cases.

Finally define the original adjusted endpoint spans

\[
D_0=x_D-x_A-h_A-h_D,\qquad
S_0=x_G-x_E-h_E-h_G.
\]

The actual A,B and B,C links and (8) give
`D_0+4beta_D/46>2`; the actual short links give `S_0>=1`.
The original A,E cap and the universal four-beta D,G cap give

\[
46D_0+\frac{27}{2}S_0+4\beta_D\le2\frac{211}{4}.
\]

The strict lower bound makes the left side greater than
`2*46+27/2=2*(211/4)`, a contradiction. No D/G height order is needed
for this negative-tilt theorem.

This closes the complete nonpositive-D-tilt domain `v<=2/3` at closed Q.
The positive-tilt complement and the remaining full-nine large-gap
domain still need their own complete arguments. The companion
`computer_assisted/weak_outer_numeric_negative_two_thirds_arithmetic.py`
reproduces every new scalar comparison exactly.
