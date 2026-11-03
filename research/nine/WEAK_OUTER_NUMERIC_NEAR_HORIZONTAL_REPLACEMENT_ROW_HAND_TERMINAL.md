# A global-angle near-horizontal replacement row closes the strict caller

November 3, 2026. Complete hand reduction with exact scalar checks.
The two new row links may each be weak; no common orientation or small
angle assumption is made. This supplies an analytic terminal around the
identified closed-weak boundary control, including its equality face.

Independent review: the root proof integrator and the global-extraction
reviewer each read the complete argument and replayed the exact scalar
checks on November 3, 2026. Both accepted the statement, all owner and
chirality cases, and the strict-caller equality exclusion. The separate
review is `GLOBAL_OUTER_LINK_EXTRACTION_REPLACEMENT_ROW_INDEPENDENT_REVIEW.md`.

Put `Q=1105/256`, `a=46`, `b=27/2`, and `epsilon=1/8`. For a canonical
folded original frame, write

\[
\alpha\ge\beta\ge0,\quad\alpha^2+\beta^2=1,\quad
t=\beta/\alpha\in[0,1],\quad
h=(\alpha+\beta)/2,\quad j=(\alpha-\beta)/2.
\]

The signed physical chirality remains unrestricted. Define the normalized
original main toll

\[
T(t)=\max\left\{\frac{2\beta}{23},\;
                  \frac{9\beta-41(1-\alpha)}{32}\right\}.
\]

The two entries are respectively the accepted universal four-beta toll
and the accepted sharp small-angle toll, divided by a. Both are valid
for the same original endpoint pair; their **maximum**, not their sum,
may therefore be used.

## 1. A physical pair estimate, with every owned axis retained

Consider original physical unit squares O,P whose centers differ by
`(d,v)`, where `d>0` and `|v|<=epsilon`. Their inscribed open disks imply

\[
d\ge\sqrt{1-\epsilon^2}=\sqrt{63}/8>\epsilon.
\]

Let one of the original squares own a physical separating normal. Call
its folded components `alpha,beta`. Set
`R=H_O(n)+H_P(n)`, the actual sum of original supports. If that axis is
shallow, physical separation gives `R<=alpha*d+epsilon*beta`. If it is
steep, it first gives `R<=beta*d+epsilon*alpha`, which is no larger than
`alpha*d+epsilon*beta` because `d>=epsilon` and `alpha>=beta`.

Every square's centered support is invariant under a quarter turn of its
direction. Thus R has the same value for the owner's shallow axis even
when its separating axis was steep. We claim

\[
                        R\ge1+\alpha|h_O-h_P|.       \tag{1}
\]

If the owner has the larger halfwidth, apply the accepted complete
free-frame support inequality to the other original square:

\[
H_P(n)+\alpha h_P\ge(1+\alpha^2+\alpha\beta)/2
                         =1/2+\alpha h_O.
\]

The owner's support is exactly `1/2`, proving (1). If `h_P>=h_O`, then
`j_P<=j_O`, since every original frame has `h^2+j^2=1/2` and `j>=0`.
The actual rightmost P vertex has coordinates `(h_P,±j_P)`, so its
projection on the owner's shallow axis gives

\[
H_P(n)\ge\alpha h_P-\beta j_P
        \ge\alpha h_P-\beta j_O.
\]

Now `alpha*h_O-beta*j_O=1/2`, and adding the owner's support `1/2`
again proves (1). Both physical chiralities and both possible owners
are covered.

Consequently the original horizontal gap satisfies

\[
d\ge1+|h_O-h_P|+q(t_{\rm owner}),\qquad
q(t)=\sqrt{1+t^2}-1-t/8.                            \tag{2}
\]

## 2. A complete two-variable scalar payment inequality

For all `s,t in [0,1]`, with `h(t)=(1+t)/(2sqrt(1+t^2))`, we prove

\[
q(s)+(h(s)-h(t))_++T(t)/2\ge0,                       \tag{3}
\]

with equality only when `s=t=0`.

### 2.1. Endpoint tilt at most 1/8

Suppose `0<=t<=1/8`. On `[0,t]`,
`q'(s)=s/sqrt(1+s^2)-1/8<=0`, so `q(s)>=q(t)` when `s<=t`.
For `s>=t`, use

\[
A(s)=\frac{\sqrt{1+s^2}}2+\frac{1+s}{2\sqrt{1+s^2}},
\]

whose derivative has minimum `1/(2sqrt(2))` on `[0,1]`. The exact
identity is

\[
(q+h)'(s)=A'(s)+\frac{s}{2\sqrt{1+s^2}}-1/8>0.
\]

Because h is increasing, these two cases show that the left side of
(3) is at least `q(t)+T(t)/2`, and hence at least the value using the
sharp toll branch. Put `r=sqrt(1+t^2)`. Multiplying that latter value by
the positive `64r` gives exactly

\[
105+64t^2+9t-(105+8t)r.
\]

The elementary bound `r<=1+t^2/2` shows this is at least

\[
t+\frac{23}{2}t^2-4t^3\ge0,
\]

strictly positive for `t>0`. At `t=0`, strict monotonicity of `q+h`
makes (3) strict for every `s>0`. This proves the claimed equality
condition on this entire domain.

### 2.2. The remaining endpoint tilts

Over the whole `[0,1]`, direct minimization gives

\[
q(s)\ge\sqrt{63}/8-1>-1/126,
\]

where the positive-root comparison has exact squared reserve
`63*126^2-1000^2=188`.

For `1/8<=t<=1/3`, write `theta=atan(t)`. The sharp normalized toll

\[
\frac{41\cos\theta+9\sin\theta-41}{32}
\]

is concave in theta and exceeds `1/63` at both endpoints. These are
exactly the positive comparisons

\[
21231>2615\sqrt{65},\qquad
8316>2615\sqrt{10},
\]

with squared reserves `6270736` and `773606` respectively. For
`1/3<=t<=1`, the four-beta branch gives

\[
T(t)\ge2/(23\sqrt{10})>1/63,
\]

with squared reserve `126^2-10*23^2=10586`. Thus in all cases
`t>=1/8`, the positive half-toll exceeds `1/126` and pays the entire
possible negative q value. Inequality (3) is strict throughout this
complement. This finishes the complete continuous scalar domain.

## 3. The two-link replacement-row theorem and equality

Let B,X,D be three distinct original physical squares, with

\[
x_B<x_X<x_D,\qquad
|y_X-y_B|\le1/8,\qquad |y_D-y_X|\le1/8.
\]

No actual projection separation is assumed for either new link. Choose
an original physical owner for each link and apply (2). Put

\[
V=|h_B-h_X|+|h_X-h_D|+h_B-h_D.
\]

If `H=max(h_B,h_X,h_D)`, then

\[
V=2[(h_B-h_X)_++(h_X-h_D)_+]\ge2(H-h_D).
\]

In particular V is at least the sum of
`(h_owner-h_D)_+` for the two chosen owners. Adding the two copies of
(3), with D as the fixed endpoint in each, therefore yields

\[
\boxed{x_D-x_B+h_B-h_D+T(t_D)\ge2.}                 \tag{4}
\]

Equality forces both scalar payments to vanish. Hence D and both
chosen owners are aligned. The remaining nonnegative width variation
must also vanish; with `h_D=1/2`, this implies
`h_B=h_X=h_D=1/2`. Thus **B,X,D are all aligned**. Since their vertical
gaps are below one, original physical nonoverlap then gives each
horizontal gap at least one. Equality in (4) forces both gaps to be
exactly one. This proves the complete equality characterization needed
below; their heights are not asserted equal at this stage.

## 4. Closed-Q exclusion inside the original strict 001/00 caller

Now retain all nine originals of the fixed `001/00` caller, normalized
so `y_D-y_C>=2/3`. Suppose one of the two unchanged extras X has the
replacement-row properties in Section 3. The original A,B link is
actual, so (4) implies

\[
x_D-x_A-h_A-h_D+T(t_D)\ge2.
\]

The two original actual short links give adjusted short span at least
one. Add the ordinary original A,E cap and the original D,G cap with
the stronger of the two separately accepted tolls. The weighted sum is
at most `211/2` and at least `2*46+27/2=211/2`. Thus equality holds
everywhere, including (4), and `R^2=Q`.

In particular B,X,D are aligned and their two horizontal gaps are one.
The accepted equality theorem for the physical two-square cap forces
the endpoint originals to align as well. Its right-hand equality
coordinates, with the already proved `G_y>D_y`, are

\[
D=(3/2,-1/16),\qquad G=(1,15/16).
\]

Thus `x_B=-1/2` and `x_X=1/2`; X and G are aligned and have horizontal
gap `1/2`. The replacement row gives
`y_X<=y_D+1/8<y_G`, so their actual nonoverlap forces

\[
y_X\le y_G-1=y_D.
\]

It also gives `y_X>=y_D-1/8>y_C`, since the original C,D transverse
gap is at least `2/3`. The original B,C link remains actual, hence

\[
x_C\ge x_B+h_B+h_C=h_C\ge1/2.
\]

The original C,D cone and its transverse lower bound give `x_C<=5/6`.
Put `p=x_C-1/2`, so `0<=p<=1/3`. The unchanged C,X centers satisfy

\[
0<y_X-y_C\le y_D-y_C\le x_D-x_C=1-p.
\]

Their physical inscribed disks require center distance at least one,
but the preceding original bounds imply

\[
1\le|c_C-c_X|^2\le p^2+(1-p)^2.
\]

The right side is strictly below one for `0<p<=1/3`. Consequently
`p=0`. Now `1/2=x_C>=h_C>=1/2`, so C is aligned as well. The original
C,D horizontal gap is exactly one, equal to `h_C+h_D`, contradicting
its retained **strict** weak bit. This closes the equality face too.

The equality inputs are Sections 1, 6 and 7 of
`PHYSICAL_TWO_SQUARE_CAP_SUPPORT_AND_UNRESTRICTED_FOUR_PLUS_THREE_CHAINS_2026_10_31.md`.
The inherited G-order theorem applies because the original gap is at
least `2/3`. No assertion about an unproved global classification of
equality packings is used.

## 5. Exact table use and exhaustive escape branches

For each unchanged extra X, the preceding theorem excludes the complete
closed replacement-row region. Therefore the original strict caller
must satisfy at least one of these six closed necessary alternatives:

The closed x-order faces `x_X=x_B` or `x_X=x_D` are also impossible:
the corresponding vertical gap is at most `1/8`, contradicting the
unit lower bound on the distance between two original centers.

\[
\begin{array}{ll}
x_X\le x_B,&x_X\ge x_D,\\
y_X-y_B\le-1/8,&y_X-y_B\ge1/8,\\
y_D-y_X\le-1/8,&y_D-y_X\ge1/8.
\end{array}
\]

They cover the complement of the excluded region; their shared boundary
faces are retained. A computer-assisted forest may branch exhaustively
on these alternatives or invoke the proved analytic terminal when a
cell is wholly inside the excluded row region. It must label this as a
proved analytic implication, not invent a positive Farkas reserve for
the feasible closed-weak boundary control.

The exact companion
`computer_assisted/weak_outer_numeric_replacement_row_arithmetic.py`
checks every new scalar comparison and coefficient identity. The
continuous support, concavity, equality and original-caller arguments
are given above. This terminal removes an entire original neighborhood
of the identified boundary control, but the remaining full-nine
frontier still needs a complete proof.
