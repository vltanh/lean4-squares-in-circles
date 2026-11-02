# A complete small-transverse-gap exclusion for the weak-outer masks

November 2, 2026. A new hand argument based on the accepted physical
endpoint-pair tolls. No interval search, Lean, Lake, or CI is needed for
the proof. The exploratory numerical searches in this working directory
are not proof evidence and are not premises below.

**Result.** In the complete original-nine `001/00` predicate, even with
closed containment at `Q=1105/256`, the final weak pair must satisfy

\[
                 |y_3-y_2|>\frac7{30}.                 \tag{1}
\]

The same conclusion holds for the reversed first weak pair in `100/00`.
Every original physical square and both arbitrary extras remain present.
This proves an entire transverse-gap subdomain; it does **not** close
either full mask or change the fixed ledger.

The proof actually needs only the seven designated originals. It does
not contradict the accepted subcritical eight-original control: that
control's weak-pair transverse gap is greater than `7/30`.

## 1. Original pair supports and the required accepted inputs

Let `e=(1,0)`. For a physical unit square `S`, write

\[
 h_S(v)=\frac{|v\cdot u_S|+|v\cdot v_S|}{2},\qquad
 h_S=h_S(e),\qquad
 \alpha_S\ge\beta_S\ge0,\quad \alpha_S^2+\beta_S^2=1,
\]

where `alpha,beta` are the absolute horizontal components of its two
side axes. Thus `h=(alpha+beta)/2`. Set

\[
 a=46,\quad b=27/2,\quad T=211/4,\qquad
 \tau(S)=\max\left\{4\beta_S,
 \frac{207}{16}\beta_S-\frac{943}{16}(1-\alpha_S)\right\}.
                                                               \tag{2}
\]

The accepted `UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md` and
`SHARP_SMALL_MAIN_ENDPOINT_TILT_TOLL.md` imply, for any original
physical pair `M,B` in the closed Q-disk,

\[
 a[-e\cdot c_M-h_M]+b[-e\cdot c_B-h_B]+\tau(M)\le T.
                                                               \tag{3}
\]

These are the two separate inequalities with the same load and right
side, so taking the maximum in (2) is legitimate. Their penalties are
not added. The folded-frame penalty is unchanged under replacing `e`
by `-e`.

The remaining ingredient is an elementary physical-pair transfer lemma.
It preserves both original frames, both separator owners and both
physical chiralities.

## 2. A horizontal transfer lemma for an arbitrary original pair

Let `C,D` be two physical unit squares with disjoint open interiors.
Write their center difference as `(d,v)`, where `d>0`. Suppose

\[
 V=\frac7{30},\qquad d\ge V,\qquad d+V<\sqrt2,
 \qquad |v|\le V.                                      \tag{4}
\]

No disk bound is needed in this lemma. Let `alpha=alpha_D`,
`beta=beta_D`, and `tau=tau(D)`.

**Transfer lemma.**

\[
                 d+h_C-h_D+\tau/a\ge1.                 \tag{5}
\]

If additionally `d<h_C+h_D`, then (5) is strict.

### 2.1. Every physical separator is accounted for

The separating-axis theorem supplies a unit normal `n`, owned by an
axis of either original square, such that

\[
            n\cdot(c_D-c_C)\ge h_C(n)+h_D(n).           \tag{6}
\]

Each support on a unit vector is at least `1/2`. Consequently `n_x>0`:
otherwise the left side is at most `|v|<=V<1`.

Write `c=n_x>0`, `s=|n_y|`. If `s>=c`, then, since `d>=V`,

\[
 cd+s|v|\le cd+sV\le(d+V)/\sqrt2<1,
\]

contradicting (6). The middle bound follows because
`d cos(phi)+V sin(phi)` decreases on `pi/4<=phi<=pi/2` when
`d>=V`. Thus every usable physical separator satisfies

\[
       0\le s<c,\qquad c^2+s^2=1.                      \tag{7}
\]

Reflect the vertical coordinate if needed to make its vertical
component nonnegative. This keeps both original chiralities available.
Equation (6) gives

\[
 d+h_C-h_D\ge
 \frac{h_C(n)+c h_C(e)+h_D(n)-Vs}{c}-h_D.              \tag{8}
\]

### 2.2. Minimize the C-frame without changing the original statement

For every original C-frame,

\[
          h_C(n)+c h_C(e)\ge\frac{1+c^2+cs}{2}.        \tag{9}
\]

Here is the full one-angle proof. Between the finitely many projection
sign changes, the expression on the left is a positive linear
combination of sine and cosine, and its second derivative is its
negative. A minimum therefore occurs at a sign-change endpoint, where
a C-axis is parallel to either `e` or `n`. These two candidate values
are respectively

\[
             c+s/2,\qquad (1+c^2+cs)/2.
\]

The second is no larger because their difference, second minus first,
is `(1-c)(1-c-s)/2<=0`. This proves (9), including `s=0`.
It is a lower bound on the unchanged C-frame; no replacement square is
inserted into the original packing.

### 2.3. Retain both D-chiralities and reduce to two endpoints

Put

\[
 h=(\alpha+\beta)/2,
 \quad k=(\alpha-\beta)/2,
 \quad t=s/c\in[0,1],
 \quad t_D=\beta/\alpha\in[0,1],
 \quad r(t)=\sqrt{1+t^2}.
\]

The smaller support over the two possible D-chiralities is

\[
 h_D(n)\ge
 \begin{cases}
   ch-sk,&0\le t\le t_D,\\
   ck+sh,&t_D\le t\le1.
 \end{cases}                                           \tag{10}
\]

This follows directly by evaluating the two absolute-coordinate support
expressions for the frames `(alpha,beta),(-beta,alpha)` and
`(alpha,-beta),(beta,alpha)`. For `t<=t_D` the first has value
`ch-sk`; for `t>=t_D` it has value `ck+sh`. The other has value
`ch+sk` throughout `0<=t<=1`; the first is no larger in both ranges,
since `c>=s` and `h>=k`.

Substituting (9)-(10) into (8) gives the two functions

\[
 \begin{aligned}
 F_-(t)&=r(t)/2+(1+t)/(2r(t))-t(k+V),&&0\le t\le t_D,\\
 F_+(t)&=r(t)/2+(1+t)/(2r(t))-\beta+t(h-V),
                    &&t_D\le t\le1.
 \end{aligned}                                         \tag{11}
\]

The common nonlinear term has second derivative

\[
      \left(r/2+(1+t)/(2r)\right)''
           =\frac{3t(t-1)}{2(1+t^2)^{5/2}}\le0.        \tag{12}
\]

Each function is therefore concave on its stated interval, so its
minimum occurs at an endpoint. The complete endpoint values are

\[
 F_-(0)=1,\qquad
 F_-(t_D)=F_+(t_D)=\frac{1-V\beta}{\alpha},\qquad
 F_+(1)=\sqrt2+k-V>1.                                 \tag{13}
\]

The last strict inequality uses `V=7/30` and
`2-(37/30)^2=431/900>0`. Hence

\[
             d+h_C-h_D\ge
             \min\{1,(1-V\beta)/\alpha\}.             \tag{14}
\]

No separator orientation, physical owner or chirality has been removed
without a valid lower bound.

## 3. The accepted main toll covers the entire transfer deficit

We prove

\[
                 \alpha\,\tau/a+(1-\alpha)-V\beta
                 \ge0,                                \tag{15}
\]

strictly when `beta>0`. Combined with `tau>=0`, (14) gives (5).

For `beta=0`, (15) is equality. Otherwise set the folded half-angle
parameter

\[
 z=\frac{1-\alpha}{\beta}
   =\frac{\beta}{1+\alpha}\in(0,\sqrt2-1],\quad
 \alpha=\frac{1-z^2}{1+z^2},\quad
 \beta=\frac{2z}{1+z^2}.                              \tag{16}
\]

If `0<z<=2/13`, use the sharp small-angle toll in (2). The left side of
(15), divided by `beta`, is at least

\[
 \frac{1095z^3-247z^2-135z+23}{480(1+z^2)}.             \tag{17}
\]

The numerator `p(z)` decreases on this whole interval, since

\[
 p'(z)=3285z^2-494z-135
       \le3285(2/13)^2-135=-9675/169<0.
\]

Its endpoint value is `p(2/13)=817/2197>0`. This proves strict positivity
throughout this first closed range.

If `z>=2/13`, use the four-beta toll in (2). The left side of (15),
divided by `beta`, is at least

\[
            z+\frac{2}{23}\frac{1-z^2}{1+z^2}-\frac7{30}.
                                                               \tag{18}
\]

The function before `-7/30` has derivative
`1-8z/[23(1+z^2)^2]>19/23>0`, because `z<=sqrt(2)-1<1/2`.
At `z=2/13`, (18) equals exactly `5351/1551810>0`.
This proves the entire complementary range, including their common
boundary.

For `beta>0`, (15) and `tau>=4 beta>0` make (5) strict. If `beta=0`
and `d<h_C+h_D`, a horizontal separator is impossible. Therefore the
normal used in (6) has `t>0`. In this case `t_D=0`, and the concave
function `F_+` has endpoint values `1` and `sqrt(2)+1/2-V>1`.
Its chord is strictly above one at every `0<t<=1`, so (14)'s underlying
bound is strict. This proves the strict assertion of the transfer lemma
also when D is aligned.

## 4. Apply the lemma to every original weak-outer configuration

Label the four original main units `A,B,C,D` in their designated order.
The actual first two links give

\[
       x_C-x_A\ge h_A+2h_B+h_C\ge2.
\]

The universal center-radius estimate in the closed Q-disk is
`|c_i|<91/60`. Thus

\[
       0<d=x_D-x_C<2(91/60)-2=31/30.                  \tag{19}
\]

The weak final cone link and its original contained aligned squares give

\[
       d\ge g_C+g_D\ge1/\sqrt2>7/30,
       \qquad d<h_C+h_D.
\]

Suppose `|y_D-y_C|<=7/30`. Conditions (4) hold, since
`d+V<19/15<sqrt(2)` and `2-(19/15)^2=89/225>0`.
The strict transfer lemma yields

\[
                 d+h_C-h_D+\tau(D)/a>1.               \tag{20}
\]

Let the actual short chain be `E,F,G`, and define the adjusted original
endpoint spans

\[
 D_0=x_D-x_A-h_A-h_D,
 \qquad S_0=x_G-x_E-h_E-h_G.
\]

The actual first two links, (20), and the actual short links give

\[
 D_0+\tau(D)/a\ge2h_B+h_C+d-h_D+\tau(D)/a>2,
 \qquad S_0\ge2h_F\ge1.                              \tag{21}
\]

Apply the original physical endpoint-pair cap (3) to `(A,E)` in direction
`e` and `(D,G)` in direction `-e`. These pairs use four distinct original
units, so adding their two inequalities is legitimate:

\[
           aD_0+bS_0+\tau(A)+\tau(D)\le2T=211/2.
                                                               \tag{22}
\]

But (21) and `tau(A)>=0` make the left side strictly larger than
`2a+b=211/2`, a contradiction. This proves (1) even at closed Q.
Simultaneous chain reversal proves the `100/00` version without any
new physical or orientation premise.

## 5. Exact scope of the remaining work

This is a complete hand exclusion of the specified low-transverse-gap
complement, not a numerical failure to find an instance. The remaining
weak-outer search can use the strict constraint `|v|>7/30`, while keeping
both signs, all original frames, all corners and pairs, and both extras.
The larger transverse-gap domain contains the known subcritical
eight-original control and still requires the ninth original or an
equivalent theorem derived from all nine. No whole mask is marked closed.
