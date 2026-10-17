# The exact two-square capacity of a disk cap

This note proves a sharp, orientation-independent cap bound in the parameter
range needed for the eight-square argument. It strengthens the earlier
outward-cap count in `HUMAN_CAPACITY_BOUND.md`.

**Theorem.** Let `2/3 <= h <= 1`. If two unit squares with disjoint interiors
are contained in

\[
 D_R\cap\{x\ge h\},
\]

then

\[
 R^2\ge(h+1)^2+1.
\tag{1}
\]

Equality is possible only for the two axis-parallel squares

\[
 [h,h+1]\times[0,1],\qquad [h,h+1]\times[-1,0].
\tag{2}
\]

These squares attain equality. The proof uses a common point of all unit
squares in a suitable isosceles triangle; no choice of a pairwise separating
axis is required.

## 1. A common-point theorem for an isosceles triangle

For

\[
 \frac12\le t\le\frac35,
\]

define

\[
 T_t=\{(x,y):x\ge0,\quad x+t|y|\le1+t\},
 \qquad w=(1/2,0).
\tag{3}
\]

**Triangle lemma.** Every unit square contained in `T_t` contains `w`.
Every square whose sides are not parallel to the coordinate axes contains
`w` in its open interior. Among the axis-parallel squares, the only ones
having `w` on their boundary are

\[
 [0,1]\times[0,1],\qquad [0,1]\times[-1,0].
\tag{4}
\]

We prove this lemma in sections 2--5. Reflection in the horizontal axis and
the freedom to relabel the side frame let us write an arbitrary square with
side directions

\[
 e=(c,s),\qquad f=(-s,c),\qquad
 c=\cos\theta,\quad s=\sin\theta,\quad
 0\le\theta\le\frac\pi4.
\tag{5}
\]

Put `L=c+s` and `D=c-s`. The triangle is symmetric under that reflection,
so this orientation normalization loses no case.

## 2. The triangle of possible centres

The square's horizontal half-width is `L/2`. Its half-widths in the
directions `(1,t)` and `(1,-t)` are respectively

\[
 H_+=\frac12(c+ts+|tc-s|),\qquad
 H_-=\frac12((1+t)c+(1-t)s).
\tag{6}
\]

Set

\[
 H=\frac{H_++H_-}{2},\qquad
 d=\frac{H_--H_+}{2t},\qquad
 B=1+t-\frac L2-H.
\tag{7}
\]

If a square of this orientation fits, then `B>=0`, and its centre `p` lies
in the triangle with vertices

\[
 A=(1+t-H,d),\qquad
 U=(L/2,d+B/t),\qquad
 V=(L/2,d-B/t).
\tag{8}
\]

Indeed, its three containment inequalities are exactly

\[
 p_x\ge L/2,\quad
 p_x+tp_y\le1+t-H_+,\quad
 p_x-tp_y\le1+t-H_-.
\]

The two formulas needed below are

\[
\begin{array}{c|c|c|c}
 &H&d&B\\ \hline
 s\le tc & (1+t)c/2 &(1-t)s/(2t)
             &1+t-(1+t/2)c-s/2\\[1mm]
 s\ge tc &L/2&D/2&1+t-L.
\end{array}
\tag{9}
\]

A square with centre `p` contains `w` precisely when

\[
 |e\cdot(p-w)|\le\frac12,\qquad
 |f\cdot(p-w)|\le\frac12.
\tag{10}
\]

It therefore suffices to bound these four affine functions on the centre
triangle (8).

### 2.1 The apex is strictly inside the relevant half-widths

For `s<=tc`, the two coordinates of `A-w` are

\[
 \frac12+t-\frac{1+t}{2}c,\qquad
 \frac{1-t}{2t}s.
\]

The first is positive and increases with `theta`. At `theta=arctan t` it
equals

\[
 F(t)=\frac12+t-\frac{1+t}{2\sqrt{1+t^2}}.
\]

Since

\[
 F'(t)=1-\frac{1-t}{2(1+t^2)^{3/2}}>0,
\]

it is at most

\[
 F(3/5)=\frac{11}{10}-\frac4{\sqrt{34}}<\frac{21}{50}.
\]

The last strict comparison follows from `5000>4913` after squaring the
positive quantities in `4/sqrt(34)>17/25`. The second coordinate is at
most `(1-t)c/2<=1/4`. Consequently

\[
 |A-w|^2<\left(\frac{21}{50}\right)^2+\frac1{16}
   =\frac{2389}{10000}<\frac14.
\tag{11}
\]

For `s>=tc`, formula (9) gives instead

\[
 |A-w|^2=(1/2+t)^2+\frac12-(1/2+t)L.
\]

At fixed `t` this decreases with `theta` on `[arctan t,pi/4]`, because
`L` increases. Thus (11) also holds in this branch. In particular, both
absolute scalar products in (10) are strictly less than `1/2` at `A`.

### 2.2 The negative `e` direction is always strict

Formula (6), without a branch split, gives

\[
 V_y=-\frac12-(1/t+1/2)(1-c)+(1/t-1/2)s.
\tag{12}
\]

For `theta>0`,

\[
 \frac{1-c}{s}=\tan(\theta/2)
 \le\sqrt2-1<\frac12<\frac7{13}
 \le\frac{2-t}{2+t}.
\]

Hence `V_y>-1/2`; at `theta=0` there is equality. Every possible centre
therefore has `p_y>=-1/2` and `p_x>=L/2>=1/2`. It follows that

\[
 e\cdot(p-w)\ge-\frac s2>-\frac12.
\tag{13}
\]

## 3. Orientations with `s<=tc`

The maximum of `e dot (p-w)` on the centre triangle is attained at `A`,
because `c>=s/t`; (11) handles it. The maximum of `f dot (p-w)` is at `U`,
and the maximum of `-f dot (p-w)` is at `V`, since `c/t>s`.

Write `k=1+1/t`. Direct substitution from (9) gives

\[
 f\cdot(U-w)=kc-\frac{c^2}{t}-cs+\frac s2-\frac12,
\tag{14}
\]

and

\[
 -f\cdot(V-w)=\frac12-\frac s2
       +kc(1-c)+(1-1/t)cs.
\tag{15}
\]

For `theta>0`, inequality (14) being strictly less than `1/2` is equivalent
to

\[
 (1-c)(c-t)<ts(c-1/2).
\]

Using `1-c=s^2/(1+c)` and `s<=tc`, it is enough that

\[
 c(c-t)<(1+c)(c-1/2),
\]

or `c(t+1/2)>1/2`. This holds because `c>=1/sqrt(2)` and `t>=1/2`.

Likewise, (15) is strictly less than `1/2` exactly when

\[
 \frac{kc s}{1+c}<\frac12+(1/t-1)c.
\tag{16}
\]

The left-hand side is at most

\[
 \frac{(1+t)c^2}{1+c}\le\frac{1+t}{2}\le\frac45,
\]

whereas the right-hand side is greater than

\[
 \frac12+\frac23\frac12=\frac56.
\]

Thus all four inequalities in (10) are strict for `theta>0` in this
orientation branch.

## 4. Orientations with `s>=tc`

The only remaining extrema are the positive `e` value at `U` and the two
`f` extrema. Put

\[
 g=\cos(2\theta)+\sin(2\theta)-c,\qquad
 j=\cos(2\theta)-\sin(2\theta)+s.
\]

Formula (9) gives

\[
 e\cdot(U-w)=\frac g2+\frac{s}{t}(1+t-L),
\tag{17}
\]

\[
 f\cdot(U-w)=\frac j2+\frac{c}{t}(1+t-L),\qquad
 -f\cdot(V-w)=-\frac j2+\frac{c}{t}(1+t-L).
\tag{18}
\]

For fixed `theta>0`, each expression increases with `t`, since

\[
 \frac{1+t-L}{t}=1+\frac{1-L}{t}
\]

and `L>1`. If `theta<=arctan(3/5)`, increase `t` to `tan theta`. This
remains in `[1/2,3/5]` in the present branch, and the already proved
boundary case `s=tc` gives strict bounds for (17)--(18).

It remains to set `t=3/5` and consider

\[
 \theta_0=\arctan(3/5)\le\theta\le\pi/4.
\tag{19}
\]

At `theta_0`,

\[
 c=\frac5{\sqrt{34}},\quad s=\frac3{\sqrt{34}},\quad
 \cos(2\theta_0)=\frac8{17},\quad
 \sin(2\theta_0)=\frac{15}{17}.
\tag{20}
\]

### 4.1 The positive `e` bound

On (19),

\[
 g''=-4\cos(2\theta)-4\sin(2\theta)+c<0,
\]

and

\[
 g'(\theta_0)=-\frac{14}{17}+\frac3{\sqrt{34}}<0.
\]

Hence `g` decreases and

\[
 g\le\frac{23}{17}-\frac5{\sqrt{34}}<\frac12.
\tag{21}
\]

The last comparison follows from `850>841` after squaring
`5/sqrt(34)>29/34`.

For `1/2<=s<=1/sqrt(2)`, concavity of `sqrt(1-s^2)` gives

\[
 c>\frac54-\frac45s.
\tag{22}
\]

To check (22), it is enough to check its two endpoints. These reduce to
`sqrt(3)/2>17/20` and `9/(5 sqrt(2))>5/4`, respectively. Both are strict.
Thus

\[
 s(8/5-L)<\frac7{20}s-\frac15s^2
 \le\frac7{20\sqrt2}-\frac1{10}<\frac3{20}.
\tag{23}
\]

The middle quadratic increases over the stated interval; the last
comparison is `49<50`. Combining (21)--(23) in (17) gives

\[
 e\cdot(U-w)<\frac14+\frac53\frac3{20}=\frac12.
\]

### 4.2 The two `f` bounds

On (19),

\[
 j'=-2\sin(2\theta)-2\cos(2\theta)+c
 \le-\frac{30}{17}+1<0.
\]

Its endpoint values satisfy

\[
 -\frac3{10}<-1+\frac1{\sqrt2}
   =j(\pi/4)\le j(\theta)
   \le-\frac7{17}+\frac3{\sqrt{34}}<\frac3{10}.
\tag{24}
\]

Also, (19)--(20) imply

\[
 L\ge\frac8{\sqrt{34}}>\frac{137}{100},\qquad
 c\le\frac5{\sqrt{34}}<\frac{43}{50}.
\]

It follows that

\[
 \frac ct(1+t-L)
 <\frac53\frac{43}{50}\frac{23}{100}
 =\frac{989}{3000}.
\tag{25}
\]

Equations (24)--(25) bound both quantities in (18) strictly above by

\[
 \frac3{20}+\frac{989}{3000}
 =\frac{1439}{3000}<\frac12.
\]

This completes every non-axis orientation case.

## 5. The boundary cases of the triangle lemma

When `theta=0`, the centre triangle has vertices

\[
 A=(1/2+t/2,0),\qquad U=(1/2,1/2),\qquad V=(1/2,-1/2).
\]

Every centre in this triangle satisfies

\[
 0\le p_x-1/2\le t/2<1/2,\qquad |p_y|\le1/2.
\]

Thus the square contains `w`, and equality in a half-width condition occurs
only at `U` or `V`. Those are exactly the squares in (4). Together with
sections 2--4, this proves the triangle lemma with its complete equality
description.

## 6. From the triangle to the sharp cap bound

Fix `h` in `[2/3,1]`, and put

\[
 t=\frac1{h+1},\qquad
 R_0=\sqrt{(h+1)^2+1}.
\]

Then `1/2<=t<=3/5`. The disk of radius `R<=R_0` satisfies

\[
 x\mathbin\pm ty\le R\sqrt{1+t^2}
 \le R_0\sqrt{1+t^2}=h+1+t.
\]

After translating `x` by `-h`, any square in the cap lies in `T_t`.
Consequently every such square contains the same point

\[
 w_h=(h+1/2,0).
\]

If two squares have disjoint interiors and both contain `w_h`, neither can
contain it in its open interior: every neighbourhood of any point of a
square meets that square's open interior. The triangle lemma therefore
forces both squares to be the two boundary cases (2). Each of these has a
vertex of norm `R_0`, so `R>=R_0`. Equality is attained by that pair and
has no other configuration.

## 7. Application to a central square and the remaining global issue

Let a central unit square have centre `p` and side normal `n`. Any square
which admits separation on that central side lies in

\[
 \{x:n\cdot x\ge n\cdot p+1/2\}.
\]

Thus, whenever `h=n dot p+1/2` lies in `[2/3,1]`, this side can contain
two such squares only if

\[
 R^2\ge(n\cdot p+3/2)^2+1.
\tag{26}
\]

This statement counts squares admitting the central-owned separator. It
does not assign a square to a side by an arbitrary choice of SAT branch,
and it does not eliminate the corner exceptions in
`HUMAN_STRUCTURAL_LEMMAS.md`.

The numerical constants in the following observation are exact. Suppose
some further geometric reduction forces three axis-parallel unit squares
sharing centre abscissa `s`, whose union has vertical span at least `3`.
Suppose it also forces two squares in the opposite central cap whose
threshold is `h=3/2-s`, with `2/3<=h<=1` (equivalently,
`1/2<=s<=5/6`). One of the column's vertices has vertical coordinate of
absolute value at least `3/2`, and its rightmost vertices have horizontal
coordinate `s+1/2>0`. Thus the column bound and (1) imply

\[
 R^2\ge(s+1/2)^2+\frac94,\qquad
 R^2\ge(5/2-s)^2+1.
\]

Minimizing their maximum gives

\[
 s=\frac{19}{24},\qquad R^2\ge\frac{2257}{576}.
\tag{27}
\]

Equation (27) is a conditional occupancy consequence, not a proved
classification of an arbitrary eight-square packing. Establishing the
column geometry and covering the corner exceptions are separate remaining
tasks.
