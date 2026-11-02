# Weak outer link: complete negative-tilt exclusion through gap 5/8

November 2, 2026. Complete hand argument, with exact rational verification
of its scalar constants. Numerical discovery motivated the argument; no
floating-point outcome is a premise. No Lean, Lake, or CI.

## 1. Statement and original physical hypotheses

Retain all nine original squares in the fixed `001/00` predicate, at closed
`Q=1105/256`. Label the main four `A,B,C,D` and the actual short three
`E,F,G`. The first two main links and both short links are actual projection
separations. The C,D link satisfies the original cone comparison and the
strict weak inequality.

Reflect the vertical coordinate if necessary so that

\[
 d=x_D-x_C>0,\qquad v=y_D-y_C\ge0.
\]

Write the D side frame, modulo its own square symmetries, as

\[
 u_D=(\alpha,-\beta),\quad v_D=(\beta,\alpha),\qquad
 \alpha^2+\beta^2=1,\quad \alpha\ge\beta\ge0.
\]

Thus D has nonpositive folded tilt after the one vertical reflection.

**Theorem.** These original physical hypotheses are impossible if
`v<=5/8`. The conclusion holds even at closed Q. The two unselected
originals remain present; the contradiction needs only the seven selected
originals and does not add any condition to their frames or centers.

The same statement holds for the exact reversed `100/00` witness.

The accepted inputs are the original two-square cap theorem and its
universal four-beta main toll from `UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md`,
and the universal center-radius bound `|c_S|<91/60`. Put

\[
 a=46,\quad b=27/2,\quad T=211/4,\quad V=5/8.
\]

## 2. A narrow physical-separator theorem for the entire low-gap domain

This section does **not** assume the D-tilt sign.

Write `h_S=(alpha_S+beta_S)/2` for the true horizontal halfwidth. Since the
first two main links are actual,

\[
 x_C-x_A\ge h_A+2h_B+h_C\ge\frac32+h_C.
\]

The center-radius bound gives `x_A>-91/60`, while containment gives
`x_D+h_D<=sqrt(Q)<133/64`. Consequently

\[
 d+h_C+h_D<\frac{133}{64}+\frac{91}{60}-\frac32
                 =\frac{2011}{960}.                 \tag{1}
\]

Let n be **any usable original owned separating normal** for C,D:

\[
 n\cdot(c_D-c_C)\ge h_C(n)+h_D(n).
\]

Each support of a physical unit square on a unit normal is at least 1/2.
If `n_x<=0`, its left side is at most `v<=5/8<1`, impossible. Hence set
`c=n_x>0`, `s=|n_y|`, so `c^2+s^2=1`.

For any physical square S,

\[
 h_S(n)+c h_S(e)\ge\frac{1+c^2+cs}{2}.                \tag{2}
\]

Here is the complete free-frame argument. On each interval between
projection-sign changes, the left side has negative second derivative
equal to its negative, so its minimum is at a sign-change endpoint.
A side axis there is parallel to e or n. The two values are respectively
`c+s/2` and `(1+c^2+cs)/2`. The second is smaller by
`(1-c)(1-c-s)/2<=0`. A vertical reflection handles either sign of `n_y`.

For the square that owns n, its exact supports are
`h_owner(n)=1/2`, `h_owner(e)=(c+s)/2`. Apply (2) to the other square and
add the horizontal widths to the physical separation. This gives

\[
 \begin{split}
 c(d+h_C+h_D)
 &\ge h_C(n)+c h_C(e)+h_D(n)+c h_D(e)-Vs\\
 &\ge 1+c^2+cs-Vs.
 \end{split}
\]

Thus, with `c=cos(phi)`, `s=sin(phi)` and `0<=phi<pi/2`,

\[
 d+h_C+h_D\ge J(\phi):=
 \sec\phi+\cos\phi+\sin\phi-\frac58\tan\phi.         \tag{3}
\]

This function is strictly increasing, because

\[
 J'(\phi)=\frac{\sin^3\phi+\cos^3\phi-5/8}{\cos^2\phi}>0.
\]

Indeed `sin^3(phi)+cos^3(phi)>=1/sqrt(2)>5/8` on the first quadrant.
The first inequality follows by minimizing `c^3+s^3` subject to
`c^2+s^2=1`, or from the power-mean inequality.

At `tan(phi)=1/3`, (3) equals

\[
 \frac{22}{3\sqrt{10}}-\frac5{24}>\frac{2011}{960}.
\]

The last comparison is exact: after moving `5/24` and multiplying positive
denominators it is `7040>2211 sqrt(10)`, whose squared reserve is

\[
 7040^2-10\cdot2211^2=676390>0.
\]

Together with (1), this proves for every usable owned normal

\[
                 \boxed{\ |n_y|/n_x<1/3\ }.          \tag{4}
\]

Both original owners, every sign, and steep normals have been accounted
for. This is a derived restriction on usable physical normals, not an
assumption that coordinate separation is available.

## 3. Transfer with the universal four-beta endpoint toll

Set

\[
 h=(\alpha+\beta)/2,\qquad k=(\alpha-\beta)/2,
 \qquad t=|n_y|/n_x<1/3,
\]

and define

\[
 r(t)=\sqrt{1+t^2},\qquad
 A(t)=\frac{r(t)}2+\frac{1+t}{2r(t)}.
\]

We shall prove the strict transfer inequality

\[
       d+h_C-h_D+\frac{4\beta}{46}>1.                \tag{5}
\]

### 3.1. Upward physical normals

Suppose `n_y>=0`. Since D has the stated nonpositive tilt, and
`t<1/3<=alpha/beta` when beta is nonzero, its support is exactly

\[
                         h_D(n)=ch+sk.
\]

Use (2) for the unchanged C-frame in the physical separation. It gives

\[
 d+h_C-h_D\ge A(t)+t(k-v)
                   \ge A(t)+t(k-5/8).                \tag{6}
\]

The elementary function A is concave on `[0,1/3]`, since

\[
 A''(t)=\frac{3t(t-1)}{2(1+t^2)^{5/2}}\le0.
\]

Its endpoint values satisfy

\[
 A(0)=1,\qquad A(1/3)=\frac{11}{3\sqrt{10}}>\frac{23}{20}.
\]

The second inequality follows from `220^2-10*69^2=790>0`.
The chord bound is therefore

\[
                   A(t)\ge1+\frac9{20}t.             \tag{7}
\]

For beta positive, if `k>=7/40`, equations (6)-(7) already give transfer
at least one, and the positive four-beta toll makes (5) strict.

If `k<7/40`, then `t<1/3` and (6)-(7) instead give

\[
 \begin{split}
 d+h_C-h_D+\frac{2\beta}{23}
 &\ge1+t(k-7/40)+\frac{2\beta}{23}\\
 &\ge1+\frac{k+(6/23)\beta-7/40}{3}>1.               \tag{8}
 \end{split}
\]

The final strict inequality holds over the **entire** folded D-angle
range. In fact

\[
 k+\frac6{23}\beta
 =\frac\alpha2-\frac{11}{46}\beta
 \ge\frac6{23\sqrt2}>\frac7{40}.
\]

Here `alpha>=1/sqrt(2)` and `beta<=1/sqrt(2)`; the last comparison is
`240>161 sqrt(2)`, with squared reserve `5758>0`.

If beta is zero, (6)-(7) give `d+h_C-h_D>=1+(13/40)t`.
For `t=0` the physical separator would be horizontal and imply
`d>=h_C+h_D`, contrary to the exact weak bit. Hence `t>0`, proving (5)
also for an aligned D.

### 3.2. Downward physical normals

Suppose `n_y<0`. Reflect the vertical coordinate in this local support
calculation. D then has positive chirality and the transverse displacement
is `-v<=0`, so replacing it by zero only weakens the physical inequality.

For completeness, put `t_D=beta/alpha`. Direct evaluation of the original
D support and (2) gives the following lower bounds on the adjusted gap:

\[
 \begin{cases}
 A(t)-tk,&0\le t\le t_D,\\
 A(t)-\beta+th,&t_D\le t\le1.
 \end{cases}                                        \tag{9}
\]

Both functions are concave on their intervals. The complete endpoint
values at `0,t_D,1` are respectively

\[
                  1,\qquad 1/\alpha,\qquad\sqrt2+k.
\]

They are all at least one. Thus (9) gives `d+h_C-h_D>=1`, and a positive
beta makes (5) strict by its positive toll. If beta is zero, the same
calculation gives `A(t)+t/2>1` for `t>0`; a downward normal has `t>0`.
This completes every physical normal and every beta boundary case.

## 4. Add the two original physical endpoint caps

Define the adjusted endpoint spans

\[
 D_0=x_D-x_A-h_A-h_D,\qquad
 S_0=x_G-x_E-h_E-h_G.
\]

The first two actual main links and (5) imply

\[
 D_0+\frac{4\beta_D}{a}
 \ge2h_B+h_C+d-h_D+\frac{4\beta_D}{a}>2.
\]

The actual short links give `S_0>=2h_F>=1`.

Apply the original physical endpoint cap to A,E in direction e, and its
accepted universal four-beta version to D,G in direction `-e`. The folded
beta is unchanged by this direction reversal, so adding the two valid
inequalities gives

\[
                    aD_0+bS_0+4\beta_D\le2T.
\]

The lower bounds above make its left side strictly greater than
`2a+b=211/2=2T`, a contradiction. All four endpoint witnesses are distinct
original squares. No G,D height order, replacement witness, new cone
comparison, or restriction on the two unselected originals was used.

## 5. Scope and exact checks

This proves the whole `v<=5/8`, nonpositive-D-tilt portion of `001/00`
at closed Q. It is not a complete weak-outer-mask closure. The low-gap
positive-D-tilt complement and the `v>5/8` domain require their own
complete arguments before either whole mask can be marked closed.

The companion rational checker verifies the horizontal reserve, both
radical comparisons, the chord comparison, and the positive folded-angle
reserve. The proof of all continuous domains is given above; no grid
evaluation or numerical optimizer failure is used to infer positivity.
