# A low side square has a narrow inner proxy edge

November 2, 2026. Complete hand proof with exact rational arithmetic
replay. The scalar inequality was first located by a computer direction
check; the quartic proof below covers the full orientation interval.
No Lean or CI.

Retain an actual horizontal four-chain of physical units in the centered
closed disk of squared radius \(Q=1105/256\). Set

\[
 \rho=91/60,\quad l=29/60,\quad u=13/12,\quad
 A=503/480,\quad c=221/600,\quad \zeta=2211/4000.
\]

For every physical unit put
\(h=(a+b)/2\), \(g=1/(4h)\), with
\(a\ge b\ge0\), \(a^2+b^2=1\). Its centered aligned square of
halfwidth g is contained in the physical unit.

## 1. Statement and endpoint data

Let U be any original outsider on the right side with

\[
 l\le x_U<u,\qquad |y_U|<7/16.
\]

Then

\[
 \boxed{x_U<\zeta,\qquad x_U-g_U<23/150.}
 \tag{1}
\]

Horizontal reflection gives the corresponding bounds
\(|x_U|<\zeta\) and \(|x_U|-g_U<23/150\) on the left side.
All physical orientations and separator owners are included.

The actual-four endpoint theorem supplies, for the right endpoint E,

\[
 x_E<\rho,\quad g_E>15/32,\quad
 g_E-|y_E|>c,\quad |y_E|\le1/8.
 \tag{2}
\]

In particular \(x_E-g_E<A\). The outsider strip also gives
\(x_U<x_E\). These facts are proved in
`UNRESTRICTED_ACTUAL_FOUR_CHAIN_OUTSIDER_STRIP_HAND_PROOF.md`.

## 2. The absolute center band

Let \(D=x_E-x_U>0\) and \(V=|y_E-y_U|\). By (2),

\[
 V-g_E<7/16-c=83/1200=:e.
\]

The radius-one-half disk contained in U avoids E's aligned inset.
Its squared distance to that inset is at least one quarter, so

\[
 D-g_E>\sqrt{1/4-e^2}.
\]

Therefore

\[
 x_U<A-\sqrt{1/4-e^2}<\zeta.
 \tag{3}
\]

The final positive-root comparison is exact:

\[
 A-\zeta=2971/6000>0,
 \qquad 1/4-e^2-(2971/6000)^2=934/36000000>0.
\]

We record two later useful comparisons:

\[
 \zeta<47/80,\qquad
 \zeta^2<11/36,
 \quad 11/36-\zeta^2=3311/144000000.
 \tag{4}
\]

## 3. Retain U's orientation in its endpoint clearance

Write \(a\ge b\ge0\) for U's absolute side-axis components.
The coordinate vertical axis cannot separate U from E's inset:
\(V<9/16<g_E+h_U\). A coordinate horizontal separator requires
\(D-g_E\ge h_U\).

For a side axis owned by U, its support is exactly one half. Taking
absolute components in its center projection gives one of

\[
 a(D-g_E)+b(V-g_E)\ge1/2,
 \qquad b(D-g_E)+a(V-g_E)\ge1/2.
\]

When b is positive, the first alternative has the smaller necessary
horizontal gap, because

\[
 \frac{1/2-ea}{b}-\frac{1/2-eb}{a}
   =\frac{(a-b)(1/2-e(a+b))}{ab}\ge0.
\]

Here \(e(a+b)<(83/1200)(3/2)<1/2\). The aligned case b=0 is covered
directly by the coordinate axes. Consequently every possible separator
implies

\[
 x_U<A-m,
 \qquad m=\min\left\{h_U,\frac{1/2-eb}{a}\right\}.
 \tag{5}
\]

We prove the uniform orientation inequality

\[
                            m+g_U>2147/2400.
 \tag{6}
\]

For the first branch of the minimum, \(h_U+g_U\ge1\), which suffices.
For the second branch, put \(t=b/a\in[0,1]\) and
\(J=\sqrt{1+t^2}\). Its sum with the inset halfwidth is

\[
 \frac{(t+2)\sqrt{1+t^2}}{2(t+1)}-\frac{83}{1200}t.
\]

Both sides of the desired inequality are positive after moving the
linear term. Multiplication and one squaring reduce it exactly to

\[
\begin{aligned}
 P(t)={}&1440000(t+2)^2(1+t^2)
                -(t+1)^2(2147+166t)^2>0,\\
 P(t)={}&1412444t^4+4992084t^3+1137227t^2
                    -4172022t+1150391.
\end{aligned}
 \tag{7}
\]

The second derivative has positive coefficients:

\[
 P''(t)=16949328t^2+29952504t+2274454>2000000
 \quad(t\ge0).
\]

At the rational anchor \(t_0=3/7\),

\[
 P(t_0)=28507100/2401>10000,
 \qquad P'(t_0)=-610980/343,\quad |P'(t_0)|<2000.
\]

The tangent quadratic therefore gives, for every \(t\in[0,1]\),

\[
\begin{aligned}
 P(t)&\ge P(t_0)+P'(t_0)(t-t_0)+1000000(t-t_0)^2\\
 &\ge P(t_0)-P'(t_0)^2/4000000>10000-1=9999>0.
\end{aligned}
 \tag{8}
\]

This proves (6) on the entire orientation interval. Equations (5)--(6)
now give

\[
 x_U-g_U<A-2147/2400=23/150,
\]

which completes (1).

## 4. The zero unit of a full bottom side has a high proxy top

Assume now that the original main chain is also a center-cone chain,
and one side has two outsiders above its inner main. Denote the lower
outsider by U and the higher by H. No projection separation is assumed
between these three units.

The main cone and endpoint budget give \(y_M>-139/120\).
The same-half-plane clearance gives

\[
 y_U>y_M+97/100>-113/600.
 \tag{9}
\]

The complete side-pair cap at height \(7/16\), in
`SIDE_PAIR_SEVEN_SIXTEENTHS_AND_EQUAL_EXTREME_ROUTING_HAND_PROOF.md`
Sections 1--2, gives \(y_U<7/16\). Thus \(|y_U|<7/16\), and
Sections 1--3 apply to U.

Its horizontal gap from its near-aligned inner main is less than
\(5/48\), since \(l\le|x_U|<\zeta<47/80\) and the main center
has magnitude in \((29/60,31/60)\). The inset margin is therefore
greater than \(15/31-5/48>3/8\). The near-main physical clearance
proved in Section 2 of `FULL_SIDE_EXTREME_MAIN_THREE_FIFTHS_HAND_PROOF.md`
gives

\[
 y_U-y_M\ge g_M+h_U-1/128.
\]

Combining this with the main cone bound and \(h_U+g_U\ge1\),

\[
 \boxed{y_U+g_U>A_0:=1-139/120+15/31-1/128
                         =18911/59520>3/10.}
 \tag{10}
\]

Finally, the horizontal gap between U and H is below \(u-l=3/5\).
Their two radius-one-half disks give \(y_H-y_U>4/5\). Thus

\[
                     \boxed{y_H>367/600>3/5.}
 \tag{11}
\]

These are local full-side consequences and do not require the other
side to be full. They retain the original zero unit, its physical
orientation, its aligned inset, and its upper companion.

## 5. Verification and scope

`verify_full_side_occupancy_arithmetic.py` reconstructs the quartic
identity, its rational anchor and curvature comparisons, and the
displayed geometric reserves. The quantified proof consists of the
physical separating-axis coverage above and the complete polynomial
argument, not an angular sample or optimizer verdict.
