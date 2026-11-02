# An actual diagonal entering edge forces two weak links and a branch tilt

November 2, 2026 UTC (November 1 in America/Chicago). Complete hand
inequality. No scripts, numerical search, Lean, Lake, or CI.

This note supplies a quantitative constraint and complete adjacent-link
case exclusions for one of the retained first-birth branches. It does
not assert a global extraction of actual outer links or close those
marked-chain masks outside the stated first-birth geometry.

## 1. Statement

All squares below are physical units contained in the closed Q-disk,
where Q=1105/256, with pairwise disjoint open interiors. Write
h_S for the common x/y projection halfwidth, g_S=1/(4h_S), and
k_S=sqrt(1/2-h_S^2). Suppose the following distinct squares exist:

- E and F have an actual diagonal center comparison
  x_F-x_E=y_F-y_E=d>=h_E+h_F;
- F,C,D form a center-cone x-three-chain;
- F\prec_y T is a center-cone y-comparison.

Then **both F--C and C--D are weak**, and

\[
                         \boxed{h_C>\frac8{15}.}
\tag{1}
\]

The conclusions allow arbitrary independent orientations and arbitrary
physical separators. It applies after any common rotation or reflection
that puts the stated directed branches in these coordinates.

In the full-nine first-birth normal form, it applies when the entering
edge runs from S_11 to S_12 with Delta x=Delta y>=h_11+h_12:
take F=S_12, C=S_22, D=S_32, T=S_13. The centrally indexed square
S_22 must then have halfwidth greater than 8/15, and both links of
S_12,S_22,S_32 are weak. The selected four-chain consequently has
mask (011), independent of the status of the disjoint third row.
Reflected versions
give the corresponding outward-corner branches. Other first-birth
positions are not silently included.

## 2. Unary and inset bounds locate the entering source

The established unary proxy-support bound from
`UNRESTRICTED_FIVE_PROXY_CHAIN_HAND_PROOF.md` is

\[
                      |x_S|-g_S<\frac{17}{16},\qquad
                      |y_S|-g_S<\frac{17}{16}.
\tag{2}
\]

Every center-cone comparison has its coordinate gap at least the sum
of the inset halfwidths. From the x-three-chain and (2),

\[
 x_F\le x_D-g_F-2g_C-g_D
          <\frac{17}{16}-g_F-2g_C.
\]

The y-comparison F\prec_y T similarly gives
y_F<17/16-g_F. Subtract the actual diagonal gap and use
h_F+g_F>=1. With h=h_E, we obtain

\[
 x_E<\frac1{16}-h-2g_C,\qquad
 y_E<\frac1{16}-h.
\tag{3}
\]

Suppose for a contradiction h_C<=8/15. Then g_C>=15/32, and (3)
gives the two positive center-magnitude bounds

\[
                       X:=|x_E|>h+\frac78,
                       \qquad Y:=|y_E|>h-\frac1{16}.
\tag{4}
\]

## 3. A whole-interval corner inequality

For any physical unit square centered at coordinate magnitudes X,Y,
an actual outward-quadrant corner has offsets (h,k) or (k,h).
Its squared norm is at least the smaller of
(X+h)^2+(Y+k)^2 and (X+k)^2+(Y+h)^2. Both expressions increase
with nonnegative X,Y. At the lower bounds in (4), X>Y and h>=k,
so the second is the smaller. Thus containment would require

\[
 Q>f(h):=(h+\sqrt{1/2-h^2}+7/8)^2+(2h-1/16)^2.
\tag{5}
\]

We instead prove f(h)>Q on the complete interval
1/2<=h<=1/sqrt(2). Put k=sqrt(1/2-h^2). On its interior,
direct differentiation gives

\[
 f''(h)=8-\frac{6h}{k}-\frac{2h^3+7/8}{k^3}<0.
\tag{6}
\]

Indeed h/k>=1, so 8-6(h/k)-2(h/k)^3<=0, and the remaining
term -(7/8)/k^3 is negative. The continuous function f is therefore
concave on the closed interval and is bounded below by the smaller
of its endpoint values. Those values are exactly

\[
 f(1/2)=\frac{1125}{256},\qquad
 f(1/\sqrt2)=\frac{837+192\sqrt2}{256}.
\tag{7}
\]

Both exceed Q. In fact sqrt(2)>7/5 makes the second exceed
Q+1/320, and the first exceeds Q by 20/256>1/320. Consequently

\[
                    f(h)>Q+\frac1{320}>Q
                    \quad\left(\frac12\le h\le\frac1{\sqrt2}\right).
\tag{8}
\]

This contradicts (5) and proves (1).

## 4. Either actual link in the forward three-chain is impossible

We now prove the two-link assertion without assuming h_C<=8/15.
Write eta_S=h_S+g_S-1>=0 and delta_S=h_S-g_S>=0.

If F--C is actual, combine that gap with the completed C--D gap
and the unary bound at D:

\[
 \begin{split}
 x_F&\le x_D-h_F-h_C-g_C-g_D\\
    &<\frac{17}{16}-h_F-(h_C+g_C)
     =\frac1{16}-h_F-\eta_C.
 \end{split}
\]

Subtracting d>=h_E+h_F and using 2h_F>=1 gives

\[
                       x_E<-h_E-\frac{15}{16}.
\tag{9}
\]

If C--D is actual instead, use the completed F--C gap:

\[
 \begin{split}
 x_F&\le x_D-g_F-g_C-h_C-h_D\\
    &<\frac{17}{16}-g_F-(g_C+h_C)-(h_D-g_D)\\
    &=\frac1{16}-g_F-\eta_C-\delta_D.
 \end{split}
\]

After subtracting the same actual diagonal gap, h_F+g_F>=1
again gives (9). This covers either actual-link possibility, including
the case in which both are actual.

The retained y-cone successor F\prec_y T, just as in Section 2,
gives y_E<1/16-h_E. Thus either actual link forces

\[
             |x_E|>h_E+15/16>h_E+7/8,
             \qquad |y_E|>h_E-1/16.
\]

These are stronger than (4), and the whole-interval corner contradiction
(5)--(8) applies unchanged. Therefore neither forward link is actual.
Since both are cone comparisons by hypothesis, both are genuinely weak.

In particular, in the stated outward first-birth corner branch with
an actual entering edge, the four-chain masks (000), (001), and
(010) are excluded throughout q<=Q, regardless of the disjoint third
row's mask or any other exceptional physical pairs. Only (011) remains
for that chosen directed four-chain, and it additionally has h_C>8/15.
This is a conditional first-birth branch closure; those masks are not
declared impossible in other extracted arrangements.

## 5. Scope

The proof retains the directed x-branch and y-branch explicitly.
It does not apply if the available two-step branch points in the
opposite x-direction, or if F has no successor in the specified
y-cone. It proves both forward links weak and a genuine orientation
threshold in the outward first-birth corner case. The small-tilt
domain and every domain with an actual forward link are closed by
the displayed corner inequalities. The remaining double-weak tilted
domain and other first-birth positions are still open;
canonical root counts and A.2 status do not change.
