# A shallow D-root side excludes a boundary neighbor on the whole original window

**Status: new complete force-free hand proof, submitted for independent
review.** This strengthens the local geometric domain of
`D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md` to the full interval

\[
                    \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16}.
\tag{1}
\]

No radius-two theorem or mass certificate is used. The accepted earlier
source is unchanged. No original fine or coarse gate is declared closed.

## 1. Exact physical statement and full-window margins

Keep the actual three interior-disjoint contained unit squares `H,L,T`
and their unchanged circle origin. Set

\[
 r=R-\sqrt2,\quad s=1-r,\quad \sigma=1/\sqrt2,
 \qquad H=[-s,r]\times[-b,a],
\]

where `a,b>0`, `a+b=1`, and `0<a<=1/4`. The real D leaf `L` is the
diamond with vertices

\[
 (r,0),\quad(r+\sigma,\sigma),\quad(R,0),\quad
 (r+\sigma,-\sigma).
\]

Suppose `T` physically touches `H` and the containing circle. Let `p`
be any actual common support point and `n` its original separating
unit normal directed from `H` into `T`. Arbitrary side means, side
endpoints, owners and strict vertex normals are all permitted.

**Theorem.** The original normal satisfies `n_y<=0`.

This theorem uses no force equation at any square. In particular `T`
may have arbitrary true degree and zero total circle multiplier. All
other physical units in a nine-square caller remain unchanged.

The following strict margins hold throughout (1):

\[
 \frac{11}{20}<r<\frac23,\qquad
 \frac13<s<\frac9{20}<r,\qquad
 r^2-s^2=2r-1>\frac1{10}>\frac1{16}.
\tag{2}
\]

For the lower bound use `sqrt(2)<57/40`, with squared reserve
`(57/40)^2-2=49/1600`. For the upper bound use
`R<133/64` and `sqrt(2)>140/99`, whose positive squared reserves
are `9/4096` and `2/9801`. The final difference is
`2/3-(133/64-140/99)=17/6336>0`.

Every point of the physical boundary unit `T` has norm at least `r`:
compare it with any actual circle corner of `T` and use the unit
diameter `sqrt(2)`. If `n_y>0`, its root support is on the upper
side or at an upper vertex. The northwest vertex is impossible,
because `s^2+a^2<r^2` by (2). Every surviving upward contact thus has

\[
 P=(q,a),\quad 0<q\le r,\quad
 q^2\ge r^2-a^2>s^2,
\]

\[
 q>\sqrt6/5>2/5,\qquad r+q>r+s=1,\qquad |P|<3/4.
\tag{3}
\]

The quantitative bound on `q` follows from
`(11/20)^2-(1/4)^2=6/25`. The last norm bound follows from
`4/9+1/16=73/144<9/16`. A strict northeast normal has precisely
`q=r`; a North normal retains the whole actual interval in (3).

## 2. Every upward minimum-support vertex is impossible

First let the actual unit have the full upward-vertex form

\[
 T=P+[0,1]u+[0,1]w,
 \quad u=(c,d),\quad w=(-d,c),
 \quad c,d\ge0,\quad c^2+d^2=1.
\tag{4}
\]

This includes both axis limits. The two adjacent vertices have norms
less than `|P|+1<7/4<R`, as does `P`. The only possible circle corner
is therefore

\[
 Z=(q+\Delta,a+\Sigma),\quad
 \Delta=c-d\in[-1,1],\quad\Sigma=c+d=\sqrt{2-\Delta^2}.
\tag{5}
\]

Put `g=r-q>=0`. Since `|P|>=r`, (3) gives

\[
                  g\le\frac{a^2}{r+q}<\frac1{16}.
\tag{6}
\]

If `Delta>=1/2`, the actual side `P+t u` meets the inner upper
leaf edge `y=x-r` at

\[
 t_0=(a+g)/\Delta<5/8<1,
 \qquad y_0=(ca+dg)/\Delta\in(0,5/8)\subset(0,\sigma).
\]

It enters the open leaf immediately after that intersection, a
contradiction. A point of a closed full-dimensional square inside
another square's open interior forces overlap of the open interiors.
Hence `Delta<1/2`.

For fixed actual `q,a`, the squared norm in (5) has derivative

\[
                   2\left(q-\frac{a\Delta}{\sqrt{2-\Delta^2}}\right)>0
\]

on the entire interval `[-1,1/2]`. For nonpositive `Delta` this is
immediate; for positive `Delta` use `q>2/5`, `a<=1/4` and
`Delta/sqrt(2-Delta^2)<=1/2`. Consequently

\[
 |Z|^2
 <(2/3+1/2)^2+(1/4+\sqrt7/2)^2
 =\frac{49}{36}+\frac{29}{16}+\frac{\sqrt7}{4}
 <\frac{553}{144}<\left(\frac{79}{40}\right)^2\le R^2.
\tag{7}
\]

Here `sqrt(7)<8/3`, and the last strict reserve is
`(79/40)^2-553/144=869/14400`. Thus no corner of (4) can be a
physical circle corner. This contradiction excludes the whole
upward-vertex form, without any concurrence or circle-weight premise.

## 3. The full North-support domain is exhausted

If `n` is North and `T` has a bottom support vertex, Section 2 applies.
Otherwise its bottom support is a side and the complete unit is

\[
                    T=[x,x+1]\times[a,a+1].
\]

The unchanged actual contact `(q,a)` lies on that side, so
`x>=q-1>-1` and `x<=q<=r`. Physical disjointness from the real leaf
forces `x+1<=r+a`: if not, choose `y=a+epsilon<sigma` with
`x+1>r+y`. At this height the open horizontal interval of `T`
intersects the open leaf interval `(r+y,R-y)`.

It follows that every corner `(X,Y)` of `T` satisfies

\[
 -1<X<11/12,\quad 0<Y\le5/4,\quad
 X^2+Y^2<41/16<(79/40)^2\le R^2.
\]

The squared reserve is `2141/1600`. This contradiction includes
positive-length shared sides and every aligned singleton endpoint;
no North application mean was fixed in advance.

## 4. A northeast normal owned by a neighbor side is impossible

Let the original normal be `n=(c,d)`, with `c,d>0` and
`c^2+d^2=1`. Its actual root point is `P=(r,a)`. If the minimum
support of `T` is a side, retain its complete side parameter:

\[
 k=(-d,c),\qquad
 T=P+[0,1]n+[-\rho,1-\rho]k,\qquad 0\le\rho\le1.
\tag{8}
\]

The actual segment `P-t k` crosses the inner upper leaf edge at
`t_0=a/(c+d)`, at a height strictly between zero and `sigma`.
Disjointness from `L` therefore gives

\[
                     \rho\le\frac a{c+d}<\frac14.
\tag{9}
\]

The decisive stronger physical bound is

\[
                              d>\frac14.
\tag{10}
\]

Indeed, if `d<=1/4`, then `c>3/4`, `d/c<1/3`, and
`c-d>1/2`. The actual segment `P+t n`, `0<=t<=1`, meets that same
leaf edge at

\[
 t_1=\frac a{c-d}<\frac12<1,
 \qquad y_1=t_1c=\frac{ac}{c-d}<\frac32a\le\frac38<\sigma.
\]

It then enters the open leaf. This contradicts interior disjointness,
even if this segment is a boundary side of `T`. It proves (10) with
the weak endpoint `d=1/4` fully included in the excluded domain.

Since `P.n>0`, a corner on the far `n`-face has strictly greater
squared norm than its near-face counterpart with the same `k`
coordinate. It is enough to bound the two actual far-face corners.
The negative-`k` one satisfies

\[
 |P+n-\rho k|\le |P|+\sqrt{1+\rho^2}
 <3/4+\sqrt{17}/4<15/8<79/40\le R.
\tag{11}
\]

The positive-`k` far corner lies on the segment from `P+n` to
`P+n+k`. The first endpoint has norm less than `7/4<R`. For the
second, use the exact identity `R=r+sqrt(2)`:

\[
 \begin{aligned}
 |P+n+k|^2-R^2
 &=a^2+2(r+a)c+2(a-r)d-2\sqrt2\,r\\
 &<a^2+\frac52a+\left(\frac32-2\sqrt2\right)r\\
 &<\frac{11}{16}-\frac{13}{10}\frac{11}{20}
 =-\frac{11}{400}<0.
 \end{aligned}
\tag{12}
\]

The first strict inequality uses `c<1`, (10), and `a-r<0`.
The second uses `a<=1/4`, `r>11/20`, and `sqrt(2)>7/5`.
Convexity of squared norm on the segment bounds its actual corner
strictly below `R` as well. Thus all four actual corners of (8)
lie strictly inside the circle, a contradiction. Both side endpoints
and all original side-interior means have been retained.

## 5. Every northeast vertex/vertex interval is included

It remains that `P=(r,a)` is a vertex of `T` and the original
northeast normal is in its minimum-support normal cone. The inward
tangent sector of `H` at `P` is the southwest quadrant. The actual
right-angle sector of `T` has interior disjoint from it.

Choose the two orthogonal inward axes of `T` in counterclockwise
order, with angles `theta,theta+pi/2` lifted so
`-pi/2<=theta<=pi/2`. The original strict northeast normal lies in
their cone, so the two endpoints of this theta interval are excluded.
If `theta<=0`, the first axis is `(c,-d)` with `c>0,d>=0`.
Its actual side from `P` meets the inner upper leaf edge at

\[
 t_0=\frac a{c+d}\le\frac14<1,
 \qquad x-r=y=t_0c\in(0,\sigma),
\]

and then enters the open leaf. Therefore `theta>0`. The unit now
has precisely the upward-vertex form (4), with `q=r`, already
excluded in Section 2.

This covers the complete free vertex/vertex normal interval and all
axis-ray limits permitted by the actual support feature. No generic
normal avoidance or post-extraction reselection has been used. The
northwest, North and northeast alternatives exhaust `n_y>0`, proving
the theorem throughout (1). Reflection gives the corresponding shallow
bottom-side theorem with the entire configuration reflected together.

## 6. Direct inputs and comparison with the accepted prior source

The new physical theorem is proved in full above using only elementary
unit-square geometry, the actual containing circle, and the displayed
physical chart. It has no external radius lower-bound premise.

For an original genuine D-leaf caller, that chart is supplied by
`RADIAL_BRIDGE_AND_LEAF_REDUCTION.md`, Theorem 6.1 and Corollary 6.2,
SHA256 `faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676`.
The common original compatible certificate is retained; the theorem
does not select a new free normal after any forces are extracted.

The accepted earlier local source is
`D_LEAF_SHALLOW_SIDE_BOUNDARY_EXCLUSION.md`, SHA256
`79ddc3bc94613ba34b30ea3b1e4176a14d644b08887020cbc38f9ef9d785d8a8`.
The present proof preserves its complete feature cover while proving
the stronger physical inequality (10) and the full-window strict
reserves (2), (7), and (12). The earlier source's radius-two-dependent
comparison is not imported as a premise.

All actual physical masks, arbitrary degrees, zero individual circle
weights, original normals and contact means remain. No force equation,
concurrence, sampled pose, scalar certificate, changed normal, Lean
compilation, CI run, ledger mutation or remote write is used.
