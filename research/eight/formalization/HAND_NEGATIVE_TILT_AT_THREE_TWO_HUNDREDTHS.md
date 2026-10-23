# Nonpositive tilt is impossible at S <= 3/200

## 1. Statement and dependencies

Assume the hypotheses of
`HAND_MIXED_OWNER_CLOSURE_AT_THREE_TWO_HUNDREDTHS.md`, including
`q <= Q = 9789/2500`, the signed cuts, the zero and quarter owners,
and `S <= 3/200`. Retain the original intended mixed witnesses G0/E1.
Let A's physical frame be zero and G's physical frame be t.

**Theorem.** Every such feasible cycle satisfies `t > S`.
This replaces the old nonpositive-tilt argument at the larger mismatch
threshold, without assuming `S <= 1/1000` or any positive tilt window.
All originally feasible aligned owners and their ties are included.

The already proved theorem
`HAND_NEAR_ZERO_MIXED_TILT_AT_THREE_TWO_HUNDREDTHS.md` excludes
`|t| <= S`. It remains to exclude `t < -S`. We prove that whole tail
below. All terminating decimals are exact rational numbers.

## 2. Actual coordinates and the forced negative arc

Write the five errors as

\[
 x_1=\theta_B,\quad x_2=\theta_T-\theta_B,\quad
 x_3=\theta_D-\theta_T,\quad x_4=\theta_E-\theta_D,
 \quad h=\theta_H-t,
\]
\[
 S=|x_1|+|x_2|+|x_3|+|x_4|+|h|,
 \qquad z=t+h-x_1-x_2-x_3-x_4.
\]

Suppose `t=-u<-S`, and put `r=sin(u)`, `c=cos(u)`.
The geometric bounds already proved from the cuts and corner disks are

\[
 L=447/800<a_i<283/200,\quad b_i<9/10,
\]
\[
 7/12\le a_G,a_T<349/250=1.396,
 \quad b_G,b_T<4/5,
 \quad a_H<29/25=1.16.
\tag{1}
\]

The full frame chart gives `0 <= r <= .7`, `c >= 3/4`, and
`1-c <= 4r^2/7`. The nominal E1 projection is
`a_H-r a_E-c b_E`, and actual E1 feasibility implies that this is at
least `(1+c+r)/2-2S`. Therefore

\[
 1+(1/2+L)r-(2/7)r^2\le1.16+2S\le1.19.
\]

The left side increases on `[0,.7]`. At `r=1/5` it exceeds `1.19`.
Consequently

\[
 0<r<1/5,\qquad c>97/100,\qquad u<.202,
 \qquad |z|<.217.
\tag{2}
\]

For the angle bound, `sin(.202) >= .202-.202^3/6 > .2` suffices.
Also `z<0`, because `t<-S`.

## 3. One four-circle stress and a legitimate E-coordinate comparison

Set

\[
 p=24/41,\quad e=36/31,\quad m=12/41,\quad n=12/31.
\]

Use edge weights `(1,1,p,1,1,e,e)` on HG,G,AB,BT,TD,DE,E,
and circle masses `(m,m,n,n)` on A,B,D,H. For every actual anchor use

\[
 Xa+Yb\le \mu Q+(X^2+Y^2)/(4\mu)-(X+Y)/2.
\tag{3}
\]

This is the exact two-square completion of its shifted corner disk.
Collect the two incident contributions at each anchor before applying
(3). G,T,E remain free coordinates.

In the weighted projection sum, the coefficient of `a_E` is
`e sin z` when E owns DE and `e(sin z+sin x_4)` when D owns DE.
Both are nonpositive. For the second assertion put
`z_0=t+h-x_1-x_2-x_3`; then `z_0<=-|x_4|` and

\[
 \sin(z_0-x_4)+\sin x_4
 =2\sin(z_0/2)\cos(z_0/2-x_4)\le0.
\]

The cosine is positive on (2). Replacing `a_E` by L can therefore
only increase the projection upper bound. Perform precisely this
one-sided comparison; keep `b_E` actual, in `[0,.9)`, and keep all G/T
coordinates actual. Let Phi be demand minus the resulting upper bound.
Every feasible configuration necessarily has `Phi<=0`.

## 4. The nominal gap and all first-order cusps

At zero errors, the four forces on A,B,D,H are
`(c,p+r),(1,p),(e,1),(e,1)`. Direct substitution in (3) gives

\[
 \Phi(0)=\Psi_0+C_b(c-1)+Jr,
 \qquad \Psi_0=3027/794375,
\]
\[
 C_b=1+e/2+e b_E\le1+7e/5,
 \qquad J=e(L+1/2)=7623/6200.
\tag{4}
\]

Since `r<1/5`,

\[
 C_b(c-1)+Jr
 \ge\left[J-(1+7e/5)\frac4{35}\right]r
 =\frac{40337}{43400}r>\frac{23}{25}r.
\tag{5}
\]

The common smooth E correction, as a coefficient of each aligned
frame increment (with the opposite direction on HG), is

\[
 D=e\{c(L+1/2)-r(b_E+1/2)\}.
\tag{6}
\]

The virtual anchor centers are derivatives of (3), not assumed actual
centers. Their primary coordinates are `41c/24-1/2,29/24,1,1` on
A,B,D,H; the required secondary coordinates are `1/2` on B and
`19/24` on D. The smooth coefficient on an aligned edge has magnitude
`|D-lambda R|`, with receivers

\[
\begin{array}{c|c|c}
\text{edge}&\lambda&\text{possible }R\\ \hline
 HG&1&a_G,\ 1\\
 AB&p&41c/24-1/2,\ 29/24\\
 BT&1&a_T,\ 1/2\\
 TD&1&a_T,\ 1\\
 DE&e&L,\ 19/24.
\end{array}
\tag{7}
\]

These are the two original allowed owners on each edge. The aligned
linear cusp is `lambda |x|/2`. Every lower endpoint
`lambda(R-1/2)` in (7) is at most `112/125=.896`; every upper endpoint
`lambda(R+1/2)` is at least c. The potentially smallest upper endpoint,
for A-owned AB, is exactly c because `p(41c/24)=c`.

Equations (1),(2),(6) give the exact bounds

\[
 \frac{537831}{620000}<D\le\frac{7623}{6200}.
\]

Thus D lies within `27/100` of every receiver interval:

\[
 |D-\lambda R|-\lambda/2<27/100.
\tag{8}
\]

For the upper comparison, the largest required enlargement is
`7623/6200-97/100=1609/6200<27/100`; the lower comparison is smaller.
The full first-order expression, including all five linear cusps, is
therefore bounded below by `-(27/100)S`. This uses one shared S,
not one copy per edge.

## 5. A uniform second-order estimate

Remove the five aligned sine cusps from Phi and hold t and the free
comparison coordinates fixed. Consider the entire straight error
segment of norm at most `S<=.015`.

The nonconstant negative anchor-force norms are sine terms with
coefficients `1,1,3/2,3/2` on A,B,D,H. The A argument can include t;
the other arguments are sums of the incident aligned errors. Their
absolute values are at most `.217,.015,.015,.015`, respectively.
The only possible overlap in a Hessian entry is A/B on `x_1`.
Hence every force-norm Hessian entry has magnitude less than `.24`.

After combining each aligned width with its linear corner shifts and
its free-coordinate projection, the largest smooth second derivative
is bounded by

\[
 1/2+b_T+a_T(.015)<1.3+1.396(.015)<1.321.
\]

This is the BT alternative with the free T coordinate. The other
alternatives have cosine coefficient at most one in magnitude and
sine coefficient at most `1/2`, or cosine coefficient at most `1/2`
and sine coefficient at most `1.396`, before their weight. For DE the
weight is e, giving at most `e(1+.015/2)<1.171`.
Each such contribution occupies only its own aligned diagonal.

The varying mixed E smooth term is, apart from a constant,

\[
 e\{(b_E+1/2)\cos z-(L+1/2)\sin z\}.
\]

Every one of its Hessian entries has magnitude less than

\[
 e\{1.4+(L+1/2)(.217)\}<1.9.
\]

G has no aligned error. Therefore every smooth Hessian entry is bounded
by `.24+1.321+1.9<4`. Taylor's integral remainder loses at most `2S^2`.
The five sine cusps lose less than `S^3/10` from their linear cusps,
because their weights are below `6/5` and
`|sin x|-|x| >= -|x|^3/6`.

These estimates hold on the full segment for every actual owner in
(7), including zero errors and every tie. No angular subdivision is
used.

## 6. Strict contradiction and conclusion

Since `sin u >= u cos u`, equations (2),(5) and `u>S` give

\[
 C_b(c-1)+Jr>\frac{23}{25}\frac{97}{100}S
 \ge\frac{27}{100}S.
\]

Combining the exact nominal gap, (8), and the remainder bounds yields

\[
 \Phi\ge\Psi_0-2S^2-S^3/10
 \ge\frac{3027}{794375}-2\left(\frac3{200}\right)^2
                    -\frac1{10}\left(\frac3{200}\right)^3
 =\boxed{\frac{341665683}{101680000000}}>0.
\]

This contradicts `Phi<=0` on the entire negative tail. The independent
near-zero theorem excludes `|t|<=S`, so necessarily `t>S`.

This closes the full nonpositive-tilt alternative at `S<=3/200`,
conditional on the earlier candidate cuts and owner conclusions. It
proves no earlier global contraction. Its premises are the displayed
circle supports, the actual original projections, whole-domain derivative
bounds, and individual rational comparisons. No numerical table, Lean
compilation, or CI run is used.
