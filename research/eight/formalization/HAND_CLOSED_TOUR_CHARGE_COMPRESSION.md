# Exact width charges on a closed frame tour

## Status and use

This note proves an inequality for the actual closed real frame tour. It
uses no geometric lookup, state subdivision, or numerical minimization.
The theorem strengthens the usual replacement
`h(|d|) >= .29 |d|`: a return edge also pays width, even when it lies
outside the five edges whose mismatch is being bounded.

It is an auxiliary theorem, not a claim that the coarse geometric pair
inequality or G4 has been proved. In particular, the rational charges in
Section 4 are a proved consequence of a bad mismatch, not a substitute
for a geometric lower bound on the actual seven-cycle.

Put

\[
h(x)=\frac{\sin x+\cos x-1}{2},\qquad 0\le x\le D\le\pi/4.
\tag{1}
\]

Thus `h(0)=0`, `h` is nonnegative and increasing, and

\[
h''(x)=-\frac{\sin x+\cos x}{2}<0.
\tag{2}
\]

Let the real increments `d_i` satisfy

\[
\sum_i d_i=0,\qquad |d_i|\le D.
\tag{3}
\]

For a specified nonempty set of charged edges `I`, write

\[
J=I^c,\qquad S=\sum_{i\in I}|d_i|,
\qquad U_I=\sum_{i\in I}h(|d_i|),\quad
U_J=\sum_{j\in J}h(|d_j|).
\tag{4}
\]

The candidate application has
`I={0,2,3,4,5}`, `J={1,6}`, and `D=7/10`. All increments and the
closure in (3) belong to one shared real frame assignment.

## 1. Compression on a segment

Concavity and `h(0)=0` imply

\[
h(x)+h(y)\ge h(x+y)\qquad(x,y\ge0, x+y\le D).
\tag{5}
\]

Indeed, apply the chord from zero to `x+y` separately at `x` and `y`
and add. The same argument applies to any finite sum whose total is at
most `D`.

We will also use the signed version

\[
\sum_r h(|v_r|)\ge h\left(\left|\sum_r v_r\right|\right)
\tag{6}
\]

when `|v_r|<=D` and `|sum v_r|<=D`. To prove it, take the terms whose
sign agrees with the sum. Their absolute values have total at least
`|sum v_r|`. Reduce some of these values until their total is exactly
`|sum v_r|`, discard all other terms, and use monotonicity followed by
(5). This proof does not require the original unsigned total to be at
most `D`.

## 2. Two weights and the compulsory return

**Theorem 1.** Suppose `0<s<=D`, `S>=s`, and `alpha,beta>=0`. Then

\[
\boxed{
\beta U_I+\alpha U_J\ \ge\
\min\left\{2\beta h(s/2),(\beta+\alpha)h(s)\right\}.
}
\tag{7}
\]

First multiply every increment by `s/S`. This preserves its sign and
the exact closure, makes the charged unsigned sum equal to `s`, and
can only decrease the left side of (7). It is therefore enough to
prove the assertion when `S=s`.

Let `P` and `N` be the positive and negative charged totals. Then
`P+N=s`, and put `x=|P-N|`, so `0<=x<=s`. Formula (5) on each of the
two charged sign groups gives

\[
U_I\ge h(P)+h(N)
=h((s+x)/2)+h((s-x)/2).
\tag{8}
\]

The sum of the unpaid increments is `N-P`; hence (6) gives

\[
U_J\ge h(x).
\tag{9}
\]

The resulting lower bound

\[
f(x)=\beta\bigl(h((s+x)/2)+h((s-x)/2)\bigr)+\alpha h(x)
\tag{10}
\]

is concave on the whole interval `[0,s]`. It therefore lies above
the chord between its endpoints, and in particular above the smaller
endpoint value. Those two values are

\[
f(0)=2\beta h(s/2),\qquad f(s)=(\beta+\alpha)h(s).
\tag{11}
\]

This proves (7). Notice that it retains the compulsory return in (9).

For `alpha=0`, the theorem includes the useful simpler bound

\[
S\ge s\quad\Longrightarrow\quad U_I\ge h(s),
\tag{12}
\]

because `2h(s/2)>=h(s)`. No assertion `|d_i|<=s` about the original
configuration is used here.

## 3. Arbitrary nonnegative edge weights

The same argument has an exact weighted form. Let `w_i>=0`, and let
`m_ij` be the number of charged edges in the distinct pair `{i,j}`.

**Theorem 2.** Under (1)--(4), if `S>=s>0` and `s<=D`, then

\[
\boxed{
\sum_i w_i h(|d_i|)
\ \ge\
\min_{i\ne j,\ m_{ij}>0}
(w_i+w_j)h(s/m_{ij}).
}
\tag{13}
\]

As before, first scale until the charged total is `s`. If the unpaid
increments have both signs, cancel equal amounts from one positive
and one negative unpaid increment until all nonzero unpaid increments
have the same sign. This preserves closure and the charged total,
and decreases each modified absolute value. It can only decrease the
left side of (13). Denote the remaining increments by `e_i`.

Match the positive masses `e_i>0` to the negative masses `-e_j>0`.
There exist nonnegative numbers `mu_ij` with those row and column
sums: repeatedly match the smaller of a remaining positive and a
remaining negative mass. At least one mass is exhausted at each step.
Because all unpaid increments now have the same sign, every used
pair has `m_ij=1` or `m_ij=2`.

For a used pair, let `v^(ij)` have the two increments

\[
v_i^{(ij)}=s/m_{ij},\qquad
v_j^{(ij)}=-s/m_{ij},
\tag{14}
\]

and zero elsewhere. Set `lambda_ij=m_ij mu_ij/s`. Then

\[
\sum_{ij}\lambda_{ij}=1,
\qquad
e=\sum_{ij}\lambda_{ij}v^{(ij)}.
\tag{15}
\]

The first identity counts the charged mass exactly once. The second
follows from the row and column sums. Every nonzero contribution at
a given coordinate has the same sign as that coordinate of `e`.
Consequently its absolute value is also the corresponding convex
combination of the absolute values in (14). Concavity of `h`, applied
coordinate by coordinate, yields

\[
\begin{aligned}
\sum_i w_i h(|e_i|)
&\ge\sum_{ij}\lambda_{ij}
      \sum_r w_r h(|v_r^{(ij)}|)\\
&=\sum_{ij}\lambda_{ij}(w_i+w_j)h(s/m_{ij}).
\end{aligned}
\tag{16}
\]

Taking the smallest summand proves (13). All arguments of `h` in
(14)--(16) lie in `[0,s]`, so no extension of its concavity domain is
being made.

This estimate is sharp given only the hypotheses on the frame tour.
For every pair in (13), take the two opposite increments in (14).
They give charged total `s` and a closed real frame walk with spread
`s/m_ij<=D`. Thus a larger universal lower bound cannot follow from
closure and the charged total alone. This sharpness statement concerns
frame increments; it does not assert that such a walk satisfies the
square-separation inequalities.

## 4. Rational consequences for the two coarse thresholds

On `[0,7/10]`, alternating Taylor bounds give

\[
h(x)\ge p(x)
=\frac{x}{2}-\frac{x^2}{4}-\frac{x^3}{12}
 +\frac{x^4}{48}+\frac{x^5}{240}
 -\frac{x^6}{1440}-\frac{x^7}{10080}.
\tag{17}
\]

For the first coarse threshold, exact substitution gives

\[
\begin{aligned}
p(1/5)-\frac{2234}{25000}&=\frac{87}{10937500}>0,\\
p(2/5)-\frac{15523}{100000}&=\frac{7607}{787500000}>0.
\end{aligned}
\tag{18}
\]

Choose the unpaid weight `alpha=(19/125) beta`. The two alternatives
in (7), with `s=2/5`, are then both strictly greater than
`(1117/6250) beta` when `beta>0`: the first follows by doubling the
first bound in (18), while the second follows from

\[
\frac{144}{125}\frac{15523}{100000}
-\frac{1117}{6250}
=\frac{328}{3125000}>0.
\tag{19}
\]

Therefore the actual closed tour satisfies

\[
\boxed{
S\ge\frac25\quad\Longrightarrow\quad
U_I+\frac{19}{125}U_J>\frac{1117}{6250}.
}
\tag{20}
\]

For example, taking `beta=3/80` and `alpha=57/10000` gives the exact
weighted width charge

\[
\frac3{80}U_I+\frac{57}{10000}U_J>
\frac{3351}{500000}.
\tag{21}
\]

For the sharper threshold `s=13/50`, the same polynomial gives

\[
h(13/100)>\frac{12119}{200000},\qquad
h(13/50)>\frac{11173}{100000}.
\tag{22}
\]

The exact positive remainders from (17) are respectively
`3042311545183/1008000000000000000` and
`13819961111/2625000000000000`; no small interval around either
argument is used. Since

\[
\frac{217}{200}\frac{11173}{100000}
-\frac{12119}{100000}
=\frac{741}{20000000}>0,
\tag{23}
\]

Theorem 1 also gives

\[
\boxed{
S\ge\frac{13}{50}\quad\Longrightarrow\quad
U_I+\frac{17}{200}U_J>\frac{12119}{100000}.
}
\tag{24}
\]

These are width consequences of the full signed closure. They remain
valid with arbitrary original SAT owners and arbitrary compatible
radial kinds, since neither is used in their proof.
