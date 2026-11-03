# The three-link replacement row allows total variation 11/30

November 2, 2026, America/Chicago. Independent hand verification and a
stronger scalar payment for the three-link row theorem. Computer exploration
of the scalar expression preceded this proof. No Lean, Lake, or CI.

## 1. Statement and retained original scope

The theorem in `WEAK_OUTER_INWARD_ENDPOINT_THREE_LINK_ROW_HAND_TERMINAL.md`
remains valid when every occurrence of the total vertical variation bound
`1/3` is replaced by **11/30**. In particular, four distinct original
physical squares in horizontal order satisfy

\[
 x_3-x_0-h_0-h_3+\sigma(t_0)+\sigma(t_3)\ge2,
 \qquad
 \sigma(t)=\frac{1+(23/32)t}{\sqrt{1+t^2}}-1,
 \tag{1}
\]

provided

\[
 \sum_{i=0}^{2}|y_{i+1}-y_i|\le\frac{11}{30}.
 \tag{2}
\]

All four original orientations, both separating-axis owners, and all
physical axis signs are retained. Equality in (1) forces all four
originals aligned, with their three horizontal gaps exactly one.

Within the original-nine `001/00` caller, take the row to be A,H,I,D,
where H,I are the two unchanged extra originals. If A's original signed
tilt is nonpositive and D's is nonnegative, the established upward A/E
and D/G normal premises supply both signed endpoint caps. Thus this row
region is excluded even at closed Q=1105/256. The equality contradiction
is the same original AB,BC,CD inset argument as in the cited theorem.
Neither endpoint sign is dropped. This does not assert exhaustive routing
of the two extras or a whole-mask closure.

## 2. The only scalar strengthening required

Use the cited proof's unchanged functions

\[
 r(s)=\sqrt{1+s^2},\quad h(s)=\frac{1+s}{2r(s)},\quad
 f(s)=\sigma(s)-h(s)+\frac12,
\]

\[
 K(s)=\min\{f(s),\;\sigma(1)+\tfrac12-h(s)\}.
\]

Its endpoint transfer, proved by monotonicity and concavity, is

\[
 f(t)+|h(t)-h(s)|\ge K(s)\qquad(0\le s,t\le1).
\]

We prove the stronger continuous scalar inequality

\[
 2K(s)+r(s)-1-\frac{11}{30}s\ge0,
 \tag{3}
\]

strictly when s>0. It suffices to prove it for each entry of the minimum.

### First entry

For K=f(s), multiplication of the left side by r gives exactly

\[
 (r-1)^2+s\left(\frac7{16}-\frac{11}{30}r\right).
 \tag{4}
\]

If r<=105/88, both terms are nonnegative, and the square is positive
when s>0. If r>=105/88, the coefficient in parentheses is nonpositive.
Since s<=1, (4) is at least

\[
 g(r)=(r-1)^2+\frac7{16}-\frac{11}{30}r.
\]

Here g(105/88)=(17/88)^2>0 and

\[
 g'(r)=2r-2-\frac{11}{30}
 \ge\frac{13}{660}>0.
\]

This proves the first entry on its entire domain, including the split face.

### Second entry

For K=σ(1)+1/2-h(s), the left side of (3) is

\[
 2\sigma(1)-\left(\frac{s-s^2}{r(s)}+\frac{11}{30}s\right).
 \tag{5}
\]

Set L(s)=1+s²/2-s⁴/8. On [0,1], L>=1 and

\[
 1+s^2-L(s)^2=\frac{s^6(8-s^2)}{64}\ge0,
\]

so r(s)>=L(s)>0. As s-s²>=0, it is enough to prove

\[
 \frac{s-s^2}{L(s)}+\frac{11}{30}s<\frac{4301}{10000}.
 \tag{6}
\]

Multiplication of the difference between the right and left sides of
(6) by the positive 240000L(s) gives the integer polynomial

\[
 p(s)=103224-328000s+291612s^2-44000s^3-12903s^4+11000s^5.
\]

The whole continuous interval is handled by a quadratic lower support:

\[
 p''(s)=583224-264000s-154836s^2+220000s^3\ge164388.
\]

Indeed the difference from 164388 is
264000(1-s)+154836(1-s²)+220000s³, a sum of nonnegative terms.
At s0=2/3, direct fraction arithmetic gives

\[
 p(s_0)=\frac{6184}{243},\qquad p'(s_0)=-\frac{184592}{81}.
\]

Integrate the lower bound on p'' from s0 in either direction, and
complete the square. For every s in [0,1],

\[
 p(s)\ge p(s_0)+p'(s_0)(s-s_0)+82194(s-s_0)^2
 \ge\frac{2602608088}{269637417}>0.
 \tag{7}
\]

This proves (6). Finally,

\[
 2\sigma(1)=\frac{55\sqrt2}{32}-2>\frac{4301}{10000}.
\]

The equivalent positive-root comparison is 34375√2>48602, with
exact squared reserve

\[
 2\cdot34375^2-48602^2=1126846>0.
\]

Equations (5)--(7) prove strict positivity for the second entry on the
entire interval. Thus (3) is proved, with equality possible only at s=0.

## 3. Transfer to physical rows and equality

Each original link now has |v|<=11/30. Unit center distance gives
d>=sqrt(1-v²)>=sqrt(779)/30>11/30>=|v|. The last strict comparison
uses 779>121. Consequently the original all-owner pair estimate used
in the cited proof still applies unchanged.

For the three chosen physical owners, put s=max(s1,s2,s3). Their height
loss is at most s times the total variation, hence at most (11/30)s.
Their nonnegative radical gains have sum at least r(s)-1. The original
width variation and the two endpoint transfers supply 2K(s). Equation
(3) therefore proves (1) by exactly the same finite sum of original
physical inequalities. No numerical optimization value enters the proof.

The strictness in (3) forces s=0 in an equality case. The remaining
nonnegative endpoint terms and width variation then force all four
widths to be 1/2. Original physical nonoverlap, with individual vertical
gaps below one, makes all three horizontal gaps at least one; their
sum in equality is three, so each is exactly one.

The signed-cap assembly, the distinction between the two original
endpoint signs, and the strict weak-bit contradiction in Section 5 of
the cited theorem are unchanged. After sorting the extra labels H,I,
its necessary escape union is likewise unchanged except that its eight
signed height inequalities use 11/30 as the threshold. The unique-leftmost
theorem may separately remove the x_H<=x_A escape.

The companion `weak_outer_three_link_eleven_thirtieths_arithmetic.py`
checks the polynomial identities and all new exact numerical reserves.
The support, monotonicity, concavity, continuous lower support and
equality arguments are printed here and in the cited complete theorem.
