# A full-angle four-row terminal at total height variation 13/100

November 4, 2026. Computer-assisted discovery, complete exact tables,
independently reconstructed arithmetic, and physical lifting below.
No Lean, Lake or CI. This theorem and its explicit closed complement
add zero original-cell and zero whole-mask closures until a complete
original caller supplies their hypotheses and closes its complement.

## 1. The geometric theorem

Let `A,H,I,D,E,F,G` be seven distinct retained original physical unit
squares with pairwise disjoint open interiors, contained in a centered
disk of radius R. All seven frames are independent and unrestricted.
Suppose

\[
 x_A\le x_H\le x_I\le x_D,\qquad
 V:=|y_H-y_A|+|y_I-y_H|+|y_D-y_I|\le\frac{13}{100}.         \tag{1}
\]

Let EF and FG be actual horizontal projection links, retaining their
original center-cone comparisons:

\[
\begin{split}
 x_F-x_E&\ge h_E+h_F,& |y_F-y_E|&\le x_F-x_E,\\
 x_G-x_F&\ge h_F+h_G,& |y_G-y_F|&\le x_G-x_F.
\end{split}                                               \tag{2}
\]

Then

\[
 R^2\ge Q=\frac{1105}{256}.                               \tag{3}
\]

At equality, all seven frames are aligned with the fixed horizontal and
vertical directions, and `x_D-x_A=3`. No endpoint sign, original angle
magnitude, absolute height, shoulder order, or projection condition on
the three new four-row links is added to (1)--(2).

For the unchanged original-nine `001/00` caller with its original
extras H,I, the hypotheses exclude even closed Q, using its strictly
weak CD bit as proved in Section 6. Every original frame, all 36 corners,
all 36 physical pairs, all five original center cones, actual AB/BC/EF/FG,
and strictly weak CD remain in that caller.

## 2. Complete endpoint-sign and vertical-side reduction

It suffices to work under `R^2<=Q`, because a larger radius already
satisfies (3). If the canonical endpoint angles obey `theta_A theta_D<=0`,
the accepted `OPPOSITE_ENDPOINT_TILTS_FULL_ANGLE_FOUR_ROW_HAND_TERMINAL.md`
applies: its variation allowance `23/100` is larger than (1), and it
requires only the actual short links from (2).

It remains to prove the case with the two endpoint angles of the same
sign. The independently proved `SHORT_ROW_COMMON_SIDE_HAND_PROOF.md`
applies because `13/100<23/100`. It proves that E,F,G all lie above the
four-row or all lie below it. It also proves

\[
 0<x_E-x_A<29/30<1,\qquad0<x_D-x_G<29/30<1.                \tag{4}
\]

A vertical reflection makes the short row lie below. If the endpoint
angles are then both nonpositive, a horizontal reflection with simultaneous
reversal of both selected lists makes them both nonnegative. These
transformations preserve (1)--(2) and the seven physical squares.
Consequently assume

\[
 \theta_A,\theta_D\in[0,\pi/4],\qquad E,F,G\text{ below the four-row}.
\]

By (4), each genuine owned separator from A toward E and from D toward G
has negative vertical component. The new oriented endpoint theorem
therefore applies on the left. The unrestricted accepted endpoint cap
applies on the right. These transformations occur inside the seven-square
geometric proof; the all-nine application in Section 6 uses the original
labels and original mask inequalities again.

## 3. The asymmetric pair of endpoint tolls

Write `alpha_i=cos(theta_i)`, `beta_i=|sin(theta_i)|`,
`h_i=(alpha_i+beta_i)/2`. Put

\[
 T_g(\theta_A)=\frac{55}{64}\beta_A
                   -\frac{119}{92}(1-\alpha_A),
\]

\[
 T_b(\theta_D)=\max\left\{\frac{2\beta_D}{23},
                       \frac{9\beta_D-41(1-\alpha_D)}{32}\right\}.
                                                               \tag{5}
\]

The oriented good-cap proof is
`ORIENTED_GOOD_ENDPOINT_TILT_TOLL_HAND_PROOF.md`. Its complete complement
has 6,170 positive interval leaves and a separate directed-integer replay.
The unrestricted right cap is inherited from
`UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md` and
`SHARP_SMALL_MAIN_ENDPOINT_TILT_TOLL.md`.

Summing the two physical pair caps, with
`a=46`, `b=27/2`, `K=211/4`, gives

\[
 a[x_D-x_A-h_A-h_D+T_g+T_b]
 +b[x_G-x_E-h_E-h_G]\le2K.                                \tag{6}
\]

Both caps are strict below Q. The actual short row supplies
`x_G-x_E-h_E-h_G>=2h_F>=1`. Since `2K=2a+b`, (6) implies

\[
 x_D-x_A-h_A-h_D+T_g+T_b\le2,                             \tag{7}
\]

strictly below Q. The task is to prove the reverse inequality from the
same four physical row squares, without losing their individual angles.

## 4. Exact all-angle scalar certificate

Number A,H,I,D by `0,1,2,3`. For an adjacent physical pair i,j, put

\[
 R_{ij}=\frac{1+\cos(\theta_i-\theta_j)
                    +|\sin(\theta_i-\theta_j)|}{2}.
\]

The original separating-axis theorem supplies a normal owned by one of
the two original frames. If its owner is o, horizontal gap is `d>0`,
and signed vertical gap is v, then

\[
 d\ge R_{ij}/\alpha_o-|\tan\theta_o|\,|v|.               \tag{8}
\]

For completeness, the incircles and `|v|<=13/100` imply
`d>|v|` because `d^2+v^2>=1` and `2(13/100)^2<1`. A separating normal
cannot point backward horizontally: its center projection would be less
than one. For either the shallow or steep axis owned by o, its forward
projection is at most `alpha_o d+beta_o|v|`, using `d>|v|` and
`alpha_o>=beta_o`. The square support sum is invariant under a quarter
turn of that axis and is exactly `R_ij`. This proves (8) while retaining
both owners, both chiralities and all angle/contact endpoints.

For each edge j choose its actual owner `o_j in {j,j+1}`. The delivered
finite polynomial table proves, for each distinct selected owner k,

\[
\begin{split}
 C:=\sum_{j=0}^2\frac{R_{j,j+1}}{\alpha_{o_j}}
       -h_0-h_3+T_g(\theta_0)+T_b(\theta_3)-2
 \ge\frac{131}{1000}|\tan\theta_k|.                      \tag{9}
\end{split}
\]

Its domain is all `theta_0,theta_3 in [0,pi/4]` and independently
`theta_1,theta_2 in [-pi/4,pi/4]`, with all eight actual owner patterns.

### Rational scalar and positive denominators

Set `z_i=s_i x_i`, where `x_i=tan(|theta_i|/2)`,
`s_0=s_3=1`, and `s_1,s_2` independently equal plus or minus one.
The table covers the larger rational box `0<=x_i<=5/12`.
Every factor `1-x_i^2`, `1+x_i^2`, and

\[
 D=\prod_{i=0}^3(1-x_i^4)
\]

is positive there. On the physical domain the exact identities are

\[
 \frac{R_{ij}}{\alpha_o}
 =\frac{(1+z_i z_j)(1+z_i z_j+|z_i-z_j|)}
        {(1-x_o^2)(1+x_q^2)},                            \tag{10}
\]

where q is the other endpoint of edge ij, and

\[
 T_g-h_0=\frac{-368+529x_0-1536x_0^2}{736(1+x_0^2)}.       \tag{11}
\]

The right endpoint uses the maximum of

\[
 E_4(x)=\frac{-23-38x+23x^2}{46(1+x^2)},\qquad
 E_*(x)=\frac{-8-7x-33x^2}{16(1+x^2)},
\]

with difference

\[
 E_*(x)-E_4(x)=\frac{x(143-943x)}{368(1+x^2)}.              \tag{12}
\]

A leaf supplies three dyadic numbers `epsilon_j in [-1,1]` and one
dyadic number `tau in [0,1]`. In (10), replace each absolute value by
`epsilon_j(z_j-z_(j+1))`. Replace the right endpoint maximum by
`E_4+tau(E_*-E_4)`. Subtract
`(131/1000)*2x_k/(1-x_k^2)` and multiply by the positive `92000 D`.
Multiplying again by the common positive dyadic weight denominator
produces a polynomial with integer coefficients, degree at most four
in each of its four variables.

The independent checker reconstructs these integer coefficients from
(10)--(12). Its good-endpoint integer numerator is exactly
`-368+529x_0-1536x_0^2`, and the selected-slope integer coefficient is
`-24104 x_k` before multiplying by the denominator complement.
No discovered polynomial or floating Bernstein coefficient is trusted.

### Complete Bernstein boxes and exact replay

Every split replaces one dyadic interval by both of its closed halves.
For a leaf coordinate `[l,u]`, the degree-four Bernstein coefficient
of a univariate power `x^r` at index j is

\[
 \sum_{m=0}^{\min(j,r)}
  {r\choose m}l^{r-m}(u-l)^m\frac{{j\choose m}}{{4\choose m}}.
\]

Applying these transforms successively to all four coordinates gives
625 coefficients per leaf. If all are nonnegative, the polynomial is
nonnegative throughout the closed box. The checker multiplies every
transform by an explicit positive integer denominator, so its arithmetic
uses integers throughout.

The certificate has four internal-angle sign patterns, eight owner
patterns, and every distinct selected owner: exactly 80 complete domains.
There are 892 leaves, of which 812 have strictly positive coefficient
minimum and 80 are nonnegative leaves containing alignment. All 557,500
integer coefficient checks pass. Every full binary cover is reconstructed;
there are 1,704 nodes and no frontier. Files are in `same_sign_row/cover/`,
with independent checker `same_sign_row/check_same_sign_cover.py`.

## 5. Physical conclusion and equality

Let `M=max_j |tan(theta_(o_j))|`. Summing (8), then using (1) and (9),
gives

\[
\begin{split}
 x_D-x_A-h_A-h_D+T_g+T_b
 &\ge2+C-MV\\
 &\ge2+\left(\frac{131}{1000}-\frac{13}{100}\right)M
 =2+\frac{M}{1000}\ge2.                                 \tag{13}
\end{split}
\]

This contradicts the strict form of (7) for `R^2<Q`, proving (3).
At closed Q, (7) and (13) force `M=0`. Thus every selected owner is
aligned. Every unselected interior row frame has two aligned neighbors;
its contribution to C is `alpha+beta-1`, strictly positive unless it too
is aligned. An unselected endpoint contributes its endpoint toll after
the pair support and halfwidth terms cancel. The bad toll is at least
`2beta/23`; the good toll is positive for beta>0 because

\[
 T_g/\beta\ge\frac{55}{64}-\frac{119}{92}\frac5{12}
             =\frac{1415}{4416}>0.
\]

Consequently all four row frames align. Their three horizontal gaps are
then at least one, and (7) forces `x_D-x_A=3`. Equality in (6) forces
`h_F=1/2` and equality in both endpoint caps. The cap equality statements
align E and G, and `h_F=1/2` aligns F. This proves the claimed equality
information for all seven originals. The opposite-endpoint case has the
same conclusion from the accepted theorem.

## 6. The unchanged original-nine 001/00 equality blocker

Retain the original A,B,C,D, their actual AB and BC links, original
CD center cone, and strictly weak CD bit. At a hypothetical closed-Q
terminal, A and D are aligned and their horizontal span is three.
The actual links and the original inset consequence on CD give

\[
 3=x_D-x_A\ge h_A+2h_B+h_C+g_C+g_D
             =1+2h_B+h_C+g_C\ge3.
\]

Here `g=1/(4h)`, `h_B>=1/2`, and

\[
 h_C+g_C-1=\frac{(2h_C-1)^2}{4h_C}\ge0.
\]

Equality forces `h_B=h_C=1/2`, so both original B and C align. It also
forces `x_D-x_C=1=h_C+h_D`, contradicting the retained strict weak bit.
The same nine originals, corners, frames, pairs and marked comparisons
are used throughout; no seven-original relaxation is claimed to close
an entire nine-original caller.

For direct four-row use with `A,B,C,D` instead of `A,H,I,D`, the theorem
also applies to every original mask `abc/00`. At equality each main-row
gap is one and all four frames align, so any main bit equal to one is
impossible. This is a conditional transfer; it closes no whole mask
without proving the variation hypothesis over that entire mask.

## 7. Explicit complete closed escape cover

For the unchanged original-nine 001/00 caller, either (1) holds and
Section 6 excludes it, or at least one of these eleven closed domains
holds:

1. `x_H-x_A<=0`;
2. `x_I-x_H<=0`;
3. `x_D-x_I<=0`;
4. one of the eight signed-height inequalities

\[
 \epsilon_0(y_H-y_A)+\epsilon_1(y_I-y_H)
       +\epsilon_2(y_D-y_I)\ge13/100,
 \qquad(\epsilon_0,\epsilon_1,\epsilon_2)\in\{-1,1\}^3.
\]

All eleven retain the complete original caller predicate. They overlap
on closed faces. Their completeness follows from
`|p|+|q|+|r|=max_epsilon(epsilon_0 p+epsilon_1 q+epsilon_2 r)`.
When horizontal order is already independently proved, its hypotheses
may be retained and only the eight height escapes are needed.

`FULL_ANGLE_SMALL_VARIATION_COMPLEMENT.json` prints all eleven exact
rows. `full_angle_common_side_four_row_guard.py` checks quantitative
order and signed-height bounds, using exact decompositions into original
pair differences. `review_full_angle_common_side_guard.py` separately
checks its formulas and arithmetic: 445 checks pass. The helper does not
prove original-bound ancestry or assemble a whole original-cell cover.

The fixed 231 original IDs, 32 masks, 7,915 positional roots and fifteen
roadmap IDs receive no changes or new gates from this theorem.
