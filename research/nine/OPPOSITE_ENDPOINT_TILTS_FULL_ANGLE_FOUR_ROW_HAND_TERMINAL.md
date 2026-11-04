# Opposite endpoint tilts: a full-angle four-square row terminal

November 4, 2026 (UTC). Computer-assisted discovery followed by a complete
finite polynomial certificate, an independently reconstructed exact integer
replay, and the continuous physical hand proof below. No Lean, Lake or CI.
This is a conditional theorem, not an original-cell or whole-mask closure.

## 1. The geometric theorem

Let A,H,I,D,E,F,G be seven distinct original physical unit squares with
pairwise disjoint open interiors in a disk of radius R. Their frames are
independent. Use one fixed horizontal direction, and the originals' canonical
signed angles `theta_i in [-pi/4,pi/4]`. Suppose

\[
x_A\le x_H\le x_I\le x_D,\qquad
\theta_A\theta_D\le0,
\]

\[
|y_H-y_A|+|y_I-y_H|+|y_D-y_I|\le\frac{23}{100},             \tag{1}
\]

and E,F,G are an actual horizontal projection chain. Then

\[
R^2\ge Q=\frac{1105}{256}.                               \tag{2}
\]

For the proof it suffices to assume `R^2<=Q`, since `R^2>Q` already
implies (2); every use of the inherited cap below is under this radius
hypothesis. Equality forces all seven originals aligned and `x_D-x_A=3`. Neither
shoulder height order, any original center height, any angle magnitude,
nor a common orientation is an extra hypothesis. The three new row links
need not be actual projection links or original center-cone links.

Consequently the complete strict original-nine `001/00` caller is excluded
even at closed Q whenever (1), the horizontal order, and the opposite
endpoint signs hold for its unchanged original extras H,I. Section 7 proves
this final original-caller implication, including the strictly weak CD bit.

The closed horizontal-order faces are included. If adjacent row x coordinates
coincide, their vertical separation is at most `23/100<1`, contradicting
the unit center-distance bound supplied by the original open incircles.
Thus all three row horizontal gaps are positive in any physical caller.

A common vertical reflection negates all signed angles and all heights,
preserves every physical square and actual horizontal link, and leaves (1)
unchanged. It suffices below to treat `theta_A>=0`, `theta_D<=0`.
The reflected case `theta_A<=0`, `theta_D>=0` is therefore included too.

## 2. Exact original-pair inputs

Put `a=46`, `b=27/2`, and `K=211/4`. For a canonical signed angle theta write

\[
\alpha=\cos\theta>0,\qquad \beta=|\sin\theta|,\qquad
h=(\alpha+\beta)/2,
\]

and use the accepted normalized main-endpoint toll

\[
T(\theta)=\max\left\{\frac{2\beta}{23},
                    \frac{9\beta-41(1-\alpha)}{32}\right\}. \tag{3}
\]

The universal four-beta theorem and sharp small-angle-coefficient theorem
are both valid over the **entire** folded angle interval. Their maximum,
not their sum, gives the physical weighted pair cap

\[
a[-e\cdot c_M-h_M(e)+T(\theta_M)]
 +b[-e\cdot c_B-h_B(e)]\le K.                            \tag{4}
\]

It is strict if `R^2<Q`. Both frames, both centers and every genuine physical
separator owner are unrestricted. These are the accepted sources
`UNIVERSAL_MAIN_ENDPOINT_TILT_TOLL.md` and
`SHARP_SMALL_MAIN_ENDPOINT_TILT_TOLL.md`, normalized by a. The earlier
unrestricted cap supplies its equality statement. Their proofs are inherited;
a new arithmetic replay of their old finite tables is not claimed here.

For two adjacent row originals i,j, the separating-axis theorem supplies
an actual normal owned by one of their original frames. Write the horizontal
gap as `d>0` and the signed vertical gap as v. The incircles give

`d^2+v^2>=1`, hence `d>|v|` when `|v|<=23/100`,

because `2(23/100)^2<1`. A separating normal cannot have nonpositive
horizontal component: its center projection would be at most `|v|<1`,
whereas its support sum is at least one.

Let o be its original owner. Its shallow forward axis has components
`(alpha_o,sin(theta_o))`; its steep forward axis has absolute components
`(beta_o,alpha_o)`. On either axis the projection is at most
`alpha_o*d+beta_o*|v|`, since `d>|v|`.
Each centered square's support is invariant under a quarter turn of the
axis, so the actual support sum is the same on the owner's shallow axis.
It is exactly

\[
R_{ij}=\frac{1+\cos(\theta_i-\theta_j)
                    +|\sin(\theta_i-\theta_j)|}{2}.       \tag{5}
\]

Here the cosine is nonnegative because the difference of the two canonical
angles belongs to `[-pi/2,pi/2]`. Thus every actual owner gives

\[
d\ge R_{ij}/\alpha_o-|\tan\theta_o|\,|v|.                \tag{6}
\]

The steep owner, both chiralities, angle endpoints, contacts and all
signed vertical gaps have been retained in this derivation.

## 3. The complete scalar theorem

Number the row originals `A,H,I,D` by `0,1,2,3`. For each edge j choose
one of its two actual possible owners `o_j in {j,j+1}`. For every
`theta_0 in [0,pi/4]`, `theta_3 in [-pi/4,0]`, and independently
`theta_1,theta_2 in [-pi/4,pi/4]`, the delivered finite table proves

\[
\begin{split}
C:=\sum_{j=0}^2\frac{R_{j,j+1}}{\alpha_{o_j}}
       -h_0-h_3+T(\theta_0)+T(\theta_3)-2
\ge\frac{231}{1000}|\tan\theta_k|                         \tag{7}
\end{split}
\]

for every distinct selected owner k among `o_0,o_1,o_2`.
Choosing one with maximum absolute slope proves (7) with the maximum.

The table covers all continuous original angles and all eight owner
patterns. It is stronger than the geometric variation bound by exactly
`231/1000-23/100=1/1000`. It is not an infeasibility claim from a sampled
angle grid or an optimizer tolerance.

### 3.1 Rational coordinates and positive denominators

Set `z_i=tan(theta_i/2)=s_i x_i`, where `x_i>=0`, `s_0=1`, `s_3=-1`,
and `s_1,s_2` are independently -1 or 1. The original canonical domain
has `x_i<=sqrt2-1<5/12`. The strict rational upper comparison is
`(17/12)^2-2=1/144>0`. We certify the larger rational box

\[
0\le x_i\le5/12\quad(i=0,1,2,3).                         \tag{8}
\]

Every factor `1-x_i^2`, `1+x_i^2`, and their product

\[
D(x)=\prod_{i=0}^3(1-x_i^4)                               \tag{9}
\]

is positive on (8). On the physical subdomain, direct half-angle
identities give

\[
\alpha_i=(1-x_i^2)/(1+x_i^2),\quad
|\sin\theta_i|=2x_i/(1+x_i^2),\quad
|\tan\theta_i|=2x_i/(1-x_i^2),
\]

\[
\frac{R_{ij}}{\alpha_o}
=\frac{(1+z_i z_j)(1+z_i z_j+|z_i-z_j|)}
       {(1-x_o^2)(1+x_q^2)},                             \tag{10}
\]

where q is the other endpoint of edge ij. Formula (10) uses
`sin(theta_i-theta_j)=2(z_i-z_j)(1+z_i z_j)/[(1+x_i^2)(1+x_j^2)]`.
The factor `1+z_i z_j` is strictly positive throughout (8).

The two endpoint terms `T-h` in (7) are the maximum of

\[
E_4(x)=\frac{-23-38x+23x^2}{46(1+x^2)},\qquad
E_*(x)=\frac{-8-7x-33x^2}{16(1+x^2)}.                     \tag{11}
\]

Their difference is

\[
E_*(x)-E_4(x)=\frac{x(143-943x)}{368(1+x^2)}.              \tag{12}
\]

These formulas are lower-bound tools on the enlarged rational box;
only the physical subdomain is used to identify them with original angles.

### 3.2 The polynomial certified on each box

A table leaf supplies three rational numbers
`epsilon_0,epsilon_1,epsilon_2 in [-1,1]` and two rational numbers
`tau_0,tau_3 in [0,1]`. Use

`|z_j-z_(j+1)| >= epsilon_j (z_j-z_(j+1))`

in (10), and use `E_4+tau_i(E_*-E_4)` as a lower bound on the endpoint
maximum (11). Subtract `(231/1000)*2x_k/(1-x_k^2)`.
Multiply the resulting expression by the positive `46000 D(x)`.
This gives a polynomial P of degree at most four in each x coordinate,
with rational coefficients. The common scale 46000 clears the fixed
constant denominators 46, 368 and 500.

The five leaf numbers have a common dyadic denominator `2^p`; multiplying
P by that positive denominator makes every coefficient an integer. The
independent checker reconstructs those integer coefficients directly from
(9)--(12). No polynomial coefficient supplied by numerical discovery is
trusted.

For clarity, the numerator in a pair contribution has the exact expansion

\[
(1+z_i z_j)^2+\epsilon_j(1+z_i z_j)(z_i-z_j),
\]

whose epsilon coefficient is
`z_i-z_j+z_i^2 z_j-z_i z_j^2`. Multiplying its denominator complement
adds `(1+x_o^2)(1-x_q^2)` and `1-x_l^4` for the other two coordinates.
For an endpoint, the denominator complement is `1-x_i^2` on that
coordinate and `1-x_l^4` on each other coordinate. For the slope loss,
it is `1+x_k^2` and the other three factors. These are precisely the
finite polynomial identities expanded by the separate integer checker.

### 3.3 Exact Bernstein check on a closed dyadic box

A path step chooses one coordinate and one of the two **closed** halves
of its current interval. Every initial coordinate interval is `[0,5/12]`.
Thus a terminal coordinate has the exact form

`[5n/(12*2^d), 5(n+1)/(12*2^d)]`.

For a polynomial `p(x)=sum_r a_r x^r` of degree at most four on `[l,u]`,
its degree-four Bernstein coefficient with index j is

\[
b_j=\sum_{r=0}^4 a_r
     \sum_{m=0}^{\min(j,r)}
     {r\choose m}l^{r-m}(u-l)^m
     \frac{{j\choose m}}{{4\choose m}}.                  \tag{13}
\]

Apply this identity independently in the four coordinates. It produces
625 rational coefficients. The Bernstein basis functions are nonnegative
on the entire closed box and sum to one. Therefore nonnegativity of all
625 coefficients proves `P>=0` throughout that box, including every face.

The independent evaluator multiplies each one-coordinate transform in
(13) by the positive integer `12*(12*2^d)^4`; all operations are integer
addition and multiplication. It checks all 625 signs exactly. There is
no floating-point arithmetic, directed numerical rounding, external
optimizer, numerical source import, or unchecked radical in this replay.

## 4. Complete domain and finite-table accounting

For each of the four choices of signs `(s_1,s_2)`, the table covers all
of the following owner patterns and all the listed selected-owner choices:

| Edge owners `(o_0,o_1,o_2)` | Selected k values |
|---|---|
| `(0,1,2)` | `0,1,2` |
| `(0,1,3)` | `0,1,3` |
| `(0,2,2)` | `0,2` |
| `(0,2,3)` | `0,2,3` |
| `(1,1,2)` | `1,2` |
| `(1,1,3)` | `1,3` |
| `(1,2,2)` | `1,2` |
| `(1,2,3)` | `1,2,3` |

This is `4*(3+3+2+3+2+2+2+3)=80` complete scalar roots.
The independent reader constructs these expected domains itself, checks
that every one occurs once, and reconstructs a full binary split tree for
each root. A missing child, repeated leaf, unresolved frontier, wrong root,
wrong original owner or out-of-range weight is rejected.

| Exact replay item | Count |
|---|---:|
| Complete scalar roots | 80 |
| Closed binary-tree nodes | 2,730 |
| Terminal boxes | 1,405 |
| Individually reconstructed Bernstein coefficient signs | 878,125 |
| Leaves with every coefficient strictly positive | 1,325 |
| Leaves with nonnegative coefficients, including the aligned face | 80 |
| Unresolved frontier | 0 |

The 80 nonnegative leaves are accepted with exact zero coefficients;
no positive clearance from alignment is assumed. The stronger coefficient
`231/1000` in (7) supplies the separate strict owner-slope reserve used
in Section 5. All table paths and five rational weights are included in
the delivered JSON records. The replay report binds every record by SHA-256.

Numerical optimization suggested the scalar target. Linear programming
then chose the five rational lower-bound weights and the finite boxes.
Those computations are discovery only. The independent exact polynomial
reader, finite-cover check, and physical proof are the accepted premises.

## 5. Lift the scalar inequality to the actual row

Choose the three actual original owners in (6), and set
`M=max_j |tan(theta_(o_j))|`. Sum (6), use (1), and apply (7) to an
owner attaining M. This gives

\[
\begin{split}
x_D-x_A-h_A-h_D+T(\theta_A)+T(\theta_D)
&\ge 2+(231/1000)M-(23/100)M\\
&=2+M/1000.                                             \tag{14}
\end{split}
\]

No owner is changed to minimize an expression: the table covers the
actual three owners selected by physical separation. Each folded slope
and every support remains that of the same original square.

Apply (4) to A,E in the left direction and D,G in the right direction.
The sum is

\[
a[x_D-x_A-h_A-h_D+T(\theta_A)+T(\theta_D)]
+b[x_G-x_E-h_E-h_G]\le2K.                               \tag{15}
\]

EF and FG are actual projection links, so the second bracket is at
least `2h_F>=1`. Equations (14)--(15) imply

`2K >= 2a+b+aM/1000 = 2K+aM/1000`.

For `R^2<Q`, the cap sum is strict, a contradiction. This proves (2).
At closed Q, equality is necessary and M=0.

## 6. Equality, including the aligned faces

When M=0, all three actual owners are aligned. Their steep axes are
vertical and cannot separate a pair with `|v|<=23/100<1`, since the
support sum on any axis is at least one. Their horizontal axes therefore
give **actual** row projection separation:

`d_j >= h_j+h_(j+1)`.

Consequently the first bracket in (15) is at least

`2h_H+2h_I+T(theta_A)+T(theta_D) >= 2`.

Equality in (15) and the short-chain bound forces `h_H=h_I=1/2` and
`T(theta_A)=T(theta_D)=0`. Since `T(theta)>=2|sin(theta)|/23`, both
endpoints are aligned as well. The three actual row gaps all equal one,
so `x_D-x_A=3`.

Now both main tolls vanish, and equality in (15) is equality in each
ordinary physical pair cap. The accepted cap equality theorem aligns E,G;
short-chain equality gives `h_F=1/2`. Thus all seven originals are aligned.
The argument covers all original physical contacts and the exact zero-angle
face; no numerical positive-margin exclusion of that face is used.

## 7. The strict original-nine caller and its complete complement

Retain the unchanged nine original squares A,B,C,D,E,F,G,H,I, all 36
corners, all 36 physical pairs, all five original center-cone comparisons,
actual AB, BC, EF, FG, and the **strictly weak** CD bit. If the theorem's
AHID hypotheses hold, Sections 5--6 force `x_D-x_A=3` at closed Q and
align A,D,H,I. Original actual AB,BC and the original CD cone-inset
inequality give

\[
3\ge h_A+2h_B+h_C+g_C+g_D
  =1+2h_B+h_C+\frac1{4h_C}\ge3.                         \tag{16}
\]

The last inequality uses `h_B>=1/2` and

`h_C+1/(4h_C)-1=(2h_C-1)^2/(4h_C)>=0`.

Equality forces B,C aligned. The original CD inset inequality then
requires horizontal gap at least one, equal to `h_C+h_D`, contradicting
its retained strictly weak bit. Thus the entire guarded original-nine
region is excluded even at closed Q. No new cone comparison is assigned
to H or I. No lower bound on the normalized CD transverse gap is needed
by this terminal itself.

The theorem's horizontal order is an **explicit guard**. A normalized
original caller may use its independently proved A-leftmost and D-rightmost
facts and the chosen `x_H<=x_I` normalization to discharge it. This proof
does not infer those facts merely from an arbitrary partial coordinate box.

On a parent with opposite A/D signs already proved, a complete closed
complement consists of eleven domains. Three are

`x_H<=x_A`, `x_I<=x_H`, `x_D<=x_I`.

The other eight, one for each `(e_1,e_2,e_3) in {-1,1}^3`, are

\[
e_1(y_H-y_A)+e_2(y_I-y_H)+e_3(y_D-y_I)\ge23/100.            \tag{17}
\]

Equivalently their left sides are
`-e_1 y_A+(e_1-e_2)y_H+(e_2-e_3)y_I+e_3 y_D`.
The maximum of these eight expressions is exactly the total variation
in (1). Every guard failure lies in the displayed closed union. All
shared equality faces remain covered. If an exact original ancestor
already excludes an order domain, that domain may be discharged by its
own proved interval/order contradiction; it is not silently omitted.

There is a separate safe simplification: if the parent already proves a
**nonstrict** order guard, that theorem hypothesis is settled and the
complement may be constructed using only the remaining hypotheses. Thus
all three proved weak orders permit a complement with just the eight
height domains (17). This does not assert exclusion of the corresponding
oversized closed order-failure halfspace, which also contains equality.
In particular, `x_H<=x_I` alone does not exclude `x_I<=x_H` at equality.
A fixed eleven-domain assembly must retain that overlap; a reduced
eight-domain assembly must explicitly bind the parent proofs of its three
order hypotheses.

For the current C family, `theta_A>=0` and `theta_D<=0` are original
sign-root facts. For the current A family the reflected sign facts hold,
but its surviving inward-escape predicates already force total variation
at least `11/30`; consequently this low-variation terminal does not by
itself close those original cells. An application to a parent without
proved opposite endpoint signs must additionally retain that sign guard
and its complete complement.

## 8. Replay and scope

The portable directory `computer_assisted/opposite_tilt_ahid_row` contains
the complete 80-root finite table, the independent standard-library integer
checker, numerical discovery sources, exact raw report, and immutable
inherited hand premises. Run

```sh
python -B -S verify_chiral_cover.py --directory cover --output FRESH_REPLAY.json
```

The expected result is `PASS_COMPLETE_EXACT_CHIRAL_ROW_COVER`, with 1,405
leaves and zero frontier. This replay proves the scalar table. Sections
1--7 provide its continuous physical lifting and strict-caller equality
argument; the old physical cap inputs retain their earlier acceptance.

No original cell or mask is credited by this conditional theorem alone.
Every future caller must prove the original ancestry and all row guards,
or complete every member of the fixed complementary union. No mandatory
roadmap gate, positional-root ID, or original fixed-cell path is changed.
No human or proof-kernel verification is claimed.
