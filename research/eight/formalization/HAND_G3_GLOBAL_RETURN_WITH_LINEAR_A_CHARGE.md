# A global three-edge return bound with a linear A charge

## 1. Statement and scope

Work on the actual G0--G2 boundary cycle at
\[
 Q=\frac{9789}{2500},\quad
 c_0=\sqrt{Q/2}-\frac12,\quad U=\frac{283}{200},
 \quad\Gamma=\frac{8833}{10000},\quad
 \beta=\frac9{50},\quad\kappa=\frac{49}{50}.
\tag{1}
\]
Retain the common G1 signed marker once at each vertex. Its unsigned
value is F_i; a signed own-frame center is `(a_i,-y_i)`, with
`b_i=|y_i|` and marker `ell_i=sign(y_i) F_i`. At zero transverse
coordinate either compatible signed label is allowed.

Assume only the endpoint signs
\[
                         y_E=-b_E\le0,\qquad y_A=b_A\ge0.
\tag{2}
\]
The return path E--H--G--A has quarter word `(1,0,1)`. Put
\[
 r=\theta_H-\theta_E,\quad
 v=\theta_G-\theta_H,\quad
 t=\theta_A-\theta_G,
 \qquad R_0=|r|+|v|+|t|,
\tag{3}
\]
so its frame-angle sum is `pi+r+v+t`. Each individual error has
absolute value below 7/10 by G1.

**Global return theorem.** Every actual such path satisfies
\[
 \boxed{\pi+r+v+t-\kappa b_A-F_E>\frac{103}{40}=2.575.}
\tag{4}
\]
H and G may have either sign. Every original EH and GA owner is
included, as are both original transverse HG owners and both radial
kinds at every vertex. No frame ordering, mismatch bound, tangent
cut, BT owner or additional E owner is assumed.

For a forbidden BT0/1 candidate, the global zero--quarter theorem
already supplies the A sign in (2); E has the usual reflection
normalization. The complementary AB--BT--TD--DE path has charge
`pi-(r+v+t)+kappa b_A+F_E`. Thus proving that complementary charge
at least `710/113-103/40=16761/4520` would exclude the candidate,
since `2 pi<710/113`. This note proves the return bound (4), not
that still separate complementary-path estimate.

## 2. The unchanged G1 inequalities retain an error gain

Define
\[
                    h(x)=\frac{\sin x+\cos x-1}{2}.
\tag{5}
\]
Each actual edge satisfies the proved G1 inequality
\[
 \phi_i+\ell_i-\ell_{i+1}-\beta h(|d_i|)>\Gamma.
\tag{6}
\]
This is the complete four-type pair theorem, with its common marker,
as recalled in Section 9 of
`HAND_G3_GLOBAL_D_OWNER_BY_CYCLIC_MARKER.md`.
Adding (6) on the three return edges cancels H and G exactly and gives
\[
 \pi+r+v+t-\kappa b_A-F_E
 >3\Gamma+F_A-\kappa b_A
        +\beta\{h(|r|)+h(|v|)+h(|t|)\}.
\tag{7}
\]

The function h is increasing and concave on `[0,7/10]`, and h(0)=0.
Consequently
\[
 h(|r|)+h(|v|)+h(|t|)
       \ge h\bigl(\min(R_0,3/10)\bigr).
\tag{8}
\]
For `R_0<=3/10`, this is ordinary subadditivity. For larger R_0,
decrease the three nonnegative arguments until their sum is 3/10,
use monotonicity, and then use the same subadditivity. This argument
does not require R_0 itself to remain below 7/10.

## 3. A nominal three-edge bound covers every owner

Suppose `R_0<=3/10`. The all-original-axis nominal theorem in
Section 2 of `HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md`
applies separately to these three actual witnesses and gives
\[
              P_{EH}(0)+P_{HG}(0)+P_{GA}(0)\ge3-R_0.
\tag{9}
\]
Both remaining original HG owners have the same nominal projection
`y_H-y_G`. The quarter projections have only two nominal forms:
\[
\begin{array}{c|cc}
 &\text{axis 0 or 1}&\text{axis 2 or 3}\\ \hline
 EH&a_H-b_E&a_E-y_H\\
 GA&a_A+y_G&a_G-b_A.
\end{array}
\tag{10}
\]
The sorted circle gives, at every vertex,
\[
                              a_i+b_i\le2c_0.
\tag{11}
\]
The sum of the three nominal projections in the four intrinsic owner
combinations is as follows:
\[
\begin{array}{c|c|l}
 EH&GA&\text{sum}\\ \hline
 0/1&0/1&a_H+y_H+a_A-b_E\\
 0/1&2/3&a_H+y_H+a_G-y_G-b_E-b_A\\
 2/3&0/1&a_E+a_A\\
 2/3&2/3&a_E+a_G-y_G-b_A.
\end{array}
\tag{12}
\]
Every row is at most `4c_0-b_A`: use `y_H<=b_H`, `-y_G<=b_G`,
`b_E>=0`, (11), and, in the first and third rows,
`a_A<=2c_0-b_A`. No H or G sign is inferred or needed.
Combining (9)--(12) proves the global endpoint constraint
\[
 \boxed{b_A\le4c_0-3+R_0\qquad(R_0\le3/10).}
\tag{13}
\]

## 4. Core, low and middle A charts already have enough margin

For a core A, the unchanged marker formula is
\[
 F_C=7.506931(7/12-a_A)+1.077372b_A.
\]
Since a core primary is at most 7/12, `F_C-kappa b_A>=0`.
Equation (7) is then stronger than (4).

For either outer low or middle chart, the proved whole-chart bound
`F_A>=.86b_A` in
`HAND_G3_BT_PATH_MARKER_AND_NEGATIVE_AB_COMPARISON.md` applies.
Also `b_A/a_A<=3/7` and `a_A<U`. Hence
\[
 3\Gamma+F_A-\kappa b_A
 >3\Gamma-\frac3{25}\frac37\frac{283}{200}
 =\frac{103}{40}+\frac{149}{70000}.
\tag{14}
\]
The nonnegative gain in (7) completes these two charts. At a chart
junction both retained marker formulas satisfy their respective proof.

## 5. The high A chart when the return error is large

On the high outer chart put
\[
 p=\frac{569472}{10^6},\quad s=\frac{390886}{10^6},
 \qquad a(b)=\sqrt{Q-(b+1/2)^2}-\frac12.
\tag{15}
\]
Its exact marker gives
\[
 F_A-\kappa b_A
 =\frac\pi4+(p-s)c_0-p\,a(b_A)-(\kappa-s)b_A.
\tag{16}
\]
The derivative of the right side with respect to b_A is
\[
 p\frac{b_A+1/2}{a(b_A)+1/2}-(\kappa-s)
 \le p+s-\kappa=-\frac{9821}{500000}<0.
\]
Its minimum on this chart is therefore the diagonal value
`pi/4-kappa c_0`.

The exact enclosures
\[
 c_-:=\frac{449607}{500000}<c_0<
 c_+:=\frac{179843}{200000}
\tag{17}
\]
follow by squaring: their positive reserves are respectively
`45551/250000000000` and `104649/40000000000`.
Use `pi>3.14159`, as proved by the explicit Machin comparison
in the marker note cited above.

If `R_0>=3/10`, equations (7)--(8), (16), (17) and the alternating
Taylor lower bound `h(x)>=x/2-x^2/4-x^3/12` give
\[
\begin{split}
 3\Gamma+F_A-\kappa b_A+\beta\sum h
 &>3\Gamma+\frac{3.14159}{4}-\kappa c_+
       +\beta\left(\frac{.3}{2}-\frac{.3^2}{4}
                                      -\frac{.3^3}{12}\right)\\
 &=\frac{103}{40}+\frac{8059}{5000000}.
\end{split}
\tag{18}
\]
This proves (4) throughout this large-error case.

## 6. One strongly convex scalar covers the remaining high chart

It remains that A is on the high outer chart and `R_0<=3/10`.
Set
\[
 \overline B=4c_+-3=\frac{29843}{50000},\quad
 z=b-\overline B,\quad k=\kappa-s,
 \qquad J(b)=-p\,a(b)-kb+\beta h(b-\overline B).
\tag{19}
\]
For b=b_A, (13) gives `z<R_0<=3/10`. If z is nonnegative,
(8), monotonicity and (13) give `sum h>=h(z)`. If z is negative,
`h(z)<=0` while the original three terms are nonnegative; the
same conclusion holds. Thus (7), (16), (17) reduce the claim to
\[
 3\Gamma+F_A-\kappa b_A+\beta\sum h
 >3\Gamma+\frac{3.14159}{4}+(p-s)c_-+J(b_A).
\tag{20}
\]

The high chart satisfies `b/a>=3/7`, so `a<6/5`. Indeed the
corner square at `(a,b)=(6/5,18/35)` exceeds Q by `389/122500`.
On the entire interval between b_A and `b_0=21/25`, we therefore
have `a(b)+1/2<17/10`, and `z<=3/10`. Also
`sin z+cos z<=13/10`: for nonnegative z use `sin z<=z` and
`cos z<=1`; for negative z it is at most one. Differentiating (19),
\[
 J''(b)=\frac{pQ}{(a(b)+1/2)^3}
                -\frac9{100}(\sin z+\cos z)
 >\frac13.
\tag{21}
\]
The exact reserve after substituting the displayed rational bounds is
\[
 \frac{pQ}{(17/10)^3}-\frac9{100}\frac{13}{10}-\frac13
                 =\frac{32506681}{9211875000}>0.
\tag{22}
\]
The reference point b_0 belongs to the high chart and has
`z_0=12157/50000`. The two positive-square comparisons
\[
 \frac{1456021}{10^6}
 <\sqrt{Q-(b_0+1/2)^2}
 <\frac{728011}{500000}
\tag{23}
\]
have reserves `2847559/1000000000000` and
`16121/250000000000`, respectively.

At this one rational reference point,
\[
 J'(b_0)=p\frac{b_0+1/2}{\sqrt{Q-(b_0+1/2)^2}}-k
              +\frac9{100}(\cos z_0-\sin z_0).
\]
Use the two roots in (23), `1-z_0^2/2<=cos z_0<=1-z_0^2/2+z_0^4/24`,
and `z_0-z_0^3/6<=sin z_0<=z_0`. They prove
\[
                             0<J'(b_0)<\frac1{1000}.
\tag{24}
\]
The lower rational expression is
`159140050979749/364005500000000000`; the reserve between 1/1000
and the upper expression is
`2429642483151737252688337/7280105000000000000000000000`.

Integrating (21) and completing one square gives, for every b in
the full interval under consideration,
\[
 J(b)\ge J(b_0)+J'(b_0)(b-b_0)+\frac16(b-b_0)^2
 >J(b_0)-\frac{3}{2000000}.
\tag{25}
\]
Finally, substitute the upper root in (23) into `-p a(b_0)` and
the lower cubic `h(z_0)>=z_0/2-z_0^2/4-z_0^3/12` into J(b_0).
The resulting exact rational comparison is
\[
\begin{split}
 &3\Gamma+\frac{3.14159}{4}+(p-s)c_-
   -p\left(\frac{728011}{500000}-\frac12\right)-k\frac{21}{25}
   +\beta\left(\frac{z_0}{2}-\frac{z_0^2}{4}-\frac{z_0^3}{12}\right)
   -\frac{3}{2000000}-\frac{103}{40}\\
 &\hspace{35mm}=\frac{15155937748321}{25000000000000000}>0.
\end{split}
\tag{26}
\]
Equations (20), (25), (26) prove (4) on the remaining entire chart.

The proof uses the already established common G1 markers, the three
actual witness inequalities, four intrinsic nominal owner combinations,
one global curvature estimate and one rational reference point. Neither
a numerical minimum nor an angle or state cover is a premise. The
complementary four-edge charge remains an explicit additional task.
