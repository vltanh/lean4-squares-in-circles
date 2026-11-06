# Four further sharp guards from one parameter inequality

The [uniform one-tenth terminal](CB882_UNIFORM_SHARP_TERMINAL.md)
retains a comparatively wide height allowance. This chapter gives
four additional complete guards permitting larger tilts when the
height differences are better controlled. Each row is a continuous
pen-and-paper theorem on its entire stated guard. No cover of the
guards' complement is asserted.

## 1. Guard parameters and conclusion

Retain seven distinct physical originals A,B,I,D,E,F,G with disjoint
interiors and all corners in the closed Q-disk, Q=1105/256. Use their
original frame variables alpha_P,beta_P and projection widths h_P.
For one row of the tables below, assume

\[
\begin{gathered}
 0\le\beta_A\le s,\quad -s\le\beta_D\le0,
 \quad |\beta_P|\le s\ (P=B,I,E,F,G),\\
 x_A\le x_B\le x_I\le x_D,\quad x_B-x_A\ge h_A+h_B,\\
 x_F-x_E\ge h_E+h_F,\quad x_G-x_F\ge h_F+h_G,\\
 -L\le y_I-y_B\le H,\quad |y_D-y_I|\le J:=1/10,\\
 1/3\le x_E-x_A\le2/3,\quad 0<y_E-y_A\le v,\\
 1/3\le x_D-x_G\le2/3,\quad 0<y_G-y_D\le v.
\end{gathered}                                                   \tag{1}
\]

**Theorem.** Every row forces all seven tilts to vanish and gives

\[
 c_A=(-3/2,-1/16),\quad c_D=(3/2,-1/16),\quad
 c_E=(-1,15/16),\quad c_G=(1,15/16),
 \qquad x_B=-1/2,\ x_I=1/2,\ x_F=0.                    \tag{2}
\]

The retained original actual AB,BC and strictly weak CD conditions
therefore exclude each guard in the full Cb882 caller.

| Row | s | L | H | v |
|---:|---:|---:|---:|---:|
| 1 | 1/8 | 1/20 | 37/50 | 5/2 |
| 2 | 1/7 | 3/100 | 17/25 | 2 |
| 3 | 1/6 | 1/50 | 33/50 | 19/10 |
| 4 | 1/5 | 1/200 | 29/50 | 3/2 |

The proof constants are as follows; put kappa=s/(1+a_0) in each row.

| Row | a_0 | c_1 | c_2 | eta | gamma | lambda |
|---:|---:|---:|---:|---:|---:|---:|
| 1 | 991/1000 | 467/1000 | 43/100 | 1/150 | 13/40 | 1/4 |
| 2 | 989/1000 | 463/1000 | 211/500 | 1/125 | 13/40 | 51/200 |
| 3 | 197/200 | 457/1000 | 51/125 | 11/1000 | 8/25 | 27/100 |
| 4 | 979/1000 | 56/125 | 97/250 | 3/200 | 159/500 | 147/500 |

## 2. A common physical support inequality

The positive reserve 1-s^2-a_0^2 gives alpha>=a_0 and
1-alpha<=kappa abs(beta). For two original signed tilts b,f,
the concavity argument in Section 2 of the uniform terminal applies
with p=max(abs(b),abs(f)), q=min(abs(b),abs(f)). At q=0 the
relative support excess is at least ((1-kappa)/2)p; at q=p it
is zero for equal signs and at least (a_0-s)p for opposite signs.
Consequently the two comparisons

\[
 c_1\le(1-\kappa)/2,\qquad c_2\le(a_0-s)/2
\]

and the same endpoint chords prove

\[
 R(b,f)\ge1+c_2|b-f|+(c_1-c_2)\bigl||b|-|f|\bigr|.   \tag{3}
\]

All four rows have c_1>c_2>=1/3, H>=L>=0, H>=J and H<1.

## 3. Horizontal separators and their total slope loss

The incircles force positive BI and ID horizontal gaps. Actual AB
and the universal center bound rho=91/60 give x_B>1-rho;
B<=I<=D then bounds each horizontal gap by 2rho-1=61/30.
A secondary normal has absolute projection at most s(61/30)+H<1.
A negative primary normal has projection at most sH<1. Thus both
physical separators are positive primary normals owned by one of
the two corresponding originals. Their normalized inequalities are
Delta_x>=R-t_O Delta_y, t_O=beta_O/alpha_O.

Put b=beta_B, i=beta_I, delta=-beta_D and

\[
\begin{aligned}
 T&=|b|+|i-b|+|i+\delta|,\\
 W&=|b|+\bigl||i|-|b|\bigr|+\bigl||i|-\delta\bigr|.
\end{aligned}
\]

As lengths of real-line paths, T,W>=delta. Also
P=max(b,i,0)<=(T-delta)/2 and
N=max(-b,-i,0)<=(T+delta)/2. Therefore
Z=max(abs(i),delta)<=(T+delta)/2.

The BI slope loss is at most max(HP,LN)/a_0. Since H>=L,
this is at most ((H/2)(T-delta)+L delta)/a_0. The ID loss
is at most JZ/a_0. Their sum is at most

\[
 \frac{H+J}{2a_0}(T-\delta)+\frac{L+J}{a_0}\delta.
\]

Combine this with (3) and actual AB to obtain

\[
\begin{aligned}
 x_D-x_A\ge{}&2+(\alpha_A+\alpha_B)/2+\beta_A/2
                       +(1/2-c_1)|b|\\
 &+k_D\delta+k_T(T-\delta)+(c_1-c_2)(W-\delta),\\
 k_D={}&c_1-(L+J)/a_0,\qquad
 k_T=c_2-(H+J)/(2a_0).                                 \tag{4}
\end{aligned}
\]

## 4. Vertical separators

On A,E, every primary normal has absolute projection at most
2/3+sv<1. Every downward secondary normal has projection at
most 2s/3<1. The physical separator is consequently upward,
owned by A or E. Normalization of its slope costs at most
eta abs(beta_O), since eta>=(2/3)(1/a_0-1).
Using the weaker part R>=1+c_2 abs(beta_E-beta_A) of (3), its
inequality gives, with d=x_E-x_A in [1/3,2/3],

\[
 y_E-y_A\ge1+c_2|\beta_E-\beta_A|
                         +d\beta_O-\eta|\beta_O|.
\]

If O=A, the gain is at least (1/3-eta)beta_A. If O=E and
beta_E>=0, the inequality c_2>=1/3 gives
c_2 abs(beta_E-beta_A)+d beta_E>=beta_A/3.
If O=E and beta_E<0, the angular contribution is at least
c_2 beta_A-(2/3-c_2+eta)abs(beta_E).
Thus the comparisons

\[
 \gamma\le1/3-\eta,\quad\gamma\le c_2,\quad
 \lambda\ge\eta,\quad\lambda\ge2/3-c_2+\eta
\]

prove y_E-y_A>=1+gamma beta_A-lambda abs(beta_E) in every
case. Reflect the D,G pair horizontally to obtain

\[
\begin{aligned}
 y_E-y_A&\ge1+\gamma\beta_A-\lambda|\beta_E|,\\
 y_G-y_D&\ge1+\gamma\delta-\lambda|\beta_G|.            \tag{5}
\end{aligned}
\]

The following literal reserves check every nontrivial comparison
used in Sections 2--4. Strict positivity is stronger than required
for the non-strict coefficient comparisons.

| Reserve | Row 1 | Row 2 | Row 3 | Row 4 |
|---|---:|---:|---:|---:|
| 1-s^2-a_0^2 | 1147/500000 | 72071/49000000 | 719/360000 | 1559/1000000 |
| (1-kappa)/2-c_1 | 3203/1991000 | 15151/13923000 | 1213/1191000 | 727/494750 |
| (a_0-s)/2-c_2 | 3/1000 | 3/2800 | 7/6000 | 3/2000 |
| eta-(2/3)(1/a_0-1) | 91/148650 | 217/370875 | 167/197000 | 137/195800 |
| 1/3-eta-gamma | 1/600 | 1/3000 | 7/3000 | 1/3000 |
| c_2-gamma | 21/200 | 97/1000 | 11/125 | 7/100 |
| lambda-eta | 73/300 | 247/1000 | 259/1000 | 279/1000 |
| lambda-(2/3-c_2+eta) | 1/150 | 7/3000 | 1/3000 | 1/3000 |
| 1-s(61/30)-H | 7/1200 | 31/1050 | 1/900 | 1/75 |
| 1-2/3-sv | 1/48 | 1/21 | 1/60 | 1/30 |

## 5. Exact corner coefficients and equality

Use the same four actual corners and positive weighted sum S as
Sections 4--5 of the uniform terminal. In particular S<=32Q and

\[
\begin{aligned}
 S={}&23(x_D-x_A)+(27/4)(x_G-x_E)\\
 &+(207/32)((y_E-y_A)+(y_G-y_D))\\
 &+(943/64)(\alpha_A+\alpha_D)-(529/64)(\beta_A+\delta)\\
 &+(423/64)(\alpha_E+\alpha_G)+(9/64)(\beta_E-\beta_G).
\end{aligned}
\]

Use (4), (5), actual EFG, and 1-alpha<=kappa abs(beta).
The constant part is exactly 32Q, and the remaining inequality is

\[
\begin{aligned}
 S-32Q\ge{}&K_A\beta_A+K_B|b|+K_D\delta
       +K_E(|\beta_E|+|\beta_G|)+K_F|\beta_F|\\
 &+K_T(T-\delta)+K_W(W-\delta).                        \tag{6}
\end{aligned}
\]

Writing j=207/32, the seven coefficients are, in order,

\[
\begin{gathered}
 23/2+\gamma j-529/64-\kappa(1679/64),\\
 23(1/2-c_1)-\kappa(23/2),\\
 23k_D+\gamma j-529/64-\kappa(943/64),\\
 27/8-\lambda j-9/64-\kappa(639/64),\\
 (27/4)(1-\kappa),\qquad23k_T,\qquad23(c_1-c_2).
\end{gathered}                                                   \tag{7}
\]

Here are all their exact positive values.

| Coefficient | Row 1 | Row 2 | Row 3 | Row 4 |
|---|---:|---:|---:|---:|
| K_A | 9403021/2548480 | 61528013/17821440 | 5910517/1905600 | 83598077/31664000 |
| K_B | 73669/1991000 | 348473/13923000 | 27899/1191000 | 16721/494750 |
| K_D | 10817253947/63138592000 | 7743435127/19158048000 | 518434421/1877016000 | 4326286407/30999056000 |
| K_E | 252387/254848 | 8591221/9900800 | 825117/1270400 | 10244259/31664000 |
| K_F | 25191/3982 | 38769/6188 | 9819/1588 | 48033/7916 |
| K_T | 14099/99100 | 13679/21500 | 12581/24625 | 229149/244750 |
| K_W | 851/1000 | 943/1000 | 1127/1000 | 69/50 |

Every term in (6) is nonnegative. Therefore all the displayed beta
terms vanish and T=0, forcing beta_I=0 as well. Equality in the
four positively weighted corner inequalities then gives the four
anchors in (2). Aligned BI,ID with height gaps below one have
horizontal gaps at least one; together with actual AB their three
gaps sum to three. Actual EFG likewise has two gaps summing to two.
This proves the remaining coordinates in (2).

For the retained Cb882 caller, actual BC yields x_C>=h_C and
the CD cone and contained insets give x_C<=1-g_C. Equality
h_C+g_C=1 forces x_C=h_C=g_C=1/2. Thus CD is actual,
contrary to its retained strictly weak bit. No frame has been
replaced or discarded.

## 6. What each finite use must certify

The ten target vectors in the
[guard certificate chapter](CB882_SHARP_GUARD_ROW_CERTIFICATES.md)
remain the same, with the BI lower and upper right sides replaced
by L and H. Add the two targets

\[
                         y_E-y_A\le v,\qquad y_G-y_D\le v.
\]

Each of these twelve targets must be supplied by the proved box,
a literal nonnegative row sum with residual payment, or an explicit
previously proved whole-parent bound. The angular endpoint checks
must use the same row's s. The table row, inherited A,D signs,
physical hypotheses, actual AB/EF/FG and strict upper endpoint
orders must all be retained.

For row 1, the two added targets already hold throughout Cb882:
the [left-cap proof](CD402_H_ABOVE_B.md) gives abs(y_A)<1/4,
and x_D>4/3 with the center bound gives abs(y_D)<3/4. The latter
comparison has reserve 9/16-(rho^2-16/9)=1/25. Hence the two
endpoint height differences are less than rho+3/4=34/15<5/2.
For rows with a smaller v, that automatic estimate does not by
itself certify both targets. Their remaining gap must be proved.
