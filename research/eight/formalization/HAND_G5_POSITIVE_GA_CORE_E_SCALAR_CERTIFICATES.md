# Seven scalar certificates for positive GA entry with core E

## 1. The scalar statements

Use the constants and two coefficient families in
[the angular envelope](HAND_G5_POSITIVE_GA_CORE_E_ANGULAR_ENVELOPE.md):
\[
 Q=9789/2500,\quad R=\sqrt Q,\quad h=7/10,\quad
 K=13/12,\quad k=.863,
\]
\[
\begin{array}{c|c|c|c|c}
 &l&c&\eta&\lambda\\ \hline
 P&.5052+.49d-.108d^2&k&.25+.1645d&1.03\\
 N&.5054+.55d-.2d^2&.863+.35d-.15d^2&.38&.8888+.2d.
\end{array}
\tag{1}
\]
All terminating decimals in this note are rational constants.
For either family put
\[
 f(d)=\cos d+\eta\sin d,\quad n=kf(d),\qquad
 C_\eta(d)=1+2\cos d+
              \{1+2\eta-R\sqrt{1+\eta^2}\}\sin d,
\tag{2}
\]
and define the two base scalars
\[
\begin{split}
 B_P(d)={}&3+2l+3k+kC_\eta(d)\\
 &-R\{2\sqrt{1+k^2}+\sqrt{k^2+l^2}+\sqrt{l^2+n^2}\},\\
 B_N(d)={}&3+2l+3c+kC_\eta(d)\\
 &-R\{\sqrt{1+n^2}+\sqrt{k^2+l^2}
                  +\sqrt{l^2+c^2}+\sqrt{1+c^2}\}.
\end{split}
\tag{3}
\]
Write
\[
 \begin{split}
 V(d)&=k(\cos d-1)
    -R\{\sqrt{k^2+l^2-2kl\sin d}-\sqrt{k^2+l^2}\},\\
 J(e)&=-\sin e/12-K(1-\cos e),\qquad A(l)=l-.0696.
 \end{split}
\tag{4}
\]
The seven required strict inequalities on the entire interval
\(0\le d\le h\) are
\[
\begin{array}{c|l}
 PV&B_P+V>0\\
 PL&B_P+1.03d>0\\
 PE&B_P+J(h-d)+A(l)>0\\ \hline
 NV&B_N+V>0\\
 NL&B_N+\lambda d>0\\
 NE&B_N+J(h-d)+A(l)>0\\
 NET&B_N+J(h-d)+\lambda h>0.
\end{array}
\tag{5}
\]
The family coefficient l in each row is the one in (1).
Sections 2--4 give a single explicit polynomial construction
for every row. Section 5 records the auxiliary exact bounds
used by the angular envelope. These are whole-interval
coefficient identities; there is no subdivision of the angle
interval and no sampled acceptance premise.

## 2. A rational coefficient norm

For any rational polynomial p and rational interval [a,b], put
\[
 p\left(\frac{a+b}{2}+\frac{b-a}{2}u\right)
       =\sum_{j=0}^D v_ju^j=\sum_{j=0}^D b_jT_j(u).
\tag{6}
\]
Here \(T_j\) is the Chebyshev polynomial, and its exact
coefficients in this identity are
\[
 b_0=\sum_{2i\le D}v_{2i}2^{-2i}\binom{2i}{i},\qquad
 b_j=\sum_{\substack{i\ge j\\i-j\ {\mathrm{even}}}}
          v_i2^{1-i}\binom i{(i-j)/2}\quad(j\ge1).
\tag{7}
\]
Define
\[
 \mathscr L_{[a,b]}p=b_0-\sum_{j\ge1}|b_j|,
 \qquad
 \mathscr U_{[a,b]}p=b_0+\sum_{j\ge1}|b_j|.
\tag{8}
\]
Since \(|T_j(u)|\le1\) for \(|u|\le1\), these are lower
and upper bounds throughout [a,b]. Equations (6)--(8)
specify a finite rational calculation directly from p; they
require neither numerical polynomial fitting nor a list of
sampled angles. Unless a different interval is displayed,
\(\mathscr L,\mathscr U\) below mean [0,h].

Use the usual rational Taylor polynomials
\[
 S_j(d)=\sum_{i=0}^{(j-1)/2}\frac{(-1)^id^{2i+1}}{(2i+1)!},
 \qquad
 C_j(d)=\sum_{i=0}^{j/2}\frac{(-1)^id^{2i}}{(2i)!}.
\tag{9}
\]

## 3. The seven polynomial builders

For this section only, let
\[
 S=S_{15}(d),\quad C=C_{16}(d),\quad
 n_*=k(C+\eta S),\quad R_+=1.978787508,\quad
 \epsilon=10^{-12}.
\tag{10}
\]
The strict square inequality \(R_+^2>Q\) is exact. Start
the polynomial demand with
\[
                    D=3+2l+3c+k\{1+2C+(1+2\eta)S\}.
\tag{11}
\]
Each row below is a triple \((v,a,w)\), representing the
radical term \(w\sqrt v\). The rational positive mass a
gives its upper bound
\[
                    w\sqrt v\le w(v+a^2)/(2a).
\tag{12}
\]

For family P use these rows:
\[
\begin{array}{c|c|c}
v&a&w\\ \hline
1+k^2&(21+20k)/29&2\\
k^2+l^2&(4k+3l)/5&1\\
l^2+n_*^2&(3l+4n_*)/5&1\\
1+\eta^2&(24+7\eta)/25&kS.
\end{array}
\tag{13}
\]
For family N use these rows:
\[
\begin{array}{c|c|c}
v&a&w\\ \hline
1+n_*^2&(21+20n_*)/29&1\\
k^2+l^2&(4k+3l)/5&1\\
l^2+c^2&(3l+4c)/5&1\\
1+c^2&(21+20c)/29&1\\
1+\eta^2&(24+7\eta)/25&kS.
\end{array}
\tag{14}
\]
For a V row in (5), delete the row \(k^2+l^2\) from
(13) or (14), add \(k(C-1)\) to D, and add instead
\[
           (v,a,w)=
   (k^2+l^2-2klS,\ 1-.2d-.33d^2,\ 1).
\tag{15}
\]
This deletion is the exact cancellation of the positive
\(R\sqrt{k^2+l^2}\) term in V against (3), before any
radical is estimated.

For an L row, add \(\lambda d\) to D. For an E row, add
\[
       -S_{15}(h-d)/12-K\{1-C_{16}(h-d)\}+l-.0696.
\tag{16}
\]
For the ET row add the same expression with \(l-.0696\)
replaced by \(\lambda h\). These instructions, (1), and
(10)--(16) specify all the polynomial data.

If the resulting rows are \((v_j,a_j,w_j)\), let
\[
 M=\prod_j a_j,\qquad
 \mathcal P=2(D-\epsilon)M
           -R_+\sum_jw_j(v_j+a_j^2)\prod_{i\ne j}a_i.
\tag{17}
\]
All rows have \(w_j\ge0\), all radicands are positive,
and (7)--(8) give
\[
                            .69<a_j<1.5.
\tag{18}
\]
Thus (12) is legitimate, and multiplication by M preserves
the inequality direction.

The Taylor replacement has a uniform error smaller than
\(\epsilon\). Indeed
\[
 |S_{15}(u)-\sin u|<h^{17}/17!<7\cdot10^{-18},\qquad
 |C_{16}(u)-\cos u|<h^{18}/18!<3\cdot10^{-19}
\tag{19}
\]
for \(u=d\) and \(u=h-d\). Along the segment between the
exact and Taylor data, every radicand in (13)--(15) exceeds
.14. For the smallest one use
\[
 k^2+l^2-2kl\sin d=(k-l\sin d)^2+l^2\cos^2d
                              >.5052^2(.7648)^2>.149.
\]
The same bound with .14 holds throughout that segment by
(19). All coefficients are below 2, there are at most five
radical rows, and direct differentiation of (3)--(4) bounds
each partial derivative with respect to the four sine/cosine
inputs by 1000. This deliberately loose bound makes the
total replacement error less than
\(1000\{2(7\cdot10^{-18})+2(3\cdot10^{-19})\}<10^{-12}\).
Consequently every exact scalar F in (5) satisfies
\[
                              F>\frac{\mathcal P}{2M}.
\tag{20}
\]
The use of \(R_+\) only decreases the right side because
every remaining radical enters with a negative sign.

## 4. Whole-interval reserves

Applying the single rational operator (7)--(8) to (17)
gives
\[
\begin{array}{c|c|c}
\text{row}&\deg\mathcal P&\mathscr L\mathcal P\text{ is greater than}\\ \hline
PV&35&.00870\\
PL&35&.00334\\
PE&35&.02316\\
NV&38&.01173\\
NL&38&.00938\\
NE&38&.15688\\
NET&38&.14079.
\end{array}
\tag{21}
\]
These inequalities are rational coefficient inequalities
specified by (1), (7), and (10)--(17), rather than numerical
values of trigonometric functions. Together with (18) and
(20), they prove all seven claims in (5), including d=0
and d=h.

## 5. Exact auxiliary bounds for the angular envelope

The following checks use the same coefficient operator.
They make the longer angular proof reproducible without
introducing any additional interval partition.

For \(r(d)=.585+.255d\), the coefficient comparisons are
\[
 \mathscr L\{l_P-rk(1+d/4)\}>.000344,\quad
 \mathscr L\{l_N-rc_N\}>.000544,\quad
 \mathscr L\{r-S_9\}>.095.
\tag{22}
\]
For the degree-70 polynomial \(\mathcal P_B\) defined in
(15) of the angular envelope,
\[
            \mathscr L\mathcal P_B>.07925,\qquad
            \mathscr L\{2r-(1+r^2)S_9\}>.5022.
\tag{23}
\]
Its numerator has an exact double zero at d=0, so its
division by \(d^2\) is polynomial division, including at
zero. All branch signs required for its two positive
squares are supplied by (22)--(23).

For the two low-coefficient secant comparisons, put
\[
 \mathcal Q_{q,a,b}(d)=
 \{q(C_{10}-1)+aS_{11}+bS_{11}^2-.71286d+.2398d^2\}/d.
\tag{24}
\]
Again the quotient is a polynomial. The exact bounds are
\[
 \mathscr L\mathcal Q_{k,.8627,.1880}>.0704,\qquad
 \mathscr L\mathcal Q_{1,.8922,.1795}>.0465.
\tag{25}
\]
The coefficient squares justifying a and b are, with
\(p=.5052,A=p^2+q^2\),
\[
                       a^2A<Qp^2q^2,\qquad
                       4b^2A^3<Qp^4q^4.
\tag{26}
\]

For the common secant gain use the polynomial
\[
 \mathcal T(d)=
 \{KS_{11}-1.03dC_{12}-1.613775(1-C_{10})
                      +.557855S_{11}^2+.059531S_{11}^4\}/d.
\tag{27}
\]
Its degree is 43. Expand it exactly as
\(\mathcal T(.45+z)=\sum b_jz^j\). Rational arithmetic gives
\[
 b_0>.0019416,\quad |b_1|<.000845,\quad
 b_2-\sum_{j\ge3}|b_j|(.45)^{j-2}>.12849,
\]
\[
 b_0-\frac{b_1^2}
  {4\{b_2-\sum_{j\ge3}|b_j|(.45)^{j-2}\}}>.0019402.
\tag{28}
\]
Since \(|d-.45|\le.45\) throughout [0,h], the completed
square in (28) proves positivity on the whole interval.
The three positive squares required to pass from (27) to
the actual gain are
\[
 \begin{split}
 (2.613775)^2&>Q(1+k^2),\\
 4(.557855)^2(1+k^2)&<Qk^4,\\
 64(.059531)^2(1+k^2)^3&<Qk^8.
 \end{split}
\tag{29}
\]

For the far negative endpoint set \(R_-=1.9787875\), so
\(R_-^2<Q\). The following brackets are exact rational
numbers for \(\sqrt{p^2+q^2}\) from below and
\(\sqrt{p^2+q^2-2pqS_{11}(h)}\) from above:
\[
\begin{array}{c|c|c|c}
p&q&a_-&a_+\\ \hline
.5052&.863&.999998019&.662007699\\
.5052&1.04&1.156212368&.812325543\\
.8&.863&1.176762083&.703728085\\
.8&1.04&1.312097557&.805991172.
\end{array}
\tag{30}
\]
Each bracket is verified simply by squaring. Substitution
in
\[
        q\{C_{10}(h)-1\}+R_-(a_--a_+)-p+.0696
\tag{31}
\]
gives, respectively, strict lower bounds
.03026, .000314, .00269, and .02651. These are the four
corners of a separately concave function on a coefficient
rectangle, not four selected angles.

Finally, the explicit local bounds needed for negative T
entry are the positive rational checks
\[
 \begin{split}
 .4-.085C_6(.3)-KS_7(.3)&<0,\\
 1+K^2+.6^2+1.2C_6(.09)+2KS_7(.09)&>Q,\\
 (1.78)^2\{1+.25C_6(.09)^2\}&>Q,\\
 K-.39(.09)&>1.048.
 \end{split}
\tag{32}
\]
The coefficient gains obey
\[
 \begin{split}
 1.03c_N-\lambda_N&=.00009+.1605d-.1545d^2>0,\\
 1.048c_N-\lambda_N&=.015624+.1668d-.1572d^2>0.
 \end{split}
\tag{33}
\]
Both are concave quadratics and are positive at 0 and h.

The positive split uses these further exact squares:
\[
 Q(.92)^2<(1.45)^2\{1+(.92)^2\},\qquad
 Q(.92)^2<(1.75)^2\{(.5052)^2+(.92)^2\},
\]
\[
 \begin{split}
 (1+.55e+.907)^2&>Q(1+e^2),\\
 (1+.25e+1.017)^2&>Q(1+e^2)
            \qquad(e\in\{.25,.36515\}).
 \end{split}
\tag{34}
\]
Its two trigonometric coefficients are bounded by
\[
 -.55-.25C_{10}(h)+1.017S_9(h)<-.085,
\]
\[
 .907-.25S_{11}(h)-1.017C_{10}(h)<-.03,
                       \qquad .907-1.017<-.03.
\tag{35}
\]
The remaining elementary slope and ratio bounds in the
angular envelope follow from its displayed rational
constants and the same alternating Taylor bounds.
No result in this note depends on floating-point output,
Lean compilation, or CI.
