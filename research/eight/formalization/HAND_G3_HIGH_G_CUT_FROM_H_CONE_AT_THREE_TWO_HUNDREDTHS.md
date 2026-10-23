# The remaining G cut follows from the H cone at S <= 3/200

## 1. The theorem and its precise dependency

Assume the actual G0--G2 candidate geometry with
\[
q\le Q=9789/2500,\qquad
S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le\sigma:=3/200.
\tag{1}
\]
Use the roles \((H,G,A,B,T,D,E)\), quarter word \(0101011\),
own-frame centers \((a_i,-y_i)\), and \(a_i\ge |y_i|\). Retain the
G2 normalization \(y_E\le0\), the concentrated real frames, and the
global zero-primary theorem: every feasible original witness on
HG, AB and TD belongs to axes \(\{0,2\}\).

If in addition
\[
y_H\ge a_H/2,                                        \tag{2}
\]
then
\[
\boxed{u_G=y_G/a_G>-4/5.}                             \tag{3}
\]

No G, T or D tangent cut is an input. No sign on the six zero-edge
roles, quarter owner, mixed owner, tilt window beyond G2, or
radial-boundary kind is assumed. The quarter directions used below
are obtained in forward order from the cut-free theorems at
\(S\le1/32\), a weaker mismatch hypothesis than (1):

- [Every DE witness has its intended quarter direction](HAND_G3_D_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md).
- [Every BT witness has its intended quarter direction](HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md).

Only the resulting BT direction is needed here. The conclusion is
conditional on both (1) and (2); this note does not prove either
capture hypothesis and does not close global G3. In particular it
allows the remaining H cone to be proved first, without importing
the G cut established here.

## 2. Nominal inequalities and a stronger A bound

Set \(L=447/800\) and \(U=283/200\). Actual corner containment and
the entry core bound give
\[
(a_i+1/2)^2+(|y_i|+1/2)^2\le Q,\qquad
a_i>L,\quad |p_i|<U,\quad |y_i|<9/10,\quad
a_i+|y_i|<9/5.                                      \tag{4}
\]
The center norm and the all-axis nominal estimate are proved in
[the center-norm note](HAND_G3_CENTER_NORM_AND_HIGH_TAIL_DIRECTIONS.md),
Sections 1--2. With \(e_i=|d_i|\), every feasible original aligned
witness has nominal projection at least \(1-e_i\). This applies
to either error sign and every original axis, including ties.

Since \(1-\sigma>9/10\), the three actual zero edges and (4) force
\[
(y_H,y_G,y_A,y_B,y_T,y_D)
=(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad b_i>0,
\quad b_E=-y_E\ge0.                                 \tag{5}
\]
The cut-free BT theorem now applies. Retaining an actual witness on
each relevant edge yields
\[
\begin{split}
b_H+b_G&\ge1-e_H,\\
b_A+b_B&\ge1-e_A,\\
a_B-b_T&\ge1-e_B,\\
b_T+b_D&\ge1-e_T.
\end{split}                                         \tag{6}
\]

First sharpen the transverse bound at D:
\[
b_D<8993/10000,                                      \tag{7}
\]
because \(a_D\ge b_D\) and
\[
2(8993/10000+1/2)^2-Q=24049/50000000>0.
\]
Put \(z=e_A\), so \(0\le z\le\sigma\). The BT--TD part of (6),
the shared budget, and (7) give
\[
a_B+1/2>5/2-8993/10000-\sigma+z
=15857/10000+z.                                     \tag{8}
\]
If \(b_A\le79/250\), the AB part of (6) would also give
\[
b_B+1/2\ge148/125-z>0.
\]
Squaring these positive lower bounds in the B corner inequality
would imply
\[
\begin{split}
Q
&>(15857/10000+z)^2+(148/125-z)^2\\
&=Q+\frac{70049}{100000000}
       +\frac{4017}{5000}z+2z^2>Q,
\end{split}
\]
which is impossible. Thus the A corner, with its exact endpoint
reserve, proves
\[
\boxed{b_A>B_*:=79/250,\qquad a_A<A_*:=1303/1000,}
\tag{9}
\]
\[
(1303/1000+1/2)^2+(79/250+1/2)^2-Q=213/200000>0.
\]
The only budget use in (8)--(9) is the shared sum in (1).

Normalize \(\theta_A=0\), and write
\[
t=\theta_G-\theta_A,\quad c=\cos t,\quad s=\sin t,
\quad r=|s|,\quad W=(1+c+r)/2.
\]
The concentrated frames give
\[
|t|<7/10,\qquad c\ge3/4,\quad 0\le r\le13/20,
\quad c^2+r^2=1,\quad 1-c\le(4/7)r^2.                \tag{10}
\]
GA is used at its actual phase \(\pi/2-t\). The nominal EH phase
is \(\pi/2+t\), differing from its actual phase by
\(-d_H-d_A-d_B-d_T-d_D\). Since \(|p_i|<U\) and the support
width is \(1/2\)-Lipschitz, every feasible original EH axis obeys
\[
P_E^{\rm nominal}\ge W-2S.                           \tag{11}
\]
The coefficient two bounds \(U+1/2=383/200<2\).
Consequently a combination with HG weight at most one and EH
weight at most one loses at most
\[
e_H+2S\le3S\le9/200.                                \tag{12}
\]

## 3. A high G leaves only GA axes 1 and 3, at negative tilt

Suppose, towards a contradiction, that \(u_G\le-4/5\). Then
\[
b_G\ge(4/5)a_G>447/1000,\qquad a_G<1.                 \tag{13}
\]
Indeed \(a_G\ge1\) would put its corner beyond Q, since
\((3/2)^2+(13/10)^2=197/50>Q\).

The four exact GA projections, in their original indexing, are
\[
\begin{array}{c|l}
0&c a_A-s b_A-b_G\\
1&a_A-s a_G-c b_G\\
2&c a_G-s b_G-b_A\\
3&a_G-s a_A-c b_A.
\end{array}                                         \tag{14}
\]
Axis 0 is impossible at every angle: its projection is at most
\[
|p_A|-b_G<U-447/1000=121/125<1\le W.
\]
If \(s\ge0\), axis 1 has the strict gap
\[
W-P_{G1}>
-183/200+(947/1000)c+(847/800)s
\ge4/125>0,
\]
using \(c+s\ge1\). The other two projections in (14) are then
at most \(a_G<1\). Thus any feasible original GA witness forces
\[
s=-r<0.                                             \tag{15}
\]

We also have a stronger norm bound on this high-G tail:
\[
|p_G|<32/25.                                         \tag{16}
\]
To see this, put \(v=b_G/a_G\in[4/5,1]\) and
\(R=|p_G|\). The concave quadratic \(50v-24-24v^2\) is
positive on this interval: its endpoint values are \(16/25\) and
2. Therefore
\[
(a_G+b_G)^2-\frac{49}{25}R^2
=\frac{a_G^2}{25}(50v-24-24v^2)>0.
\]
The G corner gives \(R^2+(7/5)R+1/2<Q\), whereas at \(R=32/25\)
the left side minus Q is \(37/2500>0\), proving (16).

If original GA axis 2 were feasible, adding its exact projection
to AB, intended BT and TD in (6) would give
\[
c a_G+r b_G+(a_B+b_B)+b_D
\ge W+3-(e_A+e_B+e_T)\ge4-\sigma.
\]
By (4) and (16), the left side is strictly below
\(32/25+9/5+9/10=199/50\). This is impossible because
\[
4-\sigma-199/50=1/200>0.                             \tag{17}
\]
Every possible actual GA witness is now in \(\{1,3\}\), with
negative sine, independently of the H cone.

## 4. The H cone bounds the entire remaining EH arc

By (2), (4) and (5),
\[
b_H\ge a_H/2>L/2,\qquad a_H<H_*:=29/25.              \tag{18}
\]
The upper bound uses the exact corner reserve
\[
(29/25+1/2)^2+(29/50+1/2)^2-Q=4/625>0.
\]
On (15), the four nominal EH projections are
\[
\begin{array}{c|l}
0&c a_H-r b_H-b_E\\
1&a_H-r a_E-c b_E\\
2&c a_E-r b_E-b_H\\
3&a_E-r a_H-c b_H.
\end{array}                                         \tag{19}
\]
Each feasible original EH witness must obey (11).

For axis 0, \(c-r/2>0\), so (18)--(19) give
\[
W-P_{E0}>
\frac12-\frac{33}{50}c+\frac{27}{25}r
\ge-\frac4{25}+\frac{27}{25}r.
\]
Feasibility implies \(r<19/108<1/5\), since \(2S\le3/100\).

For axis 1, use \(a_E>L\) and \(b_E\ge0\):
\[
W-P_{E1}>
-\frac4{25}+\left(\frac12+L\right)r-\frac27r^2.
\]
This lower polynomial is increasing on \([0,13/20]\).
At \(r=1/5\), its value minus \(3/100\) is \(289/28000>0\).
Hence feasibility forces \(r<1/5\).

For axis 3, (4) and (18) give
\[
W-P_{E3}>
-\frac{183}{200}
+\left(\frac12+\frac L2\right)c
+\left(\frac12+L\right)r.                            \tag{20}
\]
The right side increases on \(0\le r\le13/20\), with
\(c=\sqrt{1-r^2}\): its derivative is
\[
\left(\frac12+L\right)
-\left(\frac12+\frac L2\right)\frac r c> L/2>0,
\]
because \(r/c\le13/15<1\). At \(r=9/50\), one has \(c>49/50\);
using \(49/50\) in (20), the value minus \(3/100\) is
\(749/80000>0\). Thus feasibility forces \(r<9/50<1/5\).

For axis 2, use \(a_E<U\), \(b_E\ge0\), and
\(c\le1-r^2/2\):
\[
W-P_{E2}>
\frac L2-\frac{83}{200}+\frac r2+\frac{183}{400}r^2.
\]
This polynomial increases for \(r\ge0\). At \(r=27/100\),
its value minus \(3/100\) is \(10907/4000000>0\).
Hence feasibility forces \(r<27/100\).

Every originally feasible EH witness therefore supplies one of
the following bounds:
\[
\begin{array}{c|c|c}
\text{EH axis}&r&c\\\hline
0,1,3&r<1/5&c>97/100\\
2&r<27/100&c>24/25.
\end{array}                                         \tag{21}
\]
The cosine bounds follow by squaring, using \(c>0\).

## 5. Exclusion of the two remaining GA witnesses

If original GA axis 3 were feasible, (9), (13), and the weaker
row of (21) would give
\[
\begin{split}
W-P_{G3}
&>-\frac12+\left(\frac12+B_*\right)c
                    +\left(\frac12-A_*\right)r\\
&>-\frac12+\frac{102}{125}\frac{24}{25}
                   -\frac{803}{1000}\frac{27}{100}\\
&=\frac{1331}{20000}>0.
\end{split}
\]
Thus axis 3 is impossible for every EH owner.

Consider original GA axis 1. If an actual EH witness belongs to
\(\{0,1,3\}\), use the stronger row of (21):
\[
\begin{split}
W-P_{G1}
&>\frac12-A_*+\frac{947}{1000}c-\frac r2\\
&>-\frac{803}{1000}
      +\frac{947}{1000}\frac{97}{100}-\frac1{10}\\
&=\frac{1559}{100000}>0.
\end{split}                                         \tag{22}
\]
The only remaining possibility is an actual EH axis 2. Add HG
with weight c, the retained exact GA axis 1 with weight one, and
this EH axis with weight c. Their transverse terms cancel exactly:
\[
a_A+r a_G+c^2a_E-crb_E
\ge c+(1+c)W-c e_H-2cS.                             \tag{23}
\]
By (4), (9), (13), the left side is strictly below
\(A_*+r+Uc^2\). The nominal demand minus this upper bound is
\[
\frac12-A_*+2c-\frac{183}{200}c^2+\frac{c-1}{2}r.
\tag{24}
\]
The polynomial \(2c-(183/200)c^2\) increases on
\([24/25,1]\). Also \((c-1)r/2>-(1/50)(27/100)\).
The weaker row of (21) therefore gives this strict lower bound for (24):
\[
-\frac{803}{1000}
+2\frac{24}{25}
-\frac{183}{200}\left(\frac{24}{25}\right)^2
-\frac1{50}\frac{27}{100}
=\frac{16771}{62500}>\frac14.
\]
The full error in (23)
is at most \(3S\le9/200\), by (12). The surviving reserve is at least
\[
1/4-9/200=41/200>0,
\]
contradicting (23).

All four original GA axes have been excluded under the putative
high-G condition. Every case uses the retained actual witness,
and every original EH axis is covered, so equality and owner ties
produce no omitted case. This contradiction proves (3).

## 6. A partial high-G restriction that does not use the H cone

For possible earlier use, the same argument before Section 4 also
shows
\[
S\le3/200,\quad u_G\le-4/5,\quad
\text{original GA axis 3 feasible}
\quad\Longrightarrow\quad r>1/4,
\tag{25}
\]
under the G0--G2 and E-sign hypotheses of Section 1, with no H cone.

Indeed add GA axis 3 to AB, intended BT, and TD, each with weight c.
The resulting force is
\[
a_G+r a_A+c(a_B+b_B+b_D)
<1+Ur+\frac{27}{10}c,
\]
while the demand is \(W+3c\) with loss at most
\(c(e_A+e_B+e_T)\le S\). By (10), the gap is at least
\[
\frac3{10}-\frac{183}{200}r-\frac{16}{35}r^2.
\]
This polynomial decreases for \(r\ge0\). On \(0\le r\le1/4\)
it is at least \(239/5600\), and
\(239/5600-\sigma=31/1120>0\). This proves (25).
It supplies only a direction restriction and does not replace
the H-cone hypothesis in the theorem proved above.
