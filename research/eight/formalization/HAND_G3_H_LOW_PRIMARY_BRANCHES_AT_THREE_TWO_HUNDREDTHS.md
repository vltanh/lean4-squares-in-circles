# Three primary mixed pairs are impossible under the forbidden H cone

## 1. Exact scope and forward bounds

Assume the actual G0--G2 candidate geometry at
\[
q\le Q=9789/2500,\qquad
S=|d_H|+|d_A|+|d_B|+|d_T|+|d_D|\le\rho:=3/200,
\]
with roles \((H,G,A,B,T,D,E)\), quarter word \(0101011\), and
own-frame centers \((a_i,-y_i)\), \(a_i\ge|y_i|\). Retain the
weak G2 normalization \(y_E\le0\). Suppose
\[
                         y_H\le a_H/2.                      \tag{1}
\]
Then none of the following negative-tilt original witness pairs
is possible:
\[
                         (G1,E0),\quad(G1,E1),\quad(G3,E0).
\tag{2}
\]
Here the indices are the original GA and EH indices. This note
does not assume that either mixed edge has a preferred owner.
It proves the three exclusions whenever the indicated original
witnesses are actually feasible, including weak ties.

The six strict signs, the zero directions \(\{0,2\}\), and both
quarter directions \(\{2,3\}\) follow in forward order from the
cut-free theorems at \(S\le1/32\), in particular
[the cut-free BT theorem](HAND_G3_B_OWNER_WITHOUT_TANGENT_CUTS_AT_ONE_THIRTY_SECOND.md).
No G/T/H/D tangent cut is an input. The other mixed cases are
handled independently in
[the H-low high-index note](HAND_G3_H_LOW_HIGH_INDEX_STRESSES_AT_THREE_TWO_HUNDREDTHS.md);
none of its mixed-case conclusions is used below.

Write
\[
(y_H,y_G,y_A,y_B,y_T,y_D)
=(b_H,-b_G,b_A,-b_B,b_T,-b_D),\qquad
b_i>0,\quad b_E=-y_E\ge0.
\]
Use the constants
\[
L=447/800,\quad U=283/200,\quad K=37/40,\quad M=383/200.
\]
The unchanged original centers satisfy
\[
(a_i+1/2)^2+(b_i+1/2)^2\le Q,\qquad
a_i>L,\quad |p_i|<U,\quad b_i<9/10.                         \tag{3}
\]
Every originally feasible aligned witness has nominal projection
at least \(1-K|d_i|\). Thus, for \(e_i=|d_i|\),
\[
\begin{split}
b_H+b_G&\ge1-Ke_H,& b_A+b_B&\ge1-Ke_A,\\
a_B-b_T&\ge1-Ke_B,& b_T+b_D&\ge1-Ke_T,\\
a_D+b_E&\ge1-Ke_D.
\end{split}                                                  \tag{4}
\]
In particular every strict transverse magnitude exceeds
\(1-9/10-K\rho=689/8000>43/500\).

The H-low assumption (1) and the H corner imply
\[
b_H<29/50,\qquad b_G>203/500,\qquad a_G<63/50.                \tag{5}
\]
Indeed \(b_H\ge29/50\) and \(a_H\ge2b_H\) would make its
corner squared norm at least \(Q+4/625\). Then HG gives
\(b_G>21/50-K\rho=3249/8000>203/500\), and the corner value
at \((63/50,203/500)\) exceeds Q by \(709/250000\).

The shared BT--TD--AB path also gives, without using (1),
\[
                  b_A>B_*:=79/250,\qquad
                  a_A<A_*:=1303/1000.                        \tag{6}
\]
For completeness, the diagonal corner gives \(b_D<8993/10000\),
with reserve \(24049/50000000\). Weaken K to one in (4), and
put \(z=e_A\). Then
\(a_B+1/2>15857/10000+z\). If \(b_A\le79/250\), AB gives
\(b_B+1/2\ge148/125-z>0\). Their two squared lower bounds
sum to
\[
Q+\frac{70049}{100000000}+\frac{4017}{5000}z+2z^2>Q,
\]
a contradiction. The A corner at the two bounds in (6) exceeds
Q by \(213/200000\).

One weak core consequence, valid also for E, is
\[
                         a_i+b_i/20\ge7/12.                  \tag{7}
\]
If \(b_i\le1/2\), original core avoidance gives \(a_i\ge7/12\).
Otherwise \(a_i+b_i/20>L+1/40=467/800>7/12\).
Equality in (7) is permitted.

Normalize A's real frame to zero and write G's frame as \(t<0\).
Set
\[
c=\cos t,\quad r=-\sin t>0,\quad W=(1+c+r)/2.
\]
The G2 frame concentration gives
\[
c\ge3/4,\quad r<13/20,\quad c^2+r^2=1,\quad
1-c\le(4/7)r^2.                                             \tag{8}
\]
The exact actual EH tilt is
\[
                    z=t-d_H-d_A-d_B-d_T-d_D.                 \tag{9}
\]
Every originally feasible EH witness has nominal projection at
t at least \(W-MS\). This follows from the center-norm and
width Lipschitz constants \(U\) and \(1/2\).

## 2. Whole-arc bounds used by the three proofs

The relevant nominal projections are
\[
\begin{array}{c|l}
G1&a_A+r a_G-cb_G\\
G3&a_G+r a_A-cb_A\\
E0&c a_H-rb_H-b_E\\
E1&a_H-r a_E-cb_E.
\end{array}                                                  \tag{10}
\]
The two GA projections are exact at their actual phase; only EH
uses the nominal-to-actual comparison in (9).

### EH0 forces \(r<11/20\)

By (3)--(5), its gap obeys
\[
W-P_{E0}>
\frac12-\frac{183}{200}c+\frac{293}{500}r.
\]
The right side increases with r on the whole arc (8). At
\(r=11/20\), using \(c<21/25\), it exceeds
\(537/10000>3/100>M\rho\). Thus an actual E0 witness forces
\[
r<11/20,\qquad c>167/200,\qquad
1-c<(200/367)r^2.                                          \tag{11}
\]

### GA1/EH1 is confined to \(1/10<r<12/25\)

For \(r\le1/10\), one has \(c>99/100\). Equations (5)--(6)
give
\[
W-P_{G1}>-\frac{803}{1000}+\frac{453}{500}c-\frac{19}{25}r
>\frac{897}{50000}>0.
\]
Hence an actual G1 witness requires \(r>1/10\).

For E1, (3) and \(b_E\ge0\) give
\[
W-P_{E1}>-\frac{183}{200}+\frac c2+
                         \left(\frac12+L\right)r.
\]
This lower function increases throughout (8). At \(r=12/25\),
use \(c>877/1000\); its value exceeds \(3/100\) by
\(17/10000\). Thus the pair requires
\[
\frac1{10}<r<\frac{12}{25},\qquad c>\frac78,\qquad
1-c<\frac8{15}r^2.                                        \tag{12}
\]

### A feasible G3 has \(t<-S\)

For \(r\le1/20\), (5)--(6), with \(c>499/500\), give
\[
W-P_{G3}>-\frac{19}{25}+\frac{102}{125}c-\frac{803}{1000}r
>\frac{7109}{500000}>0.
\]
Consequently every actual G3 witness has \(r>1/20\), so
\(-t\ge r>1/20>S\). Along the full straight error segment
\((d_H,\ldots,d_D)\mapsto\tau(d_H,\ldots,d_D)\),
\(0\le\tau\le1\), the EH tilt in (9) remains negative.

## 3. A circle support and the H-low tangent

For a positive mass m, (3) gives the complete support inequality
\[
Xa+Yb\le T(X,Y;m):=
mQ+\frac{X^2+Y^2}{4m}-\frac{X+Y}{2}.                        \tag{13}
\]
It holds for arbitrary real forces X,Y. This notation will keep
the force collection and its circle bound distinct.

One linear support specific to the H-low bound (5) is
\[
a_H+\frac{54}{83}b_H
<\frac{29}{25}+\frac{54}{83}\frac{29}{50}.                   \tag{14}
\]
The vector \((83/50,27/25)\) is the corner at
\((a,b)=(29/25,29/50)\), with squared norm \(Q+4/625\).
Cauchy's inequality against that vector in the actual H circle,
followed by division by \(83/50\), proves (14).

## 4. GA1/EH0: one three-circle stress

Use weights, in HG--GA--AB--BT--TD--DE--EH order,
\[
\left(c,1,\frac{51}{100},\frac{19}{25},
             \frac{19}{25},\frac{81}{100},\frac{81}{100}\right).
\tag{15}
\]
Put \(\alpha=51/100\), \(\beta=19/25\), and \(e=81/100\).
T and E cancel in the nominal sum. The force is
\[
a_A+\alpha b_A+r a_G+\beta a_B+\alpha b_B
+e a_D+\beta b_D+ec a_H+(c-er)b_H,
\tag{16}
\]
and the nominal demand is
\[
(1+e)W+c+\alpha+2\beta+e.
\]
Every aligned weight is at most one, so the entire actual
nominal loss, preserving the single shared budget, is at most
\[
(K+Me)S\le148569/4000000.                                  \tag{17}
\]
This bound covers both signs of every actual error.

From (14) and \(0<b_H<29/50\), the last two terms in (16) are
strictly below
\[
\frac{3799}{2500}c-\frac{2349}{5000}r+\frac3{100}.
\tag{18}
\]
To verify the uniform remainder, subtract the first two terms
of (18) from the tangent bound. The result is at most
\[
\frac{29}{50}\left[er-
             \left(1-\frac{54}{83}e\right)c\right]_+.
\]
By (11) it is bounded above by
\[
\frac{29}{50}\left[
\frac{81}{100}\frac{11}{20}
-\left(1-\frac{81}{100}\frac{54}{83}\right)\frac{167}{200}
\right]
=\frac{152047}{5187500}<\frac3{100}.
\]
The final comparison has reserve \(1789/2593750\).

Use \(a_G<63/50\). Complete A, B, D in (16) with respective
forces and masses
\[
(1,\alpha;71/250),\quad
(\beta,\alpha;231/1000),\quad
(e,\beta;281/1000).
\]
Their support sum is
\[
C=\frac{46723501055839}{11521702500000}<\frac{203}{50},
\]
with reserve \(54611094161/11521702500000\). Demand minus
the resulting coordinate bound is therefore greater than
\[
-\frac{63}{200}+\frac{1927}{5000}c
                  +\frac{287}{2500}r-\frac3{100}.             \tag{19}
\]
The two direction terms in (19) form a concave function of r.
Its minimum on \([0,11/20]\) is bounded by its endpoints.
At zero the value is \(1927/5000\); at \(11/20\), replacing
c by \(167/200\) gives \(384949/1000000\), the smaller bound.
After subtracting (17), the remaining gap is greater than
\[
-\frac{63}{200}+\frac{384949}{1000000}
-\frac3{100}-\frac{148569}{4000000}
=\frac{11227}{4000000}>0.                                  \tag{20}
\]
This excludes every original GA1/EH0 pair.

## 5. GA1/EH1: use the original core on the same E center

Work on (12). Use weights
\[
(c,1,\alpha,\beta,\beta,\delta,e),\qquad
\alpha=\frac{57}{100},\quad \beta=\frac{19}{20},\quad
e=\frac{57}{50},\quad \delta=e(c-r/20).
\tag{21}
\]
All five aligned weights are positive and at most e. The E
force is exactly
\[
\delta b_E-e(r a_E+c b_E)
=-er(a_E+b_E/20)\le-(7/12)er                              \tag{22}
\]
by (7). This uses the unchanged original E center.

The nominal H force is \(e a_H+c b_H\). Since
\(c-e(54/83)>0\) on (12), (14) and \(b_H<29/50\) give
\[
e a_H+c b_H<\frac{29}{25}e+\frac{29}{50}c.
\tag{23}
\]
Use \(a_G<63/50\), and complete A, B, D with respective
forces and masses
\[
(1,\alpha;291/1000),\quad
(\beta,\alpha;7/25),\quad
(\delta,\beta;9/25).
\]
After (22)--(23), their exact demand-minus-support gap is at least
\[
C_0+\frac{16}{5}c+\frac{779}{2000}r
+\frac{144039}{160000}r^2+\frac{361}{4000}cr,
\qquad
C_0=-\frac{96895490723}{30555000000}>-\frac{127}{40}.
\tag{24}
\]
The last comparison has reserve \(116634277/30555000000\).
Identity (24) follows directly from (13) and (21); in particular,
\(\delta^2=e^2(1-399r^2/400-cr/10)\).

Using (12), (24) is strictly greater than the concave polynomial
\[
\frac1{40}+\frac{14991}{32000}r-\frac{387083}{480000}r^2.
\tag{25}
\]
The whole actual nominal loss is at most
\[
e(K+M)S\le12141/250000.
\]
At the two endpoints \(r=1/10,12/25\), (25) minus this loss is,
respectively,
\[
\frac{146099}{9600000}>0,\qquad
\frac{387529}{25000000}>0.
\tag{26}
\]
Concavity proves positivity on the entire interval. This excludes
every original GA1/EH1 pair, with all actual error signs retained.

## 6. GA3/EH0: an actual four-circle stress on the full arc

Work on (11); Section 2 also gives \(t<-S\). Use the following
single family on the entire interval \(0\le r\le11/20\):
\[
\begin{split}
h&=\frac7{15}+\frac98r,&
\beta&=\frac{11}{8}+\frac{16}{25}r,&
e&=\frac{13}{20}+\frac{97}{50}r,\\
\kappa&=\frac7{15},&
\alpha&=c+\kappa r.
\end{split}
\tag{27}
\]
The seven edge weights are \((h,1,\alpha,\beta,\beta,e,e)\).
They satisfy
\[
\beta-e=\frac{29}{40}-\frac{13}{10}r\ge\frac1{100}>0.
\]
Complete G, B, D, H with masses
\[
\begin{split}
m_G&=\frac7{25}+\frac{17}{100}r,&
m_B&=\frac{43}{100}+\frac4{25}r,\\
m_D&=\frac5{28}(\beta+e),&
m_H&=\frac15+\frac{19}{50}r.
\end{split}
\tag{28}
\]
Before completing D, add the nonnegative original cone slack
\(((\beta-e)/2)(a_D-b_D)\). This is valid at every point of the
error segment. Keep A, T and E actual in the nonzero-error stress.

At zero errors the completed forces are
\[
\begin{array}{c|cc}
G&1&h\\
B&\beta&\alpha\\
D&(\beta+e)/2&(\beta+e)/2\\
H&ec&h-er.
\end{array}                                                  \tag{29}
\]
The free T and E forces cancel. The free A force is
\(r(a_A+\kappa b_A)\). At zero errors only, use
\[
a_A+\kappa b_A
\le A^\dagger:=T(1,\kappa;7/25)=5710699/3937500.             \tag{30}
\]
No comparison center is introduced at A or E.

Let \(\Phi\) be the weighted actual width demand minus the
four circle supports and the unchanged free-center terms.
Original feasibility implies \(\Phi\le0\). The nominal lower
bound is
\[
\begin{split}
\Phi(0)\ge N(r,c):={}&h+\alpha+2\beta+e+(1+e)W-rA^\dagger\\
&-T(1,h;m_G)-T(\beta,\alpha;m_B)\\
&-T((\beta+e)/2,(\beta+e)/2;m_D)-T(ec,h-er;m_H).
\end{split}
\tag{31}
\]
The D support in (31) simplifies exactly to
\[
                  (12589/14000)(\beta+e).
\tag{32}
\]

### 6.1 One exact polynomial proves \(N>1/25\)

Put \(D_*=4m_Gm_Bm_H>0\). Reducing \(c^2=1-r^2\), write
\(D_*N=A(r)+B(r)c\). Direct expansion of (27)--(32) gives
\[
B(r)=\frac{15953}{62500}+\frac{130427}{150000}r
+\frac{11744269}{12500000}r^2
+\frac{8233991}{18750000}r^3+\frac{31331}{390625}r^4>0.
\]
Define the single rational polynomial
\[
P(r)=A(r)+B(r)(1-200r^2/367)-D_*/25.
\]
Its coefficientwise expansion has the following lower bound:
\[
\begin{split}
P(r)\ge{}&
\frac{67}{200000}-\frac{427}{100000}r-\frac{29}{10000}r^2
+\frac{19}{125}r^3+\frac1{25}r^4
-\frac{121}{1000}r^5-\frac{11}{250}r^6.
\end{split}
\tag{33}
\]
This is rational coefficient arithmetic from the displayed
weights and supports, not an interval sample.

On \(0\le r\le11/20\), the last four terms in (33) are at
least \(13r^3/100\). Indeed their difference, divided by \(r^3\),
is
\[
g(r)=\frac{11}{500}+\frac1{25}r
              -\frac{121}{1000}r^2-\frac{11}{250}r^3.
\]
This function is concave on the interval. Its endpoint values
are \(11/500\) and \(77/1000000\), both positive.

It remains to bound the cubic
\[
p(r)=\frac{67}{200000}-\frac{427}{100000}r
                      -\frac{29}{10000}r^2+\frac{13}{100}r^3.
\]
Let \(a=9/80\), \(x=r-a\). For every \(r\ge0\),
\[
p(r)\ge \frac{773}{256000000}
            +\frac{43}{3200000}x+\frac{527}{20000}x^2.
\]
The omitted term is \((13/100)r x^2\ge0\). Completing this
last square leaves the exact positive reserve
\[
\frac{773}{256000000}
-\frac{(43/3200000)^2}{4(527/20000)}
=\frac{3257119}{1079296000000}>0.
\]
Thus \(P(r)>0\). Since \(B(r)>0\), (11) proves the whole-arc
nominal estimate
\[
                            \Phi(0)>1/25.                   \tag{34}
\]

### 6.2 All five signed first derivatives have loss at most S

For clarity, the two retained original projections on each
aligned edge are
\[
\begin{array}{c|l}
HG&b_H+a_G\sin d_H+b_G\cos d_H;\
       a_H\sin d_H+b_H\cos d_H+b_G\\
AB&b_A+a_B\sin d_A+b_B\cos d_A;\
       a_A\sin d_A+b_A\cos d_A+b_B\\
BT&a_B\cos d_B+b_B\sin d_B-b_T;\
       a_B+a_T\sin d_B-b_T\cos d_B\\
TD&b_T+a_D\sin d_T+b_D\cos d_T;\
       a_T\sin d_T+b_T\cos d_T+b_D\\
DE&a_D\cos d_D+b_D\sin d_D+b_E;\
       a_D+a_E\sin d_D+b_E\cos d_D.
\end{array}
\tag{35}
\]
The actual EH0 projection is
\(a_H\cos z+b_H\sin z-b_E\), with (9).

The derivative of \(T(X,Y;m)\) in its force coordinates is the
virtual center \((X/(2m)-1/2,Y/(2m)-1/2)\). These coordinates
are used only for differentiating the support; they are not
assumed to describe a packing.

After removal of the five aligned sine cusps, the derivative
of \(\Phi\) in any one \(d_i\), at zero errors, is
\[
                             D-\lambda_i R_i,
\qquad
D=e\left(\frac{ch}{2m_H}-r\right).                          \tag{36}
\]
The common term is obtained from (9) and the virtual H force
in (29). More explicitly it is
\(e\{r(a_H^*-1/2)+c(b_H^*+1/2)\}\), which simplifies to (36).
Each aligned width cusp restores \(\lambda_i|d_i|/2\).

On the entire arc,
\[
                              3/4<D<27/20.                  \tag{37}
\]
Here is a rational check of both bounds. For the lower one, (11)
gives
\[
2m_H(D-3/4)\ge \frac1{300}+r q(r),
\]
\[
q(r)=\frac{9679}{12000}+\frac{65813}{88080}r
               -\frac{6513161}{2752500}r^2-\frac{873}{734}r^3.
\]
The cubic q is concave on \([0,11/20]\), with positive endpoint
values \(9679/12000\) and \(223034721/734000000\).
For the upper one, use \(c\le1\). Then
\[
2m_H(27/20-D)\ge
v(r):=\frac{71}{300}-\frac{4207}{12000}r
                         -\frac{73}{80}r^2+\frac{1843}{1250}r^3.
\]
The derivative \(v'\) is convex and its endpoint values are
\(-4207/12000\) and \(-24473/1500000\). Thus v decreases, and
its right endpoint is \(787073/60000000>0\). This proves (37).

The receiver alternatives in (36), from (35), are
\[
\begin{array}{c|c}
HG&a_G^*,a_H^*\\
AB&a_A,a_B^*\\
BT&a_T,b_B^*\\
TD&a_T,a_D^*\\
DE&a_E,b_D^*.
\end{array}
\]
Every one satisfies \(1/2<R_i<3/2\). The actual receivers use
(3). For the virtual receivers,
\[
a_G^*=\frac1{2m_G}-\frac12,\quad
a_H^*=\frac{ec}{2m_H}-\frac12,\quad
a_B^*=\frac{\beta}{2m_B}-\frac12,\quad
b_B^*=\frac{\alpha}{2m_B}-\frac12,\quad
a_D^*=b_D^*=\frac9{10}.
\]
The G and B primary comparisons are immediate from (27)--(28).
For the B transverse lower bound, (8) gives
\[
\alpha-2m_B\ge\frac7{50}+\frac{11}{75}r-\frac47r^2>0;
\]
the concave quadratic has endpoint values \(7/50\) and
\(251/5250\). The upper bound \(\alpha<4m_B\) uses \(c\le1\).
For H, \(ec>2m_H\) follows already from \(c\ge3/4\).
For the upper bound use \(c\le1-r^2/2\):
\[
4m_H-ec\ge\frac3{20}-\frac{21}{50}r+\frac{13}{40}r^2
                                   +\frac{97}{100}r^3>0.
\]
The quadratic part has completed-square reserve \(93/6500\).

All five aligned weights lie in \([7/15,7/4]\).
Consequently (37) proves, for every original receiver choice,
\[
|D-\lambda_iR_i|-\lambda_i/2
<\max\{27/20-7/15,\ (7/4)(3/2-1/2)-3/4\}\le1.
\tag{38}
\]
The entire first-order contribution is therefore at least
\(-S\). This is the signed shared-error cancellation; no error
was first replaced by an independent absolute allowance.

### 6.3 A uniform Hessian bound on the actual error segment

If a completed force obeys
\[
|F|\le M_0,\qquad
|\partial_jF|,\ |\partial_j\partial_kF|\le D_0,
\]
then a Hessian entry of its support (13) has absolute value at
most
\[
\frac{D_0^2+M_0D_0}{2m}+\frac34D_0.                         \tag{39}
\]
This follows by differentiating (13), with
\(\sqrt2/2<3/4\) for the corner offset.

Valid triples \((m\text{ lower bound},M_0,D_0)\), throughout
the complete straight error segment, are
\[
\begin{array}{c|ccc|c}
G&7/25&21/10&11/10&1991/280\\
B&43/100&29/10&7/4&7413/688\\
D&81/224&7/2&7/4&6055/432\\
H&1/5&57/20&57/20&171/4.
\end{array}
\tag{40}
\]
The last column is (39), respectively less than \(8,11,15,43\).
At G only HG varies. At B the two possible varying incident
rotations have different aligned increments. At D they also
have different increments, and the cone correction is constant.
For its force norm,
\[
|F_D|\le\beta+e+\frac{\beta-e}{\sqrt2}
<\frac74\beta+\frac14e<\frac72.
\]
At H both the HG and EH terms may contribute to the same
derivative; their sum is less than \(57/20\), as used in (40).
Also \(\alpha<10/9\), since \(1+\kappa^2<(10/9)^2\).

The free A, T, E contributions to a Hessian entry are respectively
less than \(8/5,5,5/2\), by their unchanged center norms and
(35). At E only DE can rotate the free center in this branch;
the EH0 term is the constant \(-e b_E\).
The smooth width contributions total less than \(23/4\).
Indeed the five aligned cosine parts contribute at most \(35/8\)
and the EH part at most \(21/16\). All these bounds together
are less than 100. Taylor's theorem therefore loses at most
\(50S^2\).

Restoring the aligned sine cusps uses
\(|\sin d|\ge|d|-|d|^3/6\); since \(\lambda_i\le7/4\), the
total additional loss is at most
\((7/48)\sum_i|d_i|^3<S^3/6\).
Equations (34), (38)--(40) prove
\[
\begin{split}
\Phi&>\frac1{25}-S-50S^2-S^3/6\\
&\ge\frac{219991}{16000000}>0.
\end{split}
\tag{41}
\]
This contradicts original feasibility and excludes every
original GA3/EH0 pair on the entire negative arc.

## 7. Consequence and dependency boundary

Equations (20), (26), and (41) prove all three exclusions in
(2). Together with the independently proved cases in the
H-low high-index note, they exclude the entire H-low condition
\(y_H\le a_H/2\) at \(S\le3/200\).

The statements here use original contained centers, the forward
cut-free short-quarter owners, the exact EH error sum, and every
original feasible witness. The circle derivatives use virtual
support coordinates only as algebraic derivatives. No new packing,
owner preference, boundary-kind replacement, angle mesh, generated
state inventory, Lean compilation, or CI result is a premise.
The mismatch bound \(S\le3/200\) remains a separate hypothesis.
