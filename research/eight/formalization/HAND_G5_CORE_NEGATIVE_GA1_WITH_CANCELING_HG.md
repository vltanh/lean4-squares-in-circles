# The canceling companion for an exceptional negative GA1 angle

## 1. Statement and relation to the noncanceling reduction

Use the normal signed H,G,A triple, actual sorted circles,
true central exclusion, and real frame spread at most \(7/10\).
Put
\[
 Q=\frac{9789}{2500},\qquad K=\frac{13}{12},\qquad
 a_G=\frac7{12},\qquad z=\theta_G-\theta_A>0.
\tag{1}
\]
Assume \(q\le Q\), that GA1 is feasible, that the actual GA0
witness is not feasible, and that HG2 is retained.

**Canceling reduction.** Keeping H,A and every other point
and frame fixed, one can replace G on its true flat core,
strictly inside the same q-circle, so that the retained
neighboring inequalities remain feasible and either
\[
                     \theta_G'=\theta_A
             \quad\hbox{or}\quad
                     \theta_G'=\theta_H.
\tag{2}
\]
At the first endpoint the actual GA0 witness is available.
At the second HG is aligned. A nonzero HG error gives
strict slack in a surviving HG0 or HG2 witness at the
chosen endpoint.

Combined with
[the noncanceling companion](HAND_G5_CORE_NEGATIVE_GA1_WITH_NONCANCELING_HG.md),
this gives the same two-endpoint reduction for either
surviving HG owner. For an original normal boundary
representative with negative GA1, either GA0 is already
feasible or Section 4 of
[the low-GA/high-EH exclusion](HAND_G3_HIGH_EH_EXCLUSION_UNDER_LOW_GA.md)
forces exactly the flat-core alternative in (1).
No original H/G/A frame order is assumed.

As in the companion, this is a local necessary-system
reduction. Only G changes; it need not preserve omitted
nonneighbor packing inequalities or G1 markers. The
reflected statement applies to exceptional negative BT3
with the two surviving TD owners.

## 2. The exceptional primary angle has two stronger cuts

Write
\[
 D_G=b_G+\frac12,\qquad X=a_A+\frac12,\qquad
 Y=b_A+\frac12.
\tag{3}
\]
The exact comparison-vector inequality from the cited
negative-primary proof gives
\[
 \begin{split}
 Q&>1+K^2+D_G^2+2(D_G\cos z+K\sin z),\\
 D_G&<\frac{82}{125},\qquad b_G<\frac{39}{250}.
 \end{split}
\tag{4}
\]
These use the actual two projections, not a chosen
descendant. The square reserve for the second line is
\[
 K^2+(1+82/125)^2-Q=\frac{781}{2250000}>0.
\]

Since \(D_G\ge1/2\), the first line of (4) implies
\[
 Q>1+K^2+\frac14+\cos z+2K\sin z.
\tag{5}
\]
The right side increases on \([0,7/10]\): its derivative
is greater than
\(-13/20+2K(3/4)=39/40>0\). At \(z=1/4\), lower Taylor
bounds give
\[
 1+K^2+\frac14+
       \left(1-\frac{z^2}{2}\right)
       +2K\left(z-\frac{z^3}{6}\right)-Q
                  =\frac{6137}{480000}>0.
\tag{6}
\]
Thus
\[
                             0<z<\frac14.
\tag{7}
\]

The strict difference of the actual primary and rotated
projections is
\[
 P_{GA1}-P_{GA0}
 =(a_A+b_G)(1-\cos z)+(b_A-a_G)\sin z>0.
\]
After division by \(\sin z>0\), this gives
\[
                 b_A+(a_A+b_G)\tan(z/2)>\frac7{12}.
\tag{8}
\]
On \(0\le z/2\le1/8\),
\[
 \tan(z/2)<\frac{63}{500},
\tag{9}
\]
because at \(x=1/8\)
\[
 \frac{63}{500}\left(1-\frac{x^2}{2}\right)
       -\left(x-\frac{x^3}{6}+\frac{x^5}{120}\right)
           =\frac{33511}{98304000}>0.
\]

Suppose \(b_A\le2/5\). The circle gives
\(a_A\le a_Q(b_A):=\sqrt{Q-(b_A+1/2)^2}-1/2\).
The function \(b+(63/500)a_Q(b)\) is increasing on
\([0,2/5]\); its derivative is
\[
 1-\frac{63}{500}\frac{b+1/2}{\sqrt{Q-(b+1/2)^2}}
                        >1-\frac{63}{500}>0.
\]
Also
\[
 a_Q(2/5)<\frac{1263}{1000},
\quad
 \left(\frac{1763}{1000}\right)^2+\frac{81}{100}-Q
                    =\frac{2569}{10^6}>0.
\]
Using (4), the left side of (8) would consequently be less than
\[
 \frac25+\frac{63}{500}
           \left(\frac{1263}{1000}+\frac{39}{250}\right)
       =\frac7{12}-\frac{6809}{1500000},
\]
a contradiction. We have proved
\[
       b_A>\frac25,\qquad
       P:=a_A-\frac12<\frac{763}{1000}=:p_0.
\tag{10}
\]

These cuts concern the unchanged original A. They remain
available after changing G, even if a GA0 witness becomes
feasible along the way.

## 3. A nonpositive HG2 error already has HG0 feasible

If \(h=\theta_G-\theta_H<0\), the HG2 projection is
\[
                    a_H\sin h+b_H\cos h+b_G.
\]
It is strictly less than \(b_H+b_G\). Since the retained
projection is at least \(W(h)\ge1\), (4) gives
\[
 b_H>1-b_G>\frac{211}{250}>\frac7{12}=a_G,
                    \qquad b_H>b_G.
\tag{11}
\]
Sorting also gives \(a_H\ge b_H>a_G\). Therefore
\[
 \begin{split}
 P_{HG0}-P_{HG2}
   &=(a_G-a_H)\sin h+(b_H-b_G)(1-\cos h)\\
   &>0.
 \end{split}
\tag{12}
\]
The same actual G has an HG0 witness with strict slack.
Apply the noncanceling companion. It supplies (2), with
strict HG0 slack at the selected endpoint. If \(h=0\),
HG was already aligned and no move is needed.

It remains to treat \(h>0\).

## 4. The positive-error composite and its H-circle bound

Rotate so that \(\theta_A=0\), and put
\(\Theta=\theta_H\). Use the maximal flat-core tangent
\[
 D(x)=\frac{P-K\sin x}{\cos x},\qquad
 a_G(x)=\frac7{12},\qquad b_G(x)=D(x)-\frac12.
\tag{13}
\]
The original GA1 inequality implies that this replacement
increases or preserves \(b_G\) at \(x=z\), so it improves
HG2 and makes GA1 tight. On the interval
\[
                     \max\{0,\Theta\}\le x\le z,
\tag{14}
\]
the companion's intrinsic-cap calculation gives
\[
 \frac12\le D(x)\le P<p_0,\qquad
 D'(x)=D(x)\tan x-K<0.
\tag{15}
\]
The G corner remains below the actual q, as in its
equation (12). The positive HG error is
\(h=x-\Theta\in[0,7/10]\).

Put
\[
 \begin{split}
 S_H(h)&=(a_H-\tfrac12)\sin h+(b_H-\tfrac12)\cos h,\\
 U_H(h)&=(a_H-\tfrac12)\cos h-(b_H-\tfrac12)\sin h.
 \end{split}
\tag{16}
\]
The retained HG2 inequality is exactly
\[
                   F(x):=D(x)+S_H(x-\Theta)\ge1,
\]
and its derivative is
\[
                   F'(x)=D(x)\tan x-K+U_H(h).
\tag{17}
\]

At a feasible point put \(d=1-D(x)\in(1-p_0,1/2]\).
Then \(S_H(h)\ge d\). For
\(m=\sin h+\cos h\), \(n=\cos h-\sin h\), the actual
H-circle identity gives
\[
 (S_H+m)^2+(U_H+n)^2
      =(a_H+\tfrac12)^2+(b_H+\tfrac12)^2\le Q.
\]
Consequently
\[
 U_H(h)\le \phi_d(h):=\sqrt{Q-(d+m)^2}-n.
\tag{18}
\]
The radicand is positive on the full rectangle under
consideration: \(d\le1/2\), \(m\le\sqrt2<10/7\), and
\[
                         Q-(1/2+10/7)^2
                                =\frac{6009}{30625}>0.
\]

The function \(\phi_d\) has no interior maximum on
\([0,7/10]\). Indeed
\[
 \phi_d'(h)
   =m-\frac{(d+m)n}{\sqrt{Q-(d+m)^2}},
\]
and, since all comparison factors are positive, the sign
of this derivative is the sign of
\[
                      (\sqrt{Q/2}-1)m-d.
\tag{19}
\]
Here \(m\) increases strictly and \(\sqrt{Q/2}-1>0\).
The derivative can therefore change sign only from
negative to positive. Thus
\[
                U_H(h)\le
                   \max\{\phi_d(0),\phi_d(7/10)\}.
\tag{20}
\]

Lower Taylor polynomials give
\[
 \sin(7/10)+\cos(7/10)>\frac{176}{125},
 \qquad
 \cos(7/10)-\sin(7/10)>\frac3{25}.
\tag{21}
\]
Using \(S_7(x)=x-x^3/6+x^5/120-x^7/5040\) and
\(C_6(x)=1-x^2/2+x^4/24-x^6/720\), the respective
rational reserves are
\[
 S_7(7/10)+C_6(7/10)-\frac{176}{125}
             =\frac{7620061}{7200000000},
\]
\[
 C_6(7/10)-S_5(7/10)-\frac3{25}
             =\frac{436931}{720000000}.
\]
It follows from (20) that
\[
 U_H(h)\le
 \max\left\{
  \sqrt{Q-(2-D)^2}-1,\;
  f(D)
 \right\},
\quad
 f(D)=\sqrt{Q-(301/125-D)^2}-\frac3{25}.
\tag{22}
\]

## 5. The composite derivative is uniformly negative

On \(0\le x\le1/4\),
\[
 \tan x<\frac{13}{50}=:t_0.
\tag{23}
\]
At \(x=1/4\), the lower cosine and upper sine comparison
has reserve
\[
 t_0(1-x^2/2)-(x-x^3/6+x^5/120)
                    =\frac{2747}{614400}>0.
\]
In particular, throughout (14),
\[
 \begin{split}
 D\tan x&<\frac15,\\
 D'&<-\frac{22}{25},\\
 D\sec^2x&<\frac{163}{200}.
 \end{split}
\tag{24}
\]
The three exact rational reserves are
\[
 \frac15-p_0t_0=\frac{81}{50000},\quad
 K-p_0t_0-\frac{22}{25}=\frac{743}{150000},\quad
 \frac{163}{200}-p_0(1+t_0^2)=\frac{1053}{2500000}.
\]

For the first branch in (22), the positive-squaring
comparison
\[
 (31/20)^2+(2-p_0)^2-Q=\frac{17069}{10^6}>0
\]
gives \(\sqrt{Q-(2-D)^2}-1<11/20\).
Using (24), that branch of (17) is strictly less than
\[
                         \frac15-K+\frac{11}{20}
                                     =-\frac13.
\tag{25}
\]

For the second branch, \(301/125-D\ge329/200\).
The square reserve
\[
 (11/10)^2+(329/200)^2-Q=\frac{17}{40000}>0
\]
gives
\[
 f(D)<\frac{49}{50},\qquad
 f'(D)=\frac{301/125-D}{\sqrt{Q-(301/125-D)^2}}
             >\frac{329}{220}>\frac75.
\tag{26}
\]
The last gap is \(21/220\).

Retain the correlation with x by putting
\[
                         g(x)=D(x)\tan x+f(D(x)).
\]
Equations (24) and (26) give the whole-interval derivative
bound
\[
 \begin{split}
 g'(x)
  &=D\sec^2x+D'(\tan x+f'(D))\\
  &<\frac{163}{200}-\frac{22}{25}\frac75
           =-\frac{417}{1000}<0.
 \end{split}
\tag{27}
\]
Thus \(g(x)\le g(0)=f(P)<49/50\), even if the actual
movement interval (14) does not include zero. The formula
for D and all bounds remain valid on \([0,z]\).
This second branch of (17) is therefore less than
\[
                     \frac{49}{50}-K=-\frac{31}{300}
                                          <-\frac1{10}.
\tag{28}
\]
Combining (25) and (28) proves
\[
             F'(x)<-\frac1{10}
       \quad\hbox{at every feasible point of (14)}.
\tag{29}
\]

Lower x from z to \(\max\{0,\Theta\}\). The inequality
\(F\ge1\) cannot first fail: at any feasible boundary,
(29) points strictly into its feasible side in the
decreasing-x direction. In fact F increases strictly
along the move, so the endpoint has positive HG2 slack.
The endpoint is G=A if \(\Theta\le0\), and G=H otherwise.

## 6. Actual witnesses and equality bookkeeping

At G=A, formula (13) gives \(b_G=a_A-1\), so both
GA0 and GA1 have projection 1. At G=H both surviving
zero owners have the same projection \(b_H+b_G\).
The new G frame lies between the original three frames,
and every unchanged point retains its original corner.
The G corner is strictly below q.

If a strict A-circle loss is needed and the other
retained A-neighbor witness is independent of \(a_A\)
(as for AB0 or aligned AB), use the strict slack just
created exactly as in Section 5 of the noncanceling
companion: lower the positive G tangent a little, then
lower \(a_A\) by a smaller amount. Both retained local
constraints survive, and the A corner strictly decreases.
No such restoration is asserted for an arbitrary
unaligned AB2 witness.

The original boundary no-GA0 alternative is used only
to obtain (4), (7) and (10). After those fixed-A cuts
are established, the movement itself uses the explicit
GA1 cap and the actual H-circle support. It does not
silently reuse a radial-boundary hypothesis on a
constructed G.

