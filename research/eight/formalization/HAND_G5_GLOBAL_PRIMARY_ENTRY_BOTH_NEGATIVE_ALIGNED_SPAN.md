# Two aligned negative primary endpoints have a short H--D span

## 1. Original-data span theorem

Put
\[
 Q=9789/2500,\quad h=7/10,\quad
 c=\sqrt{Q/2}-1/2,\quad K=13/12,
 \quad m=3/2-c.
\tag{1}
\]
Retain sorted true-core states H,G,A,B,T,D contained at a
common actual ceiling \(q\le Q\), with real frame spread
at most h. H,A are nonnegative, B,D are nonpositive, and
the two transverse pairs are aligned:
\[
              \theta_H=\theta_G>\theta_A,
        \qquad\theta_B>\theta_T=\theta_D.
\tag{2}
\]
Retain actual HG and TD transverse witnesses, actual GA1
and BT3, and either actual AB0 or AB2. Suppose actual GA0
and BT2 are both unavailable. Then
\[
                         \theta_H-\theta_D<11/50.
\tag{3}
\]
No E state or E witness is used. The theorem retains every
original coordinate, frame and weak contact. It does not
assume that either exceptional primary was already converted
to a hard owner.

Aligned HG and TD force G's sign negative and T's sign
positive, because their projections are respectively
\(b_H-y_G\ge1\) and \(y_T+b_D\ge1\), while
\(b_H,b_D\le c<.9\). Put
\[
           t=\theta_H-\theta_A,
        \qquad u=\theta_B-\theta_D.
\]
The genuine negative-primary comparison on H/G/A and its
local reversed counterpart on D/T/B give
\[
              0<t,u<.09,
       \qquad a_A\ge f(t),\quad a_B\ge f(u),
       \qquad f(z)=\tfrac12+m\cos z+K\sin z.
\tag{4}
\]
These are the same local comparisons used in Section 1 of
[the one-primary TD0 span theorem](HAND_G5_NEGATIVE_GA_ALIGNED_HG_TD0_SPAN_BOUND.md).
For the second side, actual BT3 at error -u reads
\(a_B-a_T\sin u-y_T\cos u\ge W(u)\).
The unavailable-BT2 comparison gives the same short angle
and \(a_T\ge7/12\), while aligned TD gives
\(y_T\ge1-c\). Thus (4) follows directly, without any
assumption about E under that local reversal.

## 2. Two actual circle caps reduce the long-span alternative

Define, for \(0\le z\le.09\),
\[
 X(z)=1+m\cos z+K\sin z,
 \qquad Y(z)=\sqrt{Q-X(z)^2},
 \qquad J(z)=X'(z)=K\cos z-m\sin z.
\tag{5}
\]
The actual A/B primary corners are at least X(t),X(u);
their tangent corners are consequently at most Y(t),Y(u).

Suppose \(\alpha=\theta_H-\theta_D\ge.22\), and put
\[
                    v=\theta_A-\theta_B=\alpha-t-u.
\]
Then \(v>.04\), and actual frame spread gives v<=h.
For AB0, its exact shifted inequality at the negative
error -v is
\[
                    Y_A+Y_B\cos v-X_B\sin v\ge1+\cos v.
\tag{6}
\]
Since the sine and cosine are positive, the actual circle
caps imply the necessary inequality
\[
        Y(t)+\{Y(u)-1\}\cos v-X(u)\sin v-1\ge0.
\tag{7}
\]
For these caps Y(u)>1, so the expression on the left
decreases strictly with v. Its largest permitted value
therefore occurs at \(v=.22-t-u\). Define
\[
 S(t,u)=Y(t)+\{Y(u)-1\}\cos(.22-t-u)
                         -X(u)\sin(.22-t-u)-1.
\tag{8}
\]
It suffices to prove S<0 on the entire rectangle
\(0\le t,u\le.09\).

For AB2, (6) instead has A's rotated corner and B's
unrotated tangent. Its upper bound is exactly S(u,t).
Thus the same rectangle proof covers either actual owner,
including every original weak tie.

## 3. Whole-interval cap bounds

The following coarse rational bounds hold on \([0,.09]\):
\[
 \begin{gathered}
 .6007859<m<.600786,
 \qquad 1.6007859<X<1.697,\\
 1.018<Y\le Y(0)<1.163222<1.164,
 \qquad 1.024<J\le K.
 \end{gathered}
\tag{9}
\]
For explicit verification, the first bounds follow by
squaring \(.8992140<c<.8992141\). Their reserves are
\[
 Q-2(1.3992140)^2=45551/125000000000,
 \quad 2(1.3992141)^2-Q=9763881/50000000000000.
\]
X increases and J decreases, since \(J'=-(X-1)<0\).
At z=.09 use
\[
 \overline X=1+.600786C_4(.09)+KS_5(.09)<1.697,
 \quad\underline J=KC_6(.09)-.600786S_5(.09)>1.024.
\tag{10}
\]
The two Y checks are
\[
 Q-\overline X^2>1.018^2,
 \qquad (1.163222)^2>Q-(1.6007859)^2.
\tag{11}
\]
The latter reserve is \(91892281/10^{14}\).
Here \(C_j,S_j\) denote the alternating cosine and sine
Taylor polynomials of degree j.

Put \(L=XJ/Y=-Y'\). We will use
\[
                            L>1.49.
\tag{12}
\]
Indeed
\[
                (XJ)''=-J(4X-3)<0,
\]
so XJ has its minimum at an endpoint. Its endpoint at
.09 is larger than its endpoint at zero: a completely
rational check is
\[
 \{1+.6007859C_6(.09)+KS_7(.09)\}\,
       \{KC_6(.09)-.600786S_5(.09)\}
                         >(1+.600786)K.
\tag{13}
\]
Since Y decreases,
\[
 L\ge\frac{(1+.6007859)K}{1.163222}
                 >1.49,
\]
with exact last reserve \(196789/232644400\).

Differentiating Y twice gives
\[
 Y''=-\frac{QJ^2}{Y^3}+\frac{X(X-1)}Y
 \le-\frac{Q(1.024)^2}{1.164^3}
            +\frac{1.697(.697)}{1.018}<-1.44.
\tag{14}
\]
The last strict reserve is \(12504958847/8361910026000\).
Introduce only for the derivative calculation
\[
                       A(z)=X(z)-L(z),
       \qquad B(z)=Y(z)-1-J(z).
\]
Then
\[
 A'=J+Y''<K-1.44<0,
 \qquad B'=-L+X-1<-1.49+.697<0.
\]
Their maximum values are at zero. The same rational
endpoint bounds give
\[
 \begin{split}
 A(z)&\le A(0)
  <1.600786\{1-K/1.163222\}<.11,\\
 B(z)&\le B(0)<1.163222-1-K<-.92.
 \end{split}
\tag{15}
\]
The respective reserves are
\(52320631/872416500000\) and \(167/1500000\).

## 4. A direct rectangle estimate contradicts AB

Write \(v=.22-t-u\in[.04,.22]\) in this section.
Differentiating (8) in t gives
\[
 S_t=-L(t)+\{Y(u)-1\}\sin v+X(u)\cos v.
\]
One circle identity and (9),(12) yield
\[
 S_t<-1.49+\sqrt{X(u)^2+(Y(u)-1)^2}
       =-1.49+\sqrt{Q-2Y(u)+1}
       <-1.49+1.697<.208.
\tag{16}
\]
The positive square check is
\(1.697^2-(Q-2(1.018)+1)=209/10^6\).
The other derivative is
\[
                    S_u=A(u)\cos v+B(u)\sin v.
\]
By (15) and v>=.04,
\[
 S_u<.11-.92\sin(.04)
              \le.11-.92S_3(.04)<.074.
\tag{17}
\]
The last reserve is \(926/1171875\).

At the single rectangle corner (0,0),
\[
 \begin{split}
 S(0,0)
 &<1.163222+.163222C_4(.22)
                       -1.6007859S_7(.22)-1\\
 &<-.0268.
 \end{split}
\tag{18}
\]
The last reserve is
\(54270805312822291/1875000000000000000000\).
Integrate (16) along the t direction and (17) along
the u direction inside the rectangle:
\[
 \begin{split}
 S(t,u)&<-.0268+.208t+.074u\\
       &\le-.0268+.09(.208+.074)
          =-.00142<-.0014<0.
 \end{split}
\tag{19}
\]
This contradicts (7). Since S(u,t) satisfies the same
bound, it also contradicts the other actual AB owner.
The strict span conclusion (3) follows.

The proof uses just the two original primary lower bounds,
the two actual circle caps and the actual AB inequality.
Its finite alternatives are the two AB owners. All angular
estimates are derivative bounds on the whole rectangle,
with the isolated rational comparisons displayed above.

## 5. One genuine primary can now be converted while the other is retained

For a same-radius application assume \(q_L\le q\le Q\),
restore an E state with nonpositive tangent, and retain
\(DE\in\{2,3\}\), \(EH\in\{0,1\}\). Let E be on
its true-core boundary or outer q-circle. H and D may be
inside their q-circles: both primary lifts at fixed tangent
are eligible here because both HG and TD are aligned.

The finite E-position argument in Sections 2--3 of
[the complete one-primary negative-endpoint assembly](HAND_G5_GLOBAL_PRIMARY_ENTRY_ALIGNED_NEGATIVE_ENDPOINT_COMPLETE.md)
now applies with (3) supplying its span input. That argument
uses no BT2 after the span has been obtained. It therefore
reaches actual EH0 or positive EH1 of error at most .22,
preserving the actual BT3. The local H/G transport then
reaches actual GA0 at the same q with a strict H-circle loss.
B,T,D and their frames remain unchanged apart from an eligible
D primary lift before the E transport. In particular the
remaining actual BT3 error is still negative and TD is
still aligned.

This supplies an actual reduction from two genuine aligned
negative primaries to one genuine primary. It is not yet a
standalone application of the sharp GA0/BT2 theorem, because
BT3 remains retained. Nor may one silently reflect the final
one-primary theorem: physical reflection reverses E's sign,
and its EH-specific local proof states that sign explicitly.
Any later opposite-side conversion must retain its own radial,
sign and strict-anchor-loss obligations. The H loss proved
here is an actual anchor loss; no loss at G or T is being used
as a substitute for the sharp equality conditions.
