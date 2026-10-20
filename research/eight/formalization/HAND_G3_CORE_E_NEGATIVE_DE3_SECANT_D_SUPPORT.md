# A negative core DE3 error paid by the secant D-circle support

## 1. Scope and notation

Work on the fixed-original-witness G0--G2 boundary at
\[
 Q=\frac{9789}{2500},\qquad R=\sqrt Q,\qquad h=\frac7{10},
 \qquad
 a_0=\sqrt{Q-\frac14}-\frac12,\qquad
 c_0=\sqrt{Q/2}-\frac12.
\tag{1}
\]
The sorted outer states H, G, B and D have signed tangents
respectively positive, negative, negative and negative.
E is nonpositive and is a true core state. Retain original
BT2, EH0, and either HG0 or HG2. The original DE owner is 3,
with error \(-s\le0\). The EH0 error has either sign.

This note excludes that configuration in each of the following
two A/TD regimes:

* GA2 and AB0 may have arbitrary errors; GA3 or AB2 may replace
  their corresponding secondary owners when their errors are
  nonpositive. TD0 has arbitrary error, or TD2 has nonpositive
  error. Several such nonpositive alternatives may occur together.
* The selected A primary is a single nonnegative GA3 or AB2,
  or both GA3 and AB2 have nonnegative signed total
  \(0\le a\le1/6\). The other A edge, when secondary, has arbitrary
  error. Again TD0 has arbitrary error, or TD2 has nonpositive
  error. The case with no A primary is also allowed by putting
  \(a=0\).

No frame order is assumed. Positive TD2 and larger positive A
total are not included. All decimals in this note are exact
rationals. We use the original variation bounds
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+=\sum_i(-d_i)_+<h.
\tag{2}
\]
The argument compares positive weighted sums of the actual
neighboring inequalities. Its virtual angles assert no new
original separating witnesses.

Put
\[
 \begin{split}
 W(t)&=\frac{1+\cos t+|\sin t|}{2},\\
 a(b)&=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\\
 S(f,g)&=\max_{0\le b\le c_0}\{f a(b)+g b\}.
 \end{split}
\tag{3}
\]
The two fixed coefficient choices used below are
\[
 (c,L)=\left(2,\frac{21}{20}\right)
 \quad\hbox{or}\quad
 (c,L)=\left(\frac95,\frac{103}{100}\right).
\tag{4}
\]
They are respectively the choices in the
[preferred four-circle theorem](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md)
and the low-angle part of the
[positive-A TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md).

## 2. EH0 forces the actual core E onto its flat side

The original EH0 projection is
\[
                 a_H\cos r+b_H\sin r-b_E\ge W(r)\ge1.
\tag{5}
\]
On the sorted outer H arc, \(a_H+b_H\ge a_0\), and hence
\[
 a_H^2+b_H^2=Q-\frac12-(a_H+b_H)\le a_0^2.
\]
Cauchy's inequality in (5) gives
\[
                        b_E\le a_0-1<.415<\frac12.
\tag{6}
\]
The actual true-core boundary therefore has
\[
                              a_E=\frac7{12}.
\tag{7}
\]
No change of E or its frame has been made. The facts used in
(6), including \(a_0<1.415\), follow by positive squaring from
(1). The true core has its flat side \(a=7/12\) for
\(0\le b\le1/2\).

## 3. A one-angle D support with a secant coefficient

For either choice (4), and for
\[
                 1\le q\le\bar q:=\frac{327}{250}=1.308,
\]
define
\[
 T_{c,q}(z)=cW(z)+q-S(q+c\sin z,c\cos z)+Lz.
\tag{8}
\]
We prove the whole-interval support inequality
\[
           T_{c,q}(z)\ge T_{c,q}(0)=(q+c)(1-c_0)
                         \qquad(-h\le z\le h).
\tag{9}
\]

The rational bounds used throughout this proof are
\[
 \begin{gathered}
 1.978787<R<1.978788,\qquad .8992140<c_0<.8992141,\\
 \cos h>.7648,\qquad .6442<\sin h<.6445,\qquad
 \cos h+\sin h>1.409.
 \end{gathered}
\tag{10}
\]
Positive square comparisons give the radical bounds. The degree
six/eight cosine and degree seven/nine sine Taylor polynomials
give the trigonometric bounds, as in the two cited fixed-stress
proofs.

For \(z\le0\), the second force component exceeds the first,
because
\[
 c\{\cos(-z)+\sin(-z)\}-q\ge c-q>0.
\]
The support is diagonal. Its derivative is
\[
 L-c\{(c_0+\tfrac12)\cos(-z)+(c_0-\tfrac12)\sin(-z)\}<0.
\tag{11}
\]
The brace is positive and concave in \(-z\). Its two endpoint
values, multiplied by \(c\ge9/5\), exceed \(L\le21/20\);
for the right endpoint (10) gives the explicit reserve
\[
 \frac95\{1.399214(.7648)+.399214(.6442)\}-\frac{21}{20}
                  =\frac{3347816367}{2500000000}>0.
\tag{12}
\]
Thus moving a negative z to zero cannot increase (8).

For \(z\ge0\), a support maximizer cannot have \(b=0\).
Indeed the second force is at least \((9/5)(.7648)\), the
first is at most \(1.308+2(.645)\), and
\[
 \frac95(.7648)-\frac{1.308+2(.645)}{3.8}
                       =\frac{164577}{237500}>0.
\tag{13}
\]
Since \(a_0+1/2>1.9\), this makes the derivative of the
support objective at zero positive. The only possibilities
are therefore the diagonal and the interior full-circle point.

On the diagonal branch,
\[
                T'_{c,q}(z)=L-c(c_0-\tfrac12)(\cos z-\sin z)
                              >L-.4c>0.
\tag{14}
\]
There is at most one transition from that branch to the
interior branch: the difference of the force components,
\(q+c(\sin z-\cos z)\), is strictly increasing.

On the interior branch, put
\[
 A=q^2+c^2,\qquad B=qc,\qquad
 N(z)=\sqrt{A+2B\sin z},\qquad C(z)=-RN''(z).
\]
Then
\[
 T''_{c,q}(z)=-c(\cos z+\sin z)+C(z).
\tag{15}
\]
We have \(2\le A/B\le5/2\). The positive-coefficient
formula for \(N''''\) in Section 3.1 of the
[preferred theorem](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md)
shows that C is concave on \([0,h]\), so
\[
 C(z)\le C(0)+C'(0)z,\qquad
 C(0)=\frac{Rq^2c^2}{(q^2+c^2)^{3/2}},\qquad
 C'(0)=\frac{Rqc\{(q^2+c^2)^2-3q^2c^2\}}
                  {(q^2+c^2)^{5/2}}.
\tag{16}
\]
Both quantities in (16) are strictly below one on the stated
coefficient range. For \(C(0)\), its expression increases with q
because \(q^2<2c^2\). At \(q=\bar q\), the exact square reserves are
\[
 \begin{split}
 (\bar q^2+4)^3-Q\bar q^4\,16
                  &=\frac{701921249413489}{244140625000000}>0,\\
 (\bar q^2+81/25)^3-Q\bar q^4(81/25)^2
                  &=\frac{790423415455617}{762939453125000}>0.
 \end{split}
\tag{17}
\]
For the derivative, write \(\rho=q/c\in[1/2,3/4]\). The derivative
of
\[
          \frac{\rho(1-\rho^2+\rho^4)}{(1+\rho^2)^{5/2}}
\]
has the sign of \(1-7\rho^2+7\rho^4\), which is negative
on this interval. Convexity in \(\rho^2\) reduces that assertion
to its values \(-5/16\) and \(-185/256\) at the two endpoints.
Since \(c\le2\), it follows that
\[
 C'(0)\le\frac{26R}{25\sqrt5}<1,\qquad
                    3125-676Q=\frac{298784}{625}>0.
\tag{18}
\]
Consequently \(C(z)<1+h=1.7<c\). Equation (15) is strictly
negative on the entire interior branch. The diagonal part
increases, and the interior part is concave, so the minimum on
\([0,h]\) is at zero or h.

It remains to compare those endpoints. At h the support is
interior for every q in the range, by (10). Its increment is
\[
 \Delta_{c,q}
 =c(\cos h+\sin h)-\frac c2+\frac q2+(q+c)c_0
       -R\sqrt{q^2+c^2+2qc\sin h}+Lh.
\tag{19}
\]
Its derivative with respect to q is \(c_0-a_*\le0\), where
\(a_*\ge c_0\) is the primary coordinate of the support point.
Thus it suffices to use \(q=\bar q\). The norm upper bounds
are \(3.014\) for \(c=2\) and \(2.826\) for \(c=9/5\).
Their square reserves using \(\sin h<.6445\) are, respectively,
\[
 \begin{split}
 3.014^2-\{\bar q^2+4+4\bar q(.6445)\}&=\frac{327}{250000},\\
 2.826^2-\{\bar q^2+81/25+(18/5)\bar q(.6445)\}
                                      &=\frac{369}{625000}.
 \end{split}
\tag{20}
\]
Substitution of (10) in (19) therefore gives
\[
 \Delta_{2,\bar q}>
          \frac{2719161}{12500000}>\frac15,\qquad
 \Delta_{9/5,\bar q}>
          \frac{13368889}{62500000}>\frac15.
\tag{21}
\]
This proves (9). All interval reductions used actual support
branches or derivative signs; (17), (20), and (21) are fixed
coefficient and intrinsic endpoint substitutions.

## 4. The exact negative-DE gain

Set \(q=\sec s\), for \(0\le s\le h\). It belongs to the range
of (9), since
\[
                 \bar q(.7648)-1=\frac{28}{78125}>0.
\tag{22}
\]
Use multiplier q on the actual negative DE3 inequality.
By (7), its weighted projection is
\[
                qP_{DE3}(-s)=q a_D-\frac7{12}\tan s+b_E.
\tag{23}
\]
The \(b_E\) term cancels exactly with EH0, whose multiplier
remains one. If TD0 has error z and multiplier c, the resulting
D force is precisely \((q+c\sin z,c\cos z)\). If TD2 has
nonpositive error, first use its published pointwise comparison
with virtual aligned TD0, and then use (9) at \(z=0\).

The actual DE demand differs from the reference demand q in
(8), including the constant term from (23), by
\[
                 q(W(s)-1)+\frac7{12}\tan s
                 =\frac{13}{12}\tan s-\frac12(q-1).
\tag{24}
\]
The D baseline in (9) exceeds its \(q=1\) value by
\((q-1)(1-c_0)\). Thus the net gain over the old fixed baseline is
\[
 G(s)=\frac{13}{12}\tan s-(c_0-\tfrac12)(\sec s-1).
\tag{25}
\]
On the entire interval,
\[
                 G(s)\ge\left(\frac{21}{20}+\frac1{390}\right)s.
\tag{26}
\]

Here is an exact polynomial proof. Since \(c_0-1/2<2/5\),
multiply the corresponding lower bound for
\(G(s)-(21/20)s\) by the positive \(\cos s\). With
\(K=13/12\) and \(L_0=21/20\), the resulting expression is
\[
                 F(s)=K\sin s+\frac25(\cos s-1)-L_0s\cos s.
\tag{27}
\]
Use \(S_7(s)\) and \(C_6(s)\) for the positive sine and cosine
coefficients, and \(C_8(s)\) for the negative cosine coefficient.
After division by \(s>0\), this gives
\[
 \begin{split}
 \frac{F(s)}s\ge{}&
 \frac1{30}-\frac s5+\frac{31}{90}s^2+\frac1{60}s^3
 -\frac5{144}s^4-\frac1{1800}s^5\\
 &+\left(\frac{L_0}{720}-\frac K{5040}\right)s^6
                       -\frac{L_0}{40320}s^8.
 \end{split}
\tag{28}
\]
Discard the two positive coefficients at degrees three and six.
Bound each higher negative power by its value of \(s^{j-2}\)
at h times \(s^2\). The quadratic coefficient is larger than
\(13/40\), with exact reserve
\[
 \frac{31}{90}-\frac5{144}h^2-\frac1{1800}h^3
       -\frac{L_0}{40320}h^6-\frac{13}{40}
                         =\frac{85898351}{38400000000}>0.
\tag{29}
\]
Finally
\[
 \frac1{30}-\frac s5+\frac{13}{40}s^2
              \ge\frac1{30}-\frac{(1/5)^2}{4(13/40)}
              =\frac1{390}.
\tag{30}
\]
Since \(0<\cos s\le1\), (27)--(30) prove (26) for positive s.
At zero both sides vanish.

## 5. Nonpositive A and TD primary alternatives

Use the preferred weights \(k=31/40,l=31/20,c=2\) and
charge \(L=21/20\). Let S denote the sum of the magnitudes
of the selected nonpositive GA3/AB2 errors, and let w be the
magnitude of a selected nonpositive TD2 error; absent alternatives
contribute zero. Delete those arguments and the DE argument
inside the reference four-circle expression. Its signed sum is
\[
                                  S+w+s.
\tag{31}
\]
Both variations remain at most h.

Keep the old H/G/B circle estimates in the
[preferred theorem](HAND_G3_HIGH_GA_LOW_EH_SECONDARY_OWNER_FOUR_CIRCLE_EXCLUSION.md).
Replace just its D estimate by (9). Those independent estimates
still give the strict charged baseline reserve \(7/10000\).
The modified D baseline and DE gain have already been combined
in (25).

The independent negative-A and negative-TD pointwise comparisons
from the
[negative-intermediate theorem](HAND_G3_NEGATIVE_INTERMEDIATE_ERRORS_FIXED_STRESS_EXCLUSION.md)
give gains at least
\[
       \frac{1121983}{10^6}S,\qquad \frac{409}{350}w.
\tag{32}
\]
They do not modify (23) or its cancellation at E. Consequently
the actual positive stress is strictly greater than
\[
 \begin{split}
 &\frac7{10000}-L(S+w+s)
       +\frac{1121983}{10^6}S+\frac{409}{350}w+G(s)\\
 &\qquad\ge
 \frac7{10000}+\frac{71983}{10^6}S+\frac{83}{700}w+\frac{s}{390}
 >0.
 \end{split}
\tag{33}
\]
Feasibility would make this demand-minus-projection sum
nonpositive, a contradiction.

## 6. Small nonnegative A total

Use \(k=39/50,l=63/50,c=9/5,L=103/100\). A single
nonnegative A primary, or two A primaries with nonnegative
signed total \(a\le1/6\), contributes at least \(l j(a)\),
where
\[
                    j(a)=W(a)-1-S(\sin a,1-\cos a).
\]
The
[signed A-combination theorem](HAND_G3_COMBINING_THE_TWO_A_PRIMARY_ERRORS.md)
justifies this for both signs of the individual primary errors.
The fixed low-angle proof in the
[positive-A TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md)
gives, on this entire range,
\[
                  B_0+La+l j(a)>\frac{49}{15000}.
\tag{34}
\]
It uses only the full-circle H/G/B block estimates and the
zero-angle sorted D baseline. Thus (9) supplies exactly its
needed D estimate after the secant DE collection.

For a nonpositive TD2 error \(-w\), use the secant TD comparison
in Section 2 of the
[positive-A negative-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md).
Its pointwise gain is at least \(.9cw=1.62w\). For arbitrary TD0,
put \(w=0\) and retain its actual angle.
After deleting the A primary arguments, DE, and TD2 when selected,
the virtual signed sum is \(s+w-a\), with both variations at most h.
Combining (26) and (34) therefore makes the actual stress greater
than
\[
       \frac{49}{15000}
       +\left(\frac1{50}+\frac1{390}\right)s+\frac{59}{100}w
       >0.
\tag{35}
\]
This proves the second regime in Section 1. Each comparison uses
the same actual E flat side and the same four sorted outer circles.
No original-owner conversion or frame alignment is inferred.
