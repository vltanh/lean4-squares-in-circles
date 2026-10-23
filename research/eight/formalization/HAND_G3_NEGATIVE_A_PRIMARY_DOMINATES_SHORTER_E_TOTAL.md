# A negative A primary absorbs a shorter nonnegative E total

## 1. Scope and conclusion

Retain a G0--G2 necessary boundary cycle at
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},
 \qquad K=\frac{13}{12}.
\tag{1}
\]
The four states H,G,B,D are sorted outer states with signed
tangents positive, negative, negative and negative. Retain
either HG0 or HG2, BT2, and TD2 with nonnegative error z.
E is nonpositive and may have either canonical radial kind.
Its selected DE/EH primaries have nonnegative total e in the
sense of
[the signed E comparison](HAND_G3_COMBINING_THE_TWO_E_PRIMARY_ERRORS.md).
An unselected secondary E argument remains arbitrary.

At A retain one genuine negative primary of magnitude s and
the secondary owner on the other edge. Thus either

* GA3 has error −s, AB0 is arbitrary, A is positive flat core,
  \(b_A<39/250\), and \(s\le1/4\); or
* AB2 has error −s, GA2 is arbitrary, A is positive flat core,
  \(b_A<1/2\), and \(s\le19/50\).

These are the actual same-state alternatives and cuts of
[the negative-A entry theorem](HAND_G3_NEGATIVE_A_PRIMARY_ERRORS_REDUCE_TO_FLAT_CORE.md).
Assume the retained neighboring inequalities and
\[
 \sum_i d_i=0,\qquad
 \sum_i(d_i)_+\le h,\qquad\sum_i(-d_i)_+\le h.
\tag{2}
\]

**Theorem.** No such system exists if \(0\le e\le s\).
The result also applies after an A-only transport preserving
the displayed local, radial, and variation conditions. It
does not assert the case e>s or remove the retained BT2 owner.

## 2. The exact A gain and the E charge

Put
\[
 a_0=\sqrt{Q-\tfrac14}-\tfrac12,
 \qquad d_A=a_0-\tfrac12<\frac{183}{200}=.915.
\tag{3}
\]
For a fixed actual positive flat-core A, the increase in demand
minus projection from zero to negative error −r is
\[
 g(r)=K\sin r-B(1-\cos r),
\tag{4}
\]
where
\[
 \begin{array}{c|cc}
  \text{primary}&B&\text{uniform bound}\\ \hline
  GA3&b_A+1/2&B<82/125,\\
  AB2&1/2-b_A&0<B<2/5.
 \end{array}
\tag{5}
\]
For the second row, the actual negative AB2 inequality gives
\[
 b_A\ge\frac12+(\frac12-b_B)\sec s+K\tan s
                         \ge1-b_B>\frac1{10}.
\tag{6}
\]
The middle expression increases with s: its derivative is
\(\{K+(1/2-b_B)\sin s\}/\cos^2s>0\), using \(b_B<.9\).
Thus (6) uses no additional marker or tangent-cut premise.

The signed E comparison supplies the single lower charge j(e).
Since \(e\le s\le19/50<1/2\), its exact support is entirely
on the axis branch:
\[
                 j(e)=-d_A\sin e-\frac{1-\cos e}{2}.
\tag{7}
\]
The support transition greater than 1/2 is proved in
[the split-concavity theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
Equation (7) holds for either E radial kind; the actual E
charge may be larger.

Let \(x=s-e\ge0\). We claim that every \(l\ge l_0\), where
\[
                  l_0=\frac{1023}{1000},
\]
satisfies
\[
                  l\sec x\{g(s)-g(x)\}+j(e)\ge0.
\tag{8}
\]
The inequality is strict when e>0. The proof below gives a
uniform positive coefficient times sin e.

## 3. One completed square proves the gain comparison

For e>0 put \(q=\tan(e/2)\). The addition formulas give exactly
\[
 \frac{l\sec x\{g(x+e)-g(x)\}+j(e)}{\sin e}
 =l\{K-B\tan x-(K\tan x+B)q\}-d_A-\frac q2.
\tag{9}
\]
On the full domains in Section 1,
\[
                 \tan x\le\alpha x,\qquad q\le\beta e,
       \qquad\alpha=\frac{53}{50},\quad\beta=\frac{51}{100}.
\tag{10}
\]
Indeed tan u/u increases for u>0. At the two maximal arguments,
alternating Taylor bounds give the exact positive reserves
\[
 \alpha\frac{19}{50}C_6(19/50)-S_5(19/50)
                =\frac{88464794072833}{28125000000000000}>0,
\]
\[
 2\beta\frac{19}{100}C_6(19/100)-S_5(19/100)
                =\frac{1744228810080437}{1200000000000000000}>0.
\tag{11}
\]
Here C_6 and S_5 are the ordinary alternating cosine and sine
Taylor polynomials. All cosines before division are positive.

The coefficient of l in (9) is positive. Even using the larger
common bounds B≤82/125, x,e≤19/50, (10) gives
\[
 K-B\tan x-(K\tan x+B)q
          \ge\frac{91109381}{150000000}>0.
\tag{12}
\]
We may therefore replace l by l_0 and d_A by .915 in (9).
For either of the two pairs
\[
            (B_*,M)=(82/125,1/4),\qquad(2/5,19/50),
\tag{13}
\]
we have B≤B_* and x+e≤M. Put
\[
 A=B_*\alpha,\qquad
 D=(B_*+1/(2l_0))\beta,\qquad C=K\alpha\beta.
\tag{14}
\]
After division by l_0, the lower bound in (9) is at least
\[
                  K-\frac{.915}{l_0}-Ax-De-Cxe.
\tag{15}
\]
All coefficients of the loss are positive. Thus e≤M−x gives
\[
 Ax+De+Cxe
 \le DM+(A-D+CM)x-Cx^2
 \le DM+\frac{(A-D+CM)^2}{4C}.
\tag{16}
\]
For the GA and AB rows of (13), respectively, the exact remaining
reserves in (15)--(16) are
\[
 \frac{552075148409}{37954118400000}>.0145,
 \qquad
 \frac{585827209334813}{817199611800000000}>.0007.
\tag{17}
\]
Consequently (9) is greater than \(.0007\), proving (8) with
strict gain greater than \(.0007\sin e\) whenever e>0.
At e=0 both terms of (8) vanish, so the weak assertion holds.

## 4. The reference negative A theorem closes the cycle

Use the already proved negative-flat-core A weights at the
unchanged TD parameter z and at the reference negative magnitude
\[
                             s'=s-e.
\tag{18}
\]
They are the two continuous families of
[the complete negative-A scalar theorem](HAND_G3_NEGATIVE_FLAT_CORE_A_POSITIVE_TD2_COMPLETE_SCALAR_EXCLUSION.md).
Both have \(l>1.023\). Give the actual negative A primary
the positive multiplier \(l\sec s'\), the other A edge
multiplier l, and retain that theorem's remaining multipliers.
In particular both E multipliers equal one.

Inside this one weighted sum, compare the actual A primary
at −s with its algebraic reference at −s'. Its outer G or B
coefficient is unchanged, and its exact demand-minus-projection
gain is
\[
                         l\sec s'\{g(s)-g(s')\}.
\tag{19}
\]
Deleting the designated E arguments contributes at least j(e).
Equation (8) shows that the sum of these changes is nonnegative.
The remaining reference force expression is precisely the
negative-flat-core expression with secondary E owners, magnitude
s', and unchanged z. This is an identity and a support bound
inside the stress; no reference projection is asserted to be
an actual separating witness.

The variation join is exact. If the deleted E arguments have
negative variation n, their positive variation is e+n.
Their deletion changes the signed sum by −e. Replacing −s
by −s' changes it by +e and removes e of negative variation.
Both total variations therefore decrease by e+n, and the
reference angular vector again has sum zero. Its negative A
magnitude remains inside the relevant cut of Section 1.
All four outer-circle states and the actual flat-core A are
unchanged. The reference theorem permits arbitrary T and E
radial kinds and signs and uses G1 only through these preserved
variation conditions.

Its angle concentration and scalar proof consequently make
the reference stress strictly positive, including s'=0 and
z=0. Equations (8) and (19) transfer that contradiction to
the positive weighted sum of the actual original inequalities.
This proves the theorem.

The proof uses exact trigonometric identities, two intrinsic
endpoint Taylor comparisons, and one quadratic maximum in each
of the two actual A-owner cases. It changes no center or frame,
requires no angle mesh, and uses no numerical acceptance premise,
Lean compilation, or CI.
