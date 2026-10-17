# The low/high parallel strip: a contact deformation proved by hand

This note uses the constants, arcs, labels and aligned lower bound in
`LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md`. It proves the entire closed
strip \(|\phi|\le1/50\) for the two opposite-sign source-\(+f\)
low/high regimes. Other pair regimes are outside its assertion.

## Statement

Let the source and target be outer boundary states, one on \(L\) and
one on \(H\), in either order. Write their centres in their own frames
as \((a,-b)\) and \((A,B)\). Let

\[
 h(\phi)=\frac{\cos\phi+|\sin\phi|-1}{2},\qquad
 \beta=\frac9{50},\qquad |\phi|\le\frac1{50}.
\]

Suppose the source \(+f\) axis separates the squares:

\[
 M:=b+A\sin\phi+B\cos\phi-1-h(\phi)\ge0.
\tag{1}
\]

Then the corrected cost satisfies

\[
 \boxed{C:=\phi-\beta h(\phi)
       +\ell_s(a,b)+\ell_t(A,B)>\frac{8833}{10000}.}
\tag{2}
\]

Here \((s,t)\) is either \((L,H)\) or \((H,L)\). The assertion
also holds for the reversed target-axis regimes obtained by reversal
and reflection, because that transformation preserves the cost.

## Uniform bounds

Throughout the strip,

\[
 \cos\phi\ge\frac{4999}{5000},\qquad
 |\sin\phi|\le\frac1{50},
\tag{3}
\]

by \(\cos x\ge1-x^2/2\) and \(|\sin x|\le|x|\). Off zero,

\[
 \begin{array}{ll}
  4899/10000\le h'\le1/2,&\phi>0,\\
  -1/2\le h'\le-4899/10000,&\phi<0.
 \end{array}
\tag{4}
\]

Direct substitution in the outer circle gives

\[
\begin{array}{c|c|c|c}
 &\text{transverse coordinate}&\text{primary coordinate}&
 r=(b+1/2)/(a+1/2)\\ \hline
 L&0\le b<13/40&129/100<a<283/200&0<r<47/100\\
 H&1/2<b<9/10&89/100<a<6/5&0<r\le1.
\end{array}
\tag{5}
\]

At the lower endpoint of \(H\), also \(b_H<103/200\). At the upper
endpoint of \(L\), \(a_L=4b_L<13/10\). The cut equations and their
rational endpoint comparisons are recorded in the aligned-contact
note. For the only additional primary-coordinate comparisons in (5):

\[
 Q-\bigl[(179/100)^2+(33/40)^2\bigr]=\frac{247}{8000}>0,
\]

\[
 (383/200)^2-(Q-1/4)=\frac{13}{8000}>0,
\]

\[
 (17/10)^2+(71/70)^2-Q=\frac{389}{122500}>0.
\]

The last comparison is the outer-circle value at \(a=6/5\),
\(b=3a/7\), and bounds the largest primary coordinate on \(H\).
Finally, \((47/100)(179/100)-33/40=163/10000>0\) proves the low
ratio bound.

The labels increase with the transverse coordinate, and

\[
 \frac{899}{1000}<\ell_L'=q-\mu r<\frac{109}{100},
 \qquad
 \frac{39}{100}<\ell_H'=v+kr<\frac{961}{1000}.
\tag{6}
\]

## Reduction to contact and its derivatives

Fix the source transverse coordinate \(b\). As the target varies
along its type arc, the derivative of its projection in (1) is

\[
 D:=\cos\phi-r\sin\phi>0.
\tag{7}
\]

The target's lowest transverse endpoint never satisfies (1). If the
target is high, its projection plus the source coordinate is at most

\[
 \frac65\frac1{50}+\frac{103}{200}+\frac{13}{40}
 =\frac{108}{125}<1.
\]

If the target is low, the corresponding bound is

\[
 \frac{283}{200}\frac1{50}+\frac9{10}
 =\frac{9283}{10000}<1.
\]

Consequently every feasible pair can be moved, at fixed \(b,\phi\),
to the unique contact \(M=0\) by decreasing \(B\). This cannot
increase the cost, by (6).

At a contact define

\[
 P:=A\cos\phi-B\sin\phi-h'(\phi).
\]

Equations (3)--(5) give \(P>0\), even using the coarse lower bounds

\[
 P>\frac{89}{100}\frac{4999}{5000}-\frac9{10}\frac1{50}-\frac12>0
\]

for a high target, and the analogous stronger bound for a low target.
The implicit derivative and the cost derivative at fixed source \(b\)
are therefore

\[
 B'=-\frac P D<0,\qquad
 C'=1-\beta h'-\ell_t'\frac P D.
\tag{8}
\]

We prove \(C'<0\) to the left of zero and \(C'>0\) to its right.
Thus a contact can always move toward \(\phi=0\) with decreasing
cost until a type boundary is met.

## Low source and high target

### Negative relative angle

On a contact with \(\phi<0\), (1) gives \(B\ge1-b\ge27/40\).
Using the deliberately weaker bounds \(\cos\phi>999/1000\) and
\(-h'>489/1000\),

\[
 P>\frac{999}{1000}A+\frac{489}{1000},\quad
 D\le\frac{51}{50},\quad
 r\ge\frac{47/40}{A+1/2}.
\]

Since \(A>89/100\),

\[
\begin{split}
 \ell_H'\frac P D
 &>\frac{1}{51/50}\left[
 \frac{39}{100}\left(\frac{999}{1000}\frac{89}{100}
                    +\frac{489}{1000}\right)
 +\frac{569}{1000}\frac{47}{40}
  \left(\frac{999}{1000}-\frac{21/2000}{139/100}\right)
 \right]\\
 &=\frac{2224591099}{1890400000}>\frac{117}{100}.
\end{split}
\tag{9}
\]

The second term uses the identity
\((999A/1000+489/1000)/(A+1/2)
=999/1000-(21/2000)/(A+1/2)\).
Since \(1-\beta h'\le109/100\), (8) gives \(C'<-2/25\).

### Positive relative angle

Contact, (3), and (5) give

\[
 B\ge1-b-A\sin\phi\ge\frac{651}{1000}.
\]

Hence \(A<9/8\), because
\((13/8)^2+(1151/1000)^2-Q=24913/500000>0\).
It follows that

\[
 D>\frac{97}{100},\qquad
 P<\frac{16}{25},\qquad
 \ell_H'<\frac{961}{1000}.
\]

Thus

\[
 C'>\frac{91}{100}
 -\frac{(961/1000)(16/25)}{97/100}>\frac{27}{100}>0.
\tag{10}
\]

## High source and low target

### Negative relative angle

The uniform bounds give

\[
 D<\frac{101}{100},\qquad P>\frac{177}{100},\qquad
 \ell_L'>\frac{899}{1000}.
\]

Therefore

\[
 \ell_L'P/D>
 \frac{(899/1000)(177/100)}{101/100}>\frac32,
\]

and (8) gives \(C'<109/100-3/2<0\).

### Positive relative angle

From contact,

\[
 B\ge1-b-A\sin\phi>
 1-\frac9{10}-\frac{283}{200}\frac1{50}
 =\frac{717}{10000}.
\]

Consequently

\[
 r>\frac{5717}{19150},\qquad
 D\ge\frac{619}{625},\qquad
 P\le\frac{9251}{10000}.
\]

The desired product has the explicit upper bound

\[
 \ell_L'P/D<
 \frac{(q-\mu\,5717/19150)(9251/10000)}{619/625}
 =\frac{1372599834881}{1517292800000}<\frac{909}{1000}.
\tag{11}
\]

It follows that \(C'>91/100-909/1000=1/1000>0\).

## Type-boundary continuation and conclusion

For \(\phi<0\), increase \(\phi\) to zero while holding the source
coordinate fixed and maintaining contact. By (8), \(B\) decreases.
Its eventual parallel value is \(1-b\). This is strictly above the
target's minimum: it is at least \(27/40>b_H\) for a high target,
and at least \(1-c>1/10>0\) for a low target. It is no larger than
the initial \(B\), because negative-angle contact implies
\(B\ge1-b\). Therefore this motion stays in both type arcs and
strictly decreases cost.

For \(\phi>0\), decrease \(\phi\) while holding the source
coordinate fixed. Then \(B\) increases. If it reaches its type's
maximum before zero, keep that target endpoint fixed and continue on
contact by setting

\[
 b=1+h-A\sin\phi-B\cos\phi.
\tag{12}
\]

Here \(b'=-P<0\), so decreasing \(\phi\) increases \(b\).
At zero the new source coordinate is \(1-c\) if the target is high,
and \(1-b_L\) if the target is low. Both are inside the source arc:
\(1-c<101/1000<b_L\), while
\(b_H<1-b_L<7/10<c\). Thus this continuation stays in its domain.

Along (12), the cost derivative is

\[
 C'=1-\beta h'-\ell_s'P.
\tag{13}
\]

If the fixed target is high, \(A=B=c\), so
\(P=(c-1/2)(\cos\phi-\sin\phi)<2/5\). By (6), (13) is greater
than \(91/100-(109/100)(2/5)>47/100\).
If the fixed target is low, \(A=a_L<13/10\) and \(B=b_L\), so
\(P<811/1000\). Then (13) is greater than
\(91/100-(961/1000)(811/1000)>13/100\).
Both boundary motions therefore decrease the cost as \(\phi\)
decreases toward zero.

Every feasible pair in (1) has now been moved to an aligned feasible
pair without increasing cost. The exact parallel-contact inequality
in `LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md` gives (2).
