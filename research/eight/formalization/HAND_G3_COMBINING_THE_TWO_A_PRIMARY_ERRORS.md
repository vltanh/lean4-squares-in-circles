# Combining the two signed primary errors adjacent to A

## 1. Local charge inequality

Use the constants and sorted-circle support

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad h=\frac7{10},
 \quad a_0=\sqrt{Q-\frac14}-\frac12,\quad
 c_0=\sqrt{Q/2}-\frac12,
\]

\[
 W(t)=\frac{1+\cos t+|\sin t|}{2},\qquad
 S(f,g)=\max_{0\le b\le c_0}
 \left\{f\left(\sqrt{Q-(b+\tfrac12)^2}-\tfrac12\right)+gb\right\},
\]

\[
                    j(t)=W(t)-1-S(\sin t,1-\cos t).
\tag{1}
\]

Suppose the original witnesses at GA and AB are respectively
GA3 and AB2, with signed errors \(u,v\). Put

\[
                    a=u+v,\qquad 0\le a\le h,
                    \qquad |u|,|v|\le h.
\tag{2}
\]

The individual errors may have different signs. The original
A state may have either sign and either radial kind. Write
its coordinates as \((a_A,y_A)\), and put \(b_A=|y_A|\).
Its true circle and sorting give

\[
 (a_A+\tfrac12)^2+(b_A+\tfrac12)^2\le Q,\qquad
             0\le b_A\le a_A,\quad a_A\le a_0,\quad b_A\le c_0.
\tag{3}
\]

Then the following exact local inequality holds:

\[
\begin{split}
 &W(u)+W(v)-2
 -a_A(\sin u+\sin v)-y_A(\cos v-\cos u)\\
 &\hspace{40mm}\ge j(a).
\end{split}
\tag{4}
\]

Thus, with equal positive multiplier \(l\) on the two original
inequalities, their combined intermediate charge is bounded
below by \(l j(a)\). This is the same charge used for a single
positive primary error in
[the two-positive-error split lemma](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).

## 2. Proof on the whole signed domain

Set

\[
 C=\cos(a/2),\qquad S_0=\sin(a/2),\qquad
                         \delta=\frac{|u-v|}{2}.
\tag{5}
\]

The elementary sum formulas imply

\[
 \sin u+\sin v=2S_0\cos\delta,\qquad
                 |\cos v-\cos u|=2S_0\sin\delta.
\tag{6}
\]

If both errors are nonnegative, then
\(0\le\delta\le a/2\), and

\[
                   W(u)+W(v)-2=(C+S_0)\cos\delta-1.
\tag{7}
\]

The left side of (4) is therefore at least

\[
 F(\delta)=(C+S_0-2a_AS_0)\cos\delta
                         -2b_AS_0\sin\delta-1.
\tag{8}
\]

Its cosine coefficient is positive on the whole domain.
Indeed \(a_0<1.415\), and the alternating Taylor bounds at
\(7/20\) give

\[
 C>.939,\qquad S_0<.343,\qquad
           C-(2a_A-1)S_0>.939-1.83(.343)=.31131>0.
\tag{9}
\]

Hence \(F\) decreases with \(\delta\), and its minimum occurs
at \(\delta=a/2\). At that endpoint it is exactly

\[
             W(a)-1-a_A\sin a-b_A(1-\cos a)\ge j(a),
\tag{10}
\]

where the last inequality is (3) and the definition of \(S\).

If the errors have opposite signs, then
\(a/2\le\delta\le h\), and

\[
                   W(u)+W(v)-2=C(\cos\delta+\sin\delta)-1.
\tag{11}
\]

The left side of (4) is now at least

\[
 G(\delta)=C(\cos\delta+\sin\delta)-1
                     -2S_0(a_A\cos\delta+b_A\sin\delta).
\tag{12}
\]

Differentiating and using \(a_A\ge b_A\) gives

\[
\begin{split}
 G'(\delta)
 &=C(\cos\delta-\sin\delta)
                +2S_0(a_A\sin\delta-b_A\cos\delta)\\
 &\ge(C-2b_AS_0)(\cos\delta-\sin\delta)>0.
\end{split}
\tag{13}
\]

For the strict sign, \(h<\pi/4\), \(c_0<.9\), and

\[
                    C-2b_AS_0>.939-1.8(.343)=.3216>0.
\tag{14}
\]

Thus this branch is minimized at \(\delta=a/2\) as well,
giving (10). This also covers \(a=0\), including two equal
and opposite nonzero errors. The only remaining same-sign
case when \(a\ge0\) is \(u=v=0\), where (4) is immediate.
This proves (4), without an angular subdivision or a sign
assumption on A.

For completeness, the two Taylor reserves used in (9) are
the exact rational inequalities

\[
 \left(1-\frac{x^2}{2}+\frac{x^4}{24}-\frac{x^6}{720}\right)
       \bigg|_{x=7/20}>\frac{939}{1000},
\]

\[
 \left(x-\frac{x^3}{6}+\frac{x^5}{120}\right)
       \bigg|_{x=7/20}<\frac{343}{1000}.
\tag{15}
\]

## 3. Joining the original cycle reductions

Retain the original G0--G2 boundary cycle and its four
sorted outer states H, G, B and D, with respective signed
tangents positive, negative, negative and negative.
The intermediate states A, T and E may have either sign
and either radial kind. Assume the original owners

\[
 HG\in\{0,2\},\quad GA3,\quad AB2,\quad BT2,\quad DE2,\quad EH0,
                     \qquad d_{GA}+d_{AB}=a\ge0.
\tag{16}
\]

These owner patterns are impossible in each of the
following three cases:

* TD2 with \(z=d_{TD}\ge0\);
* TD0 with an arbitrary original signed error.
* TD2 with a nonpositive original signed error.

Here no frame order is assumed. The conclusion follows by
inserting (4) into the already proved scalar reductions,
as follows.

The two original projections are

\[
 P_{GA3}=a_G+a_A\sin u-y_A\cos u,\qquad
 P_{AB2}=a_A\sin v+y_A\cos v+b_B.
\tag{17}
\]

Give both multiplier \(l\). Their G and B terms are
unrotated, and their exact remaining contribution is the
one in (4). In the four-circle force expressions one may
therefore set both lost GA and AB arguments to zero and
use the lower intermediate charge \(l j(a)\).
This is an algebraic force comparison; it does not assert
new original owners or new original frame angles.

In the TD2 case put \(\theta=a+z\). The original variation
bound gives

\[
 \theta\le u_++v_++z<h.
\tag{18}
\]

After deleting \(u,v,z\), the remaining angles sum to
\(-\theta\). Their total positive variation is at most
\(h-u_+-v_+-z\le h-\theta\), and their negative variation
is their positive variation plus \(\theta\). Consequently
they lie in the enlarged concentration domain used in
[the split lemma](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_SPLIT_CONCAVITY.md).
Both lost arguments may be included as additional virtual
zero angles in that domain. Its necessary scalar is
therefore again

\[
                      B(z)+l j(a)+{\cal E}_{m(z)}(\theta)\le0.
\tag{19}
\]

[The complete endpoint scalar theorem](HAND_G3_TWO_POSITIVE_INTERMEDIATE_ERRORS_COMPLETE_SCALAR_EXCLUSION.md)
makes the left side strictly positive on the whole
\(a,z\ge0,\ a+z<h\) domain, a contradiction.

In the TD0 case, delete only \(u,v\). The remaining signed
sum is \(-a\), with positive variation at most \(h-a\).
The same exact force collection and (4) now give the
necessary inequality used in
[the arbitrary-TD0 theorem](HAND_G3_POSITIVE_INTERMEDIATE_TD0_FOUR_CIRCLE_EXCLUSION.md).
Its low-range charged proof uses only this signed sum,
the variation bound, and the lower bound \(l j(a)\).
Its high-range proof permits both additional virtual zero
arguments in the four-block concentration domain.
That theorem's strict scalar reserves therefore give the
second contradiction as well.

Finally, write a nonpositive TD2 error as \(-s\). After
deleting \(u,v,-s\), the remaining signed sum is \(s-a\).
If its positive and negative variations are \(P,N\), the
original variation bounds give

\[
             P-N=s-a,\qquad P\le h-a,\qquad N\le h-s.
\tag{20}
\]

Indeed \(u_++v_+\ge a\), and deleting any negative part of
u or v only sharpens the second variation bound. Equation
(4) and the secant TD comparison of
[the nonpositive-TD2 theorem](HAND_G3_POSITIVE_INTERMEDIATE_NEGATIVE_TD2_EXCLUSION.md)
therefore give exactly that theorem's enlarged necessary
scalar. The two lost GA and AB arguments are again allowed
as virtual zeros. Its strict low-range and high-range
reserves prove the third contradiction.

This extension covers two positive errors and also either
mixed-sign allocation with nonnegative signed sum, for
both original TD owners and every TD sign. It does not
yet address a negative signed sum.
