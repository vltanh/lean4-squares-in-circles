# Small-mismatch sign rigidity without candidate tangent cuts

**Status:** Complete table-free conditional hand proof. This closes the
**sign-rigidity subgate of G5 once \(S\le1/10\) is known**. It does not
prove either mismatch contraction that reaches that threshold, any G/T/H/D
tangent cut, the remaining final contraction, or the unrestricted theorem.

## Theorem

Assume the established G0–G2 reductions for a packing of eight unit
squares at squared radius \(q\le Q=9789/2500\), with surviving exterior
quarter word \(0101011\) and cyclic roles \((H,G,A,B,T,D,E)\). Let
\(d_i\) be its actual frame increments after removing the prescribed
quarter turns, and set
\[
 I=\{H,A,B,T,D\},\qquad S=\sum_{i\in I}|d_i|.
\]
If \(S\le1/10\), then the six endpoints of the three zero-quarter
edges have **nonzero** own-frame transverse coordinates and the signs
are forced:
\[
 (\sigma_H,\sigma_G,\sigma_A,\sigma_B,\sigma_T,\sigma_D)
             =(+,-,+,-,+,-).
\]
With the G2 reflection normalization, \(u_E\le0\) as well. The assertion
makes **no** hypothesis about original separating-axis owners, radial
charts, G/T tangent cuts, or the signs of any other square.

## 1. Uniform bounds valid for every exterior center

Write the center in its own nearest-axis frame as
\((a,-\sigma b)\), with \(a\ge b\ge0\). The G0 central \(1/12\)-disk
and the second central-depth argument give, for every exterior square,
\[
 a>107/200.
\tag{1}
\]
Disk containment implies
\[
                    (a+1/2)^2+(b+1/2)^2\le Q.
\tag{2}
\]
The following *strict* bounds follow without radial boundary
normalization:
\[
 a<17/12,\quad b<9/10,\quad a+b<9/5.
\tag{3}
\]
Indeed, \( (23/12)^2+(1/2)^2=565/144>Q\) proves the
first, \(2(7/5)^2=98/25>Q\) proves the second using \(a\ge b\),
and Cauchy gives
\((a+b+1)^2\le2Q<(14/5)^2\) for the third. All comparisons are
exact rational inequalities.

For \(0\le v\le1/10\), put
\[
 W(v)=\frac{1+\cos v+\sin v}{2}.
\]
The alternating elementary bounds for sine and cosine give
\[
 W(v)\ge1+\frac v2-\frac{v^2}4-\frac{v^3}{12}
        \ge1+\frac{569}{1200}v.
\tag{4}
\]
Consequently
\[
 \frac9{10}+\frac{17}{12}v
 <1+\frac{569}{1200}v
 \le W(v),
\tag{5}
\]
because the gap is at least
\(1/10-(377/400)(1/10)=23/4000>0\).

## 2. Any two same-side neighbors with a small zero-quarter frame
##    increment overlap in their interiors

**Lemma.** Let two exterior unit squares satisfy (1)–(3). Suppose their
nearest-axis quarter increment is zero, their physical frame difference
is \(d\), \(|d|\le1/10\), and their signed transverse coordinates have
the same sign (allowing either coordinate to be zero). Then they have
intersecting interiors.

**Proof.** Reverse the common transverse axis if necessary, so that
the two own-frame center coordinates are \((a,b)\) and \((A,B)\),
where \(a\ge b\ge0\), \(A\ge B\ge0\). Put \(v=|d|\).
In the first frame the second center is
\[
             (A\cos d-B\sin d,\ A\sin d+B\cos d).
\]
For the first local horizontal axis, the absolute center separation is
at most
\[
\begin{aligned}
 |A-a|+A(1-\cos v)+B\sin v
 &<\frac{529}{600}+\frac{17}{2400}+\frac9{100}\\
 &=\frac{2349}{2400}<1.
\end{aligned}
\tag{6}
\]
Here (1),(3) yield
\(|A-a|<17/12-107/200=529/600\), while
\(1-\cos v\le v^2/2\le1/200\) and \(\sin v\le1/10\).

For the first local vertical axis consider the two signs of the
relative rotation.

* If the rotation moves the target center toward positive transverse
  coordinates, its second coordinate is
  \(A\sin v+B\cos v\ge0\). Since \(A\ge B\) and
  \(\cos v\ge\sin v\),
  \[
    A\sin v+B\cos v
       \le\frac{A+B}{2}(\sin v+\cos v)
       <\frac9{10}(1+v)\le\frac{99}{100}<1.
  \]
  The first center's transverse coordinate is \(b<9/10\).
  Their absolute difference is therefore strictly less than 1.

* For the opposite rotation, the target transverse coordinate is
  \(B\cos v-A\sin v\), which lies between
  \(-17v/12\) and \(9/10\). Therefore the absolute difference
  from \(0\le b<9/10\) is strictly below
  \(9/10+(17/12)v<W(v)\), by (5).

Thus the center-separation projection is strictly less than \(W(v)\)
on *both* axes of the first square. Interchanging the two squares
repeats the same argument on *both* axes of the second square,
since the frame difference only changes sign.

The projection half-widths of the two unit squares sum to exactly
\((1+\cos v+\sin v)/2=W(v)\) on each of those four axes. Thus none
of the four original separating-axis-test (SAT) axes separates the
squares. The SAT for convex squares then forces intersection of their
open interiors. This contradicts the packing condition and proves the
lemma. Its strict comparisons cover axis ties, \(v=0\), and every
radial chart or chart junction. \(\square\)

## 3. Apply the lemma to the actual three zero-quarter edges

The surviving word has exactly the three zero-quarter edges
\[
                         H\to G,\qquad A\to B,\qquad T\to D.
\]
Since their indices lie in \(I\), the hypothesis \(S\le1/10\) gives
\(|d_H|,|d_A|,|d_T|\le1/10\). By the lemma their transverse signs
**cannot be equal**. If either transverse coordinate were zero, it
could be assigned the sign of the other square without altering the
geometry, contradicting the lemma. Therefore both coordinates are
nonzero, and the signs are opposite.

For each such edge \(i\to i+1\), the already established physical gap
satisfies
\[
 g_i=d_i+\alpha_i-\alpha_{i+1}>19/25,\qquad
 \alpha_j=\sigma_j\arctan(b_j/a_j).
\tag{7}
\]
It follows that
\[
                  \alpha_i-\alpha_{i+1}>
                       19/25-1/10=33/50>0.
\tag{8}
\]
Of the two *opposite-sign* possibilities, source negative/target
positive makes the left side nonpositive. Hence source positive/target
negative is compulsory. Apply this to HG, AB, TD to obtain the six
stated signs. The E weak sign is the independent G2 reflection result.

No frame-angle mesh, state partition, SAT-owner selection, or
stationary-family bound was used. \(\square\)

## Dependency and remaining gate

\[
\boxed{G0+G1+G2+S\le1/10\Longrightarrow
 (H,G,A,B,T,D)=(+,-,+,-,+,-),\quad u_E\le0.}
\]
This lemma can be inserted into G5 **after** a proof of
\(S\le13/50\Rightarrow S<1/10\). It does not prove that contraction,
nor the subsequent \(S<3/200\) contraction. No Lean source or CI is
modified.
