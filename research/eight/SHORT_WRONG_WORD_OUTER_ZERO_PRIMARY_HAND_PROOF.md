# Wrong word 0010111: all zero-quarter primary cases

## Statement and scope

This hand proof closes **all fourteen outer/outer primary-axis cases**
on zero-quarter edges 0, 1, and 3 of the rational 0010111 role table.
It also closes the four same-sign secondary cases directed against
the order of the local angles. Thus it proves eighteen of the
twenty-eight zero-quarter outer/outer branches on their full
continuous domains.

All feasible cases proved here have corrected cost greater than
\(17953/20000=.89765\); the weakest displayed lower bound is .92939.
The four impossible cases are excluded directly by geometry.
No inference is made here about the ten remaining secondary cases.

The companion verify_short_outer_zero_primary_hand.js checks only
50 fixed exact scalar comparisons and regenerates the coefficients
from short_hand_labels.json. Its output is
short_outer_zero_primary_hand_arithmetic.json.

## 1. Geometry and notation

Use

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-\frac12,\quad a_0=\sqrt{Q-\frac14}-\frac12.
\]

Both states lie on the outer boundary

\[
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\tfrac12,\quad 0\le b\le d.
\]

Thus \(d\le a\le a_0\), \(a\ge b\), and
\(a'=-r\), where \(r=(b+1/2)/(a+1/2)\in[0,1]\).
The source and target coordinates in their own frames are
\((a,-\sigma b)\), \((A,-\tau B)\).
The zero-quarter frame difference obeys \(|\phi|\le.7\).
Write \(s=\sin\phi,\ c=\cos\phi\) and
\(W=(1+|s|+c)/2\). In particular \(c>0\) and \(W\ge1\).

The original affine labels and their integer coefficients are the
table in short_hand_labels.json. For a normalized edge write

\[
 C=\phi+c_*+pa+\sigma qb-PA-\tau tB.
 \tag{1}
\]

Reflection followed by reversal preserves \(C,\phi\), changes signs
to \((-\tau,-\sigma)\), and negates the constant and primary
coefficient of each reversed label. The axis correspondence is

\[
 \text{source }-e\longleftrightarrow\text{target }+e,\qquad
 \text{source }+f\longleftrightarrow\text{target }+f.
 \tag{2}
\]

We use the already-proved exterior facts
\(\delta>.76\) and the four retained SAT axes:

\[
\begin{array}{c|l}
1&\sigma b+A s-\tau Bc\ge W\\
2&-a c+\sigma b s+A\ge W\\
3&a s+\sigma bc-\tau B\ge W\\
4&a-Ac-\tau Bs\ge W.
\end{array}
\tag{3}
\]

The restrictions role 0 positive and role 2 negative, and the
impossibility of signs \((-,+)\) on a zero edge, leave exactly the
seven zero-edge/sign pairs considered below.

## 2. Four primary-axis cases are impossible

For signs \((+,+)\), axis 4 is impossible. Indeed

\[
 \delta=\phi+\alpha-\alpha'\le\phi+\frac\pi4
\]

implies \(\phi>.76-\pi/4>-.026\).
If \(\phi\ge0\), its projection is at most

\[
 a_0-d\cos(.7)<1.
\]

If \(-.026<\phi<0\), it is at most

\[
 a_0-d\cos(.026)+d\sin(.026)<1.
\]

Both contradict \(W\ge1\). Reflection/reversal excludes axis 2
for signs \((-,-)\). This covers

\[
 (0,++,4),\ (1,--,2),\ (3,++,4),\ (3,--,2).
 \tag{4}
\]

## 3. All six opposite-sign primary cases

Let the signs be \((+,-)\). Either primary axis requires \(\phi>0\).
For nonpositive \(\phi\), the source-primary projection is at most
\(a_0-d\cos(.7)<1\); the reflected target-primary case is identical.

For \(\phi>0\), axis 4 implies

\[
 B\ge z(\phi):=\frac12+(d+\tfrac12)\cot\phi
                   -(a_0-\tfrac12)\csc\phi.
\]

Axis 2 gives the same lower bound for \(b\). In both cases,

\[
 b+B\ge z(\phi)\ge
 z_0(\phi):=\frac12+1.399\cot\phi-.915\csc\phi>0.
 \tag{5}
\]

For the three opposite-sign rows the constant part of (1) satisfies

\[
 c_*+pa-PA>-.264,\qquad q,t>.767.
 \tag{6}
\]

The exact minima of that constant part are respectively greater than
−.12394, −.04167, and −.26313 on edges 0, 1, and 3.
Consequently

\[
 C>\phi-.264+.767z_0(\phi).
 \tag{7}
\]

The right side decreases for \(0<\phi\le.7\). After multiplication
by \(\sin^2\phi\), its derivative has numerator

\[
 1-c^2+.767(.915c-1.399).
\]

This quadratic decreases for \(c\ge.764\), and its value at .764
is negative. Evaluating (7) at .7 gives

\[
 C>1.004058588>1.
 \tag{8}
\]

This proves both primary axes for each of the three opposite-sign
rows, with no further state partition.

## 4. The four remaining same-sign primary cases

By (2), each case can be normalized to signs \((+,+)\) with target
primary separation

\[
 A-a\cos\phi+b\sin\phi\ge W.
 \tag{9}
\]

Again \(\phi>0\). Equation (9) gives \(b\ge z_0(\phi)\).
Since \(a\ge d,\ b\le d\), it also gives

\[
 A\ge r(\phi):=\frac12+(d+\tfrac12)\cos\phi
                       +(\tfrac12-d)\sin\phi.
\]

The function \(r\) decreases. Hence

\[
 A\ge r(.7)>1.31,\qquad
 B\le\sqrt{Q-(r(.7)+\tfrac12)^2}-\frac12<.3.
 \tag{10}
\]

Let

\[
 m=c_*+
 \begin{cases}pd,&p\ge0\\pa_0,&p<0\end{cases}
 -
 \begin{cases}Pa_0,&P\ge0\\Pd,&P<0.\end{cases}
 \tag{11}
\]

This is a lower bound for the constant part of (1).
In all four rows \(q>.767\). The same derivative argument as in
Section 3 shows that \(\phi+qz_0(\phi)\) decreases. Therefore

\[
 C\ge m+.7+qz_0(.7)-.3t.
 \tag{12}
\]

The four fixed substitutions give:

| Original edge | Signs | Axis | Lower bound from (12) |
|---:|:---:|---:|---:|
| 0 | ++ | 2 | 1.040739715181 |
| 1 | -- | 4 | .992615616247 |
| 3 | ++ | 2 | 1.086026620085 |
| 3 | -- | 4 | .929396858934 |

Equations (4), (8), and (12) prove all fourteen zero-quarter primary
branches.

## 5. Four secondary cases have a uniform forward cap

The remaining cases proved in this note are

\[
 (0,++,3),\ (1,--,1),\ (3,++,3),\ (3,--,1).
 \tag{13}
\]

Normalize each by (2) to signs \((-,-)\) and source-secondary
separation

\[
 -b+A\sin\phi+B\cos\phi\ge W.
 \tag{14}
\]

Nonpositive \(\phi\) is impossible, since then its projection is at
most \(B\le d<1\). For \(0<\phi\le.7\), the function
\(A(B)\sin\phi+B\cos\phi\) increases with \(B\), because its derivative
is \(\cos\phi-r\sin\phi>0\). Its maximum is therefore
\(d(\sin\phi+\cos\phi)\). Feasibility in (14) requires

\[
 (d-\tfrac12)(\sin\phi+\cos\phi)\ge\frac12.
\]

The left side increases in this interval and is still below \(1/2\)
at \(\phi=.3\). Thus

\[
 \phi>.3.
 \tag{15}
\]

The normalized coefficients in (1) are:

| Original case | \(c_*\) | \(p\) | \(q\) | \(P\) | \(t\) |
|---|---:|---:|---:|---:|---:|
| \(0,++,3\) | −.06130 | 0 | .99940 | 0 | .94766 |
| \(1,--,1\) | .27086 | −.13422 | 1.03828 | .09133 | .88074 |
| \(3,++,3\) | −.75097 | 0 | .71553 | −.51554 | 1.19909 |
| \(3,--,1\) | .74349 | −.33147 | 1.13360 | .19335 | .76744 |

## 6. A single multiplier closes the secondary cases

Subtract twice the SAT margin in (14). The source coefficients are
\(p\le0\) and \(2-q>0\), so their exact outer minimum is \(pa_0\).
The target coefficients are

\[
 X=-P-2\sin\phi,\qquad Y=t-2\cos\phi.
\]

The full target-circle support gives the scalar envelope

\[
 F=\phi+c_*+pa_0+\frac{2+P-t}{2}
       +2(\sin\phi+\cos\phi)-RN,
\quad
 N^2=P^2+t^2+4+4(P\sin\phi-t\cos\phi).
 \tag{16}
\]

It is strictly concave. The norm identity

\[
 N''+\frac N4=\frac{(P^2+t^2-4)^2}{4N^3}\ge0
\]

and \(\sqrt{P^2+t^2}<1.31,\ R<2\) give

\[
 F''\le-2(\sin\phi+\cos\phi)+\frac R4N
 <-2+\frac{2(3.31)}4<0.
 \tag{17}
\]

For the first, second, and fourth rows, the endpoint values of (16)
at \(.3,.7\) exceed 1.03. Thus these three whole cases are proved.

For the third row, on \([.3,.5]\), the target coefficients satisfy
\(Y\le X<0\). Its exact outer-arc minimum is therefore the diagonal:
the derivative of \(XA(B)+YB\) is \(-Xr+Y\le Y-X\le0\).
The resulting envelope is

\[
 F_d=\phi+c_*+pa_0+1+(\sin\phi+\cos\phi)
            +d\{-P+t-2(\sin\phi+\cos\phi)\}.
 \tag{18}
\]

It is increasing, since
\(F_d'\ge1-2(d-1/2)>0\).
At .3 it exceeds 1.09. On \([.5,.7]\), return to the concave
full-circle envelope (16); both endpoints exceed 1.19.
This proves the third case on its entire domain.

## 7. Exact cover and remaining scope

The preceding proof contains:

* four impossible same-sign primary branches;
* six opposite-sign primary branches with cost greater than 1;
* four same-sign primary branches bounded by (12);
* four secondary branches in (13).

These are eighteen distinct raw branches. They use the exact label
coefficients and the full continuous domains. The four same-sign
secondary branches in the other direction and the six opposite-sign
secondary branches are deliberately left to the separate contact
analysis; this note does not claim them.

