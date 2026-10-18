# The opposite-sign outer pair in the jump-two class

This note proves one continuous branch of the proposed three-row quarter-increment
table. It is a hand proof:
the only scalar comparisons are the two endpoint rows printed below.
It does not assert the other branches of that table.

All terminating decimals in this note denote exact rational numbers.
Set

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 c=\sqrt{Q/2}-\frac12,\quad
 p=\frac{13}{200},\quad q=\frac{203}{200},\quad
 \lambda=\frac34.
\]

An outer boundary state has own-frame coordinates \((a,b)\), with
\(0\le b\le a\), satisfying

\[
 (a+1/2)^2+(b+1/2)^2=Q.
\]

Its positive marker is

\[
 \ell(a,b)=-\frac9{100}+pa+qb.                                \tag{1}
\]

Consider an outer source with negative sign and an outer target with
positive sign. Write their positive coordinates as \((a,b)\) and
\((A,B)\), and let \(\phi\) be their true frame difference. The
corrected pair cost in the jump-two class is

\[
 C=\phi-\ell(a,b)-\ell(A,B),\qquad
 \pi-\frac7{10}\le\phi\le\pi+\frac7{10}.                    \tag{2}
\]

Suppose the source negative-primary axis separates the squares. In the
axis numbering of the pair kernel this is axis 4. Its exact inequality is

\[
 M=a-A\cos\phi-B\sin\phi-W(\phi)\ge0,\qquad
 W(\phi)=\frac{1+|\cos\phi|+|\sin\phi|}{2}.                 \tag{3}
\]

**Theorem.** Every pair satisfying (1)--(3) obeys

\[
 \boxed{C>\frac{163}{200}=.815.}                              \tag{4}
\]

The reflected, reversed formulation has the same corrected cost and
inherits the same bound whenever its physical signed axis is the image
of (3).

## 1. Large frame differences need no separation estimate

Write \(a=a(b)\) along the outer arc. Implicit differentiation gives

\[
 a'(b)=-\frac{b+1/2}{a+1/2}=-r,\qquad 0<r\le1.
\]

Consequently
\(\ell'(b)=q-pr\ge q-p>0\). The maximum marker value is at
the diagonal endpoint \(a=b=c\). Squaring gives \(c<9/10\), so

\[
 \ell(a,b)\le-\frac9{100}+(p+q)c
 <-\frac9{100}+\frac{27}{25}\frac9{10}=\frac{441}{500}.
\]

For every \(\phi\ge13/5\), therefore,

\[
 C>\frac{13}{5}-2\frac{441}{500}
 =\frac{209}{250}=.836>.815.                                 \tag{5}
\]

It remains to consider the one closed interval

\[
 I=[\pi-7/10,13/5].                                         \tag{6}
\]

This interval lies in the second quadrant. In particular
\(W=(1-\cos\phi+\sin\phi)/2\) throughout it.

## 2. A single multiplier eliminates both state variables

Since \(M\ge0\), subtracting \(\lambda M\) can only lower the
cost. In the resulting expression the source-state term is

\[
 -(p+\lambda)a-qb.
\]

Its derivative along the arc is

\[
 (p+\lambda)r-q\le p+\lambda-q=-\frac15<0.
\]

Its minimum is therefore exactly
\(-(p+q+\lambda)c\), at the diagonal source endpoint.

The target-state term is

\[
 (\lambda\cos\phi-p)A+(\lambda\sin\phi-q)B.
\]

Enlarge the target arc to its whole circle, with center
\((-1/2,-1/2)\) and radius \(R\). The minimum of a linear
function on that circle gives the valid lower bound

\[
 \frac{p+q-\lambda(\cos\phi+\sin\phi)}2-RN(\phi),
\]

where

\[
 N(\phi)^2=p^2+q^2+\lambda^2
       -2\lambda(p\cos\phi+q\sin\phi).                     \tag{7}
\]

No premise about the location of the target support minimizer is used.
Combining these estimates with the second-quadrant expression for
\(W\) proves

\[
 \begin{split}
 C\ge F(\phi)
 &:=\phi+\frac9{50}-(p+q)c+\frac{p+q}{2}
       +\lambda\bigl(\tfrac12-c-\cos\phi\bigr)-RN(\phi)\\
 &=\phi+\frac{219}{200}-\frac{183}{100}c
       -\frac34\cos\phi-RN(\phi).                          \tag{8}
 \end{split}
\]

## 3. The scalar lower bound is strictly concave on the entire interval

First, \(N\ge\sqrt{p^2+q^2}-\lambda>q-\lambda>0\), so all
the following derivatives are legitimate. Direct differentiation of
(7) gives the exact identity

\[
 \boxed{N''+\frac N4
 =\frac{(p^2+q^2-\lambda^2)^2}{4N^3}>0.}                    \tag{9}
\]

For completeness, if \(f=N^2=A+B\cos\phi+D\sin\phi\), then
\(f''=A-f\) and

\[
 4N^3(N''+N/4)=2Af-f^2-(f')^2
              =A^2-B^2-D^2.
\]

Substituting \(A=p^2+q^2+\lambda^2\),
\(B=-2\lambda p\), \(D=-2\lambda q\) gives (9).

The elementary bound \(\pi>157/50\) implies
\(13/5<5\pi/6\). Hence throughout \(I\),
\(\sin\phi\ge1/2\). Also

\[
 \cos\phi\le-\cos(7/10)
 \le-\left(1-\frac{(7/10)^2}{2}\right)
 =-\frac{151}{200}<-\frac34.
\]

Using also \(\cos\phi\ge-1\) in (7), we obtain

\[
 N^2\le p^2+q^2+\lambda^2
       -2\lambda(-p+q/2)
 =\frac{2333}{2500}<1.                                      \tag{10}
\]

As \(R<2\), equations (8)--(10) now yield the particularly simple
uniform curvature estimate

\[
 F''=\lambda\cos\phi-RN''
 <\lambda\cos\phi+\frac{RN}{4}
 <-\frac9{16}+\frac12=-\frac1{16}.                          \tag{11}
\]

Thus the minimum of \(F\) on \(I\) is at one of its two
endpoints.

## 4. Two rational endpoint rows

The following deliberately coarse bounds suffice:

\[
 R<\frac{1979}{1000},\qquad c<\frac9{10},\qquad
 \pi>\frac{6283}{2000}=3.1415.                               \tag{12}
\]

The first two follow by squaring. The last is implied by the
Machin/alternating-series proof of \(\pi>3.14159\) in
`LOW_HIGH_ALIGNED_CONTACT_HAND_PROOF.md`.

Here are the complete trigonometric and root estimates used at the
endpoints. All entries are rational numbers; the square-root column
is checked by substitution into (7) and squaring.

| Endpoint | Sine lower bound | Cosine lower bound | Cosine upper bound | Upper bound for \(N\) |
|---|---:|---:|---:|---:|
| \(\pi-7/10\) | \(644/1000\) | \(-765/1000\) | \(-764/1000\) | \(832/1000\) |
| \(13/5\) | \(515/1000\) | \(-857/1000\) | \(-856/1000\) | \(947/1000\) |

Indeed, the corresponding upper bounds for \(N^2\) are

\[
 \frac{276419}{400000}=.6910475<(.832)^2,
 \qquad
 \frac{44821}{50000}=.89642<(.947)^2.                         \tag{13}
\]

For an explicit check of the trigonometric row, define

\[
 S_m(x)=\sum_{j=0}^m\frac{(-1)^j x^{2j+1}}{(2j+1)!},\qquad
 C_m(x)=\sum_{j=0}^m\frac{(-1)^j x^{2j}}{(2j)!}.
\]

At \(x=7/10\), use
\(\sin x>S_3(x)>.644\) and
\(.764<C_3(x)<\cos x<C_4(x)<.765\).
At \(x=13/5\), use
\(\sin x>S_5(x)>.515\) and
\(-.857<C_7(x)<\cos x<C_6(x)<-.856\).
All follow from the alternating tail; all displayed strict comparisons
are finite rational substitutions.

Substitution of (12)--(13) in (8) gives

\[
 \begin{split}
 F(\pi-7/10)
 &>\frac{6283}{2000}-\frac7{10}+\frac{219}{200}
       -\frac{183}{100}\frac9{10}
       +\frac34\frac{764}{1000}
       -\frac{1979}{1000}\frac{832}{1000}\\
 &=\frac{203993}{250000}=.815972,\\[1ex]
 F(13/5)
 &>\frac{13}{5}+\frac{219}{200}
       -\frac{183}{100}\frac9{10}
       +\frac34\frac{856}{1000}
       -\frac{1979}{1000}\frac{947}{1000}\\
 &=\frac{815887}{1000000}=.815887.
 \end{split}                                                \tag{14}
\]

Strict concavity and (14) prove \(C>.815887>.815\) throughout
(6). Equation (5) proves the rest of the jump-two interval. This
completes the theorem. \(\square\)

`verify_jump_two_outer_opposite_hand.py` optionally replays every
printed rational comparison. It contains no minimizer, root solver,
interval subdivision, or sampled premise.
