# 0011011: four complete mixed edge-3 quarter-one families

## Theorem

At \(Q=9789/2500\), each of the following edge-3 mixed families has
corrected cost \(C>\gamma=17953/20000=.89765\) for every retained
separator and every angle \(\pi/2-.7\le\phi\le\pi/2+.7\):
\[
 (C^-,O^-),\quad(O^+,C^+),\quad(C^+,O^-),\quad(O^+,C^-).
\]
Both pieces of each core state are included. Reflected reversal gives
the corresponding edge-5 families.

The proof uses scalar monotonicity, two concavity arguments, and 68
fixed rational comparisons. It needs neither the aligned theorem nor
a contact strip. The other four mixed edge-3 sign/order families are
separate obligations.

Put
\[
 a_c=7/12,\quad d_c=1/2+\sqrt2/24,\quad
 d=\sqrt{Q/2}-1/2,\quad a_0=\sqrt{Q-1/4}-1/2.
\]
An outer state has
\(a(b)=\sqrt{Q-(b+1/2)^2}-1/2,\ 0\le b\le d\).
Every core state satisfies
\[
 1/2<a\le a_c,\quad0\le b\le d_c.
\]
Write \(\ell=\pi/2-.7\), \(\kappa=a_0-.5\), and \(q=.704\).
The exact bounds used below include
\[
 .899<d<.9,\quad1.4145<a_0<1.415,\quad
 \cos\ell<.645,\quad\sin\ell>.764.
\]

## 1. Two outer chords and one core upper bound

Define the outer labels
\[
 V(b)=-.01025a+.16031b+.63457ab,\qquad
 M(b)=-.02112a+.29090b+.44642ab.
 \tag{1}
\]
For \(r=(b+.5)/(a+.5)\), one has
\[
 r>.261,\qquad r'=\frac{Q}{(a+.5)^3}<1.5.
\]
Direct differentiation yields
\[
 V''=-1.26914r+(.01025-.63457b)r'<0,
\]
\[
 M''=-.89284r+(.02112-.44642b)r'<0.
\]
At the diagonal their derivatives are .17056 and .31202, both positive.
Thus both labels increase and are concave. Their endpoint chord
slopes are strictly greater than \(q=.704\). Consequently
\[
 V(b)\ge V(0)+qb,\qquad M(b)\ge M(0)+qb,
 \tag{2}
\]
where
\[
 V(0)=-.01025a_0,\qquad M(0)=-.02112a_0.
\]
The slopes in (2) are lower bounds; concavity puts the functions
above their endpoint chords.

The negative role-3 core label is
\[
 H(a,b)=.22042-.34492a+.98439b-.05334b^2.
\]
With
\[
 e=.22042-.34492a_c,\qquad g=.98439,
\]
we have
\[
 H(a,b)\le e+gb
 \tag{3}
\]
on the entire core boundary. On the side the difference is
\(-.05334b^2\le0\). On the corner,
\(a_c-a<.025\), \(b\ge.5\), so the difference is at most
\(.34492(.025)-.05334/4<0\).

## 2. A common whole-pair calculation

This section applies to a negative core source and negative outer
target whenever their labels satisfy
\[
 H(a,b)\le e+gb,\qquad L(B)\ge L_0+qB.
\]
We use it for the following two exact rows:

| Family after any reflected reversal | \(e\) | \(g\) | \(L_0\) |
|---|---:|---:|---:|
| \(C^-\to O^-\) | \(.22042-.34492(7/12)\) | .98439 | \(-.02112a_0\) |
| \(O^+\to C^+\), reversed | .04970 | .94831 | \(-.01025a_0\) |

The second row reverses the original pair and reflects both frames.
Its new negative core label is the original \(C_4^+=.04970+.94831b\);
its outer label is the original \(V\). The angle and cost are preserved,
and all four axes are permuted. It is thus enough to prove this
common calculation for both rows.

In these normalized coordinates the cost is bounded below by
\[
 C\ge\phi-e-gb+L_0+qB.
 \tag{4}
\]
Set \(s=\sin\phi,\ c=\cos\phi,\ W=(1+s+|c|)/2\).
The four separating margins are
\[
\begin{array}{c|l}
1&-b+As+Bc-W\\
2&-ac-bs+A-W\\
3&as-bc+B-W\\
4&a-Ac+Bs-W.
\end{array}
\tag{5}
\]
The calculations below only use necessary inequalities from (5).
Relaxed coordinate bounds need not themselves belong to the boundary.

### 2.1. Axis 1

Its inequality gives \(b\le As+Bc-W\). In (4), this yields
\[
 C\ge\phi-e+L_0+gW-gAs+(q-gc)B.
\]
The last expression increases with \(B\): its derivative is
\(grs+q-gc>0\), since
\(q-.98439(.645)>0\). Its value at \(B=0\) therefore gives
\[
 F_1(\phi)=\phi-e+L_0+gW-ga_0\sin\phi.
 \tag{6}
\]
This lower bound is valid even if the relaxed value \(B=0\) is not
itself a feasible separating state.

On the lower half,
\[
 F_1'=1-\frac g2\sin\phi-g\kappa\cos\phi.
\]
This derivative is positive at \(\ell\) and increases thereafter:
\(\kappa\sin\ell-\frac12\cos\ell>0\).
On the upper half the derivative is
\(1+\frac g2\sin\phi-g\kappa\cos\phi>0\).
Thus \(F_1\) is increasing over the whole interval, and the two rows
satisfy
\[
 F_1(\ell)>.922>\gamma.
 \tag{7}
\]

### 2.2. Axis 2, lower half

Since \(a>1/2\),
\[
 b\le\frac{A-W-\frac12\cos\phi}{\sin\phi}.
\]
Substitution into (4) gives an expression increasing with \(B\),
with derivative \(gr/s+q>0\). Set \(B=0\) to obtain
\[
 F_2(\phi)=
 \phi-e+L_0+\frac g2+
            g\frac{\cos\phi-\kappa}{\sin\phi}.
 \tag{8}
\]
Its derivative has the same sign as
\[
 1-g+\cos\phi\{g\kappa-\cos\phi\}>0,
\]
because \(g<1\), \(g\kappa>.645>\cos\phi\).
The whole lower interval is therefore bounded by its left endpoint:
\[
 F_2(\ell)>.945>\gamma.
 \tag{9}
\]

### 2.3. Axis 2, upper half

Put \(x=\phi-\pi/2\). Using \(a\le a_c\) gives
\[
 b\le\frac{A+a_c\sin x-W}{\cos x}.
\]
As above the expression increases with the outer coordinate, so its
value at \(B=0\) bounds the cost below by
\[
 U_2(x)=\pi/2+x-e+L_0+\frac g2
              -g\kappa\sec x-\frac g{12}\tan x.
 \tag{10}
\]
Both \(\sec x\) and \(\tan x\) are convex on \([0,.7]\).
Thus \(U_2\) is concave. For both rows,
\[
 U_2(0)>1.11,\qquad U_2(.7)>1.11.
 \tag{11}
\]

### 2.4. Axis 3

Its inequality implies
\(B\ge W-a_c\sin\phi+b\cos\phi\).
The coefficient \(q\cos\phi-g\) is negative, so using \(b\le d_c\)
in (4) gives
\[
 C\ge\phi-e+L_0+q(W-a_c\sin\phi)+(q\cos\phi-g)d_c.
\]
Put \(C_0=-e+L_0+q/2-gd_c\).
On the lower half this is
\[
 F_3(\phi)=\phi+C_0-\frac q{12}\sin\phi
                            +q(d_c+.5)\cos\phi,
 \tag{12}
\]
and on the upper half it is
\[
 \phi+C_0-\frac q{12}\sin\phi+q(d_c-.5)\cos\phi.
\]
The derivatives are bounded below respectively by
\[
 1-q(d_c+7/12)>0,\qquad1-q(d_c-5/12)>0.
\]
The expressions agree at the quarter angle and increase throughout.
For both rows,
\[
 F_3(\ell)>1.058>\gamma.
 \tag{13}
\]

### 2.5. Axis 4, lower half

Since \(a\le a_c\), \(A\ge d\), its inequality implies
\[
 B\ge\frac{W-a_c+d\cos\phi}{\sin\phi}.
\]
In (4) also use \(b\le d_c\). This gives
\[
 C\ge\phi+C_0-\frac q{12}\csc\phi
                     +q(d+.5)\cot\phi.
 \tag{14}
\]
Let \(L=q(d+.5)\), so \(0<L<1\).
The elementary inequality \(\tan x\ge x\) gives
\(\cot\phi\ge\pi/2-\phi\) on the lower interval. Therefore (14) is
at least
\[
 L\pi/2+(1-L)\ell+C_0-\frac q{12\sin\ell}>1.23
 \tag{15}
\]
for both rows. This is a bound on the entire interval, with no
stationary-point assumption.

### 2.6. Axis 4, upper half

Here \(A\le a_0\) and \(\cos\phi\le0\), so the necessary bound is
\[
 B\ge\frac{W-a_c+a_0\cos\phi}{\sin\phi}.
\]
The resulting cost lower bound is
\[
 U_4(x)=\pi/2+x+C_0-\frac q{12}\sec x-q\kappa\tan x.
 \tag{16}
\]
It is concave on \([0,.7]\), and both endpoint values exceed 1.26.
This completes all four axes for the first two families in the theorem.

## 3. Positive core to negative outer

For this family the exact cost is
\[
 C=\phi-.01449+1.04240b+M(B).
\]
By (2) and \(1.04240>q\),
\[
 C\ge\phi+c_0+q(b+B),\qquad c_0=-.01449-.02112a_0.
 \tag{17}
\]
For \(\phi\ge.95\), the right side is greater than .905.
It remains only to consider \(\ell\le\phi\le.95\), wholly below
the quarter angle.

For axis 1, \(b+As+Bc\ge W\) implies
\[
 b+B\ge W-a_0s.
\]
The corresponding lower cost is
\[
 Z_1(\phi)=\phi+c_0+q(W-a_0\sin\phi).
\]
Its derivative exceeds
\[
 1-q\sqrt{1/4+\kappa^2}>0.
\]
Hence \(Z_1\ge Z_1(\ell)>.912\).

For axis 2, \(-ac+bs+A\ge W\), together with \(a>1/2\), gives
\[
 b+B\ge b\ge\frac{W+\frac12c-a_0}{s}.
\]
Its cost is consequently bounded below by
\[
 Z_2(\phi)=\phi+c_0+q/2+
                      q\frac{\cos\phi-\kappa}{\sin\phi}.
\]
The derivative numerator is \(1-q+c(q\kappa-c)\).
On this short interval, \(q\kappa>.64\), \(0<c<.645\); thus it is
at least \(1-q-.645(.005)>0\).
The left endpoint gives \(Z_2(\ell)>.929\).

For axis 3, \(as+bc+B\ge W\) gives
\[
 b+B\ge W-a_c\sin\phi
 =.5-\frac1{12}\sin\phi+\frac12\cos\phi\ge5/12.
\]
Equation (17) is therefore greater than
\(\ell+c_0+5q/12>1.119\).

Finally axis 4 cannot occur in this early interval. Its margin is
bounded above by
\[
 a_c-d\cos\phi+d\sin\phi-1
 \le a_c-d\cos(.95)+d\sin(.95)-1<0.
\]
Together with the direct late bound, this proves the whole third family.

## 4. Positive outer to negative core

The exact target core label is \(.16823+.62312B\), and the source
outer label is \(V(b)\). Since \(V\) increases from \(-.01025a_0\),
the cost, independently of its separator, obeys
\[
 C=\phi+V(b)+.16823+.62312B
 \ge\ell-.01025a_0+.16823>1.024>\gamma.
\]
This proves the entire fourth family.

## 5. Coverage and arithmetic

Section 2 treats two whole families through an explicit reversible
normalization and proves all four retained axes on both angle halves.
Sections 3 and 4 treat the two remaining claimed families.
Every estimate holds for the whole core side/corner union and the
whole outer arc. All thresholds are strict, including interval endpoints.

The companion checker performs 68 fixed exact comparisons. It verifies
the two chord slopes, the core upper bound, the displayed derivative
reserves, and every scalar endpoint or whole-interval constant in the
proof. It uses integer rational arithmetic, square-root brackets, and
alternating trigonometric series. No polynomial subdivision, sampled
minimum, optimization, or numerical contact search enters the theorem.
