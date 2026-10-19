# Wrong word 0011011: the symmetric outer/outer regime for every allowed frame angle

**Status.** This is a hand proof of the entire edge-4 outer/outer sign regime
\((+,-)\), for \(-7/10\leq\phi\leq7/10\), at \(Q=9789/2500\).
It replaces a two-variable contact search by calculus and 71 fixed rational
comparisons. It does not claim the remaining signs or the mixed radial cases.
The only prior analytic inputs are the retained-axis reduction for the physical
seven-ring and the symmetric aligned quartic inequality. The label curvature
bound needed here is proved directly below.

## 1. Statement and coordinates

Put
\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\qquad 0\leq b\leq d.
\]
Write \(A=a(B)\), \(a_0=a(0)\), and
\[
 L(b)=\frac{3965}{10^5}+\frac{385510}{10^5}b
      -\frac{149748}{10^5}b^2-\frac{189442}{10^5}a(b)b.
 \tag{1}
\]
These are exactly the rational positive-half edge-4 labels in
WRONG_0011011_MONOTONE_CONTACT_REDUCTION.md. Reflection identifies the target
negative-half label with the negative of (1). Thus the pair cost is
\[
 H=\phi+L(b)+L(B).                                      \tag{2}
\]

In the source frame the source centre is \((a(b),-b)\), and in the target
frame its centre is \((A,B)\). The target frame is rotated by \(\phi\).
Set
\[
 W=\frac{1+|\cos\phi|+|\sin\phi|}{2}.
\]
The two retained source separators are
\[
 b+A\sin\phi+B\cos\phi\geq W,                            \tag{3}
\]
\[
 a(b)-A\cos\phi+B\sin\phi\geq W.                        \tag{4}
\]
Reflected reversal exchanges the two squares, preserves \(\phi\) and (2), and
takes every retained target separator to one of (3),(4). Therefore it suffices
to handle these two source inequalities.

The conclusion is
\[
 H>\gamma,\qquad \gamma=\frac{17953}{20000}.             \tag{5}
\]
For (3), the minimum over the full allowed frame interval is bounded below by
the minimum at \(\phi=0\). That aligned minimum is already proved to exceed
\(\gamma\) in WRONG_0011011_SYMMETRIC_ALIGNED_OUTER_HAND_PROOF.md.

## 2. Scalar label facts

Let \(D=L'\). If \(R(b)=a(b)+1/2\), direct differentiation gives
\[
 D(b)=3.85510-2.99496b
       -1.89442\left(a(b)-\frac{b(b+1/2)}{R(b)}\right),
\]
\[
 D'(b)=-2.99496+1.89442
       \left(\frac{2(b+1/2)}{R(b)}+\frac{bQ}{R(b)^3}\right).
 \tag{6}
\]
Every decimal in this note denotes an exact terminating rational.

Differentiating once more gives the explicit positive expression
\[
 D''(b)=1.89442\left(\frac{3Q}{R(b)^3}
       +\frac{3bQ(b+1/2)}{R(b)^5}\right)
 >\frac{3(1.8)(3.9)}{2^3}>2.                           \tag{6a}
\]
Here \(b\ge0\), \(Q>3.9\), and \(R(b)<\sqrt Q<2\).
Thus \(D''>2\) on \([0,d]\) without a prior label-curvature lemma.
In particular, \(D\) is strictly convex and \(D'\) is strictly increasing.
The following fixed evaluations suffice for everything below.

| Point or expression | Strict rational enclosure |
|---|---|
| \(d\) | \(.899<d<.9\) |
| \(a_0\) | \(1.4145<a_0<1.415\) |
| \(D(0),D(d)\) | both \(<1.176\), and \(D(d)>1.16\) |
| \(D(.5)\), \(D'(.5)\) | \(D(.5)>.6248,\quad -.0311<D'(.5)<0\) |
| \(D(.1),D(.85)\) | both \(<1.02\) |
| \(D(.2),D(.76)\) | both \(<.85\) |
| \(D(.4),D(.6)\) | both \(>.649\) |
| \(D'(.4),D'(.6)\) | \(D'(.4)<0,\quad D'(.6)>.5\) |
| \(D(.56),D'(.56)\) | \(D(.56)>.63268,\quad D'(.56)>.29\) |
| \(D(.66),D'(.66)\) | \(D(.66)>.6933,\quad D'(.66)>.93\) |
| \(D(.67)\) | \(>.703\) |
| \(D(.7),D'(.7)\) | \(D(.7)>.7365,\quad D'(.7)>1.2\) |

Convexity bounds \(D\) above by its endpoint maximum. Strong convexity at
\(b=.5\) bounds it below:
\[
 .6245<.6248-\frac{(.0311)^2}{4}<D(b)<1.176
 \quad(0\leq b\leq d).                                \tag{7}
\]
Consequently \(L\) is strictly increasing. In particular \(D>.6\).

The finite arithmetic companion derives (6) directly from (1). Each radical
bound is checked by squaring positive rationals; trigonometric constants below
use the alternating sine and cosine series. No sampled state or contact
location is used.

## 3. The primary separator is harmless

For \(\phi\leq0\), (4) is impossible, since
\[
 a(b)-A\cos\phi+B\sin\phi-W
 <1.415-.899(.764)-1<0.
\]
For \(0\leq\phi\leq.5\), its left side minus its right side is at most
\[
 a_0-\tfrac12-(d+\tfrac12)\cos\phi
                  +(d-\tfrac12)\sin\phi.
\]
This expression increases with \(\phi\), and at \(.5\) it is less than
\[
 .915-1.399(.8775)+.399(.4795)<0.
\]
Here maximizing the target term at \(B=d\) is valid because
\(-a(B)\cos\phi+B\sin\phi\) increases with \(B\).

Finally, for \(.5<\phi\leq.7\), (4) forces \(B>.6\): if \(B\leq.6\), then
\(A>a(.6)>1.1448\), and its margin is less than
\[
 1.415-1.1448(.764)+.6(.645)-1<0.
\]
Thus in this last case, by (7),
\[
 H>.5+2L(0)+.6(.6)=.9393>\gamma.                       \tag{8}
\]

## 4. Reduction of the secondary separator to equality

In (3), the projection increases strictly with both \(b\) and \(B\), because
\[
 \frac{\partial}{\partial B}(A\sin\phi+B\cos\phi)
 =\cos\phi-\frac{B+1/2}{A+1/2}\sin\phi>0.
\]
Both labels in (2) also increase strictly. Starting at any point satisfying
(3), decrease \(b\), then \(B\) if necessary, until equality holds. Both cannot
reach zero before equality, since \(a_0\sin\phi<1\leq W\).
Hence it suffices to prove (5) on the contact surface.

This reduction takes place in the larger set specified only by the outer
arcs, signs and frame interval. It therefore needs no unproved preservation
of a centre-angle constraint.

## 5. Positive frame angles: contact monotonicity

For \(0\leq\phi\leq.7\), put \(s=\sin\phi,c=\cos\phi\). Equality in (3) gives
\[
 b=\frac12+\left(\frac12-B\right)c
               -\left(A-\frac12\right)s.              \tag{9}
\]
It decreases strictly with \(B\) and \(\phi\). Indeed,
\[
 b_B=\frac{B+1/2}{A+1/2}s-c<0,\qquad
 -b_\phi=\left(A-\tfrac12\right)c
                        -\left(B-\tfrac12\right)s=:v_+>0.
\]
Moreover
\[
 v_+^2\leq(A-\tfrac12)^2+(B-\tfrac12)^2
        =Q-2(A+B).                                    \tag{10}
\]
The right side decreases with \(B\), because \(A+B\) increases.

If \(B\geq.3\), (10) gives \(v_+<.84\), and (7) gives
\[
 H_\phi=1-D(b)v_+>1-1.176(.84)>0.
\]
If \(.15\leq B\leq.3\), (9) confines every contact to
\(.1<b\leq.85\), while \(v_+<.94\). Convexity of \(D\) and the table give
\(D(b)<1.02\), so again
\[
 H_\phi>1-1.02(.94)>0.
\]
The contacts at \(\phi=0\) have \(b=1-B\) in the outer interval in both cases.
Decreasing \(\phi\) thus reaches alignment while decreasing the cost.

For \(0\leq B\leq.15\) and \(.25\leq\phi\leq.7\), (9) gives
\(.2<b<.76\). Now \(D(b)<.85\) and \(v_+<1.05\), so
\[
 H_\phi>1-.85(1.05)>0.
\]
This reduces the remaining work to \(B\leq.15,\ \phi\leq.25\).
The elementary endpoint bounds used here are
\[
\begin{aligned}
 b(.3,.7)&>.5+.2(.764)-.81(.645)>.1,\\
 b(.15,.7)&>.5+.35(.764)-.87(.645)>.2,\\
 b(0,.25)&<.5+.5(.969)-.9145(.2474)<.76.
\end{aligned}
\]
The corresponding radius evaluations are
\[
 Q-2(a(.15)+.15)<.94^2,\quad
 Q-2(a(.3)+.3)<.84^2,\quad Q-2a_0<1.05^2.
\]

## 6. The small positive-angle rectangle

Put \(c_*=400/391\). From (9) and the elementary bounds
\(\sin\phi\leq\phi,\ 1-\cos\phi\leq\phi^2/2\),
\[
 1-B-b
 \leq(a_0-\tfrac12)\phi+\tfrac14\phi^2
 <\left(.915+\tfrac1{16}\right)\phi
 =\frac{391}{400}\phi.
\]
Thus \(\phi\geq c_*(1-B-b)\).

Since \(D'(.15)<0\) and \(D'\) increases, \(L\) is concave on \([0,.15]\).
Its endpoint value satisfies
\[
 L(.15)>L(0)+.15c_*,
\]
so its chord gives \(L(B)\geq L(0)+c_*B\). Consequently
\[
 H\geq c_*+L(0)+\bigl(L(b)-c_*b\bigr).                 \tag{11}
\]

Here is a fixed scalar lower bound for the final parenthesis. On \([0,.6]\),
its derivative \(D-c_*\) is convex and negative at the right endpoint. Such
a derivative permits no interior minimum of its antiderivative; the two
endpoint values exceed \(-.15957\). On \([.6,d]\), its second derivative
is \(D'>.5\). At the rational point \(b=.85\),
\[
 L(.85)-.85c_*>-.15954,\qquad
 |D(.85)-c_*|<.005.
\]
Completing the square therefore gives
\[
 L(b)-c_*b>-.15954-(.005)^2>-.15957.
\]
Equation (11) now yields
\[
 H>c_*+.03965-.15957>.903>\gamma.                     \tag{12}
\]
Together, Sections 5 and 6 settle all nonnegative \(\phi\).

## 7. Negative frame angles: an exact contact speed

Write \(\phi=-x\), \(0\leq x\leq.7\), and \(s=\sin x,c=\cos x\).
The contact is
\[
 b=\frac12+\left(\frac12-B\right)c
                  +(A+\tfrac12)s.                   \tag{13}
\]
It increases strictly with \(x\) and decreases strictly with \(B\). Put
\[
 R=A+\tfrac12,\quad q_B=Q-2B,\quad z=b-\tfrac12,
\]
\[
 v=b_x=Rc+(B-\tfrac12)s>0,\qquad
 K=-b_B=c+\frac{B+1/2}{R}s>0.
\]
The circle equation gives the exact cancellation
\[
 v^2=q_B-z^2.                                        \tag{14}
\]
For \(H=-x+L(b)+L(B)\),
\[
 H_x=-1+D(b)v,\qquad H_B=D(B)-D(b)K.                  \tag{15}
\]
It remains to show that no minimum with \(x>0\) can exist.

## 8. Locating a possible nonpositive \(H_x\)

Suppose \(H_x\leq0\). First, \(B>.67\).
If \(B\leq.67\), then (13) implies \(b\geq1-B\geq.33\).
For \(.4\leq b\leq.6\), equations (7),(14) give
\[
 D(b)^2v^2>.6245^2(Q-1.34-.01)>1.
\]
Outside that \(b\) interval, the monotonicity of \(D'\) and the point bounds
give \(D(b)>.649\), and
\[
 D(b)^2v^2>.649^2(Q-1.34-.16)>1.
\]
Both contradict \(H_x\leq0\).

Second, \(b<.66\) always; and if \(B\leq.7\), then \(b<.56\).
For the latter assertion, on \(b\geq.56,\ B\leq.7\),
\[
 \frac{\partial}{\partial b}(D(b)v)
 =\frac{D'(b)v^2-D(b)(b-\tfrac12)}{v}>0,
\]
because
\[
 .29(Q-1.4-.16)-1.176(.4)>0.
\]
At \(b=.56\), its square is greater than
\[
 .63268^2(Q-1.4-.06^2)>1.
\]
For the global \(b<.66\) assertion, use instead
\[
 .93(Q-1.8-.16)-1.176(.4)>0,\qquad
 .6933^2(Q-1.8-.16^2)>1.
\]
These strict comparisons prove the stated exclusions without solving any
critical-point equation.

## 9. A second derivative direction rules out the minimum

Since \(H_x\leq0\) implies \(D(b)\leq1/v\), (15) gives
\[
 H_B\geq D(B)-\frac{K}{v}.                            \tag{16}
\]
Eliminating \(s,c\) from (13),(14) yields
\[
 J(B,z):=\frac{K}{v}
 =\frac{Q-B-\tfrac12}{R q_B}
      +\frac{z}{q_B\sqrt{q_B-z^2}}.                  \tag{17}
\]
Two useful derivatives are
\[
 J_z=\frac1{(q_B-z^2)^{3/2}}>0
\]
and, for \(z\geq0\),
\[
 J_B=
 \frac{Q-1}{R q_B^2}
 +\frac{(Q-B-\tfrac12)(B+\tfrac12)}{R^3q_B}
 +z\left(\frac2{q_B^2v}+\frac1{q_Bv^3}\right)>0.       \tag{18}
\]

If \(.67<B\leq.7\), Section 8 gives \(z<.06\). Thus
\[
 J(B,z)<J(.7,.06)<.702<D(.67)<D(B),
\]
where \(D(.67)>.703\). Hence \(H_B>0\).

If \(.7\leq B\leq d\), then \(z<.16\).
The single rational bound below proves
\[
 \frac{d}{dB}J(B,.16)<1.2<D'(B).
\]
For its verification set
\[
 q_-=Q-1.8,\quad R_-=\sqrt{Q-1.4^2},\quad
 v_-=\sqrt{q_--.16^2}.
\]
Every positive term in (18) is bounded above by its indicated endpoint bound:
\[
 \frac{Q-1}{R_-q_-^2}
 +\frac{(Q-1.2)(1.4)}{R_-^3q_-}
 +.16\left(\frac2{q_-^2v_-}+\frac1{q_-v_-^3}\right)
 <1.2.                                               \tag{19}
\]
At \(B=.7\),
\[
 D(.7)>.7365,\qquad J(.7,.16)<.727.
\]
Therefore \(D(B)-J(B,.16)>0\) throughout this interval.
Again (16) gives \(H_B>0\).

We have proved the decisive implication
\[
 x>0,\ H_x\leq0\quad\Longrightarrow\quad H_B>0.         \tag{20}
\]

## 10. Boundary completeness

The contact domain in the \((B,x)\)-plane is compact. There is no contact at
\(x=.7\): (13) decreases with \(B\), and even at \(B=d\) its right side exceeds
\[
 .5-.4(.765)+1.399(.644)>.9>d.
\]
For every contact, \(b\geq1-B\); thus the lower \(B\)-boundary is
\(B=1-d,x=0\). At the boundary \(b=d\),
\[
 D(d)^2v^2>1.16^2(Q-1.8-.16)>1,
\]
so \(H_x>0\). Decreasing \(x\) slightly is feasible and strictly decreases
the cost whenever \(x>0\).

An interior minimum with \(x>0\) must have \(H_x=H_B=0\), contradicting (20).
At \(B=d\), a minimum away from the other boundaries would have \(H_x=0\)
and \(H_B\leq0\), because decreasing \(B\) is feasible. This again contradicts
(20). Every minimum therefore occurs at \(x=0\), where \(b+B=1\).

The existing symmetric aligned quartic inequality now proves (5).
This completes the negative-angle half, and hence the whole stated regime.

## 11. Exact arithmetic record and scope

verify_wrong_0011011_symmetric_outer_whole_angle.js executes 71 fixed strict
comparisons using BigInt arithmetic, outward-rounded intervals with denominator
\(10^{12}\), and integer square roots. Its sine/cosine calls are fixed alternating
polynomials of explicitly chosen degrees. The recorded minimum scaled comparison
reserve is \(3959242/10^{12}\). The script contains no adaptive cover, solver,
search, imported discovery dataset, or floating-point acceptance decision.

The calculus proof above is the completeness argument; the script only checks
its displayed finite arithmetic. In particular, it does not infer a global
minimum from a numerical contact search.

This result covers edge 4, OO, signs \((+,-)\), every allowed frame angle and
every retained source or target separating axis. The other OO signs and all
mixed radial cases remain separate obligations for the full 0011011 word.

