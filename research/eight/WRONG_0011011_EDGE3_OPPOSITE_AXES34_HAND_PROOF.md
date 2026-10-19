# Wrong word 0011011: opposite-sign edge 3, axes 3 and 4

**Table-free completion.**
[HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md](formalization/HAND_WRONG_0011011_OPPOSITE_EDGE3_WITHOUT_TABLES.md)
replaces this note's critical-curve brackets and derivative ranges by
one global implicit-envelope argument and whole-domain curvature.
Together with the unchanged contact reductions below, it proves the
complete opposite-sign edge-3 family.

## 1. Statement and dependence

Use exactly the constants, labels, and signed-axis convention of
WRONG_0011011_EDGE3_OPPOSITE_AXES12_HAND_PROOF.md:
\[
\begin{gathered}
 Q=9789/2500,\qquad a(b)=\sqrt{Q-(b+.5)^2}-.5,\qquad
 d=\sqrt{Q/2}-.5,\quad a_0=a(0),\quad b_1=\sqrt{Q-2.25}-.5,\\
 T(b)=.01670+2.42322b-.91744b^2-.95769a(b)b,\\
 L(B)=.03965+3.85510B-1.49748B^2-1.89442a(B)B.
\end{gathered}
\]
All decimals are rational. Write \(a=a(b), A=a(B)\).
This note proves
\[
 C=\phi-T(b)-L(B)>.89777,\qquad 0\leq b,B\leq d,\quad
                          |\phi-\pi/2|\leq.7,                   \tag{1}
\]
under either of the remaining two retained SAT inequalities:
\[
\begin{array}{ll}
3:&a\sin\phi-b\cos\phi-B\geq W,\\
4:&a-A\cos\phi-B\sin\phi\geq W,
\end{array}
\qquad W=(1+\sin\phi+|\cos\phi|)/2.                               \tag{2}
\]
Together with the axes12 companion, this proves the complete edge-3
outer/outer \((-,+)\) row, and its reflected edge-5 row.
The aligned estimate used below is the already proved
\[
 H_{34}(b)=\pi/2-T(b)-L(a(b)-1)>.89778,\quad0\leq b\leq b_1.      \tag{3}
\]
The companion verify_wrong_0011011_edge3_opposite_axes34_hand.py
checks 83 fixed exact comparisons below. It is self-contained arithmetic:
no optimization, adaptive domain cover, or sampled input is used.

We use the elementary derivative formulas and scalar bounds proved in
Section 2 of the axes12 companion. In particular
\[
 .609<T'<1.069,\quad T''<0\ (b\leq.415),\quad T'''>1.6,
\]
\[
 .624<L'<1.176,\quad L''(.5)<0,\quad L'''>3.17,
\]
and both third derivatives are increasing.
For any coordinate \(y\), abbreviate
\[
 u=a(y)+.5,\quad r=(y+.5)/u,\quad r'=Q/u^3,\quad
                         r''=3Q(y+.5)/u^5.                     \tag{4}
\]

## 2. Axis 3 below alignment

Put \(\phi=\pi/2-x\). Since \(L\) increases, the minimum occurs at
the largest permissible target coordinate:
\[
 B=(a-.5)\cos x-(b+.5)\sin x-.5.                                \tag{5}
\]
The full contact domain is
\[
 b,B\geq0,\qquad B\leq a(b)-1,
\]
equivalently \((B+1.5)^2+(b+.5)^2\leq Q\).
Its largest angle is below .571, so no boundary at \(x=.7\) is added.
In particular \(b\leq b_1\) and \(B<.415\).

In this section \(u,r\) refer to the source \(b\). Set
\[
 q=Q+1-2u,\quad z=B+.5,\quad v=\sqrt{q-z^2},\quad
 f_1=(Q-u)/(uq),\quad N=4Qu-2u^2-Q(Q+1).
\]
For \(f=-x(b,B)\), the inverse contact derivatives are
\[
 f_B=1/v,\qquad f_b=f_1-rz/(qv),\qquad
 f_{BB}=z/v^3,\qquad f_{bB}=-r/v^3,                              \tag{6}
\]
\[
 f_{bb}=-\frac{rN}{u^2q^2}
        -\frac z{qv}\left(r'-\frac{2r^2}q-\frac{r^2}{v^2}\right).
                                                                    \tag{7}
\]
Thus \(C_{BB}=z/v^3-L''>0\) throughout the physical domain.
We may minimize first in \(B\).

### 2.1 The interior critical curve and its exit

At \(B=0\), \(C_B<0\) everywhere: \(q(b)\) increases, and the
largest value \(1/\sqrt{q(0)-.25}-L'(0)\) is negative.
At the aligned upper endpoint \(B=a(b)-1\), the derivative is
\[
 D(b)=\frac1{b+.5}-L'(a(b)-1).
\]
It strictly decreases, since
\[
 D'(b)=-\frac1{(b+.5)^2}+L''(a(b)-1)r(b)<0.
\]
The fixed comparisons \(D(.5)>0\) and \(D(.6)<0\) give a unique
exit \(b_*\in(.5,.6)\).
For \(b\geq b_*\) the minimum in \(B\) is the aligned endpoint,
already covered by (3).

For \(0\leq b<b_*\) there is a unique interior minimizer \(B=B(b)\).
It is characterized by
\[
 S(B):=(B+.5)^2+\frac1{L'(B)^2}=q(b).                            \tag{8}
\]
On \(0\leq B\leq.2\), \(S'>0\), since \(L'>0,L''<0\).
The critical curve in (8) exists smoothly through \(0\leq b\leq.6\),
even slightly beyond its physical exit. It increases, and
\[
 B'=\frac r{z-L''v^3}>0,\qquad v=\frac1{L'(B)}.                  \tag{9}
\]
Each of the following brackets is verified just by
\(S(B_{\min})<q(b_{\min})\) and
\(S(B_{\max})>q(b_{\max})\):

| \(b\) interval | \(B(b)\) bracket |
|---|---|
| \([0,.1]\) | \([.0309,.0458]\) |
| \([.1,.2]\) | \([.0457,.0628]\) |
| \([.2,.3]\) | \([.0627,.0819]\) |
| \([.3,.4]\) | \([.0818,.1028]\) |
| \([.4,.5]\) | \([.1027,.1254]\) |
| \([.5,.6]\) | \([.1253,.1499]\) |

### 2.2 A negative third derivative controls the whole reduced minimum

Let \(R(b)=C(b,B(b))\).
Here is an explicit derivative computation for its full interval;
no inference from an approximate minimum is used.
First
\[
 f_1=\frac{Q}{Q+1}\frac1u+\frac{Q-1}{Q+1}\frac1q,
\]
so its second derivative in \(b\) is
\[
 f_1''=\frac Q{Q+1}\left(\frac{r'}{u^2}+\frac{2r^2}{u^3}\right)
 -\frac{2(Q-1)}{Q+1}
                    \left(\frac{r'}{q^2}-\frac{4r^2}{q^3}\right).
                                                                    \tag{10}
\]
Put
\[
 E=r''-\frac{6rr'}q-\frac{3rr'}{v^2}
             +\frac{8r^3}{q^2}+\frac{4r^3}{qv^2}+\frac{3r^3}{v^4}.
\]
The relevant partial derivatives of the cost are
\[
\begin{aligned}
 C_{bbb}&=f_1''-\frac z{qv}E-T''',\\
 C_{bbB}&=-r'/v^3+3r^2/v^5,\\
 C_{bBB}&=-3zr/v^5,\\
 C_{BBB}&=1/v^3+3z^2/v^5-L'''.
\end{aligned}                                                     \tag{11}
\]
Differentiating \(C_B=0\) gives the exact identity
\[
 R'''=C_{bbb}+3C_{bbB}k+3C_{bBB}k^2+C_{BBB}k^3,
                   \qquad k=\frac r{z-L''v^3}.                    \tag{12}
\]
Substitute each fixed bracket from the preceding table into
(10)–(12), with \(v=1/L'(B)\). In the first line of (11), use
\(T'''(b_{\min})\) for the subtracted lower bound. The resulting
upper bounds are:

| \(b\) interval | Upper bound for \(R'''\) |
|---|---:|
| \([0,.1]\) | \(-.9\) |
| \([.1,.2]\) | \(-.78\) |
| \([.2,.3]\) | \(-.65\) |
| \([.3,.4]\) | \(-.57\) |
| \([.4,.5]\) | \(-.54\) |
| \([.5,.6]\) | \(-.55\) |

In particular \(R''\) strictly decreases.
At \(b=.5\), equation (8) gives the explicit bracket
\[
 .12539102082<B(.5)<.12539102083.
\]
Substitution into the exact reduced Hessian
\[
 R''=f_{bb}-T''-\frac{r^2}{v^3(z-L''v^3)}                         \tag{13}
\]
gives \(R''(.5)>.06\), and (6) gives \(R'(.5)>.00025\).
Hence \(R''>.06\) throughout \([0,.5]\).

At the single rational source value \(b=.495\), (8) gives
\[
 .12421535815<B(.495)<.12421535816.
\]
The exact contact evaluation then gives
\[
 R(.495)>.89779,\qquad |R'(.495)|<.0001.
\]
Its angle is the explicit positive arctangent
\[
 \tan x=\frac{(a-.5)v-(b+.5)z}{(a-.5)z+(b+.5)v}<.31.
\]
Strong convexity gives, on the whole first interval,
\[
 R>.89779-\frac{.0001^2}{.12}>.89777.                             \tag{14}
\]
On \([.5,b_*]\), \(R'\) is concave by (12), and starts positive.
It can have no crossing from negative to positive after that positive
initial value. Thus \(R\) has no interior minimum there; its minimum
is at .5 or \(b_*\). The former is covered by (14), and the latter
is the aligned cost (3). This proves the complete lower half of axis 3.

## 3. Axis 3 above alignment

For \(\phi=\pi/2+x\), the maximal target is
\[
 B_{\max}=(a-.5)\cos x+(b-.5)\sin x-.5.
\]
It is less than \(\sqrt{Q-2a_0}-.5<.543<d\), so there is no
diagonal clamp. At a positive contact,
\[
 C_x=1-L'(B_{\max})(B_{\max})_x>1-1.176(.4)>0,
\]
since \((B_{\max})_x\leq b-.5<.4\).
The feasible interval therefore reduces to its first endpoint:
alignment, or \(B_{\max}=0\) with \(b\in[b_1,d]\).

The latter is exactly the common zero exit proved in Section 4 of the
axes12 companion:
\[
 (a(b)-.5)\cos x+(b-.5)\sin x=.5,\qquad x<.31,\qquad x_b>1.25.
\]
For clarity, its proof uses the four corner values on
\([b_1,d]\times[.31,.7]\), separate concavity, and
\[
 x_b=\frac{r\cos x-\sin x}
           {(b-.5)\cos x-(a-.5)\sin x}>\frac{.5}{.4}.
\]
These same comparisons are replayed in this component.
Thus its cost \(\pi/2+x-T(b)-L(0)\) increases, as \(T'<1.069\).
It reduces to the aligned endpoint. Axis 3 is now complete.

## 4. Primary-label bounds

For use with axis 4 define
\[
 M(a)=-T\!\left(\sqrt{Q-(a+.5)^2}-.5\right).
\]
Then \(M'=T'(b)/r(b)\).
The following uniform lower bound is elementary:
\[
                             M'>.76.                             \tag{15}
\]
Indeed \(g(b)=T'(b)-.76r(b)\) has
\[
 g''=\frac{3Q\{.95769Q-1.238845(b+.5)\}}{u^5}>.7.
\]
The last inequality uses \(Q>3.9,u<2,b+.5<1.4\), and the
numerator bracket \(>2\). At \(b=.84\),
\(g>.00726, |g'|<.016\), so
\(g>.00726-.016^2/1.4>0\).

We also need the upper bounds
\[
 M'<.85\quad(d\leq a\leq1.1),\qquad
 M'<1.051\quad(d\leq a\leq1.2).                                  \tag{16}
\]
For either \(m=.85\) or \(m=1.051\),
\[
 (T'-mr)''=
 \frac{3Q\{.95769Q-(.478845+m)(b+.5)\}}{u^5}>0.
\]
The endpoint comparisons \(M'(d)<.85\), \(M'(1.1)<.85\), and
\(M'(1.2)<1.051\) therefore imply (16) by convexity of \(T'-mr\).

## 5. Axis 4 below alignment

For \(\phi=\pi/2-x\), the least source primary coordinate is
\[
 a=.5+(A+.5)\sin x+(B+.5)\cos x.                                 \tag{17}
\]
The right side increases in \(x<\pi/4\), since \(A\geq B\);
thus \(a\geq1+B>d\), with no clamp. Its positive speed satisfies
\[
 a_x^2=Q-(a-.5)^2>Q-.915^2.
\]
By (15) and the strict comparison
\(.76^2(Q-.915^2)>1\), the contact cost has
\[
 C_x=-1+M'(a)a_x>0.
\]
It flows down to alignment, proving (1) in this half.

## 6. Axis 4 above alignment

Write \(\phi=\pi/2+x\). The least source primary coordinate is
\[
 a=\max(d,a_*),\qquad
 a_*=.5+(B+.5)\cos x-(A-.5)\sin x.                               \tag{18}
\]
On an inactive part \(a_*<d\), increasing \(B\) at fixed \(x\)
decreases the cost. It reaches \(a_*=d\) before \(B=d\), because
\[
 .5+(d+.5)\cos(.7)-(d-.5)\sin(.7)>d.
\]
The expression at \(B=d\) decreases in \(x\), so this covers all
angles in question. It therefore suffices to treat active contacts.

### 6.1 For \(B\geq.2\), decrease the target coordinate

On an active contact keep the source coordinate \(b\) fixed and vary
\(B,x\) together to preserve (18). Put
\[
 U=A+.5,\quad r=(B+.5)/U,\quad
 v=(A-.5)\cos x+(B+.5)\sin x>0.
\]
Implicit differentiation gives
\[
 C_B=\frac{\cos x+r\sin x}{v}-L'(B).                             \tag{19}
\]
At fixed \(B\), the quotient in (19) decreases with \(x\):
its derivative is exactly \(-r/v^2<0\).
Thus it suffices to use the angle .7.
Let \(s=\sin(.7),c=\cos(.7)\) and
\[
 F(B)=c+rs-L'(B)\{(U-1)c+(B+.5)s\}.
\]
Writing \(v=(U-1)c+(B+.5)s\) and \(m=s-rc\), its second derivative is
\[
              F''=r''s-L'''v-2L''m+L'r'c.                       \tag{20}
\]
Direct substitutions into this one-variable formula give:

| \(B\) interval | Upper bound for \(F''\) |
|---|---:|
| \([.2,.5]\) | \(-1\) |
| \([.5,.7]\) | \(-3.5\) |
| \([.7,.9]\) | \(-3.2\) |

Consequently \(F\) is concave on \([.2,d]\), and its endpoint bounds
\[
                         F(.2)>.082,\qquad F(d)>.0068
\]
prove \(F>0\). Hence (19) is positive on every such contact.
Decreasing \(B\) decreases both its cost and its angle; it stays on the
same active contact until alignment or \(B=.2\).

### 6.2 For \(B\leq.2\), decrease the angle

Now fix the target \(B\). The contact primary coordinate (18)
decreases with \(x\), and it never exceeds \(1+B\leq1.2\).
Its speed is \(-a_x=v\), where
\[
 v^2=Q-2A-(a-.5)^2.
\]
Let \(q_{\max}=Q-2a(.2)\). If \(a\leq1.1\), (16) gives
\[
                    M'(a)^2v^2
             <.85^2\{q_{\max}-(d-.5)^2\}<1.
\]
If \(a\geq1.1\), the stronger geometric term gives
\[
                    M'(a)^2v^2
                    <1.051^2(q_{\max}-.6^2)<1.
\]
Therefore the active contact cost has \(C_x=1-M'v>0\).
The inactive source-diagonal part has derivative 1.
Decreasing \(x\) consequently decreases the cost all the way to
alignment, where (3) applies. This completes axis 4 and proves (1).

## 7. Whole-row consequence and equality scope

Axes 1/2 in the companion and axes 3/4 here exhaust the retained
signed SAT alternatives. Both notes cover the complete angle interval,
all closed coordinate boundaries, and all contact exits.
Thus the whole outer/outer edge-3 \((-,+)\) row has cost
strictly above .89777, and hence has a positive reserve above the
declared table entry .89765. Reflection gives the corresponding
edge-5 row. This is a pair theorem for the stated labels; its use
in excluding the complete wrong word is the subsequent cyclic sum.
