# Wrong word 0010111: all opposite-sign outer zero-quarter secondary cases

## Statement

For the rational role labels in short_hand_labels.json, every outer/outer
pair on a zero-quarter edge 0, 1, or 3, with signs \((+,-)\), separated
by secondary axis 1 or 3, has corrected cost

\[
 C>\frac{449}{500}=.898>\frac{17953}{20000}.
\]

The angle domain is the entire closed interval \(|\phi|\le7/10\).
Thus this is a proof of all six remaining opposite-sign secondary
branches, including exact aligned contacts. It is not a claim about
the four same-sign secondary branches or any quarter-one branch.

The companion verify_short_outer_zero_opposite_hand.js verifies 134
fixed rational comparisons. It does not subdivide a continuous domain,
search for stationary points, or call an optimizer. All continuous
reductions used below are proved here.

## 1. Coordinates and the six coefficient rows

Put

\[
 Q=\frac{9789}{2500},\quad R=\sqrt Q,\quad
 d=\sqrt{Q/2}-\frac12,\quad a_0=\sqrt{Q-\frac14}-\frac12,
\]
\[
 a(b)=\sqrt{Q-(b+\frac12)^2}-\frac12,\qquad 0\le b\le d.
\]

Write \(r_b=(b+1/2)/(a(b)+1/2)\). Then

\[
 a'=-r_b,\quad 0<r_b\le1,\qquad
 r_b'=\frac{Q}{(a(b)+1/2)^3}>0.                 \tag{1}
\]

For an original axis-3 pair, reflect and reverse it. This preserves
\(\phi\), the corrected cost, and the signs \((+,-)\), and converts
axis 3 to source axis 1. Its primary label coefficients change signs
under this normalization. Every row consequently has the form

\[
 C=\phi+c_*+L(b)+T(B),\qquad
 L(b)=pa(b)+qb,\quad T(B)=vA(B)+tB,             \tag{2}
\]
\[
 b+A(B)\sin\phi+B\cos\phi\ge
 W(\phi):=\frac{1+|\sin\phi|+\cos\phi}{2}.       \tag{3}
\]

The full table is as follows. Every decimal in the table is exact.

| Original edge | Original axis | \(c_*\) | \(p\) | \(q\) | \(v\) | \(t\) |
|---:|---:|---:|---:|---:|---:|---:|
| 0 | 1 | −.24463 | 0 | .94766 | .13422 | 1.03828 |
| 0 | 3 | −.24463 | .13422 | 1.03828 | 0 | .94766 |
| 1 | 1 | .08753 | 0 | .9994 | −.09133 | .88074 |
| 1 | 3 | .08753 | −.09133 | .88074 | 0 | .9994 |
| 3 | 1 | −.45320 | .51554 | 1.19909 | −.19335 | .76744 |
| 3 | 3 | −.45320 | −.19335 | .76744 | .51554 | 1.19909 |

All six functions \(L,T\) are strictly increasing in their transverse
coordinate, since \(q>\max(p,0)\) and \(t>\max(v,0)\).

The quantitative facts used repeatedly are

\[
 1.399<d+\tfrac12<1.4,\quad
 1.914<a_0+\tfrac12<1.915,\quad R<2.
\]
\[
 b_0:=1-d\in(.1,.101),\qquad
 H_0:=\sqrt{Q-(b_0+\tfrac12)^2}\in(1.885,1.886),
 \quad r_{b_0}<.319,                           \tag{4}
\]
\[
 \left(\frac{a_0+1/2}{d+1/2}\right)^3<2.57,\qquad
 \left(\frac{1.886}{1.399}\right)^3<2.46.       \tag{5}
\]

All are strict rational square comparisons.

## 2. A contact reduction near zero

In this section \(-.1\le\phi\le.1\). Put \(s=\sin\phi,c=\cos\phi\).
The inequalities

\[
 d(\sin .1+\cos .1)<W(.1),\qquad
 W(.1)-a_0\sin .1>d                           \tag{6}
\]

exclude \(b=0\) and \(B=0\) from (3). For the second assertion, the
function \(W(\phi)-a_0\sin\phi\) decreases on the positive half,
and on the negative half it is greater than 1. For the first,
the largest projection with \(b=0\) is at \(B=d\): its derivative
\(c-r_Bs\) is positive throughout the strip.

Because \(L\) increases, any strict inequality in (3) can be reduced
to equality by lowering \(b\). On equality,

\[
 b(B)=W-A(B)s-Bc,\quad b_B=r_Bs-c<0,
 \quad b_{BB}=r_B's.                          \tag{7}
\]

The admissible contact interval therefore has exactly its two
endpoints at \(B=d\) and \(b=d\). We show below that none of its
interior points can minimize the corrected cost in the four rows
where this contact reduction is needed.

Let \(H(B)=L(b(B))+T(B)\). Differentiating gives the single useful
formula

\[
 \frac{H''}{r_B'}=
 -p\frac{r_b'}{r_B'}(c-r_Bs)^2
 +(q-pr_b)s-v.                                \tag{8}
\]

### 2.1. Edge 0, axis 1: \(-.1\le\phi\le.08\)

Here \(p=0\), so \(H''=-(.13422-.94766s)r_B'<0\).
The contact cost is concave and is minimized at an endpoint.

### 2.2. Edge 0, axis 3: \(-.1\le\phi\le.04\)

Here \(p=.13422,\ v=0,\ q=1.03828\). For \(s\le0\), (8) is
negative. For \(0\le\phi\le.04\), (5) and \(c-s>.959\) give

\[
 \frac{r_B'}{r_b'}\,\frac{H''}{r_B'}
 \le -.13422(.959)^2+1.03828(2.57)(.04)<0.
\]

This contact cost is also concave.

### 2.3. Edge 3, axis 1: \(-.1\le\phi\le.06\)

For \(-.1\le\phi\le0\), drop the negative term \((q-pr_b)s\)
in (8). The remaining upper bound is negative because

\[
 .51554\left(\frac{1.399}{1.915}\right)^3
             \cos^2(.1)>.19335.              \tag{9}
\]

For \(0\le\phi\le.06\), the right side of (8) increases strictly
with \(B\). Indeed \(A\) decreases, \(b\) decreases and \(a\)
increases; hence \(r_b'/r_B'=((A+1/2)/(a+1/2))^3\) decreases.
Also \(c-r_Bs\) decreases, and \(q-pr_b\) increases. Consequently
\(H''\) changes sign at most once, from negative to positive.

At the right contact endpoint \(B=d\), one has \(b\le b_0\).
Thus

\[
 H'(d)
 \le -(1.19909-.51554(.319))
                (\cos .06-\sin .06)+.96079<0.               \tag{10}
\]

Since \(H'\) first decreases and then increases, but is negative
at its right endpoint, it can cross zero only from positive to
negative. Such a crossing is a maximum of \(H\). The minimum of
\(H\) is again at a contact endpoint.

### 2.4. Edge 3, axis 3: \(-.1\le\phi\le.1\)

For the positive half, the right side of (8) decreases with \(B\).
Here \(-p=.19335>0\), and all three positive factors
\(r_b'/r_B'\), \(c-r_Bs\), and \(q-pr_b=.76744+.19335r_b\)
decrease. Thus \(H''\) changes sign at most once, from positive
to negative.

At the left endpoint \(b=d\), the other coordinate satisfies
\(B\le b_0\). Hence

\[
 H'\ge1.19909-.96079-.51554(.319)>0.           \tag{11}
\]

Now \(H'\) first increases and then decreases and is positive at
the left endpoint. It cannot create an interior minimum of \(H\).

For the negative half write \(u=-\phi\). Contact and \(b\le d\)
imply \(B\ge b_0\); explicitly
\(Bc=W+A\sin u-b\ge1-d\).
Therefore \(A+1/2\le H_0\), and (5) gives \(r_b'/r_B'<2.46\).
Equation (8), \(\sin u\ge.99u\), and \(c+r_B\sin u\le1+u\) give

\[
 \frac{H''}{r_B'}
 \le -.51554+.19335(2.46)(1+u)^2-.76744(.99)u<0.
                                                               \tag{12}
\]

The last quadratic is convex; its values at \(u=0,.1\) are
strictly negative. This proves concavity on the negative half.

These arguments account for every contact in the four strips.

## 3. The two contact endpoints

We next prove the required lower bounds at both moving endpoints.
This also checks that the contact reductions above have not hidden
an angle minimization.

### 3.1. The endpoint \(B=d\)

Here \(A=d\) and

\[
 b(\phi)=
 \begin{cases}
 \frac12+(\frac12-d)(s+c),&\phi\ge0,\\
 \frac12+(\frac12-d)c-(\frac12+d)s,&\phi\le0.
 \end{cases}                                                 \tag{13}
\]

On the positive half,
\[
 C'=1-L'(b)(d-\tfrac12)(c-s)>1-1.2(.4)>0.
\]

On the negative half, (13) gives \(b<.245\), whence \(r_b<.41\).
Every one of the four source slopes then exceeds .76. Since

\[
 .76(1.399)\cos(.1)>1,
\]

the derivative of \(C\) is negative. Thus this endpoint is minimized
at \(\phi=0\).

### 3.2. The endpoint \(b=d\)

Set

\[
 K=
 \begin{cases}
 \frac12-d+s+c,&\phi\ge0,\\
 \frac12-d+c,&\phi\le0,
 \end{cases}
 \quad H=\sqrt{Q-K^2},
\]
\[
 X=A+\frac12=cH+sK,\qquad
 Y=B+\frac12=cK-sH.                            \tag{14}
\]

These formulas are the unique point of the outer arc satisfying the
contact line. They give

\[
 B'=-Xf,\qquad
 f=\begin{cases}1-(c-s)/H,&\phi\ge0,\\1+s/H,&\phi\le0,\end{cases}
 \quad C'=1-(tX-vY)f.                         \tag{15}
\]

For \(-.1\le\phi\le0\), one has \(Y<.8,\ X>1.8,\ H>1.885\).
Every target slope \(t-vY/X\) is greater than .76. Therefore

\[
 (tX-vY)f>.76(1.8)(1-.1/1.885)>1.
\]

So \(C'<0\) on the whole negative half.

On the positive half, \(K<.7,\ H>1.85,\ H\le H_0<1.886\), and

\[
 f'=\frac{s+c}{H}-\frac{K(c-s)^2}{H^3}
       >\frac1{1.886}-\frac{.7}{1.85^3}>0.      \tag{16}
\]

If \(v\ge0\), both \(tX-vY\) and \(tY+vX\) are positive, and

\[
 C''=-(tY+vX)f^2-(tX-vY)f'<0.                \tag{17}
\]

It therefore suffices to check the two ends of the positive
angle interval. The only negative-\(v\) row here is edge 3,
axis 1. For its interval \([0,.06]\),

\[
 (tX-vY)f
 \le(.76744(1.915)+.19335(.601))
       \left(1-\frac{\cos .06-\sin .06}{1.886}\right)<1,        \tag{18}
\]

so this endpoint instead increases.

The fixed substitutions in (13)–(14) give values greater than .898
at every endpoint used. At alignment the four distinct endpoint
values are

| Edge | Two aligned endpoint lower bounds |
|---:|---:|
| 0 | .898108872198, .905209290399 |
| 3 | .898099811618, .898103423422 |

For the concave positive endpoint (17), the additional values at
the positive strip limits are also greater than .898; the smallest
is .899965458771 at edge 3, axis 3, \(\phi=.1\).

This proves all four near-zero strips listed in Section 2.

## 4. Explicit support bounds for the rest of the angle range

Here is a common notation for the scalar comparisons used in the
remaining regimes. Choose any positive rational \(\lambda\).
Subtract \(\lambda\) times the left side of (3) minus \(W\) from
(2). Then

\[
 C\ge \phi+c_*+\lambda W+S+
      (v-\lambda s)A+(t-\lambda c)B,           \tag{19}
\]

where \(S\) is any lower bound for \(pa+(q-\lambda)b\) on the outer
arc. We use only these explicit bounds:

\[
 S_{\rm end}=\min\{pa_0,d(p+q-\lambda)\}\quad(p\ge0),
\]
\[
 S_{\rm circ}=-\frac{p+q-\lambda}{2}
                    -R\sqrt{p^2+(q-\lambda)^2},               \tag{20}
\]
and, when \(p<0,\ q-\lambda\le p\), the exact diagonal value
\(S_{\rm diag}=d(p+q-\lambda)\).

The first bound follows by concavity in \(b\), the second by
enlarging the arc to its circle, and the third by differentiating
the affine function along the arc.

Write \(U=v-\lambda s,\ V=t-\lambda c\). If \(U\ge0\), the target
functional \(UA+VB\) is concave and its minimum is at an endpoint.
If \(U<0,V\le U\), its derivative \(-Ur_B+V\le-U+V\le0\), so
the minimum is diagonal. If \(U<0,V\ge0\), the minimum is axial.
More generally, for \(U<0\), the derivative increases with \(B\);
thus \(V-Ur_0\ge0\), where \(r_0=(1/2)/(a_0+1/2)\), proves the
axial minimum. All uses of these tests below are displayed.

The endpoint envelopes from (19) are

\[
 F_a=\phi+c_*+S+\frac{\lambda}{2}+va_0+
 \frac{\lambda}{2}c+
 \begin{cases}
 \lambda(\frac12-a_0)s,&\phi\ge0,\\
 -\lambda(\frac12+a_0)s,&\phi\le0,
 \end{cases}                                                   \tag{21}
\]
\[
 F_d=\phi+c_*+S+\frac{\lambda}{2}+d(v+t)+
 \lambda(\frac12-d)c+
 \begin{cases}
 \lambda(\frac12-d)s,&\phi\ge0,\\
 -\lambda(\frac12+d)s,&\phi\le0.
 \end{cases}                                                   \tag{22}
\]

All multipliers used below are at least .90362. For each such
multiplier, both envelopes decrease on \([-.7,0]\). For (21),
use
\[
 .90362((a_0+\tfrac12)\cos .7-\tfrac12\sin .7)>1.
\]
For (22), the concave function
\((d+1/2)\cos u+(d-1/2)\sin u\) has its minimum at one of
\(u=0,.7\), and the product with .90362 exceeds 1 at both.

For \(\phi\ge0\), \(F_d'>1-.4\lambda>0\), whereas

\[
 F_a'>1-1.043\lambda.                         \tag{23}
\]

Here \(\sqrt{(a_0-1/2)^2+1/4}<1.043\).

The full-circle target envelope on the positive half is

\[
 F_c=\phi+c_*+S+\frac{\lambda-v-t}{2}
       +\lambda(s+c)-RN,
\]
\[
 N^2=v^2+t^2+\lambda^2-2\lambda(vs+tc).        \tag{24}
\]

For this norm,
\[
 N''+\frac N4=\frac{(v^2+t^2-\lambda^2)^2}{4N^3}\ge0.
\]
In all uses of (24) below, \(\sqrt{v^2+t^2}<\lambda\). Since
\(R<2,\ s+c\ge1\), this proves \(F_c''<0\). Only the two angle
endpoints need checking.

### 4.1. Edge 0, axis 1

Use \(\lambda=.94766=q,\ S=0\). For \(\phi\le-.1\), \(U>0\),
so the two target endpoints suffice. Their minimum at \(\phi=-.1\)
is greater than .939476.

For \(\phi\ge.08\), \(V>0\). Thus either \(U\ge0\) and the
endpoint rule applies, or \(U<0\) and the axial endpoint is exact.
Both (21) and (22) increase, and at .08 their lower bounds are
.902116291944 and .956186003149.

Together with Section 2.1, this covers \([-.7,.7]\).

### 4.2. Edge 0, axis 3

Use \(\lambda=.96135,\ S=S_{\rm end}\). On the negative half
\(U>0\); the endpoint lower bounds at \(-.1\) exceed .930480.

On \([.04,.08]\), use the concave circle envelope (24). Its two
lower bounds are .910850327794 and .913714008057.

At \(\phi=.08\), \(U<0\) and \(V-Ur_0>0\). The latter expression
increases with \(\phi\), because its derivative is
\(\lambda(s+r_0c)>0\). Thus the target is axial for all
\(\phi\ge.08\). By (23), \(F_a'>-.003\), so throughout
\([.08,.7]\),

\[
 F_a\ge F_a(.08)-.003(.62)>.912923824426.
\]

Section 2.2 supplies the interval between \(-.1\) and .04.

### 4.3. Edge 1, axis 1

Use \(\lambda=.9994=q,\ S=0\). For \(\phi\le0\),

\[
 V-U=.97207-\lambda(c-s)<0.
\]

If \(U<0\), the target is diagonal; if \(U\ge0\), both endpoints
suffice. The negative-half endpoint minimum occurs at zero and
exceeds .898104038467.

For \(0\le\phi\le.02\), \(U<0\) and
\(\lambda(\cos .02-\sin .02)>.97207\), so the same exact diagonal
support applies. Its envelope increases from the value at zero.

On \([.02,.3]\), the concave circle envelope has endpoint lower
bounds .910049540187 and .963593385453.

At .3, \(U<0\) and \(V-Ur_0>0\), hence the support remains axial
thereafter. Equation (23) gives \(F_a'>-.043\); therefore

\[
 F_a\ge F_a(.3)-.043(.4)>.948105021635
 \quad(.3\le\phi\le.7).
\]

This row needs no contact-curvature argument.

### 4.4. Edge 1, axis 3

First take \(\lambda=.9994\). The source support is exactly
diagonal, since \(p=-.09133\) and \(q-\lambda=-.11866\le p\).
For \(\phi\le0\), \(U=-\lambda s\ge0\), so the endpoint
envelopes apply and decrease to the common value
.898104038467 at zero.

For \(0\le\phi\le.2\), \(U\le0,\ V=\lambda(1-c)\ge0\), so
the target is axial. Its second derivative is negative because

\[
 \tfrac12\cos .2>(a_0-\tfrac12)\sin .2.
\]

At zero and .2 the lower bounds exceed .898104 and .906554.

For \(.2\le\phi\le.7\), use \(\lambda=.93,\ S=S_{\rm circ}\).
The target is still axial, since \(U<0,V>.9994-.93>0\).
Its envelope increases by (23), and its value at .2 exceeds
.904242. This proves the whole row.

### 4.5. Edge 3, axis 1

Take \(\lambda=.90362,\ S=S_{\rm end}\). For \(\phi\le-.1\),

\[
 V-U=.96079-\lambda(c-s)<0,
\]
as is checked at \(-.1\); \(c-s\) only increases as \(\phi\)
moves from \(-.1\) toward \(-.7\). Thus the endpoint rule applies,
and the lower bounds at \(-.1\) exceed .911399.

On \([.06,.3]\), use (24). Its endpoint lower bounds are
.899507729879 and .940601829306.

At .3, \(U<0,V-Ur_0>0\), so the target remains axial thereafter.
Equation (23) now gives \(F_a'>0\); the value at .3 exceeds
.941776. Section 2.3 fills the near-zero strip.

### 4.6. Edge 3, axis 3

For \(\phi\le-.1\), take \(\lambda=.90362,\ S=S_{\rm circ}\).
Here \(U>0\), so the endpoint rule applies. The lower bounds
at \(-.1\) exceed .904513.

For \([.1,.2]\), use \(\lambda=.9635,\ S=S_{\rm circ}\).
Since \(V>1.19909-.9635>0\), either the endpoint rule applies
or the axial endpoint is exact. By (23), \(F_a'>-.005\),
and \(F_d'>0\). Subtracting the conservative loss .0005 from
both values at .1 yields respectively

\[
 .898514881132,\qquad .898571929033.
\]

For \([.2,.7]\), return to \(\lambda=.90362,\ S=S_{\rm circ}\).
Again \(V>0\). Both endpoint envelopes now increase, and their
values at .2 exceed .903292 and 1.012009. Section 2.4 covers
the remaining central interval.

## 5. Coverage and arithmetic

The six rows in Section 1 are precisely the original edges
\(0,1,3\), signs \((+,-)\), and axes \(1,3\). Reflection/reversal
was used only to write each one in the common form (3); no row was
discarded through an additional symmetry assumption.

Every angle interval is covered by a displayed contact reduction,
a support endpoint argument, or the concavity of one explicit
circle envelope. The nearest comparison with the claimed .898
threshold is an aligned endpoint value greater than .898099811618.

The checker obtains sine and cosine brackets from alternating Taylor
sums and square-root brackets by squaring decimal rationals. The
reported 134 comparisons are the numerical substitutions in the
inequalities above. In particular the proof of every interval
comes from the displayed derivative or curvature argument, not
from sampling the interval.

