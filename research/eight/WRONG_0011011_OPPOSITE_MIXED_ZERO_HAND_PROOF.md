# Wrong word 0011011: every opposite-sign mixed zero-quarter case

## Statement and scope

For the rational role labels of the word 0011011, every permitted
opposite-sign mixed core/outer zero-quarter case has corrected angular
cost

\[
 C>\gamma=\frac{17953}{20000}=.89765.
\tag{1}
\]

This proves all **24 such signed kind/axis cases**, over the whole
allowed frame interval. Combined with
WRONG_0011011_SAME_SIGN_MIXED_ZERO_HAND_PROOF.md, it closes all 56 mixed
zero-quarter cases. Other quarter classes and outer/outer cases are
separate obligations.

The proof uses one degree-ten polynomial with eleven positive
Bernstein coefficients, fixed endpoint comparisons, and explicit
one-variable curvature arguments. Its companion
verify_wrong_0011011_opposite_mixed_zero_hand.py checks 149 fixed strict
comparisons and writes
wrong_0011011_opposite_mixed_zero_hand_arithmetic.json.
Every terminating decimal in this note is an exact rational.

## 1. Coordinates, labels, and complete normalization

Use

\[
 Q=\frac{9789}{2500},\quad
 d=\sqrt{Q/2}-\frac12,\quad
 a_0=\sqrt{Q-\frac14}-\frac12,\quad
 a_c=\frac7{12},\quad d_c=\frac12+\frac{\sqrt2}{24}.
\tag{2}
\]

The outer positive half is

\[
 a(b)=\sqrt{Q-(b+\tfrac12)^2}-\frac12,\qquad 0\le b\le d.
\tag{3}
\]

The core positive half is the side \(a=a_c\), \(0\le b\le1/2\), followed
by the corner

\[
 a=\frac12+\sqrt{\frac1{144}-(b-\frac12)^2},
 \qquad \frac12\le b\le d_c.
\tag{4}
\]

An actual center in its own frame is \((a,-\sigma b)\).
For a source and target with signs \((+,-)\), the corrected cost is the
frame change plus both positive-half labels.

The frame concentration and consecutive-zero argument, detailed in
the same-sign companion, leave exactly the opposite sign pair
\((+,-)\) on each of zero edges 0, 1, and 4. The exact reflection of
the role table takes edge \(i\) to \(1-i\pmod7\), interchanges the
radial order, and preserves this sign pair, the frame change, and
the cost. Thus it suffices to treat three families with a positive
core source and a negative outer target:

\[
 C=\phi+c_0+gb+F(B).
\tag{5}
\]

Here \(b\) is the core coordinate, \(B\) the outer coordinate, and the
three data rows are:

| Name | \(F(B)\), with \(A=a(B)\) | \(c_0\) | \(g\) |
|---|---|---:|---:|
| \(J\) | \(-.00026 A+.83194 B-.11864 B^2+.17627 AB\) | .00125 | 1.03981 |
| \(P\) | \(.02478+.93015 B+.02363 B^2-.11055 AB\) | .19555 | .63132 |
| \(L\) | \(.03965+3.85510 B-1.49748 B^2-1.89442 AB\) | .04970 | .94831 |

The \(J\) row represents edge 0 with a core source. The \(P\) row is
the reflected reversal of edge 0 with an outer source. The \(L\) row
represents edge 4; its reflected reversal covers the other radial
order. These are exact substitutions from wrong_0011011_labels.json.

We have \(|\phi|\le.7\). Put
\[
 W=\frac{1+|\sin\phi|+|\cos\phi|}{2}.
\]
The four retained signed projections are

\[
\begin{array}{ll}
\text{source }+f:&b+A\sin\phi+B\cos\phi,\\
\text{target }+e:&-a\cos\phi+b\sin\phi+A,\\
\text{target }+f:&a\sin\phi+b\cos\phi+B,\\
\text{source }-e:&a-A\cos\phi+B\sin\phi.
\end{array}
\tag{6}
\]

The earlier cap and gap lemmas exclude the other four signed axes.
The core source's negative primary projection in (6) is always less
than \(a_c<1\), since \(A\ge B\) and \(\cos\phi>|\sin\phi|\).
The target primary case is covered in Section 3 after reversal.
Sections 5--10 prove both transverse cases for each of the three
rows. Thus all four axes are covered. Restoring the reflected
partners gives \(3\cdot4\cdot2=24\) cases.

## 2. Elementary scalar facts and aligned costs

The scalar facts from the same-sign companion will be used repeatedly.
They follow by differentiating (3); the checker repeats the relevant
fixed comparisons. In particular,

\[
 .899<d<.9,\qquad .5589<d_c<.559,\qquad a_0<1.415.
\tag{7}
\]

For an outer label
\[
 F(z)=c+p a(z)+qz+r z^2+s a(z)z,
\]
write \(u=a(z)+1/2\) and \(v=z+1/2\). Then

\[
\begin{aligned}
 F'&=-p\,v/u+q+2rz+s(a-zv/u),\\
 F''&=2r-2sv/u-(p+sz)Q/u^3,\\
 F'''&=-3Q\{sQ+(p-s/2)v\}/u^5.
\end{aligned}
\tag{8}
\]

The labels \(J,P,L\) are strictly increasing. Moreover,

\[
 J''<0,\quad J'''<0,\qquad
 P'>.773,\quad P''>0,\quad P'''>0.
\tag{9}
\]

The third derivative of \(P\) is increasing on \(0\le z\le.9\).
For example its derivative has positive numerator proportional to
\(Q(5v-1/2)-2v^2\), bounded below by \(2Q-2(1.4)^2>0\).
For \(J'''\), the numerator in braces in (8) remains positive even
at \(v=d+1/2\), proving the indicated sign.

Writing \(D=L'\), we have

\[
 D''>2,\quad D>.6245,\quad D'(.6)>.5,\quad
 D(0)>.94831,\quad D(.6)<.94831.
\tag{10}
\]

For completeness, \(D''>2\) follows from

\[
 D''=1.89442\left(\frac{3Q}{u^3}
                   +\frac{3zQv}{u^5}\right)
 >\frac{3(1.8)(3.9)}8>2.
\]

The bound \(D>.6245\) follows from
\(D(.5)>.6248\), \(-.0311<D'(.5)<0\), and completion of a square.

Define the aligned scalar

\[
 A_F(z)=c_0+g(1-z)+F(z).
\tag{11}
\]

Its global lower bounds on \([0,d]\) are

\[
 A_J>.9005,\qquad A_L>.901,\qquad A_P\ge.85165.
\tag{12}
\]

For \(J\), concavity reduces the assertion to \(z=0,d\).
For \(P\), \(P'>g\), so the minimum is \(z=0\), where the value is
exactly .85165.

For \(L\), the strict convexity of \(D\), together with its two
endpoint signs relative to \(g\) in (10), implies that \(A_L\) has
no interior minimum on \([0,.6]\). Its endpoint values exceed
1.03 and .94. On \([.6,d]\),
\(A_L''=D'>.5\). At \(z_*=.8216\),

\[
 A_L(z_*)>.9010079,\qquad |A_L'(z_*)|<.0001.
\]

The uniform strong-convexity bound therefore gives
\[
 A_L(z)>.9010079-(.0001)^2>.901.
\tag{13}
\]

We also use the fixed bounds

\[
\begin{array}{c|c}
 \text{quantity}&\text{strict lower bound}\\ \hline
 A_J(.15)&.9005\\
 A_P(.435)&.926\\
 A_L(.84)&.9014\\
 A_L(.86)&.9028
\end{array}
\tag{14}
\]

The function \(A_L\) is increasing after .84, since \(D(.84)>g\)
and \(D'>0\) there.

## 3. Every primary-owner case

Reverse the target primary axis of (6). For the same three data rows,
the resulting cost and margin are

\[
 C=\phi+F(b)+c_0+gB,\qquad
 M=a-A\cos\phi+B\sin\phi-W\ge0,
\tag{15}
\]

where \(b\) is now outer and \(B\) core.
If \(\phi\le0\), its projection is at most
\[
 1.415-.5589\cos(.7)<1,
\]
so \(\phi>0\). With \(c=\cos\phi,s=\sin\phi\), the bound
\[
 M\le a_0-\frac12-(d_c+\frac12)c+(d_c-\frac12)s
\]
is negative at .45 and increases with \(\phi\).
Thus \(\phi>.45\).

Feasibility also forces \(B>.34\). Otherwise the core is on its side
and
\[
 M\le a_0-\frac12-\frac{13}{12}c-.16s<0.
\tag{16}
\]
The last assertion follows from concavity of
\((13/12)\cos\phi+.16\sin\phi\): both endpoint values at \(0,.7\)
exceed \(a_0-1/2\).

If \(\phi\le.55\), the core cannot even be on its side, since
\[
 M\le a_0-\frac12-\frac{13}{12}\cos(.55)<0
\]
for \(B\le1/2\). Hence \(B>1/2\) in that range.
As \(F(b)\ge F(0)\), all primary costs are bounded below by one of

\[
 .45+F(0)+c_0+\frac g2,\qquad
 .55+F(0)+c_0+.34g.
\tag{17}
\]

All six values, two for each row, exceed .904. This finishes every
primary-owner case without a contact selection.

## 4. Two geometric negative-angle limits

For the transverse cases with negative frame change, write
\(\phi=-x\), \(s=\sin x,c=\cos x\).

If the source \(+f\) separates, its largest possible projection is
\(d_c+d(c-s)\), so feasibility implies
\[
 d_c-\frac12+(d-\frac12)c-(d+\frac12)s\ge0.
\]
The left side decreases and is negative at .32. Thus

\[
 0<x<.32\quad\text{for a source }+f\text{ separator}.
\tag{18}
\]

If the target \(+f\) separates, the largest core projection
\(-a s+bc\) occurs at the core diagonal. Consequently
\[
 d-\frac12+(d_c-\frac12)c-(d_c+\frac12)s\ge0.
\]
This left side also decreases, and is negative at .44152. Thus

\[
 0<x<.44152\quad\text{for a target }+f\text{ separator}.
\tag{19}
\]

In particular \(\cos^2x>.81\) on (19).
Let \(x_{\max}\) denote the unique equality point in the last
geometric expression. At the core diagonal, the target coordinate
equals \(d\) precisely at \(x=x_{\max}<.44152\).

## 5. Source transverse axis: all angles and all three labels

### 5.1. The \(P\) row by a transverse-sum estimate

For positive \(\phi\), the source margin gives

\[
 b+B\ge
 1-(A-\tfrac12)\sin\phi-(\tfrac12-B)(1-\cos\phi)
 \ge1-1.09\phi.
\tag{20}
\]

Here \(A-1/2<a_0-1/2\), \(\sin\phi\le\phi\), and
\(1-\cos\phi\le\phi^2/2\le.35\phi\).
For \(\phi=-x<0\), the corresponding inequality has the opposite
first sign:

\[
 b+B\ge1+(A+\tfrac12)\sin x-(\tfrac12-B)(1-\cos x)
 >1+1.295x.
\tag{21}
\]

Indeed (18) and \(A+1/2>1.399\) give the coefficient
\[
 1.399(1-.32^2/6)-.32/4>1.295.
\]

Since \(P(B)\ge P(0)+.773B\), \(g=.63132<.773\), and \(b\le d_c\),
the common constant

\[
 G=c_0+P(0)+.773+(g-.773)d_c>.914
\tag{22}
\]

is a lower bound for the cost at zero angle. Equations (20)--(21)
give respectively

\[
 C\ge G+(1-.773\cdot1.09)\phi,\qquad
 C>G+(.773\cdot1.295-1)x.
\tag{23}
\]

Both coefficients are positive. This proves the whole \(P\) source-axis
family with a substantial strict margin.

### 5.2. Positive angle for \(J\) and \(L\)

Subtracting \(g\) times the source margin yields the valid lower
expression

\[
 E(\phi,B)=
 \phi+c_0+F(B)+g\{W-A\sin\phi-B\cos\phi\}.
\tag{24}
\]

There is no feasibility assumption on the core coordinate appearing
in this expression: it is simply a lower bound for every feasible
cost. Its angle derivative is

\[
 E_\phi=
 1-g\{(A-\tfrac12)\cos\phi-(B-\tfrac12)\sin\phi\}.
\tag{25}
\]

The norm of the vector in braces is
\[
 \sqrt{(A-\tfrac12)^2+(B-\tfrac12)^2}
 =\sqrt{Q-2(A+B)}.
\tag{26}
\]
The sum \(A+B\) increases with \(B\).

For \(L\), the fixed comparison \(g^2(Q-2a_0)<1\) makes (25) positive
for every \(B\). Therefore \(E(\phi,B)\ge A_L(B)>.901\).

For \(J\), the same argument applies when \(B\ge.15\), because
\[
 g^2\{Q-2(a(.15)+.15)\}<1.
\tag{27}
\]
Concavity gives \(A_J(B)>.9005\) on \([.15,d]\).

If \(0\le B\le.15\), the fixed derivative bound \(J'(.15)>1\) and
concavity imply \(J(B)\ge J(0)+B\). Thus
\[
 E\ge c_0+J(0)+g-.15(g-1)
       +[1-g(a_0-\tfrac12)]\phi-\frac g4\phi^2.
\]
The linear coefficient is positive, and the remaining fixed lower
bound
\[
 c_0+J(0)+g-.15(g-1)-g(.7)^2/4>.907
\tag{28}
\]
handles the complete small-\(B\) range.

### 5.3. Negative angle for \(J\) and \(L\)

Subtracting \(g\) times the source margin now gives

\[
 E(-x,B)=
 -x+c_0+F(B)+
 g\{\tfrac12+(\tfrac12-B)\cos x+(A+\tfrac12)\sin x\}.
\tag{29}
\]

For \(0\le x\le.32\),

\[
 \frac{\partial E}{\partial x}
 \ge-1+g\{1.399\cos(.32)-\tfrac12\sin(.32)\}>0
\tag{30}
\]

for both \(J\) and \(L\). Therefore the aligned bounds (12) apply.
This completes every source-transverse case.

## 6. Target transverse axis at nonnegative angle

The target margin implies

\[
 b+B\ge1-\mathcal E(\phi),\qquad
 \mathcal E(\phi)=\frac1{12}\sin\phi+\frac12(1-\cos\phi)
 \le\frac{31}{120}\phi.
\tag{31}
\]

The core bound \(a-1/2\le1/12\) is the only shape information needed.
Consequently

\[
 C\ge A_F(B)+\phi-g\mathcal E(\phi).
\tag{32}
\]

For every row \(1-31g/120>0\). Hence (12) proves the \(J,L\) rows
immediately.

For \(P\), if \(\phi\ge.06\), (32) is greater than
\[
 .85165+.06(1-31g/120)>.901.
\]
If \(\phi<.06\), the bound \(b\le d_c\) and (31) give
\[
 B\ge1-d_c-.06/12-.06^2/4>.435.
\]
The increasing aligned scalar then gives \(A_P(B)>.926\).
Thus every nonnegative target-angle case is closed.

## 7. Target transverse contact at negative angle

The remaining contact geometry is common to the three labels.
For \(\phi=-x\), \(0<x<x_{\max}\), increasing outer \(B\) increases
the cost. It is therefore enough to set

\[
 B=\frac12+(\frac12-b)\cos x+(a(b)+\frac12)\sin x.
\tag{33}
\]

This is the first feasible target value; it is always positive.
Indeed \(B\ge1-b\ge1-d_c\). The inequality follows directly from
\(\sin x\ge1-\cos x\) on this angle range.
As a function of the core coordinate, \(B\) strictly decreases:

\[
 B_b=-c-ts,\qquad B_{bb}=-\kappa s,\qquad
 t=-a'(b),\quad\kappa=-a''(b).
\tag{34}
\]

On the side \(t=\kappa=0\). On the corner,
\[
 0\le t\le1,\qquad\kappa=12(1+t^2)^{3/2}.
\tag{35}
\]

For each fixed angle, feasible core coordinates form a terminal
interval. On the corner its endpoints can only be the side junction,
the core diagonal, or the first feasible point where \(B=d\).

At the core diagonal define

\[
\begin{aligned}
 B(x)&=\tfrac12+(\tfrac12-d_c)\cos x+(d_c+\tfrac12)\sin x,\\
 w(x)&=(d_c-\tfrac12)\sin x+(d_c+\tfrac12)\cos x,\\
 w'(x)&=(d_c-\tfrac12)\cos x-(d_c+\tfrac12)\sin x.
\end{aligned}
\tag{36}
\]

Thus \(B'=w>0\), \(w''=-w<0\). For
\[
 H_F(x)=-x+c_0+gd_c+F(B(x)),
\]
we have
\[
\begin{aligned}
 H_F'&=-1+F'(B)w,\\
 H_F''&=F''(B)w^2+F'(B)w',\\
 H_F'''/w&=F'''(B)w^2+3F''(B)w'-F'(B).
\end{aligned}
\tag{37}
\]

The following exact bounds will be used:

\[
 w^2>.96,\quad w<1.061,\quad w'<.059,\quad
 w'(.44152)>-.4.
\tag{38}
\]

The lower bound for \(w\) follows from its concavity and the two
endpoints; the slight analytic extension to .44152 has positive
radicands.

## 8. The \(J\) target row at negative angle

### 8.1. Core side

On the side the derivative of the contact cost with respect to the
core coordinate is
\[
 g-J'(B)c>0,
\]
because \(B\ge1-d_c\), \(J'\) decreases, and \(J'(1-d_c)<g\).
The minimum is therefore at the first feasible point, \(B=d\).
Equation (33) then gives

\[
 b=\frac12+(\frac12-d)\sec x+\frac{13}{12}\tan x.
\tag{39}
\]

The derivative of the cost along this boundary has numerator
\[
 s^2-g(d-\tfrac12)s+\frac{13g}{12}-1.
\]
It is positive, by the discriminant bound
\[
 \frac{13g}{12}-1-\frac{g^2(d-\tfrac12)^2}{4}>0.
\tag{40}
\]
The cost increases from its aligned value \(A_J(d)>.9005\).

### 8.2. Core corner

By (9) and (34),
\[
 \frac{d^2}{db^2}J(B(b))
 =J''(B)(c+ts)^2-J'(B)\kappa s<0.
\tag{41}
\]
Thus the contact cost is strictly concave in the core coordinate.
Only its three possible corner endpoints need consideration.
The side junction has just been covered.

At the first feasible point \(B=d\), if \(x\le.41\), the bound
\(b\ge1/2\) gives
\[
 C\ge-.41+c_0+J(d)+g/2>.9056.
\]
If \(x\ge.41\), the inequality \(a\ge d_c\) in (33) gives
\[
 b\ge\frac12+
       \frac{\frac12+(d_c+\frac12)\sin x-d}{\cos x}.
\tag{42}
\]
This right side increases with \(x\), and at .41 it exceeds .5249.
Consequently
\[
 C>-.44152+c_0+J(d)+.5249g>.8999.
\tag{43}
\]

For the core diagonal, (8) gives
\[
 J''(B)\le J''(1-d_c)<-.485,\qquad
 0<J'(B)\le J'(1-d_c)<.905.
\]
Using (38),
\[
 H_J''<-.485(.96)+.905(.059)<0.
\tag{44}
\]
So the minimum is at \(x=0\) or \(x=x_{\max}\).
The former value exceeds 1.02. At the latter \(B=d\), and
\[
 H_J(x_{\max})>
 -.44152+c_0+gd_c+J(d)>.9353.
\tag{45}
\]

This completes the full \(J\) row.

## 9. The \(P\) target row at negative angle

The contact cost decreases with the core coordinate throughout both
side and corner:
\[
 g-P'(B)(c+ts)
 \le g-P'(1-d_c)\cos(.44152)<0.
\tag{46}
\]
It therefore suffices to prove the core-diagonal bound.

The function \(H_P\) in (37) is strictly decreasing on the full
extended interval \([0,.44152]\). Here is a finite curvature proof.
We have \(P'(1-d_c)>.84\). Formula (8) and fixed evaluations give:

| Angle interval | Upper bound for \(P'''(B)\) | Other useful bounds |
|---|---:|---|
| \([0,.1]\) | .331 | \(P''(B)<.236,\ w^2<1.126,\ w'<.059\) |
| \([.1,.3]\) | .513 | \(w^2<1.126,\ w'<0\) |
| \([.3,.44152]\) | .782 | \(w^2<1.06,\ w'<-.256,\ P''>.32,\ P'>.92\) |

These follow from the monotonicity in (9) and the three endpoint bounds
\(B(.1)<.548\), \(B(.3)<.757\), \(B(.44152)<.9\).
The corresponding upper bounds for \(H_P'''/w\) are

\[
\begin{aligned}
 .331(1.126)+3(.236)(.059)-.84&<0,\\
 .513(1.126)-.84&<0,\\
 .782(1.06)-3(.32)(.256)-.92&<0.
\end{aligned}
\tag{47}
\]

Thus \(H_P''\) decreases. At the right endpoint,
\[
 H_P''(.44152)>.0079,\qquad H_P'(.44152)<-.044.
\]
It follows that \(H_P''>0\), that \(H_P'\) increases, and that
\(H_P'<0\) everywhere on the interval. Finally,
\[
 H_P(x)\ge H_P(.44152)>.89779>\gamma.
\tag{48}
\]
This handles the whole \(P\) row.

## 10. The \(L\) target row at negative angle

### 10.1. The entire core side

On the side, solve (33) for \(b\). The contact cost becomes

\[
 S(x,B)=-x+c_0+L(B)+\frac g2+
 g(\frac12-B)\sec x+\frac{13g}{12}\tan x.
\tag{49}
\]

Every such target has \(B\ge1/2\).
Its derivative is bounded below by
\[
 S_x\ge
 \frac{\frac{13g}{12}-1-\frac{g^2(B-1/2)^2}{4}}{\cos^2x},
\tag{50}
\]
by completing the square in \(\sin x\).
At \(x=0\), \(S(0,B)=A_L(B)\).

For \(B\le.84\), the numerator in (50) is positive, so the aligned
lower bound \(>.901\) applies.
For \(.84\le B\le.86\), its numerator exceeds \(-.00181\).
For \(.86\le B\le d<.9\), it exceeds \(-.00864\).
Using \(x<.442\), \(\cos^2x>.81\), (14), and the increase of \(A_L\)
after .84, the last two ranges give

\[
\begin{aligned}
 S&>.9014-\frac{.442(.00181)}{.81}>.9004,\\
 S&>.9028-\frac{.442(.00864)}{.81}>.89808.
\end{aligned}
\tag{51}
\]

This covers the complete side.

### 10.2. A single polynomial proves core-corner concavity

We prove the following scalar inequality:

\[
 L''(z)<\frac{144}{13}(z-\tfrac12)L'(z),
 \qquad \frac12\le z\le.9.
\tag{52}
\]

Put
\[
 U=Q-(z+\tfrac12)^2,\quad
 \lambda=\frac{144}{13},\quad k=1.89442,\quad
 h=2.99496,\quad j=4.80231,
\]
and define the rational polynomials

\[
\begin{aligned}
 \mathcal A(z)&=\lambda(z-\tfrac12)(j-hz)+h,\\
 \mathcal B(z)&=k\left[
   \lambda(z-\tfrac12)\{(2z+\tfrac12)(z+\tfrac12)-Q\}U
   -2(z+\tfrac12)U-zQ\right],\\
 \mathcal P(z)&=\mathcal A(z)^2U^3-\mathcal B(z)^2.
\end{aligned}
\tag{53}
\]

Direct substitution in (8) gives the identity

\[
 \left\{\lambda(z-\tfrac12)L'(z)-L''(z)\right\}U^{3/2}
 =\mathcal A(z)U^{3/2}+\mathcal B(z).
\tag{54}
\]

The quadratic \(\mathcal A\) is concave and has positive values at
\(z=.5,.9\). Also \(U>0\). The degree-ten polynomial \(\mathcal P\)
has the following strict lower bounds for its Bernstein coefficients,
in order, on the single interval \([.5,.9]\):

| Degree | Strict integer lower bounds for all coefficients |
|---:|---|
| 10 | 4, 16, 34, 51, 70, 96, 133, 180, 233, 284, 326 |

For an entirely explicit convention, if
\(\mathcal P(z)=\sum_{j=0}^{10}p_jz^j\), the coefficient at index \(i\)
is
\[
 \sum_{t=0}^i\frac{\binom{i}{t}}{\binom{10}{t}}
    \sum_{j=t}^{10}p_j\binom jt(.5)^{j-t}(.4)^t.
\tag{55}
\]
Thus (53) and (55) specify every rational coefficient independently of
the checker. They are all positive, so \(\mathcal P>0\).
Since \(\mathcal A>0\), this implies
\(\mathcal A U^{3/2}>|\mathcal B|\); (54) proves (52).

On the actual core corner, (33) implies
\[
 B\le\frac12+\frac{13}{12}\sin x.
\tag{56}
\]
If \(B\le1/2\), then \(L''(B)<0\), because \(L''\) increases and
\(L''(.5)<0\). If \(B>1/2\), (52) and (56) give
\[
 \frac{L''(B)}{L'(B)}<12\sin x.
\]
On the other hand, Cauchy's inequality and (35) give
\[
 \frac{\kappa}{(c+ts)^2}
 \ge12\sqrt{1+t^2}\ge12.
\tag{57}
\]
Consequently, in both ranges,
\[
 \frac{d^2}{db^2}L(B(b))
 =L''(B)(c+ts)^2-L'(B)\kappa s<0.
\tag{58}
\]

The core-corner contact cost is therefore strictly concave. Only its
three endpoint alternatives remain. The side junction was treated in
Section 10.1.

### 10.3. The first feasible corner endpoint

If the first feasible core point is on the corner, then \(B=d\) and
the side junction was infeasible. Hence
\[
 \frac12+\frac{13}{12}\sin x>d.
\]
The exact comparison at .377 implies \(x>.377\).
The lower bound (42) gives
\[
 C\ge F_*(x):=
 -x+c_0+L(d)+\frac g2
 +g(\frac12-d)\sec x+g(d_c+\frac12)\tan x.
\tag{59}
\]

The derivative numerator is
\[
 \sin^2x-g(d-\tfrac12)\sin x+g(d_c+\tfrac12)-1.
\tag{60}
\]
It is positive at .377 and increases thereafter, as is seen by
differentiating it with respect to \(\sin x\). Thus \(F_*\) increases
on the required interval, and the one point comparison
\[
 F_*(.377)>.9008
\tag{61}
\]
closes this endpoint family.

### 10.4. The remaining core diagonal

For \(x\le.3\), convexity of \(D=L'\) bounds it by its two endpoint
values on \([B(0),B(.3)]\), both less than .82. Therefore
\[
 H_L'\le-1+.82(1.061)<0.
\]
As \(H_L(.3)>.9046\), this entire initial range is excluded.

On \([.3,.44152]\), the fixed endpoint bounds are
\[
 L''(B)>1.69,\qquad L'(B)<1.165,\qquad
 w^2>.96,\qquad w'>-.4.
\]
They follow from the monotonicities in (9)--(10) and (36).
Equation (37) gives the uniform strong-convexity estimate
\[
 H_L''>1.69(.96)-1.165(.4)>1.1.
\tag{62}
\]

At the single rational angle \(x_*=.3832\),
\[
 H_L(x_*)>.8977797,\qquad |H_L'(x_*)|<.00008.
\tag{63}
\]
Completing a square in the tangent lower bound yields, for the whole
interval,
\[
 H_L(x)>
 .8977797-\frac{(.00008)^2}{2.2}>.89777>\gamma.
\tag{64}
\]

This is the tight remaining mixed-zero regime, and (64) excludes it
strictly.

## 11. Completeness, equality, and arithmetic

Section 3 covers all primary cases that survive the universal
core-primary exclusion. Section 5 covers both angle signs for the
source transverse axis. Section 6 handles the target axis at
nonnegative angle, and Sections 8--10 handle its negative-angle
range for each of the three exact data rows. Reflection then restores
all 24 permitted opposite-sign kind/axis cases.

Every terminal bound exceeds \(\gamma\) strictly. In particular none
of these cases can realize equality at the rational role-table
threshold.

The arithmetic checker uses exact rational intervals. Every square
root is enclosed by rationals with denominator \(10^{14}\), checked
by integer squaring. Alternating sine sums of degrees 11 and 13 and
cosine sums of degrees 14 and 12 enclose every fixed trigonometric
evaluation, whose argument lies in \([0,.7]\). The polynomial
coefficients in (55) are formed by exact rational multiplication and
the displayed basis-conversion formula.

The 149 strict comparisons verify the declared scalar endpoints and
the eleven coefficients of the one polynomial. The proof's variable
ranges are resolved by the monotonicity, concavity, or strong-convexity
arguments above. There is no optimizer, adaptive partition, sampled
contact assumption, or unproved choice of the first separating axis.

