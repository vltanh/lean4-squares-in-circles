# One linear charge for every original zero-quarter edge

## 1. The complete zero-edge theorem

Work in the actual G0--G2 candidate geometry at
\(q\le Q=9789/2500\). Write the signed own-frame centers on a
zero-quarter edge as \((a,-y)\), \((A,-Y)\), with
\(a\ge |y|\), \(A\ge |Y|\), and let \(d\) be its actual lifted
frame increment. Put
\[
 h(x)=\frac{\sin x+\cos x-1}{2},\qquad
 p=\frac{49}{50},\qquad \beta=\frac1{50},
 \qquad x=|d|\le\frac7{10}.
\]
The global zero-primary exclusion supplies the following disjunction
for every originally feasible witness on the edge:
\[
 \begin{split}
 P_0&=y+A\sin d-Y\cos d\ge1+h(x),\quad\text{or}\\
 P_2&=a\sin d+y\cos d-Y\ge1+h(x).
 \end{split}                                                    \tag{1}
\]
No choice between these two original witnesses is made in the theorem.

**Theorem.** Under these hypotheses,
\[
 \boxed{
 d-\frac1{50}h(|d|)
 +\frac{49}{50}\bigl(\max(y,0)+\max(-Y,0)-1\bigr)\ge0.
 }                                                              \tag{2}
\]
The inequality is strict when \(d\ne0\). At zero, equality holds
exactly when \(y>0>Y\) and \(y-Y=1\).

This is a whole-domain theorem for **all signs**, every original radial
state, both original transverse owners, and weak separating contacts.
It uses no G/T/H/D tangent cut, mismatch contraction, preferred owner,
or radial contact equality. The elementary corner and core bounds used
below apply to the original centers as well as the boundary
representatives.

The conclusion closes the complete zero-quarter component for this
new, explicit potential. A compatible quarter/mixed-edge bound is
still required before it can prove either global G4 contraction.
The historical affine labels are not silently substituted by the new
ones on just one part of their old cyclic sum.

## 2. Reduce every signed state to one scalar box

The actual containing circle and central-disk avoidance give
\[
 \frac{447}{800}<a,A<\frac{283}{200},\qquad
 |y|,|Y|<\frac9{10}.                                         \tag{3}
\]
For the lower bound, the distance from the origin to either square is
at least \(1/12\), while it is at most
\(\sqrt2\max(a-1/2,0)\). Hence
\(a\ge1/2+\sqrt2/24>447/800\), and the same holds for A.
For the upper bound, substitute \(283/200\) in
\((a+1/2)^2+1/4\); its value is greater than Q. Finally,
\(a\ge |y|\) and containment give
\(2(|y|+1/2)^2\le Q<2(7/5)^2\), proving the transverse bound.

Set
\[
 b=\max(y,0),\qquad B=\max(-Y,0).
\]
Since \(\cos d>0\), both actual projections in (1) are at most the
corresponding expressions
\[
 b+A\sin d+B\cos d,
 \qquad a\sin d+b\cos d+B.                            \tag{4}
\]
Thus an originally feasible witness implies the same transverse-owner
disjunction for these clipped coordinates. This is a monotone scalar
comparison; it does not move an actual center or change a selected
witness. The bounds
\[
 a,A\ge L:=447/800,\quad a,A\le U:=283/200,
 \quad0\le b,B\le9/10                                \tag{5}
\]
are all that the remaining proof needs. In particular, the clipped
coordinates need not be assigned a new radial chart.

We prove (2) in the larger scalar domain (5), assuming at least one
expression in (4) is at least \(1+h(|d|)\). Put
\(D=b+B-1\). The statement becomes
\[
                   d-\beta h(|d|)+pD\ge0.             \tag{6}
\]

## 3. Every positive increment

Let \(d=x>0\), \(s=\sin x\), and \(c=\cos x\).
If the second projection in (4) is feasible, rearrangement gives
\[
 D\ge -(a-1/2)s+(b-1/2)(1-c)
   \ge-\frac{183}{200}s-\frac12(1-c).                 \tag{7}
\]
For the first projection the identical bound follows with
\((a,b)\) replaced by \((A,B)\). Consequently the left side of (6)
is at least
\[
 F(x):=x-\frac{9067}{10000}\sin x
             -\frac{12}{25}(1-\cos x).               \tag{8}
\]

Here \(F(0)=0\), \(F'(0)>0\), and
\[
 F'''(x)=\frac{9067}{10000}\cos x
                  +\frac{12}{25}\sin x>0
                   \qquad(0\le x\le7/10).            \tag{9}
\]
Thus \(F'\) is strictly convex. At the other endpoint, alternating
Taylor inequalities give
\[
 F(7/10)>\frac1{400},\qquad F'(7/10)<-\frac1{400}.    \tag{10}
\]
For an entirely explicit check, put
\[
 S_5(z)=z-z^3/6+z^5/120,
 \quad S_7(z)=S_5(z)-z^7/5040,
 \quad C_6(z)=1-z^2/2+z^4/24-z^6/720.
\]
Substitution at \(z=7/10\) gives
\[
 \begin{split}
 z-\frac{9067}{10000}S_5(z)-\frac{12}{25}(1-C_6(z))
 &=\frac{359601011}{120000000000}>\frac1{400},\\
 1-\frac{9067}{10000}C_6(z)-\frac{12}{25}S_7(z)
 &=-\frac{19480021997}{7200000000000}<-\frac1{400}.
 \end{split}                                                   \tag{11}
\]
The first expression is a lower bound for F; the second is an upper
bound for its derivative.

The sublevel set \(\{x:F'(x)\le0\}\) is an interval because \(F'\)
is convex. It contains the right endpoint and does not contain zero.
Hence F first increases and then decreases on the stated interval.
Its minimum is at an endpoint. Equations (10), together with
\(F'(0)>0\), prove \(F(x)>0\) for every \(0<x\le7/10\).
This proves the positive branch, including both original owners.

## 4. Every negative increment: use the opposite endpoint once

Let \(d=-x<0\), with \(s=\sin x\), \(c=\cos x>0\).
Suppose first that the second projection in (4) is feasible. Its exact
rearrangement is
\[
 D\ge(a+1/2)s+(b-1/2)(1-c).                           \tag{12}
\]
The same feasible projection also gives
\[
 (b-1/2)c+(B-1/2)\ge(a+1/2)s.
\]
Use the **same opposite endpoint** \(B\le9/10\):
\[
 b-1/2\ge(a+1/2)\tan x-\frac25\sec x.
\]
Insert this inequality in (12), and use \(a\ge L\):
\[
 \boxed{
 D\ge\frac{847}{800}\tan x-\frac25(\sec x-1).
 }                                                              \tag{13}
\]
The simplification uses
\(s+\tan x(1-c)=\tan x\). This is a coupled endpoint estimate.
It does not assert the false pointwise derivative lower bound for
the former quintic potential at a core endpoint.

If the first projection in (4) is feasible, exchange \((a,b)\) with
\((A,B)\) throughout this calculation. The opposite endpoint bound
is then \(b\le9/10\), and (13) follows unchanged. Thus (13) includes
both witnesses without a preferred radial endpoint.

Multiply the lower bound for (6) obtained from (13) by the positive
number c. The resulting expression is
\[
 \begin{split}
 N(x)={}&\frac{41503}{40000}\sin x
       -\frac{49}{125}(1-\cos x)-x\cos x\\
       &-\frac1{100}\cos x(\sin x+\cos x-1).
 \end{split}                                                   \tag{14}
\]
It remains to prove \(N(x)>0\) for \(0<x\le7/10\).

### 4.1 One polynomial on the entire interval

The double-angle identities turn (14) into
\[
 N(x)=\frac{41503}{40000}\sin x+\frac{201}{500}\cos x
       -\frac{397}{1000}-x\cos x
       -\frac1{200}(\sin(2x)+\cos(2x)).               \tag{15}
\]
Use the lower bounds \(S_7(x)\le\sin x\),
\(C_6(x)\le\cos x\), and the upper bounds
\(\cos x\le C_4(x)=1-x^2/2+x^4/24\),
\(\sin(2x)\le S_5(2x)\), \(\cos(2x)\le C_4(2x)\).
They are valid throughout the displayed interval, including
\(0\le2x\le7/5\). Ordinary expansion gives
\[
 N(x)\ge xP(x),                                      \tag{16}
\]
where the single degree-six polynomial is
\[
 \begin{split}
 P(x)={}&\frac{1103}{40000}-\frac{191}{1000}x
    +\frac{26699}{80000}x^2+\frac{161}{12000}x^3\\
    &-\frac{164897}{4800000}x^4
     -\frac{67}{120000}x^5-\frac{5929}{28800000}x^6.
 \end{split}                                                   \tag{17}
\]
No coefficient inventory over subintervals is involved.

Drop the positive linear term in \(P''\), and evaluate its negative
terms at \(7/10\). This gives the whole-interval bound
\[
 \begin{split}
 P''(x)&\ge\frac{26699}{40000}
   -\frac{164897}{400000}x^2-\frac{67}{6000}x^3
   -\frac{5929}{960000}x^4\\
 &\ge\frac{4417566151}{9600000000}>\frac9{20}.
 \end{split}                                                   \tag{18}
\]
The fixed rational comparison point \(z=57/200\) satisfies
\[
 P(z)>\frac{3306}{10^7},\qquad
 |P'(z)|<\frac{703}{10^6}.                            \tag{19}
\]
These are direct substitutions in the printed polynomial (17).
For example their exact values are
\[
 P(z)=\frac{67707877450407631}{204800000000000000000},
 \qquad
 P'(z)=-\frac{359463444748651}{512000000000000000}.
\]

Integrating (18) and completing a square now gives, for every x in
the entire interval,
\[
 \begin{split}
 P(x)&\ge P(z)+P'(z)(x-z)+\frac9{40}(x-z)^2\\
 &\ge P(z)-\frac{10}{9}P'(z)^2\\
 &>\frac{3306}{10^7}-\frac{10}{9}
                      \left(\frac{703}{10^6}\right)^2
  >\frac{33}{100000}>0.
 \end{split}                                                   \tag{20}
\]
Equations (16) and (20) prove strict positivity of (14), hence (6),
for every negative increment. The argument controls the whole interval
by one curvature bound and one rational reference comparison.

## 5. Zero increments, witnesses, and the common role labels

At \(d=0\), either original projection in (1) is \(y-Y\).
Feasibility says \(y-Y\ge1\). The strict bounds in (3) force
\(y>0>Y\), so clipping changes neither coordinate. Equation (2)
then becomes \(p(y-Y-1)\ge0\), with exactly the stated equality
case. This completes the theorem, including sign-zero boundaries
and every tied original witness.

For the roles \((H,G,A,B,T,D,E)\), the three zero-quarter edges are
HG, AB, and TD. Choose the following six labels, once per actual
vertex:
\[
 \begin{array}{lll}
 L_H=p\max(y_H,0),&L_A=p\max(y_A,0),&L_T=p\max(y_T,0),\\
 L_G=p(1+\min(y_G,0)),&L_B=p(1+\min(y_B,0)),
       &L_D=p(1+\min(y_D,0)).
 \end{array}                                                   \tag{21}
\]
The theorem is exactly the three full-domain inequalities
\[
 d_i-\beta h(|d_i|)+L_i-L_{i+1}\ge0,
             \qquad i\in\{H,A,T\}.                  \tag{22}
\]
Any later quarter/mixed estimates must use these **same** label values
at their shared vertices, plus one explicit label for E. Summing only
(22) is legitimate but is not the missing seven-edge bound. The
theorem therefore supplies a complete, table-free all-sign zero-edge
component of G4; it does not assert either
\(S<2/5\) or \(S<13/50\).

The proof uses actual containment, core avoidance, the previously proved
global zero-owner disjunction, elementary trigonometric inequalities,
and one printed polynomial. Exact rational arithmetic was used to
cross-check (11), (17)--(20); it is not a proof premise. No Lean source,
existing table, compilation, or CI was changed or invoked.
