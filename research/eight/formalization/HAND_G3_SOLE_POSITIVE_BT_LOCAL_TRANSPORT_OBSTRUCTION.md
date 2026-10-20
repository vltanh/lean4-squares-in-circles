# A local obstruction to universal positive-BT3 transport

## 1. Scope of the obstruction

Put
\[
 Q=\frac{9789}{2500},\qquad h=\frac7{10},\qquad
 c=\sqrt{Q/2}-\frac12,\qquad
 W(x)=\frac{1+\cos x+\sin x}{2}\quad(0\le x\le h).
\]
The two actual projections considered here are
\[
 a_B+a_T\sin u-y_T\cos u\ge W(u),\qquad
 y_T+a_D\sin v+b_D\cos v\ge W(v).                 \tag{1}
\]
They are BT3 and TD0 for sorted outer B,D with negative signed
tangents, and a sorted T of arbitrary sign and radial kind.

The following exact three-square example satisfies (1), with
\(u,v>0\), while no T-only change with its frame in the interval
\([\theta_B,\theta_D]\) can reach either alignment, a feasible
BT2/TD0 pair, or either T diagonal. The zero-tangent boundary
is infeasible as well. Thus the positive-BT3 contact calculus
can have a genuine interior feasible maximum. It does not
supply a universal endpoint reduction of sole positive BT3
with arbitrary TD0.

This is an obstruction to a local conversion based only on
these three squares. It does not assert a feasible seven-cycle
or contradict a global exclusion using the other four states.

Every decimal in this note denotes an exact rational.

## 2. The exact strictly sorted outer example

Choose
\[
 \begin{aligned}
 a_B&=\frac{237}{200}=1.185,&
 b_B&=\sqrt{Q-1.685^2}-\frac12,\\
 b_D&=\frac{49}{250}=.196,&
 a_D&=\sqrt{Q-.696^2}-\frac12,\\
 y_T&=\frac{43}{200}=.215,&
 a_T&=\sqrt{Q-.715^2}-\frac12,
 \end{aligned}                                                  \tag{2}
\]
and
\[
 u=\frac7{200}=.035,\qquad
 v=\frac{663}{1000}=.663,\qquad
 t=u+v=\frac{349}{500}=.698<h.                    \tag{3}
\]
Set \(\theta_B=0,\theta_T=u,\theta_D=t\).
All three containing-circle equalities are exact. Their
coordinates are strictly sorted: \(.5<b_B<.54<a_B\),
\(a_D>1.35>b_D\), and \(a_T>1.34>y_T\).
Their square-to-origin distances exceed \(1/12\).

The two original slacks satisfy the exact bounds
\[
 \begin{split}
 L_{BT}&=a_B-\tfrac12+(a_T-\tfrac12)\sin u
                         -(y_T+\tfrac12)\cos u>\frac1{100000},\\
 L_{TD}&=y_T-\tfrac12+(a_D-\tfrac12)\sin v
                         +(b_D-\tfrac12)\cos v>\frac7{1000000}.
 \end{split}                                                   \tag{4}
\]
Section 5 gives reproducible rational certificates for (4).

The actual physical gaps are positive. They are
\[
 \frac\pi2+u-\arctan(y_T/a_T)-\arctan(b_B/a_B),
 \qquad v+\arctan(y_T/a_T)+\arctan(b_D/a_D).
\]
The first exceeds .99 and the second exceeds .81, by the
coordinate bounds above and
\(x-x^3/3<\arctan x<x\) on \(0<x<1\).
Thus the two actual forward-axis witnesses have their
ordinary neighboring geometric interpretation.

## 3. Both aligned endpoints and every BT2 choice fail

Define the TD0 tangent demand
\[
                     e(x)=W(x)-a_D\sin x-b_D\cos x.
\]
At BT alignment, either BT3 or BT2 requires
\(y\le a_B-1=.185\). But
\[
                         e(t)-(a_B-1)>\frac1{10000}.            \tag{5}
\]
Thus no T state can satisfy the two aligned-end inequalities.

At TD alignment, TD0 requires \(y\ge1-b_D=.804\).
For a fixed tangent, the outer T state maximizes BT3; on
the sorted outer circle BT3 strictly decreases with y.
Consequently the best possible aligned-end T has
\[
                 y_*=1-b_D,\qquad
                 a_*=\sqrt{Q-1.304^2}-\frac12.
\]
Even this state has a strict BT3 deficit:
\[
       W(t)-a_*\sin t+(1-b_D)\cos t-a_B
                                      >\frac{17}{100000}.       \tag{6}
\]
No weaker radial state can improve that projection.

There is also no feasible BT2 anywhere in the entire frame
interval. For \(u'\in[0,t]\), put \(v'=t-u'\). Adding BT2
and TD0 cancels the T tangent and gives the necessary inequality
\[
                         -1+\alpha\cos u'+\beta\sin u'\ge0,
                                                               \tag{7}
\]
where
\[
 \begin{split}
 \alpha&=(a_B-\tfrac12)
       +(b_D-\tfrac12)\cos t+(a_D-\tfrac12)\sin t,\\
 \beta&=(b_B-\tfrac12)
       +(b_D-\tfrac12)\sin t-(a_D-\tfrac12)\cos t.
 \end{split}
\]
Equation (5) gives \(\alpha<1\). Moreover
\[
                  \beta<.04-.85(3/4)<0.
\]
If \(\alpha\ge0\), the left side of (7) is at most
\(-1+\alpha<0\). If \(\alpha<0\), both trigonometric
terms are nonpositive. Thus (7) is impossible for every
frame in the interval, independently of the radial kind
or signed tangent of T.

## 4. No tangent or diagonal endpoint replaces the alignments

At either a core or an outer T diagonal, write
\(a_T=|y_T|=\xi\). Core avoidance and containment give
\(447/800<\xi\le c\). At the positive diagonal, BT3 minus
its width is
\[
 a_B-\tfrac12+(\xi-\tfrac12)\sin u'
                            -(\xi+\tfrac12)\cos u'.
\]
Its derivative in \(\xi\) is \(\sin u'-\cos u'<0\).
Using the lower bound \(447/800=.55875\),
\(\sin u'<.65\), and \(\cos u'>.75\), it is less than
\[
            .685+.05875(.65)-1.05875(.75)=-.070875<0.           \tag{8}
\]
At a negative T diagonal the TD0 projection is less than
\[
                 -.55875+1.353(.65)+.196=.5167<1\le W(v').
                                                               \tag{9}
\]
Both nearest-axis ties are therefore locally infeasible for
either radial kind.

Finally,
\[
 e'(x)=-(a_D-\tfrac12)\cos x+(b_D-\tfrac12)\sin x<0
                         \qquad(0\le x\le t).
\]
Equation (5) implies \(e(x)\ge e(t)>.185>0\) throughout
the interval. The zero-tangent state cannot satisfy TD0.

Outerizing T and then increasing its tangent to saturate
BT3 preserves its strict TD0 slack. Along the unique
positive-tangent BT-contact branch, the TD0 slack is
continuous, negative at both aligned endpoints by (5)--(6),
and positive at an interior point by (4). The tangent and
diagonal boundaries are unavailable by (8)--(9).
It follows that this contact slack has a positive interior
maximum. Thus an interior stationary alternative is
substantive in this local problem; discarding it would
invalidate an endpoint argument.

## 5. Exact certificates, without sampled premises

Let \(S_n,C_n\) denote the ordinary alternating sine and
cosine Taylor polynomials ending in degree n. On \([0,h]\),
\[
             S_{11}\le\sin\le S_{13},\qquad
             C_{10}\le\cos\le C_{12}.
\]
Positive squaring gives
\[
 \begin{aligned}
 1.3450948485&<a_T<1.3450948486,\\
 1.3523455401&<a_D<1.3523455402,\\
 .9883494213&<a_*<.9883494214.
 \end{aligned}                                                 \tag{10}
\]
Substitute the following rational lower bounds into (4)--(6):
\[
 \begin{split}
 L_{BT}\ &\ge a_B-\tfrac12
  +(1.3450948485-\tfrac12)S_{11}(u)
                    -(y_T+\tfrac12)C_{12}(u)
                  >.000010173956>\frac1{100000},\\
 L_{TD}\ &\ge y_T-\tfrac12
  +(1.3523455401-\tfrac12)S_{11}(v)
                    +(b_D-\tfrac12)C_{12}(v)
                  >.000007702796>\frac7{1000000},\\
 e(t)-(a_B-1)\ &\ge \tfrac32-a_B
  +(\tfrac12-b_D)C_{10}(t)
                    -(1.3523455402-\tfrac12)S_{13}(t)
                  >.000112088336>\frac1{10000},\\
 \text{deficit in (6)}\ &\ge \tfrac12-a_B
  +(\tfrac32-b_D)C_{10}(t)
                    -(.9883494214-\tfrac12)S_{13}(t)
                  >.000176650452>\frac{17}{100000}.
 \end{split}                                                   \tag{11}
\]
Each last comparison is exact rational arithmetic at the
displayed rational arguments. The Taylor signs follow from
the alternating remainder theorem. The radical bounds in
(10) are reversible comparisons of positive squares.

These certificates prove the example itself. The exclusion
of every candidate BT2 state and every diagonal or tangent
boundary is the whole-interval argument in Sections 3--4,
rather than a collection of evaluated states.

