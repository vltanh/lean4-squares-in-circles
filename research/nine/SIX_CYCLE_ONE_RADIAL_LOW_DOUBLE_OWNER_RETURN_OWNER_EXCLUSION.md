# A low unit owning both inner axes cannot meet a strict return owner

Date: October 26, 2026.

**Status: accepted complete analytic physical-family exclusion**, after
REVIEW_C6_RADIAL_LOW_DOUBLE_OWNER_COMPLETE_C6_2026_10_26.md and
REVIEW_C6_RADIAL_LOW_REMAINING_ROOT_2026_10_26.md. The proof also establishes a reusable lower bound for the
horizontal circle coordinate of every strict return owner. No parameter
subdivision or computational certificate is used.

Retain the original alternating all-side C6 with one physically radial
loaded square S, both positive individual radial circle weights, two
physically unique loaded squares, three true reserve-one side transmitters,
all positive forces, actual means and endpoints, full transmitter sliders,
and all nine original squares.

In the complete low-turn cover, let L be the unique unit whose turn is
at most \(\pi/2\). Assume L owns both of its original inner side axes.
Its turn is therefore exactly \(\pi/2\). Assume the strict unique
partner T genuinely owns the return channel as well. Thus T is the
strict return-owner type T of the accepted A/M/O/T cover, while the
return transmitter is genuinely shared at both endpoints.

**Theorem.** This entire original both-owner/strict-T family has no
nine-square completion in the original radius window.

The accepted global geometric theorem supplies \(R>2\) from all nine
units. We prove the stronger conditional core exclusion throughout
\[
 2\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1,\qquad r_0^2=d^2+\frac14.
\tag{1}
\]
The strict bound \(d>9/10\) gives
\[
                             r_0^2>53/50.
\tag{2}
\]
The radial zero-weight endpoints retain their separate accepted proof;
they are not relabeled as unique circle masks.

## 1. Every strict return owner has horizontal circle coordinate \(>8/5\)

Use the original local chart from
SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md,
Section 1. In inward own axes, let the strict owner's circle corner
be \(z=(A,B)\), with
\[
 A>B>1/2,\qquad A^2+B^2=R^2.
\]
Its actual S-incident port is its opposite vertex, and its original
unit incoming normal is \(G=(x,y)\), with
\[
                      0<x\le y,\qquad x^2+y^2=1.
\]
The exact true channel gives its radial port
\[
                 P=(A-1-x,B-1-y),\qquad |P|^2=r_0^2.
\tag{3}
\]
These signs and the formula retain the genuine return mean endpoint
at which \(x=y\).

Suppose \(A\le8/5\). From \(R\ge2\),
\[
                   6/5\le B\le A\le8/5.
\]
Since \(x+y\ge1\),
\[
 (A-1)x+(B-1)y
     \ge(B-1)(x+y)\ge B-1.
\]
Therefore (3) implies
\[
 \begin{split}
 r_0^2
 &=(A-1)^2+(B-1)^2+1
                     -2\{(A-1)x+(B-1)y\}\\
 &\le(A-1)^2+(B-2)^2\\
 &\le(3/5)^2+(4/5)^2=1,
 \end{split}
\]
contrary to (2). Hence the full local strict-return-owner family obeys
\[
                                \boxed{A>8/5.}
\tag{4}
\]
This lemma uses neither the feature at the other unique endpoint nor
a prescribed return mean.

## 2. The actual doubly owned return fixes the other circle coordinate

Normalize the original return transmitter from T toward L horizontally,
with original height \(H>0\). In the same fixed plane coordinates,
T's actual circle corner and genuine return mean are
\[
                       z_T=(-A,B),\qquad p_T=(1-A,H).
\tag{5}
\]
Its actual H satisfies the accepted local return-owner height bound
\[
                                  H<4/5.
\tag{6}
\]
That theorem is local to the strict T endpoint; it does not assume that
the other unique endpoint has a strict turn or a particular feature.

At L, choose its actual inward own axes so its S normal points vertically
up and its return outward normal points horizontally left. Write its
circle corner as
\[
                             z_L=(b,a),\qquad
                   a,b>1/2,\quad a^2+b^2=R^2.
\tag{7}
\]
This is an interchange of actual own-axis labels: a is the coefficient
along its S-incident inward axis, and b is the coefficient along its
return inward axis. No order between a and b is assumed initially.

The complete original both-axis row has proper concurrence
\(\tau z_L\), with \(0<\tau\le1\). Its original return and
S-incident means are exactly
\[
                p_L=(b-1,\tau a),\qquad Q=(\tau b,a-1).
\tag{8}
\]
All original endpoint means are included, with their original support
restrictions. There is no choice of independent transverse parameters.
The true return channel equation \(p_L-p_T=(1,0)\) gives
\[
                              A+b=3,\qquad H=\tau a.
\tag{9}
\]
By (4), \(b<7/5\). Equation (7) and \(R\ge2\) then give
\[
 a^2=R^2-b^2>4-\frac{49}{25}
                         =\frac{51}{25}>\frac{49}{25},
 \qquad \boxed{a>7/5>b}.
\tag{10}
\]

The original S-to-L channel has direction \((0,1)\) and reserve one.
Its actual radial port is therefore
\[
       P_L=Q-(0,1)
             =\left(\frac{Hb}{a},a-2\right),\qquad
       |P_L|^2=r_0^2.
\tag{11}
\]
This uses the original linked mean in (8), not a selected vertex or a
different contact point.

## 3. One norm contradiction over the complete mean interval

The radius upper endpoint in (1) is less than \(21/10\), with
positive-square reserve
\[
                       (21/10)^2-1105/256=599/6400.
\]
Together with (10), this gives
\[
                         7/5<a<21/10,\qquad |a-2|<3/5.
\tag{12}
\]
The exact radial norm (11), (2) and (12) yield
\[
 \begin{split}
 H^2
   &=\left(\frac ab\right)^2
                         \{r_0^2-(a-2)^2\}\\
   &>\left(\frac ab\right)^2
                       \left(\frac{53}{50}-\frac9{25}\right)\\
   &=\left(\frac ab\right)^2\frac7{10}
     >\frac7{10}>\frac{16}{25}.
 \end{split}
\tag{13}
\]
The last reserve is \(7/10-16/25=3/50>0\).
But (6) gives \(H^2<16/25\), a contradiction.

The proof covers the entire actual both-axis row paired with T, including
all original mean endpoints and any originally allowed coincident
application boundary at L. If those values satisfy all physical
constraints, equations (8)--(13) still apply and exclude them. No
noncoincidence theorem from a strict-turn L chart was used.

## 4. Exact retained scope

This theorem excludes the complete low-both-inner-axis/strict-return-owner
subfamily. Its local bound (4) is reusable at every strict T endpoint
throughout the high-radius interval, independently of the opposite
feature.

The other strict partners A, M and O in the both-inner-axis row remain
separate until their own original-channel contradiction is proved.
Low nonowner-opposite and single-S-owner rows retain their full
original physical domains. No unrestricted one-radial parent gate is
closed by this source alone.

All nine original squares, both positive radial weights, actual means,
forces, support restrictions and transmitter sliders remain unchanged.
No numerical optimization, computational certificate, Lean compilation
or CI was used.

