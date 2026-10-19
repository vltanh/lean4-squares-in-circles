# Exact five-square counterexample to a naive perpendicular 3+1 cap exclusion

Research continuation 2026-10-12. This is a **negative-result
guardrail**, not a new eight-square construction.

A tempting but false global shortcut is:

> Three whole squares beyond one side of the central square cannot
> coexist with one square beyond a perpendicular distant side when
> \(R^2\le9789/2500\).

The following **five real, pairwise interior-disjoint unit squares**
disprove that assertion in the stronger subcandidate disk
\[
q=R^2=3911/1000 < 9789/2500.
\]
All center/frame entries are rational. This example does **not**
disprove the S1=(3+0,3+1) branch exclusion, because one square
has a genuine RU double-side status. A proof excluding S1 must
use its *exclusive* single-side hypothesis, or other constraints
from its full seven exterior units.

## Squares

Use orthonormal unit-square frames \(e,f=(-e_y,e_x)\);
a square with center \(p\) and frame \(e,f\) is
\(p+\{t e+u f: |t|,|u|\le1/2\}\).
Let
\[
c=2499/2501,\quad s=100/2501,\quad c^2+s^2=1.
\]
Take the following five squares:

| Name | Center \(p=(x,y)\) | Frame \(e\) |
| --- | --- | --- |
| C | \((-49/100,-2/5)\) | \((1,0)\) |
| B | \((49/50,-161/200)\) | \((c,s)\) |
| M | \((51/100,1/5)\) | \((1,0)\) |
| T | \((51/100,6/5)\) | \((1,0)\) |
| D | \((-1/50,-7/5)\) | \((1,0)\) |

C is the genuine open origin-containing square:
\[
C=[-99/100,1/100]\times[-9/10,1/10].
\]
The M and T left edges coincide with C's right side
\(x=1/100\); B lies strictly farther right, since
\[
\min_x B=49/50-(c+s)/2
=49/50-2599/5002>1/100.
\]
The lower square D has top edge \(y=-9/10\), touching
C's lower side. Thus C is disjoint from B,M,T,D
and exhibits **three whole right-cap members B,M,T**
and a **far lower-cap singleton D**.

Notice, however, that
\[
T=[1/100,101/100]\times[7/10,17/10]
\subseteq \{x\ge1/100,\ y\ge1/10\}.
\]
It is a genuine **RU double-side square**. No conclusion
about exclusive single-side S1 follows.

## Complete 10-pair separation certificates

Write \(h_i(n)=(|n\cdot e_i|+|n\cdot f_i|)/2\).
For each exterior pair the following table gives a separating
axis and exact nonnegative projection gap
\[
\Delta_{ij}(n)=|n\cdot(p_j-p_i)|-h_i(n)-h_j(n)\ge0.
\]

| Pair | Axis | Exact gap |
| --- | --- | ---: |
| B,M | \(f_B=(-s,c)\) | \(1699/500200>0\) |
| B,T | \(f_B\) | \(501499/500200>0\) |
| B,D | \(e_B=(c,s)\) | \(17/5002>0\) |
| M,T | \(y\) | \(0\) |
| M,D | \(y\) | \(3/5>0\) |
| T,D | \(y\) | \(8/5>0\) |

The remaining four C pairs are separated by C's signed
x support (for B,M,T) or signed y support (for D).
All 10 unordered pairs are accounted for. Touching boundaries
are permitted: the **open interiors** remain disjoint.

## Disk containment: 20 true vertices, checked exactly

For any frame, the four actual vertices are
\(p+(\varepsilon e+\eta f)/2\), \(\varepsilon,\eta=\pm1\).
The maximum squared vertex norms are:

| Square | Maximum squared vertex norm |
| --- | --- |
| C | \(17901/10000\) |
| B | \(390055437/100040000\) |
| M | \(15101/10000\) |
| T | \(39101/10000\) |
| D | \(9701/2500\) |

All are strictly less than \(3911/1000\).
The tightest reserve is T's
\[
3911/1000-39101/10000=9/10000>0.
\]
For B the exact reserve is
\(1201003/100040000>0\).
This checks containment of every **true square corner**, not
just center distances or bounding boxes.

## Logical scope

This is a rigorous local counterexample to dropping the
*no double-side status* condition from a proposed perpendicular
3+1 impossibility theorem. It also shows why only looking at
the central-side population counts can misleadingly suggest
a contradiction: the right-cap triple can supply an RU member.

The analytic triple-piercing and exact S1 reductions are not
contradicted. To prove S1 impossible one must maintain the
single-side requirement for all seven exterior labels and
use their interactions; to prove the unrestricted eight-square
lower bound, one must retain D1 and D2 double-side branches.
