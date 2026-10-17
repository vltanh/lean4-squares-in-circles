# Exact outer-center polarity in the exclusive S2 near-inner 2+2 branch

Research continuation, 2026-10-12. This proves a **real new joint
center-count/continuous-geometry restriction**, not a mere
renaming of the outer-center count k. It is conditional only on
the stated actual whole-square side populations and inner/outer
center classes, for independently rotated square frames.

## General six-square theorem: two R outer centers are forced to straddle +x

Let at least six distinct disjoint-interior unit squares lie in
\(D_R\), with
\[
R^2\le9789/2500,\qquad r_0=283/200.
\]
Assume two squares \(U_+,U_-\) lie *wholly* in the upper
outward half-plane \(y\ge h\), with **both centers inner**
(norm <1); two other squares \(D_1,D_2\) lie wholly beyond
the opposite lower side \(y\le-(1-h)\), with **both centers
outer** (norm \(\ge1\)); and two further distinct **outer-center**
squares \(T_1,T_2\) lie wholly beyond the positive right side
\(x\ge t\ge0\). (The total is six actual labels.)

The hypotheses force \(h<H_*=(\sqrt3-1)/2\) by the sharp two-inner
cap theorem. Suppose additionally
\[
h>7/24.
\]
This is automatic whenever U,D are an opposite 2+2 central
side pair at the n=8 search ceiling.

Write \(\delta_0=\pi/4-1/500\), the rigorous minimum
outer-outer center angular gap from
HUMAN_STABLE_OUTER_ANGLE.md.
Let \(\psi_1<\psi_2\) be the *ordinary polar angles* of
the two distinct right-cap outer centers, in \((-\pi/2,\pi/2)\).
Then
\[
\boxed{
-\pi/4+17/125<\psi_1<
-\pi/18+1/500<0
}                                                   \tag{1}
\]
and
\[
\boxed{
0<67/500<\psi_2<7\pi/36.
}                                                   \tag{2}
\]
Consequently the two **outer-center right-cap squares**
necessarily have **strictly opposite signs of their
transverse y center coordinates**, with exact angular margins.

Moreover, under the same U/D hypotheses, **there can never be
three distinct outer-center squares in the positive right cap**
at any offset \(t\ge0\).

## 1. The upper inner pair determines a narrow NE lane

The usual inscribed radius-1/2 disks imply any two inner
centers at distance at least one have smaller polar gap
\(>\pi/3\).

Write \(\alpha=\arcsin(h+1/2)\).
From \(h>7/24\),
\[
\alpha>\arcsin(19/24)>\pi/4.
\]
The two U inner centers have *strictly opposite x signs*,
by HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md.
Their ray angles lie in \((\alpha,\pi-\alpha)\)
and have gap \(>\pi/3\), so the positive-x U
member satisfies
\[
\boxed{\pi/4<\theta_{U_+}<2\pi/3-\alpha<5\pi/12.}   \tag{3}
\]
Its radial norm exceeds \(h+1/2>19/24>7/10\).

The exact mixed inner/outer angular lemma in
HUMAN_FIVE_SQUARE_INNER_OUTER_FAN.md proves
that any outer center has angular gap \(>2\pi/9\)
from an inner center of radial norm \(>7/10\)
when \(R^2\le9789/2500\).
It is proved there by the rational cosine
lower bound \(3001/3969\), with all four
squared-distance corner values strictly below one.

For an arbitrary right-cap outer center at angle \(\psi\),
the whole-square normal projection gives center
\(p.x\ge t+1/2\ge1/2\), so
\[
\cos\psi>\frac{1/2}{283/200}=\frac{100}{283}>\frac13
>\cos(2\pi/5).                                      \tag{4}
\]
The final bound uses
\(\cos(2\pi/5)=(\sqrt5-1)/4<1/3\),
which follows from \(5<(7/3)^2\).
Thus
\[
-2\pi/5<\psi<2\pi/5.                                \tag{5}
\]

The outer right-cap ray cannot lie above
the U+ inner ray, since by (3),(5) the
resulting angular gap would be less than
\(2\pi/5-\pi/4=3\pi/20<2\pi/9\),
contradicting the mixed center lemma.
It must be at least \(2\pi/9\) below U+,
hence every right-cap outer center satisfies
\[
\boxed{\psi<\theta_{U_+}-2\pi/9<7\pi/36.}         \tag{6}
\]

## 2. The far lower outer pair forces the opposite angular bound

Each D-square center p has
\[
-p.y\ge3/2-h>2-\sqrt3/2,\qquad |p|<283/200.
\]
As proved with exact rationals in
HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md,
its negative-y polar elevation \(\beta\) satisfies
\[
\beta>\arcsin(4/5)
=\pi/4+\arctan(1/7)>\pi/4+7/50.                   \tag{7}
\]
The final comparison uses
\(\arctan(x)=\int_0^x (1+t^2)^{-1}dt
>x/(1+x^2)\), which at \(x=1/7\)
equals \(7/50\).

Represent the D center rays by ordinary angles
\[
-\pi+\beta<\phi_1<\phi_2<-\beta<-\pi/4.
\]
They are distinct outer centers, so their gap
exceeds \(\delta_0\):
\[
\phi_2>\phi_1+\delta_0>-\pi+\beta+\delta_0.       \tag{8}
\]

Every right outer center must lie **above**
\(\phi_2\): if \(\psi\le\phi_2\), then by
(5) and (7) its ordinary angular gap from
\(\phi_2\) would be less than
\(2\pi/5-\pi/4=3\pi/20<\delta_0\),
contradicting the outer-outer separation theorem.
(The compared rays are within an ordinary angular
span less than \(\pi\), so no winding ambiguity occurs.)

Therefore their outer-outer angular gap gives
\[
\psi>\phi_2+\delta_0
>-\pi+\beta+2\delta_0
>-\pi/4+17/125.                                   \tag{9}
\]
This bound is valid for **every** outer right-cap center,
not just the two labels T1,T2.

## 3. Two centers must have opposite y signs; three cannot fit

Combine (6),(9). Every outer right-cap ray lies in
the single open interval
\[
I=(-\pi/4+17/125,\ 7\pi/36),
\]
whose width is
\[
|I|=4\pi/9-17/125<2\delta_0
=\pi/2-1/250.
\]
The final positive comparison follows from
\(\pi/18+33/250>0\).
Thus **three** distinct outer right-cap centers,
whose two successive linear angular gaps must
both exceed \(\delta_0\), cannot all fit in I.

For two such centers \(\psi_1<\psi_2\),
the minimum outer gap \(\psi_2-\psi_1>\delta_0\)
and (6),(9) give
\[
\psi_1<7\pi/36-\delta_0
=-\pi/18+1/500<0
\]
and
\[
\psi_2>-\pi/4+17/125+\delta_0
=67/500>0.
\]
This proves (1)–(2) and the general theorem. QED.

## New exact S2 outer-count pruning

Now take a full eight-square packing in the
**exclusive all-single-side S2** class with
\[
R:3,\quad L:0,\quad U:2,\quad D:2,
\]
where U is the **nearer** two-square cap
(offset \(h_U\)), D the farther. In particular
\(7/24<h_U<1/2\).

Suppose **both** U-square centers are inner.
The two D squares are necessarily outer since
their whole cap offset \(1-h_U\ge1/2\).
The perpendicular R triple must contribute
at least one outer center.

The separate exact six-square theorem
HUMAN_FAR_TWO_CAP_FOUR_INNER_EXCLUSION.md
rules out **only one** outer R: otherwise
the other two R members and the two U members
are distinct inner centers while both D are outer.
The theorem above rules out **three** outer R
because it would create three outer rays in I.
Thus R has **exactly two outer and one inner**
center, and necessarily
\[
\boxed{\text{S2 with both near U centers inner}
\Longrightarrow k=4.}                              \tag{10}
\]

Moreover its two outer R center-ray angles obey
(1)–(2), so one center is strictly lower-right,
the other strictly upper-right, with quantified
nonzero angular margins.

This genuinely excludes the entire **S2/k=5,
both U centers inner** subregion, while preserving
the still-open **S2/k=4, U-inner-pair** branch.
It does **not** exclude the other S2/k=5 patterns
with at least one outer U center, or S2/k=6.
The exact twelve-status assignment count is unchanged:
this pruning refers to center radii and continuous
angular geometry, not the symbolic side labels.

## Scope and guardrails

All memberships are **whole-square** cap
statuses and all inner/outer tests refer to
*center norm*, not circle contact.
The angular intervals do not force square frames,
physical contacts, or entire origin-quadrant
membership from a center sign.
If two cap populations share a label, the theorem
cannot be applied unless **six distinct actual
squares** have been selected.

The valid exact S4/k=7 equality construction
is unaffected. The unrestricted \(R_8\ge\widehat R\)
remains OPEN.
