# Exact four-inner-center angular fan in the exclusive S2 / k=3 branch

Research continuation, 2026-10-12. This converts the sharp two-inner
cap threshold and the S2 outer-center counting argument into **narrow
analytic center-ray lanes** and a new bound on the triple-side offset.
No square-frame parallelism, actual contact pattern, or stress
premise is assumed.

## Hypotheses and normalization

Let eight pairwise interior-disjoint unit squares lie in
\(D_R\) with \(R^2\le9789/2500\) and unique open central
square C. Suppose all seven exterior square labels have exactly
one central-owned whole-side separator, in coarse status type
S2=(3+0,2+2). Suppose precisely \(k=3\) of the seven
exterior centers have radial norm \(\ge1\).

Use rotations/reflections to normalize the side populations as
\[
R:3,\quad L:0,\quad U:2,\quad D:2,
\]
and to choose the U side as the **nearer** of the two
opposite 2+2 caps. Thus the signed center position of C is
\((a,b)\), with \(b\le0\), and
\[
h_R=1/2+a>0,\quad h_U=1/2+b,\quad
h_D=1/2-b\ge1/2.
\]
The standard 2+2 cap theorem gives
\[
0\le-b<5/24,\qquad h_U>7/24.
\]
The sharp two-inner cap theorem
[HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md](HUMAN_SHARP_TWO_INNER_CAP_THRESHOLD.md)
forces \(h_U<H_*=(\sqrt3-1)/2\), since the
two U centers will both be inner, so
\[
-b>1-\sqrt3/2.
\]

## Theorem: explicit strict center-ray lanes

Define the fixed angle
\[
\alpha:=\arcsin(19/24)
\quad(\pi/6<\alpha<\pi/3),
\]
and use polar angles counterclockwise from +x, with
angles of the R-minus member negative.

There are four **distinct inner-center squares**
with the following whole-side statuses and strict rays:

| Member | Status | Center-ray interval |
| --- | --- | --- |
| \(R_-\) | R | \(-\pi/3<\theta_{R_-}<-\alpha\) |
| \(R_+\) | R | \(0<\theta_{R_+}<\pi/3-\alpha\) |
| \(U_+\) | U | \(\pi/3<\theta_{U_+}<2\pi/3-\alpha\) |
| \(U_-\) | U | \(\alpha+\pi/3<\theta_{U_-}<\pi-\alpha\) |

In particular the R-triple whole-cap offset obeys the new
**strict analytic bound**
\[
\boxed{
h_R<\cos\alpha-1/2
=\frac{\sqrt{215}-12}{24}
\approx0.11096.
}                                                    \tag{1}
\]
This improves the previous \(h_R<13/100\) necessary
condition for S2/k=3.

## Proof

Since D is the **farther** two-square cap and
\(h_D\ge1/2\), its two whole squares both have
outer centers, by the cap normal projection inequality
\(n\cdot p\ge h_D+1/2\ge1\).
The separate R triple has at least one outer center,
by the three-inner-cap exclusion.
Because all statuses are exclusive one-side and \(k=3\),
there can be **no other** outer center. Thus the R triple
has exactly **two inner** square centers, and both
U-cap square centers are **inner**.

By the two-inner cap angular theorem, the two
R-inner center rays have opposite y signs, the two
U-inner rays have opposite x signs, and any two
distinct inner-center rays have angular
separation strictly greater than \(\pi/3\).

Write those four rays as \(R_-,R_+,U_+,U_-\),
ordered by their transverse signs. Every R center has
\(p_x\ge h_R+1/2>1/2\) and norm \(<1\); hence
\[
-\pi/3<\theta_{R_-}<0<\theta_{R_+}<\pi/3.       \tag{2}
\]
Every U center has
\[
p_y\ge h_U+1/2>7/24+1/2=19/24
\]
and norm \(<1\). Consequently its ray obeys
\[
\alpha<\theta_{U_+}<\pi/2
<\theta_{U_-}<\pi-\alpha.                       \tag{3}
\]

The two U inner centers are distinct and their
smaller angular gap exceeds \(\pi/3\), so
\[
\theta_{U_+}
<\theta_{U_-}-\pi/3
<2\pi/3-\alpha.                                 \tag{4}
\]
Also
\(\theta_{U_-}>\theta_{U_+}+\pi/3>\alpha+\pi/3\).

The positive-sign R-inner and U-inner centers are
**different labels** (single-side statuses). They
both lie in the open NE quadrant. If
\(\theta_{R_+}\ge\theta_{U_+}\), their angular
difference would be less than \(\pi/3\)
by (2)–(3), contradicting the inner-center
pair bound. Thus
\[
\theta_{U_+}-\theta_{R_+}>\pi/3.                 \tag{5}
\]
Combining (4)–(5) gives
\[
0<\theta_{R_+}<\pi/3-\alpha,\qquad
\pi/3<\theta_{U_+}<2\pi/3-\alpha.
\]
Finally, the two R-inner rays themselves
are separated by more than \(\pi/3\), giving
\[
\theta_{R_-}<\theta_{R_+}-\pi/3<-\alpha,
\]
which proves all four announced strict lanes.

For the \(R_-\) center, its x coordinate is
\[
p_{R_-}.x=|p_{R_-}|\cos|\theta_{R_-}|
<\cos\alpha=\sqrt{215}/24,
\]
while whole R-cap containment yields
\(p_{R_-}.x\ge h_R+1/2\).
Subtracting \(1/2\) proves (1). QED.

## Scope of the reduction

The proof gives a **necessary exact angular fan** for S2/k=3;
it neither asserts geometric realizability nor rules out the
entire S2 branch. It uses the assumption \(k=3\) critically,
because higher k may have fewer than two inner-center
members in either triple or opposite cap.

The four whole squares have **independent frames**.
Center-ray angular placement does not imply that an entire
square belongs to an origin quadrant, nor does it provide an
arbitrary chosen physical contact or inter-exterior separator.

The global target \(R_8\ge\widehat R\), and the
equality-bearing S4 cases, remain untouched.
