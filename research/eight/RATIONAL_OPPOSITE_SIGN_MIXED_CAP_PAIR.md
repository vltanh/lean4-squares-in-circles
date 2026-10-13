# Exact local counterexample: an opposite-sign mixed cap pair fits well below q+

**Status: rigorous local two-square construction, NOT an n=8 packing.**

This rational example is a negative control for the
computer-assisted [COMPUTER_ASSISTED_ATTACK_ROADMAP.md](COMPUTER_ASSISTED_ATTACK_ROADMAP.md).
It shows the S2/k4 **opposite-transverse-sign** cells A/B
cannot be excluded by the *near-U two-square cap data alone*.

## Exact construction

Let \(h=2/5\) and take two axis-parallel, genuine unit squares
\[
P=[-4/5,1/5]\times[2/5,7/5],\qquad
Q=[3/10,13/10]\times[2/5,7/5].
\]
Their actual centers are
\[
p=(-3/10,9/10),\qquad q=(4/5,9/10).
\]

* **Whole cap:** both entire squares are in \(y\ge h=2/5\).
* **Opposite transverse signs:** \(p_x=-3/10<0<4/5=q_x\).
* **Mixed center radial classes:**
  \[
  |p|^2=9/10<1,\qquad |q|^2=29/20>1.
  \]
* **True-square separation:** the support axis \(n=(1,0)\)
  separates them with a strict exact gap
  \[
  q_x-p_x-\frac12-\frac12
  =1/10>0.
  \]
  Thus even their *closed* squares are disjoint.
* **All eight true vertices contained in a disk:**
  \[
  \max_{v\in P}|v|^2=13/5,\quad
  \max_{v\in Q}|v|^2=73/20
  <9789/2500,
  \]
  the latter with exact strict margin
  \[
  9789/2500-73/20=166/625>0.
  \]

The offset \(h=2/5\) belongs to current
S2/k4 **cell A**, which has
\(37/100\le h_U<97/200\) and opposite-sign
mixed centers. This construction is a
**two-square local witness only**: it is NOT
a full S2 packing and does not solve the
remaining seven-center/contact interactions.

## Strategic consequence

It would be false to assert that *every*
opposite-sign mixed cap pair is impossible
under the n=8 radius ceiling. Any correct
elimination of S2/k4 cell A must use the
other squares and/or additional exact
requirements: especially its **two far-D
outer centers**, the **one-outer/two-inner
right-cap triple**, central square, and
all of their genuine pair-separating axes.

By contrast, the *same-sign mixed* cell C
can be targeted through a local two-square
inequality: the new
[HUMAN_MIXED_HIGH_CAP_37_100.md](HUMAN_MIXED_HIGH_CAP_37_100.md)
already excludes it for offsets h>=37/100.
These different geometric situations must
not be conflated.

The full sharp \(R_8\ge\widehat R\)
inequality, global equality classification
and Lean formalization remain OPEN.

[verify_opposite_sign_mixed_cap_pair.py](verify_opposite_sign_mixed_cap_pair.py)
checks every listed rational vertex and
separating-axis identity without floating-point
arithmetic.
