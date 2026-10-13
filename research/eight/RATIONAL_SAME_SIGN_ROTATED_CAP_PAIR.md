# Exact same-sign, nonparallel two-square cap packing below the n=8 radius ceiling

**Status: rigorously checked local counterexample, NOT an eight-square packing.**

This note records a **strict rational witness** showing that the still-open
same-sign S2/k4 near-side cap geometry cannot be ruled out using only
*two squares*, their whole-cap condition, disk containment and arbitrary
pairwise non-overlap. It explicitly complements (and does not contradict)
[HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md](HUMAN_SAME_SIDE_NEAR_AXIS_CAP.md):
that theorem requires both frames to be extremely close to the central
axes; the present witness has one frame tilted substantially.

## Construction

Put
\[
h=\frac{881}{3000}=\frac7{24}+\frac1{500}
\quad\left(\frac7{24}<h<\frac25\right),\qquad
q_+=\frac{9789}{2500}.
\]
Let \(P\) and \(Q\) be the *closed* unit squares determined by the
following exact centers and orthonormal frames:
\[
p=\left(\frac1{1000},\,\frac{11}{8}\right),\qquad
e_P=\left(\frac{399}{401},-\frac{40}{401}\right),\qquad
f_P=\left(\frac{40}{401},\frac{399}{401}\right),
\]
\[
q=\left(\frac{249}{250},\,\frac{2381}{3000}\right),
\qquad e_Q=(1,0),\quad f_Q=(0,1).
\]
Each square is the set of points
\(p_i+u e_i+v f_i\), \(-1/2\le u,v\le1/2\).
The Pythagorean identity
\(399^2+40^2=401^2\) proves that P is a genuine
rotated **unit square**, not a bounding-box rectangle.

**Both true square centers have strictly positive x coordinates**
(\(1/1000\) and \(249/250\)), so they occupy the *same strict*
transverse origin half-plane.

## 1. Both entire unit squares lie beyond y=h

The lowest true vertex ordinates are
\[
\min_{z\in P}z_y
=\frac{11}{8}-\frac{399+40}{802}
=\frac{2655}{3208}>h,
\]
\[
\min_{z\in Q}z_y
=\frac{2381}{3000}-\frac12
=\frac{881}{3000}=h.
\]
For P, the exact strict margin is
\[
\frac{2655}{3208}-\frac{881}{3000}
=\frac{80293}{150375}>0.
\]

## 2. The two actual square interiors are disjoint

For the unit separating direction \(n=e_P\), the center
projection gap between Q and P is
\[
n\cdot(q-p)
=\frac{399}{401}\left(\frac{249}{250}-\frac1{1000}\right)
-\frac{40}{401}\left(\frac{2381}{3000}-\frac{11}{8}\right).
\]
P has supporting half-width \(1/2\) in n,
while Q, which is axis-parallel, has half-width
\[
h_Q(n)=\frac{|399|+|40|}{802}
=\frac{439}{802}.
\]
The exact SAT separating-axis reserve is
\[
n\cdot(q-p)-\frac12-\frac{439}{802}
=\boxed{\frac{31}{48120}>0}.
\]
Thus the two *actual rotated squares* have **strictly
disjoint closed sets**, a stronger property than the
required disjoint open interiors. This is an
orientation-aware separating-axis certificate.

## 3. All eight true square vertices fit strictly inside q_+

The maximum squared vertex norm of any unit square
with center p and orthonormal frame e,f is exactly
\[
|p|^2+|p\cdot e|+|p\cdot f|+\frac12.
\]
Substituting the two rational square frames gives
\[
\max_{z\in P}|z|^2
=\frac{780953513}{200500000},
\qquad
\max_{z\in Q}|z|^2
=\frac{7040861}{1800000}.
\]
Both are strictly below the n=8 search ceiling:
\[
\frac{9789}{2500}
-\max_{z\in P}|z|^2
=\frac{4124287}{200500000}>0,
\]
\[
\frac{9789}{2500}
-\max_{z\in Q}|z|^2
=\frac{7219}{1800000}>0.
\]
In particular, the two actual squares already fit in the
smaller disk
\[
R^2=\frac{7040861}{1800000}<\frac{9789}{2500}.
\]
The witness has a *strict* same-sign center condition, a
*strictly positive* R-cap offset above \(7/24\), and a
*strictly positive* pairwise separating-axis margin.

## What this counterexample does and does not refute

This is a valid **two-square cap packing**, not a packing
of eight squares and **not** a valid S2/k4 configuration
of the full n=8 problem. The new exact witness shows:

* One **cannot** prove that two whole unit squares in
  \(y\ge h>7/24\) with same-sign transverse center
  coordinates are impossible **for all independent frames**.
* Any exclusion of S2/k4 cell C must use **additional**
  conditions (the inner/outer center labels, forced outer
  polar order, the central square and/or remaining five
  exterior squares), or stricter hypotheses on the cap geometry.
  The example does not certify the cell C's full
  inner/outer assignments: both center radii here are >1.
* The near-axis-frame exclusion remains correct and useful:
  one square in this example has actual frame
  \(\tan|\theta|=40/399\), far above its \(1/2600\)
  neighborhood.

There is no general eight-square optimality conclusion,
no change to the legitimate S4/k7 equality family, and
no Lean proof. All claims are based on rational vertices
and an actual rotated separating axis.

[verify_same_sign_cap_pair.py](verify_same_sign_cap_pair.py)
replays every rational equality without floating-point calculations.
