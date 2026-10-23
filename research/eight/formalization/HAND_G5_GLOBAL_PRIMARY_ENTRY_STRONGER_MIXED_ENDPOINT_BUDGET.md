# A slightly stronger whole-domain H/D/E endpoint budget

## 1. Statement on the unchanged actual mixed witnesses

Put
\[
 Q=9789/2500,\qquad R=\sqrt Q,\qquad
 S_0=2\sqrt{Q-1}-3,\qquad
 p_0=50/49,\quad p_1=41/40,\quad
 \Delta=p_1-p_0=9/1960,
 \qquad \varepsilon=27/160000.
\tag{1}
\]
Retain sorted contained true-core states H,D,E at any
common ceiling q<=Q, with H nonnegative, D nonpositive,
and E nonpositive. Retain their actual DE2 or DE3 and
actual EH0 or EH1 witnesses, with real frame spread at
most 7/10. No radial-boundary condition is required.
Let alpha=theta_H-theta_D. Then
\[
                    b_H+b_D-p_1\alpha+S_0
                                      <2-\varepsilon.
\tag{2}
\]
This uses the original coordinates, frames and owners.
It strengthens the coefficient p_0 in
[the all-mixed-owner endpoint estimate](HAND_G5_GLOBAL_INTERMEDIATE_ORDER_WITH_ALL_MIXED_OWNERS.md)
without reducing the uniform reserve recorded in
[the small-wrong-sign capture](HAND_G5_GLOBAL_SMALL_WRONG_INTERMEDIATE_SIGNS.md),
Section 2. Its proof below checks every place where an
increase of that coefficient could weaken an old bound.

The same statement holds for the physically reflected
system with positive E. Indeed exchange H with D, negate
the frame direction and signed tangents, and exchange the
corresponding actual mixed owners. This sends positive E
to nonpositive E, interchanges the two one-rotated owner
pairs, and leaves b_H+b_D and alpha unchanged. This is
only the scalar endpoint reflection; no local E transport
is being reflected or asserted.

## 2. The rotated norm comparison remains valid on its whole domain

For 4/5<=lambda<=2, let
\[
 N_\lambda(d)=\sqrt{1+\lambda^2+2\lambda\sin d},
\]
\[
 \Psi_{\lambda,p}(d)
   =RN_\lambda(d)-\lambda\{\cos d+(\sin d)_+\}-pd.
\tag{3}
\]
We retain the whole-domain comparison
\[
              \Psi_{\lambda,p_1}(d)
                       \le\Psi_{\lambda,p_1}(0)
                         \qquad (|d|\le7/10),
\tag{4}
\]
with strict inequality at nonzero d.

For d>0, increasing p only decreases the left side, so
the cited proof with p_0 applies unchanged. Its elementary
linear bound is in fact stricter, since 17/20<p_1.

For d=-x<0, Section 2 of that proof first uses concavity
in lambda to reduce to lambda=4/5 or 2. The second
lambda derivative does not involve p. After division by
x, its two explicit lower polynomials have whole-interval
lower bounds
\[
                  47849/2940000,
                       \qquad 117837/980000.
\tag{5}
\]
Replacing p_0 by p_1 subtracts just Delta from each
divided polynomial. The resulting exact bounds are
\[
 \frac{47849}{2940000}-\Delta
       =\frac{34349}{2940000}>0,
 \qquad
 \frac{117837}{980000}-\Delta
       =\frac{113337}{980000}>0.
\tag{6}
\]
Thus its same two polynomials and same lambda concavity
prove (4) on the entire angle and weight domains.

## 3. The two primary endpoint scalar families

All circle support, actual-E contact and admissible-weight
arguments in Sections 3--5 of the cited all-mixed proof
are independent of p. Only the final scalar linear term
changes. The underlying primary endpoint proof is
[the global intermediate-frame-order note](HAND_G5_GLOBAL_INTERMEDIATE_FRAME_ORDER.md),
Sections 3--6. We check its two signs here.

### 3.1 A nonnegative primary remainder

Its scalar has the term -p x with x>=0. Therefore every
old positive-remainder bound improves by Delta x. In
particular the interval [0,1/2] retains the strict reserve
epsilon in (1), obtained from the old whole-interval
concavity certificate. For [1/2,7/10], the fixed weight
lambda=4/5 and the same support bound J_E(x)<=41x/40
give, at the worse endpoint x=1/2,
\[
 2\frac{507}{200}-\frac{17}{5}
       +\frac12\left(\frac45\frac{41}{40}-p_1\right)
       +\frac{52}{125}
                           =2-\frac{33}{2000}.
\tag{7}
\]
The coefficient of x is negative, so (7) controls the
entire second interval. Both reserves exceed epsilon.

### 3.2 A negative primary remainder

Here the scalar is
\[
 F_{d,p}(x)=2\sqrt{Q-X_d(x)^2}-1+S_0+px,
\]
\[
 X_d(x)=\frac32+\frac{847}{1600}\sin x
                         -\frac d2(1-\cos x),
\quad
 d=\begin{cases}
 183/200,&0\le x\le6/25,\\
 4/5,&6/25\le x\le7/10.
 \end{cases}
\tag{8}
\]
On the first interval, the old square-root tangent bounds
its increment over zero by x times
-41559103/612500000. Increasing p adds Delta to that
coefficient, which remains strictly negative:
\[
             -\frac{41559103}{612500000}+\Delta
                     =-\frac{38746603}{612500000}<0.
\tag{9}
\]
The zero endpoint is still below 999/500=2-1/500.

On the second interval the old exact calculation proves
that the radical term in (8) is convex. Adding a new
linear term preserves that convexity. The same positive
square bounds at its two endpoints now give exactly
\[
 \begin{split}
 F_{4/5,p_1}(6/25)
   &<2\frac{1151}{1000}-1+\frac{52}{125}
                               +p_1\frac6{25}
                                  =2-\frac9{250},\\
 F_{4/5,p_1}(7/10)
   &<2\frac{233}{250}-1+\frac{52}{125}
                               +p_1\frac7{10}
                                  =2-\frac1{400}.
 \end{split}
\tag{10}
\]
Convexity bounds the entire interval by the larger of these
two endpoints. Thus every negative-remainder scalar retains
a reserve at least 1/500, which is greater than epsilon.

## 4. All four actual owner pairs

For DE2/EH0 the E coefficients cancel exactly. Collect
the two original outer circles once each and apply (4)
with the unchanged weight lambda=7/6. The zero-angle
bound is the same as before, namely less than 999/500.

For DE2/EH1 or DE3/EH0, use (4) to remove the one rotated
endpoint term. The exact remaining primary scalar and its
admissible lambda range are unchanged. Section 3 verifies
that scalar for either sign of its actual primary error,
with reserve at least epsilon. No unavailable primary
owner has been substituted for the original rotated owner.

For DE3/EH1 the existing actual-primary endpoint comparison
reduces directly to the same two scalar families. Its
angle minimization, E-circle support and negative-error
true-core bounds do not involve p; hence Section 3 applies
to that pair as well.

This proves (2) for all four original owner pairs and all
their signed errors, including total zero and every weak
contact. The only new arithmetic is (6),(7),(9),(10).
All continuous interval reductions, stress-weight ranges
and true-core arguments are the same proved ones as in
the linked notes, with the strengthened coefficient checked
explicitly wherever it has the adverse sign.

## 5. A useful consequence for the remaining negative BT endpoint

For a genuine negative BT3 with aligned TD, the actual
local comparison gives b_D>.844. If H<=D, (2) therefore
implies
\[
 b_H<1.156-S_0-p_1(\theta_D-\theta_H)-\varepsilon.
\tag{11}
\]
This is a strict original-state transverse budget, not an
alignment or owner conversion. It may be combined with
the original HG/GA/AB/BT inequalities before any state is
changed. Its coefficient is stronger than the earlier
unclipped zero-edge coefficient 50/49; the positive
difference is the exact value Delta in (1).
