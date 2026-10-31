# The measure's entire inner line reduces to two fixed critical enclosures

Date: October 26, 2026.

**Current dependency update, October 27:** the complete derivative and
minimum-location arguments below are unchanged. Their two fixed mass
targets are now proved directly at the actual minima in
NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md, Section 3, after
the full reviews recorded in ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md.
The two-box checker and its margins below remain a historical
alternative and are not required on this current analytic route.

**Status: accepted complete analytic reduction and exact two-box check**
after full reviews in REVIEW_NINE_MEASURE_LINE_REDUCTION_ROOT_2026_10_26.md
and REVIEW_NINE_MEASURE_LINE_TWO_POINT_C6_2026_10_26.md.
This replaces the95 former line charges by two fixed enclosures.
The original208-charge checkers remain historical alternatives; the
complete current five-charge proof is assembled in
NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.

Use exactly the same measure, weights, open-interior convention and
disk-center normalization as NINE_RADIUS_TWO_MEASURE_LOWER_BOUND.md:
\[
 \mu=\frac1{1000}\bigl(292\delta_0+714\lambda_{1/10}
              +3858\lambda_1+2424\lambda_{11/10}
              +1709\lambda_{27/20}\bigr).
\tag{1}
\]
Only the line
\[
                   S(a)=[a-1,a]\times[-1/2,1/2],
                          \qquad9/10\le a\le11/10
\tag{2}
\]
is considered here. The accepted whole-rectangle vertical-translation
argument extends this line bound to its original two-dimensional
domain. The corner rectangle, middle rectangle and outer boundary
curve keep their existing independent obligations.

The new self-contained exact checker is
NINE_RADIUS_TWO_MEASURE_LINE_TWO_POINT_CHECK.py. It contains no
adaptive subdivision or numerical minimization. Every sign over the
continuous line is proved analytically below; the checker verifies
only two explicit fixed common rectangles surrounding its minima.

## 1. Exact circle charges on the entire line

The horizontal band in (2) contains the whole circle of radius 1/10.
Its upper x bound is inactive, and its lower bound is a-1. Thus
\[
 \lambda_{1/10}(\operatorname{int}S(a))
                       =\frac{\arccos(10(a-1))}{\pi}.
\tag{3}
\]
At each of the three larger radii, the negative x branch is outside
the square: its absolute x coordinate in the strip is at least
sqrt(1-1/4)>1/10, whereas a-1>=-1/10. The positive branch
automatically exceeds the lower x bound. With
\(\beta_r=\arcsin(1/(2r))\), its exact charge is therefore
\[
 \lambda_r(\operatorname{int}S(a))
   =\frac{[\beta_r-\arccos(\min(a/r,1))]_+}{\pi}.
\tag{4}
\]
The circle of radius27/20 contributes zero on the entire line,
since \(a^2+1/4\le(11/10)^2+1/4<(27/20)^2\).
At radius1 the positive part in (4) is already active at a=9/10,
because \((9/10)^2>1-1/4\). At radius11/10 it is active for
every a>=1, because \(1>(11/10)^2-1/4\).

All these formulas concern open interiors. The finitely many tangent
circle points have zero angular measure. The origin atom is present
exactly for a<1, and is absent at a=1 and on the whole right interval.

## 2. The whole left interval has one analytically located minimum

For 9/10<=a<1, discard only the nonnegative contribution of the
circle11/10. The remaining submeasure is
\[
 L(a)=\frac{292}{1000}
   +\frac{714}{1000\pi}\arccos(10(a-1))
   +\frac{3858}{1000\pi}\bigl(\pi/6-\arccos a\bigr),
\qquad \mu(\operatorname{int}S(a))\ge L(a).
\tag{5}
\]
For the purpose of locating its minimum, extend the displayed
function L continuously to a=1. This is only the same scalar
function; it does not credit an origin atom to the actual square
at a=1, which belongs to Section3 instead.

On 9/10<a<1, differentiation gives
\[
 1000\pi L'(a)
   =\frac{3858}{\sqrt{1-a^2}}
        -\frac{714}{\sqrt{(a-9/10)(11/10-a)}}.
\tag{6}
\]
The sign is exactly the sign of
\[
 H(a)=3858^2(a-9/10)(11/10-a)-714^2(1-a^2).
\tag{7}
\]
Both compared derivative terms are positive before subtraction,
so the positive squaring that gives this equivalence is legitimate.
Moreover
\[
 H'(a)=2\{3858^2-(3858^2-714^2)a\}\ge2\,714^2>0
                    \quad(9/10\le a\le1).
\tag{8}
\]
The endpoint signs are H(9/10)<0<H(1). Hence there is exactly
one zero a0, and L decreases before it and increases after it.
The complete line minimum is therefore L(a0).

Two exact rational evaluations locate this unique minimum:
\[
 H(927/1000)=-\frac{68424471}{31250}<0,\qquad
 H(928/1000)=\frac{14285817}{15625}>0.
\tag{9}
\]
Thus
\[
                         927/1000<a_0<928/1000.
\tag{10}
\]
The checker uses one common open rectangle contained in all squares
of (10), and only the three terms of the submeasure defining L.
Its strict charge above one consequently proves L(a0)>1 and hence
\(\mu(\operatorname{int}S(a))>1\) on the entire left interval.
No charge outside that single fixed critical enclosure is needed.

## 3. The whole right interval has one exact rational minimum

For 1<=a<=11/10 there is no origin atom. Equations (3)--(4) give
the exact whole measure
\[
 U(a)=\frac{3858}{6000}
   +\frac{714}{1000\pi}\arccos(10(a-1))
   +\frac{2424}{1000\pi}
      \left(\arcsin\frac5{11}-\arccos\frac{10a}{11}\right).
\tag{11}
\]
For 1<a<11/10,
\[
 1000\pi U'(a)
  =\frac1{\sqrt{11/10-a}}
       \left(\frac{2424}{\sqrt{a+11/10}}
                  -\frac{714}{\sqrt{a-9/10}}\right).
\tag{12}
\]
Thus its sign is exactly the sign of the increasing linear function
\[
                       J(a)=2424^2(a-9/10)-714^2(a+11/10).
\tag{13}
\]
There is one zero, lying strictly between1 and11/10:
\[
 a_*=
   \frac{9\,2424^2+11\,714^2}{10(2424^2-714^2)}
     =\frac{324943}{298110}.
\tag{14}
\]
Equations (12)--(13) show that U decreases before a_* and
increases after it. Continuity includes both endpoints of the
closed right interval, including the atom-free a=1 case.
Therefore its whole-domain minimum is U(a_*).

One fixed outward rational enclosure of this exact rational point,
with no parameter subdivision, suffices to verify U(a_*)>1.

## 4. The two complete fixed charge checks

The checker keeps the reviewed scales and pi enclosure of the
original integer verifier:
\[
 B=83886080,\quad Q=2^{56},\qquad
 P_-=226375608064909912,\quad P_+=226375608064910268,
\]
\[
                         P_-/Q\le\pi\le P_+/Q.
\tag{15}
\]
All following coordinate entries are integer numerators over B.
For the first enclosure use the lower floor of 927B/1000 and
the upper ceiling of 928B/1000. For the second use the floor
and ceiling of Ba_* from (14). Both b coordinates are exactly B/2.

| Critical enclosure | a_l | a_h | b_l=b_h | Circle contributions used | Origin atom |
| --- | ---: | ---: | ---: | --- | --- |
| Unique left minimum |77762396|77846283|41943040|1/10 and1|292/1000|
| Exact right minimum |91436699|91436700|41943040|1/10,1 and11/10|0|

Each represented common rectangle is
\((a_h/B-1,a_l/B)\times(-1/2,1/2)\). It is contained in
the square at the corresponding minimum. In the first case its
origin is strictly interior, as required for L. In the second case
the origin is outside, as required for U.

The standalone checker reproduces the independently reviewed
outward-rounded inverse-trigonometric primitives of the original
measure checker. It uses the same four-quadrant angular formulas,
and verifies for each row the strict integer margin
\[
 \sum_{r\ \mathrm{used}} w_r L_r-(1000-292I)2P_+>0.
\tag{16}
\]
No floating-point value or representative-square evaluation enters
this comparison. The exact results are
\[
 \begin{array}{c|r}
 \text{left critical enclosure}&1153182092959159440\\
 \text{right critical enclosure}&2475502032000671400
 \end{array}
\tag{17}
\]
for the same angular numerator scale Q. The margins imply mass
strictly greater than one after the conservative normalization by
the upper pi enclosure, exactly as in the original verifier.
The checker also verifies (9) and the rational identity (14).

## 5. Exact replacement and limits

Equations (5)--(17) prove the charge bound on the entire original
line (2), with its origin-atom boundary handled explicitly. The
accepted vertical-translation theorem then supplies the same full
two-dimensional coverage formerly obtained from its95 line leaves.

This replacement requires exactly two fixed charged common rectangles,
not95 adaptively generated line leaves. It removes93 current charge
obligations. With the unchanged14 corner,2 middle and97 outer
charges, the complete uniform measure proof would require115 charge
checks in total after acceptance and integration. Its six exact
empty-domain tests outside the line remain unchanged.

The current accepted208-check source and both current full checkers
have intentionally not been modified by this manuscript. The new
two-box checker is an independently reviewable replacement. This is
a reduction in finite arithmetic obligations, not a claim that the
global measure theorem is table-free. All nine original units,
arbitrary orientations, zero circle weights and every physical
contact pattern remain in the global theorem's scope. No Lean
compilation or CI was run.
