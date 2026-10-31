# Both residual measure rectangles have direct analytic charges

Date: October 26, 2026.

**Current dependency update, October 27:** this complete rectangle proof
and its fourteen displayed Taylor comparisons are unchanged. The five
mass-checker and one derivative-checker dependencies left by the
historical assembly described below are now replaced by
NINE_RADIUS_TWO_MEASURE_ANALYTIC_FIXED_VALUES.md. Full acceptance and
the exact current scope are in ANALYTIC_CERTIFICATE_CHECKPOINT_2026_10_27.md.

**Status: accepted complete whole-domain analytic proof**, after full
reviews in REVIEW_NINE_MEASURE_RECTANGLES_ROOT_2026_10_26.md and
REVIEW_NINE_MEASURE_RECTANGLES_ANALYTIC_C6_2026_10_26.md.
This removes all14 corner charges, both middle charges and all three
corner empty tests. The original208-charge programs remain historical
alternatives; the complete current five-charge assembly is
NINE_RADIUS_TWO_MEASURE_FIVE_POINT_REDUCTION.md.

Use precisely the original measure
\[
 \mu=\frac1{1000}\left(
 292\delta_0+714\lambda_{1/10}+3858\lambda_1
       +2424\lambda_{11/10}+1709\lambda_{27/20}\right)
\tag{1}
\]
and normalized actual square
\[
 S(a,b)=[a-1,a]\times[b-1,b],\qquad
                   \frac12\le b\le a,\quad a^2+b^2\le4.
\tag{2}
\]
All charges refer to open interiors. Finitely many circle contacts
with rectangle edges have zero angular measure. An origin atom is used
only when the origin is strictly inside the actual square.

The two complete domains treated here are
\[
 \mathcal C:\quad9/10\le b\le a\le11/10,\qquad
 \mathcal M:\quad11/10\le a\le27/20,\quad1\le b\le a.
\tag{3}
\]
They are the actual portions of the former corner and middle certificate
rectangles. We prove \(\mu(\operatorname{int}S)>1\) throughout both.
No parameter box is charged by an interval evaluator. Every fixed rational
comparison is displayed below and follows from elementary sine bounds.

Write
\[
 w_0=714/1000,\quad w_1=3858/1000,\quad
 w_2=2424/1000,\quad w_3=1709/1000.
\tag{4}
\]
An arc of length \(L\) at the corresponding radius has measure
\(w_jL/(2\pi)\).

## 1. Fixed inverse-sine comparisons with explicit remainders

For every \(0\le t\le63/50\), signed Taylor estimates give
\[
       t-t^3/6\le\sin t\le t-t^3/6+t^5/120.
\tag{5}
\]
These follow from the alternating sine series, whose term magnitudes
decrease on this interval; the first omitted term has the stated sign.
Every \(t\) below is less than \(\pi/2\), since \(\pi>3\).

The next table proves each lower inverse-sine bound. Its final column
is exactly \(z-(t-t^3/6+t^5/120)>0\), so \(\arcsin z>t\).

| \(z\) | \(t\) | Exact positive reserve |
| --- | --- | --- |
| \(9/10\) | \(223/200\) | \(64180522657/38400000000000\) |
| \(9/11\) | \(191/200\) | \(729120878539/422400000000000\) |
| \(10/11\) | \(227/200\) | \(880201511023/422400000000000\) |
| \(21/22\) | \(63/50\) | \(203016009/137500000000\) |
| \(2/3\) | \(18/25\) | \(1063804/146484375\) |
| \(7/9\) | \(89/100\) | \(2229221653/3600000000000\) |
| \(20/27\) | \(83/100\) | \(29765234213/10800000000000\) |
| \(22/27\) | \(19/20\) | \(4363109/3456000000\) |
| \(8/9\) | \(109/100\) | \(6858681353/3600000000000\) |

The next table proves upper bounds. Its final column is exactly
\(t-t^3/6-z>0\), so \(\arcsin z<t\).

| \(z\) | \(t\) | Exact positive reserve |
| --- | --- | --- |
| \(1/10\) | \(1/9\) | \(119/10935\) |
| \(7/20\) | \(9/25\) | \(139/62500\) |
| \(1/5\) | \(21/100\) | \(16913/2000000\) |
| \(2/11\) | \(19/100\) | \(464551/66000000\) |
| \(7/22\) | \(13/40\) | \(4633/4224000\) |

We also use \(\arcsin x\ge x\) for \(x\ge0\) and the already reviewed
\[
                            3<\pi<22/7.
\tag{6}
\]
All later comparisons are rational after these bounds.

## 2. The complete corner triangle

The following four cases are exhaustive and retain every boundary.

### 2.1 The actual origin is interior: \(a<1\)

Since \(b\le a<1\), the origin lies strictly inside the actual square.
Its interior contains
\[
                              (0,9/10)^2.
\tag{7}
\]
The actual square, separately from (7), receives the atom \(292/1000\).
The rectangle supplies a quarter of the small circle and exact positive
arc lengths \(2\arcsin(9/10)-\pi/2\) and
\(2\arcsin(9/11)-\pi/2\) at radii \(1,11/10\). Ignoring the
fourth circle gives
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &\ge \frac{292}{1000}+\frac{w_0}{4}
       -\frac{w_1+w_2}{4}
       +\frac{w_1\arcsin(9/10)+w_2\arcsin(9/11)}{\pi}\\
 &>\frac{292}{1000}+\frac{w_0}{4}
       -\frac{w_1+w_2}{4}
       +\left(w_1\frac{223}{200}
                        +w_2\frac{191}{200}\right)\frac7{22}\\
 &=1+\frac{11613}{2200000}>1.
 \end{split}
\tag{8}
\]
No atom is assigned to (7), whose boundary contains the origin. It is
assigned only to the actual square, where both strict signs hold.

### 2.2 Both lower coordinates are nonnegative: \(b\ge1\)

Here \(1\le b\le a\le11/10\), so every interior contains
\[
                              (1/10,1)^2.
\tag{9}
\]
Its radius-one arc has length \(\pi/2-2\arcsin(1/10)\).
Its radius-\(11/10\) arc has length
\(2\arcsin(10/11)-\pi/2\): at either upper face the other
coordinate is \(\sqrt{21}/10>1/10\), so the lower faces do not cut it.
Using \(\arcsin(1/10)<1/9\) and
\(\arcsin(10/11)>227/200>11/10\),
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &\ge \frac{w_1-w_2}{4}
       -\frac{w_1\arcsin(1/10)}{\pi}
       +\frac{w_2\arcsin(10/11)}{\pi}\\
 &>\frac{w_1-w_2}{4}-\frac{w_1}{27}
                         +w_2\frac{11}{10}\frac7{22}\\
 &=1+\frac{5761}{90000}>1.
 \end{split}
\tag{10}
\]
No origin atom or small-circle contribution is assumed.

### 2.3 \(1\le a\le21/20,\ b\le1\)

Every interior in this domain contains
\[
                           (1/20,1)\times(0,9/10).
\tag{11}
\]
Its small-circle arc is \(0<\theta<\pi/3\). The radius-one arc
has length \(\arcsin(9/10)\). The radius-\(11/10\) arc has length
\[
            \arcsin(9/11)+\arcsin(10/11)-\pi/2.
\]
For the latter two circles the positive x coordinate at the upper y
face already exceeds \(1/20\), so that lower x face is inactive.
Thus
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &\ge\frac{w_0}{6}-\frac{w_2}{4}
   +\frac{w_1\arcsin(9/10)
         +w_2\{\arcsin(9/11)+\arcsin(10/11)\}}{2\pi}\\
 &>\frac{w_0}{6}-\frac{w_2}{4}
   +\left(w_1\frac{223}{200}
            +w_2\frac{418}{200}\right)\frac7{44}\\
 &=1+\frac{14681}{4400000}>1.
 \end{split}
\tag{12}
\]
The weak boundary \(b=1\) causes no problem: (11) remains inside the
open interior and the proof uses no atom.

### 2.4 \(21/20\le a\le11/10,\ b\le1\)

For the three large circles alone we first prove
\[
 \mu_{\mathrm{large}}(\operatorname{int}S(a,b))
       \ge
 \mu_{\mathrm{large}}(\operatorname{int}S(21/20,9/10)).
\tag{13}
\]
This compares values of a measure; it does not move any packing unit.

At radius one put \(A=a-1\in[1/20,1/10]\) and
\(t=\sqrt{1-A^2}>9/10\). Its exact arc length is
\[
 L(b)=\arcsin(\min(b,t))-\arcsin(b-1),\qquad9/10\le b\le1.
\tag{14}
\]
The upper x face is inactive, and the negative x branch is excluded.
The function increases until \(b=t\) and decreases thereafter.
Its endpoint values are
\[
 L(9/10)=\arcsin(9/10)+\arcsin(1/10),\qquad
 L(1)=\arccos A\ge\arccos(1/10).
\]
The first is smaller, because
\(\cos(2\arcsin(1/10))=49/50>9/10\) and
\(0<2\arcsin(1/10)<\pi/2\). Thus its minimum is at \(b=9/10\).

For \(r\in\{11/10,27/20\}\) and \(-1/10\le y\le1\),
\[
          x=\sqrt{r^2-y^2}\ge\sqrt{21}/10>1/10\ge A.
\]
The lower x face is inactive and the negative x branch is excluded.
The exact angular density is
\[
 f_{r,a}(y)=\frac{\mathbf1_{\{\sqrt{r^2-y^2}<a\}}}
                       {\sqrt{r^2-y^2}}.
\tag{15}
\]
It is even and nondecreasing in \(|y|\). Translating \([b-1,b]\)
upward, with \(9/10\le b\le1\), removes absolute coordinates
at most \(1/10\) and adds coordinates at least \(9/10\).
The integral cannot decrease. This includes a possible negative-y
arc when \(a\) is close to \(11/10\).

Finally, at \(b=9/10\) the positive branch of all three large circles
has \(x\ge\sqrt{19}/10>1/10\) on \(-1/10\le y\le9/10\).
The lower x face remains inactive for \(21/20\le a\le11/10\).
Increasing the upper x face can only add measure. This completes (13).

The comparison square has the exact positive arc lengths
\[
 \begin{array}{c|l}
 r&L_r\\ \hline
 1&\arcsin(9/10)+\arcsin(1/10)\\
 11/10&\arcsin(9/11)+\arcsin(21/22)-\pi/2\\
 27/20&\arcsin(2/3)+\arcsin(7/9)-\pi/2.
 \end{array}
\tag{16}
\]
For the latter two radii the negative-y arc is absent because
\(\sqrt{r^2-(21/20)^2}>1/10\). Their upper faces give the stated
arcs; the lower x face is inactive by the preceding bounds.
Section 1 and \(\arcsin(1/10)\ge1/10\) now give
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &>
 -\frac{w_2+w_3}{4}
 +\left\{
      w_1\left(\frac{223}{200}+\frac1{10}\right)
      +w_2\left(\frac{191}{200}+\frac{63}{50}\right)
      +w_3\left(\frac{18}{25}+\frac{89}{100}\right)
                \right\}\frac7{44}\\
 &=1+\frac{2423}{550000}>1.
 \end{split}
\tag{17}
\]
Cases 2.1--2.4 cover all of \(\mathcal C\), including \(a=1\),
\(b=1\) and \(a=21/20\). No limiting origin atom is credited.

## 3. The complete middle triangle

Retain \(b\le a\). Splitting at \(b=6/5\) gives two analytic inclusions.

### 3.1 \(1\le b\le6/5\)

Every interior contains
\[
                      (7/20,11/10)\times(1/5,1).
\tag{18}
\]
Its exact positive-quadrant arc lengths are
\[
 \begin{array}{c|l}
 r&L_r\\ \hline
 1&\pi/2-\arcsin(7/20)-\arcsin(1/5)\\
 11/10&\arcsin(10/11)-\arcsin(2/11)\\
 27/20&\arcsin(20/27)+\arcsin(22/27)-\pi/2.
 \end{array}
\tag{19}
\]
For \(r=11/10\), the upper y face precedes the lower x face
because \(400+49<484\). For \(r=27/20\), the lower faces are
inactive at both upper-face intersections because \(400+49<729\)
and \(484+16<729\); the upper faces give a positive arc because
\(400+484>729\).

Section 1 gives strict lower bounds
\[
                  \pi/2-57/100,\qquad
                   189/200,\qquad89/50-\pi/2.
\]
The combined non-pi numerator is positive:
\[
      -w_1\frac{57}{100}
            +w_2\frac{189}{200}+w_3\frac{89}{50}
                        =\frac{78341}{25000}>0.
\]
Hence
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &>\frac{w_1-w_3}{4}
  +\left(-w_1\frac{57}{100}
            +w_2\frac{189}{200}+w_3\frac{89}{50}\right)\frac7{44}\\
 &=1+\frac{19681}{550000}>1.
 \end{split}
\tag{20}
\]

### 3.2 \(6/5\le b\le a\)

The actual order also gives \(a\ge6/5\). Every interior contains
\[
                              (7/20,6/5)^2.
\tag{21}
\]
Its exact large-circle arc lengths are
\[
 \begin{array}{c|l}
 r&L_r\\ \hline
 1&\pi/2-2\arcsin(7/20)\\
 11/10&\pi/2-2\arcsin(7/22)\\
 27/20&2\arcsin(8/9)-\pi/2.
 \end{array}
\tag{22}
\]
For the last arc the lower faces are inactive because
\((8/9)^2+(7/27)^2=625/729<1\), and the upper faces give a
positive arc because \(2(8/9)^2>1\). The first two circles
have inactive upper faces and the indicated lower faces.

Section 1 gives strict lower bounds
\[
                   \pi/2-18/25,\qquad
                   \pi/2-13/20,\qquad109/50-\pi/2.
\]
Now the combined non-pi numerator is negative:
\[
     -w_1\frac{18}{25}-w_2\frac{13}{20}
                   +w_3\frac{109}{50}=-\frac{31387}{50000}.
\]
Use \(\pi>3\) in this correctly oriented negative term:
\[
 \begin{split}
 \mu(\operatorname{int}S)
 &>\frac{w_1+w_2-w_3}{4}
 +\frac{-w_1(18/25)-w_2(13/20)+w_3(109/50)}6\\
 &=1+\frac{2897}{75000}>1.
 \end{split}
\tag{23}
\]
The equality \(b=6/5\) is covered by both cases.
Equations (20),(23) establish all of \(\mathcal M\).

## 4. Exact scope and certificate count

This proof replaces all 16 former rectangle charge checks:
14 corner checks and two middle checks. It also removes all three
corner empty leaves. The actual order \(b\le a\) is used directly,
so invalid portions of the rectangular parameter domains need not
be subdivided and discarded.

The auxiliary file
NINE_RADIUS_TWO_MEASURE_RECTANGLES_RATIONAL_IDENTITIES.py merely
reconstructs the displayed rational identities using Fraction.
It evaluates no inverse trigonometric function and generates no boxes.
It is not an additional measure certificate. All 14 signed Taylor
reserves and all six whole-region mass reserves are displayed above.

After review and integration with the line and outer sources, the
global measure theorem would need only five fixed mass checks:
two from NINE_RADIUS_TWO_MEASURE_LINE_ANALYTIC_REDUCTION.md and
three from NINE_RADIUS_TWO_MEASURE_OUTER_CURVE_ANALYTIC_REDUCTION.md.
The latter's one fixed derivative enclosure is also retained.
There would be no empty-domain tests or adaptive parameter partition.
Relative to the accepted 208-charge version, this removes 203 charge
obligations. The global theorem would still have a finite fixed
certificate, not zero computational checks.

All original nine squares, arbitrary orientations and every physical
contact, circle-mask and individual-weight possibility remain within
the global theorem. No force graph or equilibrium hypothesis enters
this replacement. No Lean compilation or CI was run.

