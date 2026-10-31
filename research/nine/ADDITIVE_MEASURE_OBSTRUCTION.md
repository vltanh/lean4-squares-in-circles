# A point-measure certificate cannot establish the nine-square bound

**Status: complete obstruction to one proposed proof method.** This is
not a physical nine-square packing and does not close a packing cell.
It proves that a nonnegative additive measure, charged independently to
each square, cannot give the desired capacity bound, even in the smaller
disk of squared radius `17/4`. Pairwise geometry must enter elsewhere.
No Lean compilation or CI has been run.

## 1. Exact statement

Let

\[
 D_0=\{x\in\mathbb R^2:|x|^2\le17/4\}.
\]

Suppose a finite nonnegative Borel measure \(\mu\) on \(D_0\) satisfies

\[
 \mu(\operatorname{int}T)\ge1
 \quad\text{for every closed unit square }T\subset D_0.
 \tag{1}
\]

Then

\[
                 \boxed{\mu(D_0)\ge\frac{181}{20}>9.}
 \tag{2}
\]

In particular, one cannot prove that nine interior-disjoint squares do
not fit by finding such a measure of total mass less than nine. This
obstruction applies to arbitrary nonnegative measures, not only radial
densities or measures on finitely many concentric circles. It also
applies to a measure intended for a larger disk: restrict that measure
to \(D_0\) and use the squares below.

## 2. Three square families

Put

\[
 a=\sqrt{17/8},\qquad b=a-1,
\]

and consider the three unit squares

\[
 A=[0,1]\times[-1/2,1/2],\qquad
 S=[1,2]\times[-1/2,1/2],\qquad
 B=[b,a]\times[b,a].
 \tag{3}
\]

All lie in \(D_0\). The farthest corner squared norms of \(A,S,B\)
are respectively \(5/4,17/4,2a^2=17/4\).

For a fixed point of radius \(r\), let \(f_T(r)\) be the fraction of
rotations through \([0,2\pi)\) for which that point belongs to the
open interior of the rotated square \(T\). At \(r=0\), all three
fractions vanish. At positive radii, the finitely many possible
boundary angles have zero angular measure and do not affect these
fractions.

We prove the pointwise inequality

\[
 2f_A(r)+2f_S(r)+\frac{101}{20}f_B(r)\le1
 \quad(r\ge0).
 \tag{4}
\]

This gives a fractional packing of total mass
\(2+2+101/20=181/20\). It does not assert that the differently rotated
squares in those families are simultaneously disjoint.

## 3. Angular occupancy of the rectangle and diagonal square

The union of \(A\) and \(S\) is the rectangle
\([0,2]\times[-1/2,1/2]\); their shared side contributes zero angular
measure. Thus

\[
 2(f_A(r)+f_S(r))\le
 \begin{cases}
 1,&0<r\le1/2,\\[2mm]
 \dfrac2\pi\arcsin\dfrac1{2r},&r>1/2.
 \end{cases}
 \tag{5}
\]

The second bound follows by dropping the outer constraint \(x\le2\).
It is an equality until that outer constraint clips the circle.

Let

\[
 r_0=\sqrt2\,b,\qquad r_1=\sqrt{a^2+b^2}.
\]

The square \(B\) is in the first quadrant. Its exact angular fractions
are

\[
 f_B(r)=
 \begin{cases}
 0,&0\le r\le r_0,\\[1mm]
 \dfrac14-\dfrac1\pi\arcsin\dfrac br,
       &r_0\le r\le r_1,\\[2mm]
 \dfrac1\pi\arcsin\dfrac ar-\dfrac14,
       &r_1\le r\le\sqrt2 a,\\[2mm]
 0,&r\ge\sqrt2 a.
 \end{cases}
 \tag{6}
\]

For the second line, the two inner inequalities \(x,y\ge b\) suffice:
if \(r^2\le a^2+b^2\), either inner inequality implies the opposite
outer inequality. For the third line the reverse reasoning makes the
inner inequalities redundant. Their intersection angles give (6).

The elementary bounds

\[
 \frac{29}{20}<a<\frac32,\qquad
 \frac9{20}<b<\frac12
 \tag{7}
\]

follow by squaring the positive endpoints. In particular, \(r_0>1/2\).
For \(r\le r_0\), (4) follows immediately from (5)--(6).

## 4. The only maximum to check

Write \(w=101/20\). For \(r_0\le r\le r_1\), multiply the upper
bound in (4), obtained from (5)--(6), by \(\pi\). The result is

\[
 F(r)=2\arcsin\frac1{2r}
          +w\left(\frac\pi4-\arcsin\frac br\right).
 \tag{8}
\]

This function is strictly increasing. Indeed,

\[
 F'(r)=\frac1r\left(
   \frac{wb}{\sqrt{r^2-b^2}}
       -\frac1{\sqrt{r^2-1/4}}\right)>0.
 \tag{9}
\]

To check the sign without decimal estimates, square the two positive
terms. Since \(w^2b^2>1\) and \(r^2\ge2b^2\), their squared
comparison has difference

\[
 \begin{aligned}
 w^2b^2(r^2-1/4)-(r^2-b^2)
 &\ge b^2\bigl(w^2(2b^2-1/4)-1\bigr)\\
 &>b^2\left(25\cdot\frac{31}{200}-1\right)>0,
 \end{aligned}
\]

using (7). For \(r\ge r_1\), both the bound in (5) and the third
line of (6) decrease. Hence it suffices to prove \(F(r_1)<\pi\).

Set

\[
 \alpha=\arcsin\frac1{2r_1},\qquad
 \beta=\arcsin\frac b{r_1}=\arctan\frac ba.
\]

We have the convenient exact comparisons

\[
                  \alpha<\frac{17}{50},\qquad
                  \beta>\frac3{10}.
 \tag{10}
\]

For the first, observe that

\[
 r_1^2=\frac{21}{4}-\sqrt{17/2}>\frac94,
\]

so \(1/(2r_1)<1/3\). The alternating sine estimate gives

\[
 \sin(17/50)\ge\frac{17}{50}
             -\frac16\left(\frac{17}{50}\right)^3
             >\frac13.
\]

For the second, (7) gives \(b/a=1-1/a>9/29\). The same elementary
Taylor bounds give

\[
 \sin(3/10)
 \le\frac3{10}-\frac16\left(\frac3{10}\right)^3
                +\frac1{120}\left(\frac3{10}\right)^5
 <\frac{37}{125},
\]
\[
 \cos(3/10)\ge1-\frac12\left(\frac3{10}\right)^2
             =\frac{191}{200}.
\]

Consequently

\[
 \tan(3/10)<\frac{296}{955}<\frac9{29}<\frac ba,
\]

which proves the second inequality in (10).

Finally, using the elementary bound \(\pi<22/7\),

\[
 \begin{aligned}
 F(r_1)
 &=2\alpha+w(\pi/4-\beta)\\
 &<\frac{101\pi}{80}-\frac{167}{200}\\
 &<\pi,
 \end{aligned}
\]

because

\[
 \frac{21\pi}{80}<\frac{21}{80}\frac{22}{7}
                   =\frac{165}{200}<\frac{167}{200}.
\]

Together with the monotonicity and the small-radius case, this proves
(4) for every point, including all boundary radii.

## 5. Integrating the certificate obstruction

Average (1) over all rotations of each square in (3). Tonelli's theorem
applies to the nonnegative indicator functions. Thus

\[
 \int_{D_0} f_A(|x|)\,d\mu(x)\ge1,
 \quad
 \int_{D_0} f_S(|x|)\,d\mu(x)\ge1,
 \quad
 \int_{D_0} f_B(|x|)\,d\mu(x)\ge1.
\]

Multiplying by \(2,2,101/20\), summing, and using (4), gives

\[
 \frac{181}{20}
 \le\int_{D_0}
       \left(2f_A+2f_S+\frac{101}{20}f_B\right)(|x|)\,d\mu(x)
 \le\mu(D_0).
\]

This proves (2). The argument is valid even if \(\mu\) has atoms or
is supported on curves; no area density or rotational invariance of
\(\mu\) was assumed.

**Scope.** Joint constraints on several squares, signed arguments with
separately justified cancellation, and configuration-dependent
certificates are not ruled out. The impossibility concerns a single
nonnegative additive measure satisfying (1) independently for every
contained unit square. The unrestricted nine-square theorem remains
open in this branch.
