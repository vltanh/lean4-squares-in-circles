# Every neighbor center has positive projection on both radial-S circle corners

**Status: complete geometric hand implication; root and separate independent full hand audits passed.**
Throughout

\[
                       \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
\tag{1}
\]

let S be a contained unit square with two physical circle corners,
and let A be any other unit square physically touching S. Then

\[
                     \boxed{c_A\cdot z>0}
\tag{2}
\]

for each of the two physical circle corners z of S. The conclusion
uses no circle load, force balance, contact owner or orientation
assumption on A. It includes a shared-side endpoint or mean.

## 1. A uniform geometric lower bound

A unit square with two containing-circle corners has the radial S
form. In an orthonormal frame e,k, write

\[
 T=\sqrt{R^2-\tfrac14},\qquad
 S=[T-1,T]e+[-\tfrac12,\tfrac12]k,
      \qquad z_\pm=Te\pm\tfrac12 k.
\tag{3}
\]

This is the usual two-corner classification; an opposite pair of
circle corners would force its center to zero and radius squared
1/2, outside (1). Thus the two corners are adjacent and their
midpoint is radial.

Choose any actual contact point p in A intersection S. The square
A has circumradius 1/sqrt(2), so Cauchy's inequality and (3) give

\[
\begin{split}
 c_A\cdot z_\pm
   &\ge p\cdot z_\pm-\frac{R}{\sqrt2}\\
   &\ge T(T-1)-\frac14-\frac{R}{\sqrt2}\\
   &=R^2-\sqrt{R^2-\tfrac14}-\frac12-\frac{R}{\sqrt2}
      =:f(R).
\end{split}
\tag{4}
\]

For R>=79/40, T>R/2. Therefore

\[
 f'(R)=2R-\frac{R}{T}-\frac1{\sqrt2}
       >2R-2-\frac1{\sqrt2}>0.
\tag{5}
\]

At R_0=79/40 the exact comparisons

\[
 \sqrt{R_0^2-\tfrac14}<\frac{77}{40},
       \qquad\frac{R_0}{\sqrt2}<\frac75
\tag{6}
\]

follow on squaring from 5841<5929 and 6241<6272. Consequently

\[
 f(R)\ge f(R_0)
   >\frac{6241}{1600}-\frac{77}{40}-\frac12-\frac75
    =\frac{121}{1600}>0.
\tag{7}
\]

This proves (2), with a uniform strict margin. In fact the same
argument works for every R>=79/40; the stated upper endpoint only
matches the surrounding research domain.

## 2. Every positive radial-S load contributes positive pressure

If S carries nonnegative circle weights of positive total, then

\[
 F_S=2\lambda_+z_++2\lambda_-z_-,\qquad
 \lambda_+,\lambda_-\ge0,\quad\lambda_++\lambda_->0
\tag{8}
\]

satisfies c_A dot F_S>0. Either individual weight may be zero.
No assertion that F_S is radial is needed: unequal corner weights
are retained in (8).

In particular, consider an end triangle A--B--C--A whose two
loaded tips B,C both have two physical circle corners. With

\[
                              M=F_B+F_C,
\tag{9}
\]

equation (2) at each physical contact gives c_A dot M>0. This
holds for every articulation-contact owner, every free BC normal,
every actual shared-side mean and all four circle weights.

Thus the entire two-radial-tip mask has the pressure sign required
by the bowtie argument. When the two end-block pressure signs
are available for a bowtie, their opposite resultants cannot both
have positive scalar product with c_A.

The lemma does not claim a sign for a neighboring body's unique
circle corner, and it does not alone close a one-radial/one-unique
end triangle. No numerical sample, Lean compilation or CI is used.


## 3. Whole-component consequence when every load neighbors one clear body

Suppose a positive physical component has an unloaded body A such that
all its positively circle-loaded bodies touch A and have two physical
circle corners. Summing all body force equations cancels the internal
pair forces and gives
\[
                          \sum_S F_S=0.
\tag{10}
\]
Every summand has c_A dot F_S>0 by Section2. There is positive total
circle load. Taking the scalar product of (10) with c_A is therefore a
contradiction. Additional zero-stress physical contacts and all
nonnegative individual corner weights are retained.

This applies to two complete masks in the five-body biconnected cover:

- In the surviving four-load fan, the clear universal hub touches all
  four loaded path bodies. They cannot all have two physical circle
  corners. At least one path body has a unique physical circle corner.
- For the house labels of FIVE_BODY_BICONNECTED_REDUCTION.md, an end
  triple of loads {1,2,3} has the clear hub5 touching all three; the
  reflected triple {3,4,5} has hub1. The entire all-radial mask in either
  end-triple branch is excluded.

These are complete physical-mask consequences. They do not give a sign
for any unique-circle-corner neighbor or close either whole parent
family.
