# An opposite radial-incident vertex cannot pair with a genuine radial-incident shared mean

Date: October 26, 2026.

**Status: complete analytic physical-family join, accepted after root and
separate independent saved-source and scope reviews.** See
REVIEW_C6_RADIAL_SINGLE_RETURN_AND_OPPOSITE_MEAN_ROOT_2026_10_26.md
and REVIEW_C6_RADIAL_SINGLE_RETURN_AND_OPPOSITE_MEAN_2026_10_26.md.
This proof compares two whole-interval
norm inequalities at the same original return height. It introduces no
new computational certificate.

Retain the original all-side alternating C6 with one physically
two-circle-corner loaded square S, two physically unique loads B,C,
three true unloaded degree-two transmitters, and all three extra
squares. Work throughout
\[
 K_0=79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1.
\tag{1}
\]
Both unique turns are strictly greater than \(\pi/2\). Every original
force, radial corner weight, contact mean and transmitter slider is kept.

Assume one S-incident unique application is its actual opposite
circle-corner vertex, with its B-to-C return interface nonshared.
Assume the other S-incident interface is genuinely shared, with its
full original mean, including any endpoint.

**Theorem.** This entire original physical core is impossible.

The radial right-turn endpoint is already classified and excluded;
its two S-incident unique applications are adjacent vertices, so it
does not satisfy the opposite-vertex hypothesis. Thus all three
actual turns are strict in the only branch requiring proof.

## 1. Two local charts at the same original height

Normalize the actual B-to-C return horizontally at height \(H>0\).
Its two endpoints have the following actual local types:

* At the genuine S-incident mean endpoint M, the return application
  is the opposite vertex.
* At the opposite S-incident endpoint O, its nonshared return
  application is the adjacent-to-circle vertex.

These are exactly the local strict-turn owner alternatives. They
do not change an original shared mean to an endpoint.

For M use the local chart and norm function from Sections 1--3 of
[SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md):
\[
 c=\cos\eta,\ s=\sin\eta,\quad \pi/4\le\eta<\pi/2,
\]
\[
 Z=H+s-c,\quad A=\sqrt{R^2-Z^2},\quad
 a=cA+sZ,\quad b=sA-cZ,\quad t=(s-c)/Z,
\]
\[
              F_M=(a-2)^2+(1-t)^2b^2=d^2+1/4.
\tag{2}
\]
The actual mean is \(\ell=1-tb\in(0,1]\).
The cited chart and its pointwise norm-root estimates use only
this endpoint's physical feature and original radial port norm;
they do not require the other endpoint to be a second mean.

For O use Section 1 of
[SIX_CYCLE_ONE_RADIAL_TWO_OPPOSITE_PORTS_SINGLETON_CHANNEL_EXCLUSION.md](SIX_CYCLE_ONE_RADIAL_TWO_OPPOSITE_PORTS_SINGLETON_CHANNEL_EXCLUSION.md):
\[
 c=\cos\eta,\ s=\sin\eta,\quad0<\eta<\pi/4,\quad
 Z=H+s,\quad A=\sqrt{R^2-Z^2},
\]
\[
 a=cA+sZ,\quad b=cZ-sA,\quad t=s/Z,\quad
 v=(-c,s),\quad u=(s,c),
\]
\[
 Q=z-v-u,\quad V=v+u-tz,\quad
 F_O=|Q-V/|V||^2=d^2+1/4.
\tag{3}
\]
Here \(z=(-A,Z)=av+bu\), and \(a>b>1/2\).
The negative horizontal circle branch and every strict sign are
derived before the square root is chosen in that local chart.
No assumption about the other endpoint's feature enters that argument.

Put
\[
                  r_0^2=d^2+1/4=R^2-2d-1.
\tag{4}
\]
Both norm equations (2)--(3) use exactly this original radial value.

## 2. The genuine mean gives an upper reference threshold

The pointwise M-root argument gives
\[
 a_M<211/120,\qquad b_M>89/100,\qquad
                 \eta_M<\pi/3,\qquad 0<H<4/5.
\tag{5}
\]
The last three facts, including every exact reserve, are proved in
Sections 2--4 of
[SIX_CYCLE_ONE_RADIAL_ADJACENT_AND_MEAN_CLASSIFICATION.md](SIX_CYCLE_ONE_RADIAL_ADJACENT_AND_MEAN_CLASSIFICATION.md).
Those sections use only the single M root, its own actual chart,
and the radius window, before applying any adjacent-port result.

For clarity, the same scalar interval \([\pi/4,\eta_M]\) is valid
here: \(Z<R\) and properness persist; the endpoint minimum of b
and endpoint maximum of a give
\[
       4/3<a<2,\quad b>0,\quad 0<b/a<1,\quad4/7<c/s\le1.
\]
The two complementary analytic derivative sources therefore give
\(F_M'<0\) on that entire interval, retaining
\(\ell=1-tb\) rather than freezing the mean.

Define the common reference quantities
\[
                  A_0=\sqrt{R^2-H^2},\qquad h_0=A_0+H.
\tag{6}
\]
At the reference angle \(\eta=\pi/4\), the mean chart has
\(t=0\), \(a=h_0/\sqrt2\). Thus
\[
 F_{M,0}=R^2+4-2\sqrt2\,h_0.
\]
The whole-interval decrease and the actual root (2) imply
\(r_0^2\le F_{M,0}\). Equivalently,
\[
                         h_0\le\frac{5+2d}{2\sqrt2}.
\tag{7}
\]
This includes equality at an original mean endpoint.

## 3. The opposite port gives a strictly larger lower threshold

The local norm-root lemma in Section 2 of the opposite-port source
gives \(A>c\) at the actual O endpoint. That lemma uses only
(3), its strict unique turn, the physical circle coordinates and
the norm (4), so it applies to the present mixed pairing.

We extend its increasing scalar norm from the actual O angle down
to the reference \(\eta=0\), always at the same R,H. This interval
is a comparison interval, not an interpolated packing.

At the reference, \(A=A_0,\ a=A_0,\ b=H\). Equation (5) and
the lower radius bound give \(A_0>9/5\), so
\(a-b=A_0-H>1>0\). On the entire interval,
\[
 b>0\quad\Longleftrightarrow\quad H>s(R-1)
\]
persists from the actual upper endpoint. Hence
\[
 (A-c)'=-b/A<0
\]
and the actual inequality \(A>c\) persists down to zero.
The identities
\[
 a'=b(1-c/A)>0,\qquad b'=-a(1-c/A)<0
\]
show that \(a-b\) remains positive from its reference value.
The original denominator identities
\[
 X=cb/Z>0,\qquad Y=1-sb/Z>0,\qquad |V|>0
\]
continue to hold at zero and throughout the interval.

All factors of the exact derivative
\[
 F_O'=\frac{2(a-b)}{|V|^3}
 \left[(1-c/A)\mathcal C+
                   \frac{Hc}{Z^2}(1-t)(a-b)\right],
\]
\[
 \mathcal C=|V|^3+t|V|^2+(1-t)\{2-t(a+b)\}>0
\]
are consequently positive on the full comparison interval. This
is the derivative identity of Section 3 of the opposite-port source;
no actual norm-root premise is required at the reference endpoint.

At \(\eta=0\), \(t=0\), and the inward normal is
\((v+u)/\sqrt2\). Therefore
\[
 F_{O,0}=R^2+3+2\sqrt2-(2+\sqrt2)h_0.
\tag{8}
\]
The actual nonshared O endpoint has \(\eta_O>0\). Strict increase
gives \(r_0^2>F_{O,0}\). Equivalently,
\[
                         h_0>2+(2-\sqrt2)d.
\tag{9}
\]
The reference has an axis normal only as an auxiliary comparison
point; it is not used to relabel the actual nonshared return.

## 4. One uniform gap excludes every original mean

The two reference thresholds in (7) and (9) are incompatible
throughout the entire radius window. Indeed
\[
\begin{split}
 &2+(2-\sqrt2)d-\frac{5+2d}{2\sqrt2}\\
 &\qquad=2+2d-\sqrt2\left(\frac54+\frac32d\right)\\
 &\qquad> \frac3{14}-\frac d7
 >\frac{29}{420}>0.
\end{split}
\tag{10}
\]
Here \(\sqrt2<10/7\), \(d>0\), and \(d<61/60\); the last
bound is the original upper-radius square comparison.
Thus no common actual H can satisfy both endpoint norms.

The entire opposite/nonshared-return plus genuine-S-mean feature
family is excluded. Every original M mean, including its genuine
adjacent endpoint, was retained in (2) and (7). The two actual
S corner weights were never restricted.

## 5. Remaining physical scope

Within the all-strict-turn one-radial owner cover, this source removes
the nonshared-return opposite/mean pairing. It does not claim the
mixed opposite/adjacent pairing, a return-owned opposite endpoint
paired with an adjacent or a genuine-mean endpoint, or a unique
turn at most \(\pi/2\). Those remain separate original features.

No unrestricted one-radial gate or global nine-square theorem is
declared closed here. The contradiction uses actual core norms and
all original contact data, while retaining the three extra squares.

