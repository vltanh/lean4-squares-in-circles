# Independent review of the one-owner opposite return and the opposite/mean radial families

Date: October 26, 2026.

**Verdict: PASS for both complete stated physical families and the
shared-return local height lemma.**

Reviewed sources:

* SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md;
* SIX_CYCLE_ONE_RADIAL_OPPOSITE_AND_SHARED_MEAN_EXCLUSION.md.

This review independently reconstructed the displayed local equations,
all sign and interpolation arguments, each fixed rational reserve, and
both original physical joins. The inherited O, A and M charts were
checked against their accepted sources, including their proofs fixing
the circle-corner branch before taking a square root. No numerical
sample, root finder, angle partition, Lean compilation or CI was used.

## 1. Original physical scope

Both sources retain the same original alternating all-side C6, one
physically radial loaded square S, two physically unique loaded
squares B,C, three actual degree-two side transmitters, all original
forces, both original nonnegative radial corner weights, every actual
mean and endpoint, all sliders, and all three other physical squares.
The radius is the full original interval
\(79/40\le R\le\sqrt{1105}/16\), with
\(d=\sqrt{R^2-1/4}-1\).

The results require the two unique turns to exceed \(\pi/2\).
The radial right-turn endpoint has already been classified; its
S-incident unique ports are adjacent vertices, so it cannot satisfy
an actual opposite-port premise. No right-turn or weak-corner
endpoint is discarded from a family to which it belongs.

The single-owner source excludes both S-incident opposite vertices
with exactly one genuine return owner. Together with the separately
accepted zero-owner and two-owner sources, this exhausts the full
two-opposite strict-turn family. The opposite/mean source excludes
one nonshared-return opposite endpoint paired with an arbitrary
genuine S-incident mean. Neither source asserts an unrestricted
one-radial exclusion or closes any lower-unique-turn family.

## 2. Shared-return chart and strict signs

At the left actual return owner, use the original circle corner
\(z=(-a,b)\), mean \(T=(1-a,H)\), and opposite vertex
\(Q=(1-a,b-1)\). The genuine interval is the actual side interval;
the coincident-port lower endpoint is already excluded, and the
upper mean endpoint \(H=b\) is retained.

The unchanged concurrence is \((1-t)z\), where
\(t=1-H/b\in[0,1)\). In the inward own axes the vector from Q
to that concurrence is
\((1-ta,1-tb)=(X,Y)\). Its strict positive components follow
from the original S-incident strict opposite-vertex feature.
The common negative moment gives \(a>b\), hence \(X\le Y\)
(with equality allowed at \(t=0\)), and therefore the normalized
direction obeys \(0<x\le1/\sqrt2\), \(y\ge1/\sqrt2\).

The actual reserve-one channel gives the unchanged radial port
\(P=(a-1-x,b-1-y)\) in the same orthonormal own axes, with
\(|P|^2=d^2+1/4\). This uses the physical inner radial vertex,
not an assumed location for the radial concurrence. Its norm is
valid regardless of the individual radial corner weights.

## 3. Independent audit of the complete high-height contradiction

Assume \(H\ge4/5\). Then \(4/5\le b<3/2\), and the three
radius-derived upper bounds for a are correct. Fresh exact
subtraction gives the stated squared reserves
\[
                 187/6400,\qquad103/2304,\qquad87/6400.
\]

I independently derived
\[
 b(X-\gamma Y)
 =\gamma b^2+(1-9\gamma/5)b-a(b-4/5)
\]
at \(H=4/5\). Its coefficient of H before substitution is
\(a-\gamma b>0\). Replacing a by an upper bound in the
last negative term has the correct sign because \(b\ge4/5\).
The resulting quadratics are exactly
\[
 \frac34b^2-\frac{91}{40}b+\frac{77}{50},\qquad
 \frac35b^2-\frac{287}{150}b+\frac{22}{15},\qquad
 \frac35b^2-\frac{89}{50}b+\frac{34}{25}.
\]
The first two decrease on their full declared intervals, with
respective endpoint values \(3/200\) and \(13/375\).
The last has global completed-square minimum \(239/6000\).
This verifies the complete normal-ratio bounds, without an
unproved interpolation between sample signs.

For \(4/5\le b\le1\), the physical radius gives \(a>17/10\),
with squared reserve \(17/1600\). Combining the normal bounds
gives \(|a-1-x|<13/40\), including the possibly negative lower
side. On \(b\le17/20\), the exact estimate
\(t\le1/17\) gives \(X>603/680\), \(Y\le1\); the reserve
\[
                    (603/680)^2-7/9=35681/4161600
\]
implies \(y<3/4\). On the complementary interval the direct
\(y<4/5\) bound suffices. Thus both intervals give
\(|b-1-y|<19/20\), and
\[
 |P|^2<1613/1600<53/50,
 \qquad53/50-1613/1600=83/1600.
\]

For \(b\ge1\), the bound \(a>139/100\) has squared reserve
\(1457/40000\). The source's lower own-coordinate bound is
\(-227/700>-1/3\), with positive difference \(19/2100\).
The upper bound uses \(a<11/6\) and \(x>1/2\), so
\(|a-1-x|<1/3\). Since \(b<3/2\), \(y>1/2\), and
\(y<\sqrt3/2\), its other coordinate lies in
\((-\sqrt3/2,0)\). This gives \(|P|^2<31/36<53/50\).

Both complete ranges contradict the unchanged radial norm,
because \(d>9/10\) implies \(d^2+1/4>53/50\).
Therefore the local theorem \(H<4/5\) holds on the entire
original genuine-return-owner domain, including \(H=b\).

## 4. The nonshared opposite endpoint supplies the opposite height obstruction

The accepted O chart is applicable locally at the other endpoint:
\(Z=H+s\), \(A=\sqrt{R^2-Z^2}>0\),
\(0<s<c\), and the unchanged incoming normal is parallel to
\((sA/Z+s-c,c)\). Its strict turn gives
\((c-s)Z>sA\), with positive sides. Squaring yields
\[
 H>s\left(\frac{R}{\sqrt{(c-s)^2+s^2}}-1\right).
\]

I checked both complete ranges proving that \(H\le4/5\)
forces \(s<2/5\). On \([2/5,1/2]\), the derivative of
\(w=1+s^2-2s\sqrt{1-s^2}\) is negative. Its parenthesis
\(s-c+s^2/c\) has positive derivative and remains negative
at its upper endpoint. The comparison \(w(2/5)<3/7\) is exactly
\(32<7\sqrt{21}\), with squared reserve 5. Also
\(K_0^2-27/7=487/11200\), so this range forces \(H>2s\).
On \([1/2,1/\sqrt2]\), the identity
\[
 4s^2(1-s^2)-(s^2+1/2)^2
       =5(1/2-s^2)(s^2-1/10)
\]
proves \(w\le1/2\). The displayed lower height
\(353/400>4/5\) follows with the correct strictness.

For \(s<2/5\) and \(H\le4/5\), the function
\[
 \sqrt{R^2-(4/5+s)^2}-\sqrt{1-s^2}
\]
decreases. Squaring its two positive derivative terms is equivalent
to \(4/5>s(R-1)\), valid on the entire stated radius and angle
range. Its lower endpoint comparison at \(s=2/5\), combined
with the exact radical reserves \(123/6400\), \(1457/40000\),
and \(4/625\), gives
\[
                          A-c+R/\sqrt2>2+13/400.
\]
The actual channel reserve, with the reflected other endpoint, is
\(A+a_T=2+c\). The shared endpoint's strict \(a_T>b_T\)
gives \(a_T>R/\sqrt2\), so this equality contradicts the last
bound. This verifies the full one-owner O/T exclusion using the
original applications, not a relaxed horizontal center equation.

## 5. Independent audit of the O/M common-reference proof

The M chart at the opposite endpoint has its original return port
opposite its circle corner. The accepted pointwise mean-root
arguments yield \(H<4/5\), \(\eta_M<\pi/3\), and the full
scalar interval from \(\pi/4\) to its original root. Those
arguments precede and do not require an adjacent endpoint in the
source where they were first proved.

On that whole interval, the two complementary derivative theorems
cover all \(0<b/a<1\), retaining the actual variable mean. Thus
\(F_M\) decreases from its common reference value
\[
 F_{M,0}=R^2+4-2\sqrt2 h_0,\qquad
 h_0=\sqrt{R^2-H^2}+H.
\]
The unchanged radial root gives
\[
                         h_0\le(5+2d)/(2\sqrt2).
\]
Equality, including the original genuine mean at its endpoint,
is explicitly retained.

For the O chart, its local norm-root lemma gives \(A>c\) at
the actual endpoint. The extension down to \(\eta=0\) is valid:
\(b>0\) is equivalent to \(H>s(R-1)\) and persists downward;
then \((A-c)'=-b/A<0\) keeps \(A>c\). At the reference,
\(A_0>9/5\), with squared reserve \(33/1600\), so
\(a-b=A_0-H>1\). Its derivative is positive, and hence
\(a-b>0\) throughout. The identities for X,Y ensure they and
\(|V|\) stay strictly positive at zero and on the entire interval.

The inherited exact O derivative has all positive factors there.
In particular \(2-t(a+b)=X+Y>0\), which proves positivity of
its bracket without invoking an actual root at the reference.
Therefore \(F_O\) strictly increases from zero to the original
angle \(\eta_O>0\).

I independently expanded its reference norm:
\[
 F_{O,0}=R^2+3+2\sqrt2-(2+\sqrt2)h_0.
\]
The actual root consequently gives
\(h_0>2+(2-\sqrt2)d\). Finally the exact difference between
this strict lower threshold and the M upper threshold is
\[
 2+2d-\sqrt2(5/4+3d/2)
   >3/14-d/7>29/420>0.
\]
Both radical substitutions have known positive coefficients and
the final bound uses the full original \(d<61/60\). The
thresholds are incompatible, proving the complete O/M family
exclusion with every original M mean retained.

## 6. Accepted consequence and explicit limits

The local shared-return height theorem, the two-opposite one-owner
core exclusion, and the nonshared-opposite/genuine-mean core
exclusion all pass. Their reflected and cyclic copies follow by
carrying the actual packing and certificate through those symmetries.

This review adds no sign packet and does not certify any unproved
mixed opposite/adjacent, return-owned opposite/adjacent-or-mean,
or lower-unique-turn family. It makes no completion inference for
the separate surviving all-unique one-share core.
