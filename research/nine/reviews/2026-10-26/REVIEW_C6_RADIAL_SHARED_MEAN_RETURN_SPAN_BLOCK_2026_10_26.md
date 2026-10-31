# Independent review: the full radial-incident shared-mean span and its return-owner exclusion

Date: October 26, 2026.

Reviewer: block-attachments agent, independently of the source author.

**Result: PASS for the complete stated local theorem and its physical
family join.** This review does not close the mixed opposite/adjacent
families, any lower-turn owner alternative, or an unrestricted original
one-radial C6 gate.

Reviewed source:

- SIX_CYCLE_ONE_RADIAL_SHARED_MEAN_RETURN_SPAN_EXCLUSION.md.

The physical chart was checked against the accepted
SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md,
Sections 1--2, and the partner's original own-axis chart against
SIX_CYCLE_ONE_RADIAL_SINGLE_SHARED_OPPOSITE_RETURN_EXCLUSION.md,
Section 1. The latter is used only for its displayed local chart
and common-moment sign, independently rederived below.

## 1. The whole original mean domain is retained

At the genuinely shared S-incident interface, the accepted local
strict-turn cover makes the return port the opposite circle-corner
vertex, with no loaded-axis ownership there. With the actual return
horizontal at positive height H, its left endpoint is

\[
 T=(-A+c+s,H),\quad z=(-A,Z),\quad Z=H+s-c,
\]
\[
 a=cA+sZ,\quad b=sA-cZ,\quad t=(s-c)/Z,\quad
                \ell=1-tb\in(0,1].
\]

The existing physical identities give a>b>1/2, a^2+b^2=R^2,
0<=t<1, and the true radial port norm

\[
                    (a-2)^2+(1-t)^2b^2=d^2+1/4.
\]

These facts are local to this one endpoint. They require no second
mean endpoint and no claim that the physical radial concurrence
lies inside its unit. The original endpoint ell=1 remains:
then t=0 and c=s, which is compatible with the improved bound below.

Expanding the norm with R^2=(d+1)^2+1/4 gives exactly
4a+(2t-t^2)b^2=5+2d. Thus the displayed upper bound
a<=A_*=(5+2d)/4 is valid on the full original interval.
The lower bound a>R/sqrt(2)>139/100 and a<211/120<2
justify every subsequent positive denominator and square comparison.

## 2. Independent tangent and monotonicity calculation

The inverse coordinate identity is Z=as-bc. With u=c/s and r=b/a,

\[
 t=(1-u)/(a-ub),\qquad
 \frac{\partial t}{\partial u}=(b-a)/(a-ub)^2<0.
\]

For u<=3/4, the source's upper comparison for (1-t)b therefore
has the correct direction. Its positive right side is guaranteed
by the positive actual left side and this comparison.

For f(r)=r/(1-3r/4), the independent values are
f(3/4)=12/7 and f'(3/4)=256/49. Convexity gives the global
tangent f(r)>=256r/49-108/49, not merely a comparison near
r=3/4. This gives exactly

\[
                 (1-t)b\le b(1-64/(49a))+27/49.
\]

The coefficient of b is positive since a>139/100>64/49.
After b<=sqrt(U-a^2), U=1105/256, direct differentiation gives

\[
 \frac{d}{da}\{\sqrt{U-a^2}(1-K/a)\}
       =\frac{KU-a^3}{a^2\sqrt{U-a^2}},
                         \qquad K=64/49.
\]

The source's fixed upper endpoint therefore bounds the entire a
interval. The resulting (1-t)b<21/25 and
|a-2|<61/100 contradict the actual radial norm by the strict
reserve 1/2500. Hence u>3/4, equivalently c>3/5 and s<4/5.

## 3. The span bound uses a valid full comparison interval

The actual horizontal span is

\[
 m=A-(c+s)=c(a-1)+s(b-1).
\]

At fixed R,c,s, its derivative in a is c-sa/b<0. Increasing
a to A_* preserves a>b, since b decreases; its endpoint radical
is positive because

\[
 b_*^2=R^2-A_*^2=(12d^2+12d-5)/16>(199/200)^2.
\]

Thus the full comparison interval is valid. The independent bounds
A_*>341/200, c>3/5, s<4/5 give m>419/1000. The
source correctly splits the sign of b_*-1 in using its lower
bound -1/200: if that contribution is nonnegative, it is already
stronger; if negative, the upper bound on s is the correct one.

## 4. The partner contradiction preserves the original force and mean data

At a genuine owner of the return normal, the strict-turn cover makes
the S-incident port an actual opposite vertex and its incoming normal
strict in both own coordinates. Normalize its inward own axes so
the circle corner coordinates are a_T,b_T>1/2. The common moment
has the sign of a_T-b_T, independently giving a_T>b_T.
The actual return port's horizontal span is a_T-1, independently
of its transverse mean.

The original reserve-one return thus gives
m+(a_T-1)=1. In particular a_T<8/5, and
b_T^2>K_0^2-64/25=2145/1600>1. Both coordinates of
Q=(a_T-1,b_T-1) are positive.

For the unchanged strict positive unit normal G, a_T>b_T gives
Q dot G>b_T-1. The true S port is P=Q-G, with
|P|^2=R^2-2d-1. Expansion yields precisely
a_T+2b_T<3+d.

On a>R/sqrt(2), the derivative of
a+2sqrt(R^2-a^2) is 1-2a/sqrt(R^2-a^2)<0.
The comparison endpoint 8/5 is below R and above R/sqrt(2)
throughout the radius window. Therefore

\[
 a_T+2b_T>\frac85+2\sqrt{R^2-\frac{64}{25}}.
\]

The latter minus (3+d) increases with R because its derivative is
2R/sqrt(R^2-64/25)-R/sqrt(R^2-1/4)>0.
At R=79/40 its positivity is exactly the source's two successive
positive squarings, ending at integer reserve 184105. This is the
opposite strict inequality and completes the physical contradiction.

## 5. Fresh exact arithmetic reproduction

A new independent Fraction calculation reproduced the following
displayed reserves directly from their definitions:

| Comparison | Exact value |
| --- | ---: |
| Lower d squared reserve | 101/40000 |
| Upper d squared reserve | 31/57600 |
| KU-(211/120)^3 | 17057381/84672000 |
| (10/9)^2-[U-(211/120)^2] | 5131/518400 |
| Final upper comparison for (1-t)b | 7496/2326275 |
| Contradictory radial norm reserve | 1/2500 |
| Lower b_* squared reserve | 21/20000 |
| Span lower expression | 419/1000 |
| K_0^2-64/25 | 429/320 = 2145/1600 |
| 2483^2-32^2*5841 | 184105 |

All are positive; no numerical root, sampled sign or angular cell
is used in the proof. The local tangent and monotone bounds cover
the continuum.

The reviewed conclusion excludes the complete genuine-S-mean plus
genuine-return-owner family under the stated two strict unique-turn
premise. Both original radial weights, every mean endpoint, actual
transmitter degree and slider, and all three extra squares remain.
The contradiction is in the six-body core; it does not assert an
unproved completion capacity for any other family.
