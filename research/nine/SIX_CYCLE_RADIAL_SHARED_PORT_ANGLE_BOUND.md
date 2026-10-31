# A uniform actual angle bound at a strict shared radial port

Date: October 26, 2026.

**Status: accepted complete analytic local lemma**, after
REVIEW_C6_RADIAL_LOW_SINGLE_MEAN_AND_SHARED_ANGLE_2026_10_26.md and
REVIEW_C6_RADIAL_LOW_REMAINING_ROOT_2026_10_26.md.

Retain an actual reserve-one side channel from the physical radial
loaded square S to a physical unique loaded square T. Suppose T owns
this S-incident interface and its actual turn is strictly greater
than \(\pi/2\). Keep the original genuine mean, including every
endpoint compatible with this strict-turn chart. Work throughout
\[
              2\le R\le\sqrt{1105}/16,
 \qquad d=\sqrt{R^2-1/4}-1.
\]
In the actual radial-port chart let beta be the original angle of
the channel from S, so
\[
 P=(d,1/2),\qquad G=(-\cos\beta,\sin\beta),
                  0<\beta<\pi/2.
\]
A complete reflection of the chart gives the other original port.

**Lemma.** Every such actual strict shared port satisfies
\[
                              \boxed{\beta>99/200.}
\tag{1}
\]

The unchanged local type-M chart from Sections 1--2 of
`SIX_CYCLE_ONE_RADIAL_TWO_SHARED_MEANS_STRICT_TURN_CLASSIFICATION.md`
has actual own circle coordinates a,b with
\[
 a>b>1/2,\qquad a^2+b^2=R^2,
 \qquad P=(a-2)G+\tau b\,u,
\]
where u is the actual perpendicular own axis and \(0<\tau\le1\)
is the original proper radial concurrence factor. In particular
\[
              a=2-d\cos\beta+\tfrac12\sin\beta>R/\sqrt2.
\tag{2}
\]
This uses only the one strict shared endpoint; no hypothesis about
the other unique endpoint is imported.

Put \(d_*=18729/20000\). The lower radius bound gives
\[
 d\ge\sqrt{15}/2-1>d_*,
 \qquad
 15/4-(1+d_*)^2=64559/400000000>0.
\tag{3}
\]
Suppose \(\beta\le u:=99/200\). The expression
\(2-d\cos\beta+\tfrac12\sin\beta\) decreases in d and
increases in beta on this whole interval. Signed Taylor estimates
at the fixed rational u therefore give
\[
 \begin{split}
 a
 &<2-d_*\left(1-u^2/2+u^4/24-u^6/720\right)
            +\tfrac12\left(u-u^3/6+u^5/120\right)\\
 &=\frac{144739320907905703481}{102400000000000000000}
   <\frac{7071}{5000}<\sqrt2\le R/\sqrt2.
 \end{split}
\tag{4}
\]
The first final reserve is exactly
\[
 \frac{7071}{5000}
 -\frac{144739320907905703481}{102400000000000000000}
 =\frac{74759092094296519}{102400000000000000000}>0.
\]
The positive-square reserve for the second comparison is
\(2-(7071/5000)^2=959/25000000>0\). The sine and cosine
alternating remainders have the indicated signs because
\(0<u<1/2\). Equation (4) contradicts (2), proving (1).

For uses needing only the weaker bound \(\beta>23/50\), there
is an even coarser elementary comparison. If \(\beta\le23/50\),
then \(d>187/200\), \(\sin\beta\le\beta\) and
\(\cos\beta\ge1-\beta^2/2\) give
\[
 a<2-\frac{187}{200}\left(1-\frac{(23/50)^2}{2}\right)
            +\frac{23}{100}
   =\frac{1393923}{1000000}<\frac75<\sqrt2,
\]
with rational reserve \(6077/1000000\) before \(7/5\).
This separately proves the weaker consequence without the finer
fixed Taylor comparison.

All actual mean values and physical endpoint labels remain. The
lemma is a local consequence of the high radius and strict shared
turn; it does not apply to a low-turn shared endpoint merely by
calling it type M. No computational certificate, parameter grid,
Lean compilation or CI is used.
