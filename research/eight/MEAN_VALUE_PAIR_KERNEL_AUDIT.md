# Independent audit of the optional mean-value pair rejection

This audit concerns `m5_agent/pair_mean_value_beta0.hpp` and the two new
`*_mvt.cpp` wrappers. It does not certify any role domain until its complete
execution and input bindings have passed separately. Old certificates retain
their original sources and hashes.

## Mathematical rejection

On one declared closed affine piece, for an uncharged edge, the cost-failure
condition is

\[
  \delta\le d(x,y)=\gamma+\psi_a(x)-\psi_b(y).
\]

The exact signed SAT margin, multiplied by the positive factor
\(2\sqrt{(1+t^2)(1+u^2)}\), is bounded above by each of four smooth
width-sign majorants

\[
 F=2\sigma P_j-Z-s_c Q_c-s_s Q_s.
\]

The code first bounds \(-F_\delta\) from above on the whole gap interval
\([3/5,\max(d_{\rm upper},\mathtt{hi})]\). A nonpositive bound proves
monotonicity there. Thus, at any possible cost-failure state,

\[
 F(x,y,\delta)\le H(x,y):=F(x,y,d(x,y)).
\]

The automatic derivatives of `endpoint_sat` are exactly the two derivatives
of this composed function, including the chain terms from the affine endpoint.
For the midpoint \(m\) of the closed tangent rectangle \(B\), the enclosure

\[
 H(m)+H_x(B)(x-m_x)+H_y(B)(y-m_y)
\]

is a valid mean-value enclosure. The interval arithmetic evaluates the entire
endpoint range \(d(B)\), including values below \(3/5\); such values can lie on
the midpoint-to-point path even when the final feasible state has a gap above
\(3/5\). A strict negative bound for at least one width-sign majorant of every
checked signed axis is sufficient. The choice of width signs can differ
between axes. Failed tests fall back to the old subdivision.

The optional path uses the exact affine nodal function, extended across the
rounding overhang. It does not differentiate the clamped interval evaluator.
Every actual point of the declared affine piece lies in this extension, so
the extra overhang only weakens a bound.

## Boundary derivative

Writing the positive local coordinate as \(a=a(x)\), the outer boundary is

\[
 (a+1/2)^2+(xa+1/2)^2=Q,
 \qquad a'=-\frac{a(xa+1/2)}{a+1/2+x(xa+1/2)}.
\]

The core boundary has \(a=7/12\) up to \(x=6/7\), and subsequently

\[
 (a-1/2)^2+(xa-1/2)^2=1/144,
 \qquad a'=-\frac{a(xa-1/2)}{a-1/2+x(xa-1/2)}.
\]

The derivative on the corner branch tends to zero at the junction. The code
evaluates the corner formula on the corner part of a crossing interval and
unites the result with zero. Its denominator remains positive. This is a
valid enclosure of the derivative on the whole crossing interval. The
additional guard on broad crossing boxes is optional and conservative.

## Integer range audit

The following prerequisite belongs before the first interval quotient used
to construct a slope: in signed 128-bit arithmetic, require each endpoint of
the increment to lie between \(-16\mathtt{step.lo}\) and
\(16\mathtt{step.lo}\). Otherwise return false. A later test on the quotient
alone cannot protect the unchecked narrowing inside that quotient. With this
precheck, the existing postcheck \(|\psi'|\le16\) is safe. This was reported
to the implementation owner before freezing the new source.

Let \(S=2^{48}\). The runtime tangent guard is stronger than
\(0\le x,y\le1.001\). The following deliberately loose bounds include the
outward dyadic errors; all stated inequalities have much more than one unit
of rounding reserve.

* Outer local coordinates lie in \((.7,1.5)\), and core coordinates lie in
  \((.55,.6)\). For the outer derivative, the denominator exceeds1.2 and
  the numerator is less than3.01. For the core corner derivative, the
  denominator exceeds1/50 and the numerator is less than.061. Therefore
  the interval enclosure satisfies \(|a'|<4\).
* \(A,B\) have magnitude below2.01 and derivatives below2.01. Their product
  is positive and below4.05. Thus \(|Z|<2.02\), with derivatives below2.02.
  \(K,L\) have magnitude below2.01 and first partial derivatives below1.01.
* Every point-trigonometric enclosure on \([-2.5,2.5]\) has magnitude below2.
  This follows from the alternating Taylor bounds and their dyadic errors:
  the sum of coefficient and Horner-rounding errors is below1/1000, whereas
  the omitted alternating terms are below1/1000. Consequently the composed
  sine and cosine derivatives have magnitude at most32.
* The products \(V=a_bB\), \(W=a_aA\) have magnitude below3.02 and first
  derivatives below12. Each of the four endpoint projections has magnitude
  below17 and first derivatives below270. The two width numerators have
  magnitude below9 and first derivatives below134.
* A width-sign majorant consequently has magnitude below55 and first
  derivatives below811. Midpoint offsets have magnitude below.501, so its
  final mean-value enclosure has magnitude below1024.

For completeness, the normalized step may be as small as one dyadic unit.
The slope precheck gives \(|\mathtt{increment}|\le16\mathtt{step.lo}\).
The multiplication in the affine-value expression can introduce at most one
dyadic unit before division by the step, hence at most one real unit after
division. Since the input displacement from the piece's left endpoint has
magnitude below1.002, this quotient has magnitude below18 and the affine
potential below21. The endpoint is therefore below44 before its runtime
\([-2.5,2.5]\) guard; no overflowing quotient is needed to reach that guard.

All new stored interval endpoints are therefore smaller in magnitude than
\(2^{59}\), even allowing a factor-two cushion above the largest bound.
Their pairwise products are smaller than \(2^{118}\), within signed128.
The new quotient numerators and square-root radicands multiply these values
by at most \(S\), so they are also within signed128. Their results, by the
bounds above, remain within signed64 before narrowing. Existing rational-Q
construction retains its previously audited \(2^{120}\) bound.

## Scope and binding

Each wrapper adds the optional acceptance only after the old rejection
failed, and only when the active edge charge is zero. It preserves the old
fallback and partition accounting. The masked wrapper passes precisely the
declared axis mask. The new included header must be hashed as part of the
execution binding; hashing the wrapper alone is insufficient.

Subject to the slope precheck and complete source/header/input execution
bindings, this is an independently reviewed exact additional rejection rule.

## Frozen implementation checked

The requested pre-quotient check is present. All five entries in
`m5_agent/mean_value_kernel_freeze.json` were rehashed and match.
The two driver diffs add the included-header binding and their own filenames;
partition and execution checks remain unchanged. The composition auditor
now also asserts that the complementary owner excess dominates the declared
cyclic deficit.

* `pair_mean_value_beta0.hpp`: `ee7f2e04457c9b98260cfb4a26b9b0c7982b94ee563dac3fe5440a0c4007859f`.
* `verify_boundary_pair_costs_sharp_mvt.cpp`: `6a208f3f0c479e76ab797d620b1b7d8c085d1f9e393f635ff44de7c8ee74cf52`.
* `verify_boundary_pair_costs_sharp_masked_mvt.cpp`: `e825397e3c00b46a3c6db7b1e79d05e241c1a0d3b605e1e88e81d0608652d080`.
* `run_restricted_boundary_pair_costs_mvt.py`: `3f70270aa37669b9a62a7300fee4db7c004268dcf2c03f4c61d03ecbd073977a`.
* `run_piecewise_mvt_boundary_pair_costs.py`: `597e7effcf6f4af18a80291a26936e05541bd08b4c804106ec1e7390e7ae395f`.

## Charged-edge extension, independently reviewed

The new, separate `pair_mean_value_charged.hpp` handles charges
\(0<\beta\le1/10\). It leaves the frozen zero-charge implementation intact.
For each of the four sign pairs define

\[
 h_{sc,ss}(\phi)=\tfrac12(sc\cos\phi+ss\sin\phi-1).
\]

Since \(h=\max h_{sc,ss}\) and \(\beta\ge0\), the original cost-failure
set is exactly the union of the four smooth signed-cost failure sets. Each
signed cost is strictly increasing in the gap because
\(|h'_{sc,ss}|\le\sqrt2/2\). Its unique root is enclosed by

\[
 \gamma-\Delta\psi-\beta(\sqrt2+1)/2
 \;\le d\le\;
 \gamma-\Delta\psi+\beta(\sqrt2-1)/2.
\]

The two bisections only update a returned lower endpoint after an interval
cost upper bound is nonpositive, and only update a returned upper endpoint
after a cost lower bound is nonnegative. Inconclusive internal search points
are not returned as certified root bounds. Thus both returned endpoints
cover every state in the entire tangent rectangle.

With \(A=1+x^2\), \(B=1+y^2\), the implicit root derivatives used by the
code are

\[
 d_x=\frac{\psi_a'-\beta s_a h'/A}{1-\beta h'},\qquad
 d_y=\frac{-\psi_b'+\beta s_b h'/B}{1-\beta h'}.
\]

The signs agree with
\(\phi=d+\arctan(s_by)-\arctan(s_ax)\). The root enclosures for both the
whole box and midpoint include values below the geometric gap lower bound,
so the mean-value path is covered. Every one of the four cost branches must
be rejected for every checked axis.

The charged code additionally permits constant rational SAT width
coefficients \(sc,ss\in[-1,1]\). This is valid because
\(|Q_c|+|Q_s|\ge scQ_c+ssQ_s\); it forms a convex combination of the old
majorants. A floating-point gradient heuristic proposes one numerator over
\(10^9\), and cannot accept a box. Its finite check and clamp keep the
subsequent `llround` within \([-10^9,10^9]\). The exact rational enclosure is
range-checked before the same dyadic monotonicity and mean-value inequalities
are tested. The proposed coefficient is constant throughout that box; its
method of selection has no mathematical role in the bound.

The same pre-quotient slope guard is present. For a conservative integer
range estimate, the old \(|\sin|,|\cos|<2\) enclosure gives the computed
\(|h'|<8.05\), even before using the much sharper true trigonometric bound.
Consequently the computed denominator is greater than.19 and both implicit
partials are below100 in magnitude. Repeating the previous syntactic
derivative estimates gives endpoint SAT derivatives below4300 and final
mean-value bounds below8192. Potential expressions before the root-domain
guard remain below44, and the initial brackets below45. All new stored
interval endpoints are below \(2^{62}\), with multiplication products below
\(2^{124}\); the quotient and root results are within the same limits before
integer narrowing. The long-double proposal arithmetic has magnitude below
\(10^{70}\), and all integer conversions from it are made only after the
explicit finite/clamp checks.

Thus the charged extension has the same soundness structure as the audited
zero-charge rule. Its separate source and included-header hashes still need
to be bound by each execution manifest.

### Frozen charged implementation

All entries in `m5_agent/charged_mean_value_kernel_freeze.json` were
rehashed and match the independently reviewed charged implementation.

* `pair_mean_value_beta0.hpp`: `ee7f2e04457c9b98260cfb4a26b9b0c7982b94ee563dac3fe5440a0c4007859f`.
* `pair_mean_value_charged.hpp`: `99aeb2abf4a049aff09d95fc18063326aa94f2efd36e61e25ac0ddc40d4d086a`.
* `verify_boundary_pair_costs_sharp_masked_mvt_charged.cpp`: `151a6655c7ec837bcab59b92b5fe21935b23b33147288d962dfd1e78c132eea0`.
* `run_piecewise_charged_boundary_pair_costs.py`: `a10733741ba73254ccc117b59da63316b736f73c867d984d4677fa9ad5ad1b19`.

## Convex-width extension for zero-charge edges

The separate `pair_mean_value_convex_beta0.hpp` applies the already reviewed
constant rational width majorants to the exact affine zero-charge endpoint.
Its box guards, pre-quotient slope checks, treatment of the core transition,
midpoint construction, and box derivatives are identical to the frozen
zero-charge rule. The monotonicity span ends at the maximum of the original
certified failure-gap upper bound and the affine endpoint enclosure. This
also covers any harmless affine extension across a rounded piece endpoint.

For each of the eight signed separating axes, the rule must find a strict
negative upper bound from one valid majorant. It first tries the four corner
coefficients and then the same choice-only rational gradient proposals used
by the charged rule. Every proposed coefficient remains in [-1,1], and all
acceptance inequalities use the exact dyadic arithmetic. No charged-root
inference is used by this wrapper. Its derivative and integer magnitudes are
bounded by the zero-charge estimates above; the larger charged estimates
also provide an independent conservative ceiling.

The full-source diff adds the two includes and one optional rejection after
the old zero-charge rejection. All old fallback and partition accounting
remain intact. The new driver binds all three included headers and otherwise
preserves the reviewed complete-branch execution protocol.

All six file entries in `m5_agent/convex_beta0_kernel_freeze.json` were
independently rehashed and match. The frozen status file is left unchanged;
this section records the independent approval of its implementation.

* `pair_mean_value_convex_beta0.hpp`: `2e34058fa15b69a137629c1bb161585868c19f06db9f9c104133f06433bc9f12`.
* `verify_boundary_pair_costs_sharp_mvt_convex.cpp`: `caf6c0299e26b368b434374f2746614d555ffb622b010f7c42858ad802661eb2`.
* `run_restricted_boundary_pair_costs_mvt_convex.py`: `a2e367dbf7104d6ac10b51c8c9df0bbdb7a526b5ac99d39111e174920d753472`.

The other three frozen entries are the unchanged exact dyadic base and the
previously reviewed zero-charge and charged headers. A completed geometric
certificate still requires the separately bound exhaustive execution logs.
