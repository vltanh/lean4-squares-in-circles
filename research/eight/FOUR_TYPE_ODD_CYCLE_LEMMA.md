# Exact seven-walk bound for the certified four-type inequalities

This note gives a hand proof of the finite combinatorial consequence of
`fourtype_rational_certificate_data.json`. The continuous geometric pair inequalities
have now been proved by the exact dyadic interval verifier: the authoritative
record is `fourtype_pair_logs_checked/manifest.json`, with all forty
branches and all 2,560 closed piece rectangles completed. Together these give
an exact computer-assisted mathematical theorem. A replacement of the full
continuous pair certificate by short hand inequalities remains separate.

## Certified pair inequalities

Let seven cyclically indexed boundary states have types
\(\tau_i\in\{0,1,2,3\}\), a real-valued state potential \(\psi_i\),
positive angular gaps \(\delta_i\), and width excesses \(u_i\).
Suppose every adjacent pair satisfies

\[
\delta_i-\frac9{50}u_i+\psi_{i+1}-\psi_i
\ \geq\ \Gamma_{\tau_i,\tau_{i+1}},
\qquad
\Gamma=\frac1{10^6}
\begin{pmatrix}
910793&910782&900470&883157\\
910782&910793&900481&883146\\
900470&900481&890169&893458\\
883157&883146&893458&910793
\end{pmatrix}.
\]

Then

\[
\sum_{i=0}^6\left(\delta_i-\frac9{50}u_i\right)
\geq \frac{6209669}{10^6}.
\tag{1}
\]

## Four-type graph proof

Subtract \(a=883146/10^6\) from every entry of \(\Gamma\). In units
of \(10^{-6}\), the resulting symmetric nonnegative edge-cost matrix is

\[
B=10^6(\Gamma-a)=
\begin{pmatrix}
27647&27636&17324&11\\
27636&27647&17335&0\\
17324&17335&7023&10312\\
11&0&10312&27647
\end{pmatrix}.
\]

Every triangle has cost at least \(p=27647\), since the four triangle
costs are

| Triangle | Cost |
|---|---:|
| 0,1,2 | 62295 |
| 0,1,3 | 27647 |
| 0,2,3 | 27647 |
| 1,2,3 | 27647 |

Every self-loop except the loop at type 2 also has cost at least \(p\).

A closed walk of odd length contains an odd simple cycle: repeatedly split it
at a repeated vertex, retaining an odd part until no repetition remains.
A graph on four vertices has no odd simple cycles other than self-loops and
triangles. If a seven-step walk contains a triangle or a self-loop at a type
other than 2, its total cost is at least \(p\), because every remaining
edge cost is nonnegative.

Otherwise it contains a self-loop at type 2. If it visits another type,
it must leave and return to type 2. Each of those two edges costs at least
10312, so its total cost is at least

\[
7023+2(10312)=27647=p.
\]

If it never leaves type 2, all seven edges are its self-loop, of total cost
\(7(7023)=49161>p\). Thus every seven-step closed type walk has total
residual cost at least \(p\). Restoring the baseline proves

\[
\sum_{i=0}^6\Gamma_{\tau_i,\tau_{i+1}}
\geq 7a+\frac p{10^6}
=\frac{6209669}{10^6}.
\]

Summing the certified pair inequalities telescopes the potentials and gives (1).
Equality in the type bound is attained, for example, by the type word
\((0,2,3,1,3,1,3)\).

## Universal exterior-ring consequence

The familiar strict rational estimates
\(\sqrt2>239/169\) and \(\pi<355/113\) imply

\[
\frac{6209669}{10^6}
+\frac9{50}(\sqrt2-1)-2\pi
>
\frac{6209669}{10^6}
+\frac9{50}\left(\frac{239}{169}-1\right)
-\frac{710}{113}
=\frac{19848893}{19097000000}
>0.
\]

Thus the certified pair inequalities prove the universal exterior-ring inequality

\[
\sum_i\delta_i-\frac9{50}\sum_i u_i
+\frac9{50}(\sqrt2-1)>2\pi.
\]

The numerical lower margin supplied by the displayed rational expression is
approximately 0.0010393723. Its role is arithmetic reserve. The geometric pair inequalities have been
verified over their entire continuous domain by the completed exact certificate;
this note supplies the finite hand argument that converts them into the ring theorem.

## Self-contained rational bounds for the final arithmetic

The lower estimate for \(\sqrt2\) follows immediately from
\(239^2=57121<57122=2(169)^2\).

For the upper estimate for \(\pi\), let
\(a=\arctan(1/5)\) and \(b=\arctan(1/239)\). Double-angle identities
 give \(\tan(2a)=5/12\), \(\tan(4a)=120/119\), and

\[
\tan(4a-b)
=\frac{120\cdot239-119}{119\cdot239+120}=1.
\]

Moreover \(0<4a-b<4/5<\pi/2\), so
\(4a-b=\pi/4\). This proves Machin's identity
\(\pi=16\arctan(1/5)-4\arctan(1/239)\). The mild range estimate
\(\pi/2>1\) used here follows, for example, from
\(\arctan(1)=\int_0^1(1+x^2)^{-1}\,dx>1/2\).

Integrating the finite geometric-series identity for \((1+x^2)^{-1}\)
proves the alternating arctangent bounds, with a remainder of the stated
strict sign for \(x>0\). In particular,

\[
\arctan(1/5)
<\frac15-\frac1{3\cdot5^3}+\frac1{5\cdot5^5}
-\frac1{7\cdot5^7}+\frac1{9\cdot5^9}
=\frac{24288907}{123046875},
\]

and

\[
\arctan(1/239)
>\frac1{239}-\frac1{3\cdot239^3}
=\frac{171362}{40955757}.
\]

Hence

\[
\pi<\frac{5277328977275528}{1679825970703125}
<\frac{355}{113},
\]

where the difference in the last comparison is exactly
\(45167474711/189820334689453125>0\).

The analogous lower truncation through degree seven at \(1/5\), together
with \(\arctan(1/239)<1/239\), also gives

\[
\pi>\frac{1231847548}{392109375}>\frac{157}{50}.
\]

Thus the simple trigonometric ranges used in the continuous pair verifier
are also supported by explicit rational bounds.
