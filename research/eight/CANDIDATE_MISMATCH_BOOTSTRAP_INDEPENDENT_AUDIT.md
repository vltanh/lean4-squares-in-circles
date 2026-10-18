# Independent review of the mismatch bootstrap

**PASS.** The reviewed manuscript is the version that explicitly requires
\(\kappa>0\) and states the exact core lower bound as
\(a\ge1/2+\sqrt2/24\), followed by the strict rational bound
\(a>447/800\). Core-diagonal boundary states may attain the first
equality, so retaining that distinction is correct.

I independently rederived the following complete implications.

1. The seven chosen labels telescope, as do the actual frame differences.
   Since the word has four quarter turns, \(\sum_i\phi_i=2\pi\).
   The width charge has quarter-turn period and is even, so its value
   is \((\sin|d_i|+\cos|d_i|-1)/2\) on the specified range. Subtracting
   all seven edge bounds gives exactly the stated nonnegative edge-excess
   identity; no contact-owner restriction is inserted into that identity.
2. The charge is concave on \([0,.7]\), is zero at zero, and therefore
   lies above its endpoint chord. With positive \(\beta,\kappa\), the
   strict total slack estimate gives the claimed strict bound on the sum
   of the five absolute differences. Every later restriction remains
   conditional on the preceding complete pair theorem; the note does
   not infer a theorem from an unverified fit.
3. Central-disk avoidance gives the weak exact lower bound on \(a\),
   and the rational square-root comparison makes \(a>.55875\) strict.
   The farthest-corner equation gives \(a<1.415\) and \(b<.9\) for
   both original exterior states and all boundary representatives.
4. On a zero-quarter edge with \(|d|\le.4\), the two primary-axis
   margins are at most
   \(.915-1.05875\cos|d|+.05875\sin|d|\).
   The coefficients have the required signs, and the elementary sine
   and cosine bounds give the strict negative reserve \(711/20000\).
   This eliminates both axes even at angle or owner ties.
5. With \(|d|\le.1\), the two remaining margins are negative whenever
   the source signed transverse coordinate is nonpositive or the target
   signed coordinate is nonnegative. The two bounds interchange for the
   two axes and have strict reserves \(17/2000\) and \(3/500\).
   Since \(a>0\), these coordinate signs are exactly the signed tangent
   signs. Thus all three zero-quarter pairs have the claimed strict
   positive-to-negative pattern; zero tangents are excluded explicitly.

The fixed checker replays byte-identically. The independent script
`audit_candidate_mismatch_bootstrap_independently.py` reconstructs all ten
chord bounds by Horner evaluation of the explicitly expanded lower
polynomial and separately checks all seven remaining rational reserves.
All 17 comparisons pass. It supports both the flattened and local layouts.

The conditional-kernel domain interface has its separate independent PASS
in `CONDITIONAL_AFFINE_ARC_KERNEL_INDEPENDENT_AUDIT.md`. I checked the
status-only update that points to that review; the geometric statements and
the 17 fixed comparisons are unchanged. The current manuscript hash is
`d2485f4e1db5707be71e01e4f6491061e90e4029dc6c947f661ff1c2cd042e2f`.
The bootstrap itself has no remaining continuous or arithmetic premise
beyond the full pair bounds that it explicitly assumes.
