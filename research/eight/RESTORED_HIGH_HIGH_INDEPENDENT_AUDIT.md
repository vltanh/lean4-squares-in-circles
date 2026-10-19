# Fresh independent audit of the restored whole H/H proof

**PASS.** This audit applies to the restored 108-comparison source, not
only to the earlier lost 83-comparison version.

Reviewed source hashes:

- HIGH_HIGH_WHOLE_PAIR_HAND_PROOF.md:
  b976e006a9dd0a725c5992b48af6edbb2b2ef998e9d3116ee66eef0f896ad0d3
- verify_high_high_whole_pair_hand.py:
  26c0232083346aaed26f14d9599161f43beb7d9a3bdf7e83ddddf9a6bbe078d4

The supplied checker was replayed from its frozen source and passed all
108 strict comparisons, including all 18 endpoint rows. I separately
reconstructed the degree-14 polynomial directly from the manuscript in
JavaScript BigInt rational arithmetic. All 15 printed Bernstein lower
bounds pass independently. The author uses a separate Python Fraction
implementation.

## Exact geometric checks

The diagonal fold is correct. With
a=a_old+b_old, b=a_old-b_old, sigma=-sigma_old, and new frame rotation
-sigma_old*pi/4, the actual center is (a,-sigma*b)/sqrt(2).
The label identity ell_new=pi/4-ell_old follows from
u=(.569472-.390886)/2 and v=(.569472+.390886)/2.
It preserves the signed potential exactly; the width penalty is
unchanged by the resulting quarter-turn lift.

The folded norm identity rho^2=Q-a-1/2 is exact. The monotonicity
calculation for the two-radius cosine-law quotient on [1,4/3]^2 is valid,
and its upper value is 23/32. This is less than 21/29, proving the
strict positive folded angle without assuming frame concentration.

I independently mapped the two retained original source normals after
the fold. The common normal is (-1,+1)/sqrt(2). For positive folded sign,
the extra normal is (+1,+1)/sqrt(2), whose projection is bounded by
4/3 minus the old transverse coordinate, hence below one. For negative
folded sign the extra normal is (-1,-1)/sqrt(2); its doubled projection
is bounded by (a1+b1)-(a1-b1)=2b1<2 in the first quadrant.
The later angle tail covers all other angles.

For the common normal, the doubled projection is exactly
a+sigma*b+(sin(phi)-cos(phi))*A
-tau*(sin(phi)+cos(phi))*B.
The doubled support sum is 1+sin(phi)+cos(phi) in the remaining quadrant.
Thus the stated separating margin and every multiplier coefficient are
correct. Reflected reversal supplies all retained target normals.

## Complete source cover and support choices

The initial barriers use the correct extrema of a+sigma*b and
D*A-tau*C*B. Their derivative signs select exactly the displayed
axial or cut endpoints. Each barrier is increasing up to its quoted
endpoint. The strict direct tails have the correct signs, including
the negative/positive tail obtained from h's one-half Lipschitz bound
at the quarter turn.

Every physical arc support selection in the nine-row table is valid.
In particular:

- positive sources with lambda=.34,.39,.43 select the axial point;
- the two early positive/negative target supports decrease to the cut;
- for lambda=.34 and a negative target, simultaneous negative
  coefficients would contradict 2lambda^2<u^2+v^2, so endpoint
  concavity or axial monotonicity is exhaustive;
- the varying negative/negative target derivative is bounded above
  by the displayed strictly negative quantity, including the case
  where its primary coefficient changes sign;
- the last negative/positive source derivative stays negative on
  the entire arc, selecting the cut endpoint.

All other support replacements enlarge the arc to its entire circle,
which is an unconditional lower bound.

For the fixed-endpoint scalars, A*>0 and B*<0 imply that the first
derivative is strictly convex. With a negative right endpoint derivative,
no interior negative-to-positive crossing is possible, so no interior
minimum is missed. The increasing rows follow from the exact amplitude
bound. The two circle-target scalars have the stated norm identity
N''+N/4=(u^2+v^2-2lambda^2)^2/(4N^3)>0; its denominator is nonzero.
The norm increases on each listed interval, and the quarter norm bound
therefore gives the quoted strict concavity test.

## Squaring and the fixed polynomial

The varying-multiplier expression was independently rederived from
the source full-circle support and target cut endpoint. Every endpoint
rounding in its comparison factor T is adverse. Its cosine coefficient
is positive and its sine coefficient negative, so C6 and S5 give the
required lower bound. The explicit T>.278 argument is valid before
squaring. The independently reconstructed P=T^2-2Q*((u+lambda)^2+
(v-lambda)^2) has degree 14, and all 15 printed positive lower
Bernstein coefficients match the restored manuscript.

The complete source intervals, barriers, and tails overlap at every
endpoint. No state, sign, retained axis, or allowed frame interval is
uncovered. This is a whole H/H hand proof at gamma=.9099 on the
physical seven-ring domain.
