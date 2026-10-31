# Independent review: the H-owned HK front-support bound

Date: October 25, 2026. Reviewer: low_radius_diamond.

**Verdict: PASS.** The reviewer independently rederived the argument
before reading, then read and audited the complete final saved source

    LOW_DIAMOND_H_OWNED_HK_FRONT_SUPPORT_BOUND.md
    sha256 f4078778b703c3f7e333a6e3903bdf6a5342dfe4d2da569924209dda997612c2

The theorem proves N=V dot n>3/8 on the entire original strict
H-owned n-normal HK row, throughout 6241/1600<=q<=1105/256.

The review checked all of the following directly:

- The actual A and K circle corners have n coordinates N+u+v and
  N+E+d. Their j coordinates have the required strict opposite signs.
  The positive zK dot j estimate follows from the original a<2,
  b>3/5, E>v, d<u and tau<1-v; it does not use the conclusion N>3/8.
- The exact difference of the two actual j coordinates is
  E+v-(d/E)(E-v), strictly less than E+v. Both original circle corners
  and both distinct root-contact applications are preserved.
- On the full interval 1<=t<=sqrt(2), the proposed affine lower bound
  has positive right side. Its squared reserve expands exactly to
  -102/25+(709/100)t-(74/25)t^2. Concavity reduces its sign to the two
  endpoints, with reserves 1/20 and (709sqrt(2)-1000)/100; the latter
  is strict because 2*709^2-1000^2=5362>0. The square-root domains and
  every use of squaring therefore have their signs justified.
- Under the contradiction premise 0<N<=3/8, the original two-circle
  equations give the sum of the two positive square roots used in
  the proof. The radius and N comparisons point in the correct
  direction for both terms.
- The final Cauchy bounds are the two complete unit-vector bounds
  7u+12v<=sqrt(193) and 7d+12E<=sqrt(193). Their sum, together with
  2sqrt(193)<28, gives a lower j gap strictly greater than E+v and
  contradicts the exact geometric upper gap.

No smaller-component equilibrium, K2 replacement, selected mean,
sampled angle threshold, numerical extremum or coefficient packet is
needed. True H5/K3/A2/B2, the intact petal, all nine squares, all three
extras, both initially allowed B masks and every original force and
mean remain within the declared scope.

This is acceptance of the scalar input N>3/8. It is not a proof of
the remaining unique-B block-pressure sign and does not by itself
close a roadmap gate or introduce a new ID. No Lean compilation or
CI was used for this hand review.
