# Independent review: one-sixth clearance and the full centered forty-degree arc

Date: October 28, 2026 UTC. Reviewer: house agent.

**Result: full independent PASS, with no repair requested.** I read the entire new source and its sole complete operative input, independently rederived the nearest-point endpoint cover and both coordinate estimates, and checked the exact new concavity reserve.

The target is root-authored. I did not contribute the new one-sixth theorem or its proof. The target expressly attributes the earlier concavity method to pentagon, and proves its own weaker clearance threshold rather than invoking the earlier theorem outside its premise.

## 1. Exact full sources

| Complete source | SHA-256 |
| --- | --- |
| ONE_SIXTH_CLEAR_UNIT_CENTERED_NINE_EIGHTHS_ARC.md | ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a |
| ALL_UNITS_CENTER_RADIUS_THREE_QUARTERS_CENTERED_FORTY_DEGREE_ARC.md | d575e6632c7181fc8803e7c9dc73b222cdce055eca1c636b3f15eb9d5f2279b9 |

Both current hashes match. I read both files in full. The nine-fiftieths source is transparently provenance only: the new near-center proof does not rely on its stronger clearance premise.

## 2. The complete nearest-point domain includes the equality corner

With the actual own frame signed and ordered so a>=b>=0, the b>=1/2 case has exact distance sqrt((a-1/2)^2+(b-1/2)^2). Under clearance at least 1/6 and center radius at most 5/6, the printed lower chain for the squared center radius reaches the same value 25/36 as the upper bound.

All inequalities therefore are equalities. In particular the two nonnegative nearest-corner coordinates have sum 1/6, squared norm 1/36 and zero product. Their order forces exactly a=2/3,b=1/2. The proof retains that actual endpoint.

When b<1/2, origin clearance first excludes a<=1/2, and the actual nearest-side distance is a-1/2. Thus a>=2/3. These cases genuinely exhaust the entire actual square domain, including its side/corner transition.

The resulting closed comparison domain a>=2/3, b<=1/2, 2/3<=r<=5/6, 0<=phi<=pi/4 is correct. No containing-circle premise entered this local part.

## 3. Every closed-arc endpoint is strictly inside in both coordinates

For alpha=atan(3/8), the exact cosine and sine are 8/sqrt(73),3/sqrt(73). I checked r0*cos(alpha)=9/sqrt(73)>5/6 and the stated squared reserve 1091.

The first-coordinate upper deviation is at most 11/24. Its lower deviation uses the entire angular interval [-alpha,pi/4+alpha], whose cosine minimum is 5/sqrt(146). Since sqrt(146)<13, the final upper bound is 125/312<1/2. Both signs are strict at every retained angle and center-radius endpoint.

For the second-coordinate upper deviation, the actual a>=2/3 gives b>= (2/3)*tan(phi). This establishes the printed F bound in the correct direction. Its full-interval second derivative satisfies F''<-3/8, including phi=0. I independently differentiated F and recovered

    F(alpha)=143/292,
    F'(alpha)=611/7008.

The global concavity tangent bound has quadratic term -(3/16)*(phi-alpha)^2. Completing that square gives the maximum addition (4/3)*F'(alpha)^2. Exact rational arithmetic reproduces

    1/2-143/292-(4/3)*(611/7008)^2
      =5111/36834048>0.

This is a uniform inequality on the entire continuous interval, not an evaluation at a chosen physical orientation.

For the negative second-coordinate deviation, the coefficient r-r0*cos(alpha) is strictly negative and sin(phi) is nonnegative. Dropping that term gives the correct upper bound 27/(8sqrt(73))<27/64<1/2. The proof therefore puts every point of the whole closed centered arc in the actual open square.

In particular the nearest-corner endpoint a=2/3,b=1/2,r=5/6 receives all the same strict margins; it was not handled by an unsupported continuity argument.

## 4. The all-center join and strict pair separation

The complete d575 source applies to every actual contained square with center radius at least 3/4, with no load, force or boundary-contact premise. Its near/far center regimes and exact twenty-degree comparison are compatible with the target.

The target's alpha exceeds pi/9 because tan(pi/9)<sqrt(31)/15<3/8, with exact reserve 41/14400 in the squared comparison. For r<3/4, the new near-center theorem applies; for r>=3/4, d575 applies. The overlap and the closed threshold are included.

Thus every actual contained unit with clearance at least 1/6 has its entire closed centered radius-9/8 arc of halfwidth pi/9 in its open interior. Two such units with center gap at most 2pi/9 would share the midpoint of their minor centered-arc interval in both open interiors. This includes equality, so the actual separation is strictly greater.

The proof does not presume connectedness of the entire circle intersection and supplies no unproved pocket allocation. Each future caller must establish its actual clearance and occupied geometric routing.

## 5. Scope and disposition

The near-center theorem has no containing-radius requirement. The all-center theorem uses the precise unchanged Q=1105/256 containment premise of d575. Both conclusions are force-free and preserve every square's actual frame; no point, support, mean, force, mask or true degree is changed.

No original row closure is asserted by this geometric lemma alone. No numerical pose sample, angular mesh, optimization certificate, Lean compilation, CI, remote write or ledger edit was used.

**Final disposition: full independent PASS at ae58afaf0564b403ab802bdc4ccb5f5a318013fd9aba778c6e4220e720aceb0a.**

