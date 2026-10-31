# Root review: four actual near-origin units leave capacity at most eight

Date: October 27, 2026.

**Decision: accepted after full-source mathematical review.** I read all
seven sections of FOUR_NEAR_ORIGIN_UNITS_CAPACITY.md, checked the
geometric reduction, each angular interval argument, every rational
reserve and the unequal-radius capacity conclusion. This is a physical
theorem about the unchanged original units and needs no stress or
contact-graph hypothesis.

## 1. The four original centers and their cyclic order

The farthest-corner inequality gives the stated strict universal
center bound M=91/60. The four chosen near-square centers have norm
less than m=3619/5000 by the square circumradius and the closed
1/60 small-disk hypothesis. The exact positive reserves 31/57600
and 8449/225000000 justify both strict rational relaxations even
at the enclosing-radius and small-disk boundaries. Distinct unit
centers are at distance at least one by their open incircles.

No near center is zero and no two have the same direction. The
distance formula f(a,b) is strictly increasing in each variable
when both radii are below m<1. Its exact value at (m,m) is
597161/13097161, strictly below c=57/1250 with the displayed
cross-product reserve 86927. Consequently all pairwise minor
angles exceed alpha=arccos(c). Ordering the four distinct directions
gives four cyclic gaps greater than alpha. A gap at least pi is
impossible because the other three exceed pi/3 each. Thus every
gap is genuinely minor and lies strictly below beta=2pi-3alpha.

For a putative radius at most s=6577/10000, both adjacent gaps
would exceed pi-alpha because f(s,m) is strictly below -c. I
verified f(s,m)=-4354427/95208652 (the same fraction reduces to
-56551/1236476) and the positive cross-product reserve 16140586.
The two remaining gaps exceed alpha, so their sum would exceed
2pi. This proves all four inner radii exceed s without imposing
equal radii, a common frame or a prescribed near-center polygon.

## 2. Every additional center and its actual gap

The exact beta bounds pi/2<beta<3pi/4 are valid. Any additional
center direction has a near direction within beta/2<3pi/8. The
strict comparison m<3/4<2cos(3pi/8), followed by convexity of
the squared distance as a function of the additional radius on
[0,1], excludes every additional center of radius at most one.
The two endpoint squared distances are strictly below one, so
the closed radial endpoints cause no gap.

For an additional radius t in (1,M) and near radius a in (s,m),
f(t,a)<f(M,a)<f(M,s). The first derivative sign uses a<1;
the second uses a^2-M^2+1<0, which follows already from
m<3/4 and M>3/2. Thus its direction is more than gamma from
each near direction, with k=cos(gamma)=222794623/256503000.
Each additional center has a unique original cyclic gap and is
confined to the open gap after removing gamma at each end.
No assumed common radius or unproved angular ordering of the
additional centers enters this argument.

## 3. Exact strict reserve and capacity one

I checked the angle addition identity for theta=2pi-3alpha-2gamma.
The sine of 3alpha is negative, giving the positive second term
displayed in the source. The negative first term and positive
second term retain their correct inequality directions throughout
the rational estimates. In particular k lies strictly between
1737/2000 and 4343/5000; both square-root lower bounds and the
monotonicity of 2x sqrt(1-x^2) on x>1/sqrt(2) apply with their
stated signs. Direct rational arithmetic reproduces the reserves
55615750799/156250000000000, 11943/100000000 and 129/1562500.

The resulting lower bound is exactly
97850131493/125000000000, exceeding 1957/2500 by
131493/125000000000. Hence every retained angular interval
has length less than theta and every pair of directions in one
interval has cosine greater than b=1957/2500.

The squared-distance upper quadratic is separately convex on
[1,M]^2, so its maximum lies at a rectangle corner, including
the unequal-radius corners. All four are strictly below one.
For the mixed corner, b-M/2=367/15000>0 is the exact needed
comparison. The outer corner is 4496583/4500000<1. Thus two
distinct physical centers cannot occupy one remaining interval.
Four intervals give at most four additional units, hence at most
eight units in total.

This full proof covers arbitrary independent square orientations,
closed near-disk points, side or vertex near contacts and arbitrary
circle contact masks. It removes no physical square and uses no
numerical pose, sampled-angle claim, Lean compilation or CI. The
rational arithmetic check only verifies the displayed hand proof;
the exact inequalities themselves are included in the source.
