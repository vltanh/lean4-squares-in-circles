# Independent review: expanded endpoint cover and the entire three-load seven-cycle

Date: October 30, 2026 UTC. Reviewer: block_ears.

**Verdict: PASS at the complete stated geometric, arbitrary-endpoint
channel, and three-load simple-cycle scopes.** No repair is required in
the frozen source. I did not contribute to its expanded-square cover,
coupled height estimate, inscribed-square construction, constants, or
channel-triangle proof. My parallel work independently rediscovered
the already published long-channel matching observation; that observation
is an existing input, not a new contribution to the target source.

The exact source reviewed in full is

    TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md
    SHA256 78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6
    15789 bytes

I reconstructed every geometric step, all continuous comparisons, both
tilt signs, all parts of the disk cover, and the literal complete C7
caller. I also read the complete matching source and the exact operative
physical transmission sections. The review does not re-audit the entire
global minimizer-selection pipeline, which is not a premise of the
standalone geometric theorem.

## 1. The actual long gap supplies the full endpoint domain

The actual farthest-corner identity gives

    |c|^2+|c|+1/2 <= Q,
    M^2+M+1/2-Q = 31/57600 > 0, M=91/60.

Thus every endpoint center is strictly inside D_M, including at R^2=Q.
Both halfwidths are at least 1/2. The support gap at least two therefore
forces horizontal center separation at least three. Consequently the
left/right signs in c_A=(-X_A,y_A), c_B=(X_B,y_B) are consequences,
not chosen assumptions. Each X_i>3-M and

    |y_i|^2 < M^2-(3-M)^2 = 1/10.

In particular X_i>|y_i|, as needed for the subsequent two-tilt proof.
The endpoint excesses delta_i=m_i-1 are nonnegative and their half-sum
E is strictly below 1/30. This includes E=0 and either zero individual
excess; no nonzero tilt is required or divided by.

## 2. The actual-corner lower bound treats both tilt signs correctly

For a>=b>=0 with a^2+b^2=1 and center coordinates X>=Y>=0, the first
tilt sign has absolute frame-coordinate sum

    aX+bY+|aY-bX|.

When aY>=bX this equals (a-b)X+(a+b)Y. On the other complete branch
its excess over that expression is 2(bX-aY)>=0. The opposite tilt sign
has sum (a+b)X+(a-b)Y, whose excess is 2b(X-Y)>=0. These cover both
possible signs of the near-horizontal axis after the allowed coordinate
reflections. The tie aY=bX is included in both weak comparisons.

Writing k=(a-b)/2 and h=(a+b)/2, the identity k^2+h^2=1/2 then gives

    (X+k)^2+(Y+h)^2 <= Q.

This is a lower bound on the farthest-corner norm of the **unchanged
actual square**; it is not a replacement pose. It is valid for each
endpoint independently of the other's tilt or vertical sign.

For completeness, b<=1/sqrt(2)<4/5 implies a>=1-b/2 by squaring
positive quantities. Thus delta>=b/2 and b<2/15. The exact identity
delta^2=2(1-a)(1-b) yields 1-a<=15 delta^2/26 with the alignment case
delta=0 included.

## 3. The coupled height budget does not optimize the endpoints separately

The two vectors (X_i+k_i,Y_i+h_i) both have norm at most sqrt(Q).
Their vector sum therefore has squared norm at most 4Q. The same
original long-gap inequality gives

    sum_i (X_i+k_i) >= 2+a_A+a_B
                      >= 4-(30/13)E^2 > 0.

The squared lower bound has the correct direction, because its right
side is positive throughout 0<=E<1/30. The source then drops only the
negative fourth-degree term in the radical and uses the upper tangent
to the concave square root at 81/256. This yields

    Y_A+Y_B <= F(E)=1/8-E+(320/39)E^2 <= 1/8.

The final inequality uses (320/39)E<32/117<1. No endpoint height is
given an independently unattainable extreme; the common excess E is
retained through the sum calculation. All radicals remain positive,
and the endpoint E=0 gives the literal aligned result.

## 4. The inset squares are contained in the actual tilted squares

The centered axis-parallel square with halfwidth

    r_i=1/(2m_i)

has projection at most r_i(a_i+b_i)=1/2 on each original side axis.
It is therefore inside the original square, for both tilt signs. Its
upper inward corner is an actual point of that square. No geometric
motion or independent adjustment of a contact mean is used.

With delta_A+delta_B=2E, direct positive-denominator algebra gives

    r_A+r_B >= 1/(1+E),
    |r_A-r_B| <= E/(1+2E).

Combining those estimates with the coupled height budget gives the
source's three bounds on inward corner separation, average height and
height difference. I recomputed every stated rational constant:

| Quantity | Exact value |
| --- | --- |
| 2M-30/31 | 1921/930 |
| 7/16-(160/39-15/31)/900 | 75467/174096 |
| Preceding lower bound minus 13/30 | 127/870480 |
| 1/8+(320/39-15/8)/900 | 1483/11232 |
| 2/15 minus preceding upper bound | 73/56160 |

Thus the rounded constants L=1921/930, H=13/30, D=2/15 have the
claimed safe directions. The coarse bounds r_i>=15/32 and
11/32<=t_i<=5/8 follow from delta_i<1/15 and |y_i|<=1/8.
The bottom heights are negative, at most -11/32.

The outward horizontal ends of the inset squares really do extend
beyond the center disk: the sufficient reserve is

    (3-M)+15/32-M = 209/480 > 0.

The inward x coordinates satisfy alpha<0<beta. These facts justify
the horizontal-strip cover at both closed side boundaries.

## 5. The cover includes every point of the closed disk

I checked the upper half in its three actual regions.

* At x<=alpha, the point's x coordinate lies in the horizontal
  projection of the left inset square. Its distance to that square
  is at most max(0,y-t_A)<=M-11/32<3/2. The analogous right strip
  is identical. This includes x=alpha and x=beta and does not require
  the test point to lie above the inset square.
* For alpha<=x<=beta and 0<=y<=5/8, choose the inward corner with
  smaller horizontal distance. The horizontal error is less than
  L/2<31/30; the vertical error is at most 5/8. The squared-distance
  reserve is exactly

      9/4-(31/30)^2-(5/8)^2 = 11399/14400 > 0.

  Hence this region is strictly covered, including y=0 and y=5/8.
* For alpha<=x<=beta and 5/8<=y<=M, both open disks of radius 3/2
  centered at the inward corners have nonempty horizontal sections.
  Since every actual t_i<=5/8<=y, raising y to M decreases both
  section halfwidths. Decreasing their average height to H, while
  keeping the actual difference fixed, also decreases both halfwidths.
  During this comparison every intermediate t lies between its
  actual value and H plus or minus half the actual difference; the
  entire interval stays inside (M-3/2,M). No radical becomes invalid.

  At fixed average H, concavity of
  f(t)=sqrt(9/4-(M-t)^2) implies that
  f(H+s)+f(H-s) is nonincreasing for s>=0. Thus increasing the
  absolute difference to D can only decrease the sum. This proves
  the common lower bound

      sqrt(371)/20 + sqrt(4379)/60.

The strict final overlap is exact. For A0=371/400, B0=4379/3600,
and C0=L^2-A0-B0, I recomputed

    C0 = 3671983/1729800 > 0,
    4 A0 B0-C0^2 = 2473200289/374026005000 > 0.

These positive quantities justify both squarings, giving
sqrt(A0)+sqrt(B0)>L. Since beta-alpha<L, the two open horizontal
sections overlap strictly. Each contains its own horizontal center,
so their union contains the **entire closed** interval [alpha,beta].
No gap at the meeting point or at either strip endpoint survives.

Reflection in the horizontal axis applies the same established estimates
to the lower inward corners of the same original inset squares. It
changes neither the endpoint halfwidth excesses nor the absolute-height
budget. Together the two halves cover every point of closed D_M.

## 6. The third square contradicts the cover without extra force premises

Each short support gap gives, for every actual p in A,

    n_A.(c_C-p) >= 1+h_C(n_A) >= 3/2.

Cauchy--Schwarz therefore yields dist(c_C,A)>=3/2, and the second
short gap gives dist(c_C,B)>=3/2. The actual center c_C is strictly
inside D_M by the same corner bound, contradicting the strict cover.
This uses no degree, load, physical circle corner, or contact owner at
C, A, or B.

The metric formulation also holds. If compact convex A,B have positive
distance t realized at p,q, differentiating squared distance along
the segments from p toward any a in A and q toward any b in B shows
that n=(q-p)/t supports A maximally at p and B minimally at q. Hence
its support gap equals t. Conversely a support gap t bounds every
point-pair distance from below by t. Applying this fact to the three
positive distances supplies exactly the source's metric equivalence,
including its weak thresholds two and one.

## 7. Complete channel and seven-cycle joins

At a genuine unloaded true-positive-degree-two internal body, its full
two forces cancel and its full torque makes the actual applications
collinear in their common normal. This is the exact physical transmission
lemma. Along an actual path, all original support equalities telescope;
the endpoint gap is the sum of the original internal widths plus both
actual endpoint halfwidths. No endpoint force or contact mean is replaced.

The target's reserve conditions 2,1,1 therefore imply the three geometric
inequalities just reviewed. The contradiction applies to endpoints of
arbitrary true degree, including endpoints with other blocks or positive
attachments. Additional physical contact at an internal body is allowed
if its force is zero; an additional positive edge is not allowed, because
it would violate the stated true degree. The source states this boundary
correctly. Neither planarization nor any generic normal avoidance is
needed for this geometric application.

For an entire positive C7 with exactly three loaded bodies, the three
unloaded runs have total size four. Every run has length at most two;
two length-two runs would share one loaded endpoint and have two distinct
other endpoints, contradicting the complete matching theorem. Thus the
only run pattern is (2,1,1). The long run has reserve two, and both short
runs have reserve one or sqrt(2), so the new theorem covers all four
short-run side/diagonal choices. All original endpoint circle masks,
individual zero coefficients, shared-side means and two remaining
physical squares are retained.

The same existing matching argument already excludes three-load simple
cycles on at least eight vertices. Consequently the source correctly
excludes **all simple positive components with exactly three positive
circle-loaded bodies and at least seven bodies**. It does not rely on
proper loaded concurrence, and it does not claim that an arbitrary
seven-body block is a simple cycle or has this load count.

## 8. Dependency identities and adoption boundary

| Exact operative source | SHA256 | Scope checked |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete Sections 5--6: actual two-force width and full square-ended channel identity |
| PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md | ec8be96131806c998d8a768526d2deb644c28be72559d34e033c8d07d917ffab | Complete Sections 1--2: common actual application line, reserve and width alternatives |
| LONG_CHANNEL_ENDPOINT_MATCHING.md | 38fa41694cc24fcbe7ac13bc64481323117bcf9d283832a9ec95049cc265cf59 | Entire source: all physical center matching and complete three-load run cover |

The standalone cover is proved within the target source and does not
consume these stress inputs. Its channel and C7 conclusions consume
them only at the exact scopes above. The inherited existence and common
selection of a chosen minimizing certificate remain separate global
prerequisites; this review adds no claim about G4.2.c.

No original coarse parent, fine identifier or count changes in this
review. The full n=9 lower bound and equality classification remain open.
No Lean compilation, CI, pose search, numerical mesh, remote mutation,
or packing certificate is used. The Fraction arithmetic above checks
the printed exact rational comparisons, not a finite set of poses.
