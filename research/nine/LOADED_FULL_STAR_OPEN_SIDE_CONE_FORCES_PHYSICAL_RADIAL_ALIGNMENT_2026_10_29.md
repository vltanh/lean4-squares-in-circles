# An entire loaded star inside one open side cone forces physical radial alignment

Date: October 29, 2026 UTC. Author: root continuation.

Status: complete proposed hand theorem, awaiting separate independent review. This is an arbitrary-degree strengthening of the unique-corner torque step in the new two-path theorem. It needs neither an axis-owned incoming force nor a degree-two equation. Its hypothesis concerns every positive force of the actual star.

## 1. Exact full-star theorem

Let C be an actual closed unit square contained in the disk of radius R about O=0, where R>1/sqrt(2). Give C its actual own orthonormal axes e,f, with det(e,f)=1. Every actual positive pair-force term at C is

    -mu_i n_i at P_i,     mu_i>0,
    P_i an actual minimum-n_i support point of C.

P_i may be an endpoint or the original mean anywhere on its actual shared segment. Keep all positive pair terms, at any finite true degree. Keep every physical circle corner Z_j and every original nonnegative circle coefficient c_j, with sum_j c_j>0. Require the full original equations

    F := sum_j c_j Z_j = sum_i mu_i n_i,
    sum_i det(P_i,-mu_i n_i) = 0.

The second identity is torque about the actual disk center: each circle force is radial and has zero such moment. The factor two in the repository's circle-multiplier convention is absorbed into c_j. This changes no geometric point or relative pair weight.

Assume, for every positive pair term, the strict open-side-cone inequality

    a_i := n_i.e > |n_i.f| =: |b_i|.                 (1)

The n_i are original incoming directions, so the original outward contact normal of C is -n_i. No direction is selected afresh.

**Theorem.** C has exactly two physical circle corners, and its entire actual square is

    C = [A-1,A] e + [-1/2,1/2] f,
    A = sqrt(R^2-1/4)>1/2.                          (2)

Its two physical circle corners are A e +/- f/2. Their individual coefficients remain arbitrary nonnegative values consistent with the original equations; neither is assumed positive. No unique-circle-corner mask, no radial frame perpendicular to e, and no origin-centered four-corner mask survives.

The conclusion includes the whole physical square and all its actual applications. It is independent of the number, degrees, loads, positions or mutual contacts of the neighboring squares.

## 2. Elementary complete physical-circle classification

Write C=c+[-1/2,1/2]e+[-1/2,1/2]f, with c=x e+y f. Its farthest corner norms maximize the two coordinate squares independently. The set of farthest corners has:

* one corner if x and y are both nonzero;
* two adjacent corners if exactly one of x,y is zero;
* four corners if x=y=0.

Positive circle load makes the maximum corner norm equal to R. Thus every farthest corner is physically on the circle, whether its individual coefficient is positive or zero. The four-corner alternative has R=1/sqrt(2) and is excluded by the stated radius hypothesis. Hence C has either one or two physical circle corners. A side-interior circle contact supplies no additional mask: the squared norm along a nondegenerate side is strictly convex, so an interior side point cannot have norm R while both endpoint norms are at most R.

By (1) and positivity,

    F.e = sum_i mu_i a_i > sum_i mu_i |b_i|
        >= |sum_i mu_i b_i| = |F.f|.                (3)

In particular F.e>0 and F is nonzero. There must be at least one positive pair term: otherwise F=0, whereas the farthest-corner classification at R>1/sqrt(2) puts all physical circle corners in a common strict radial half-plane and their nonzero positive sum cannot vanish.

## 3. A unique physical corner contradicts the complete torque

Suppose there is exactly one physical circle corner Z. Then F=c_0 Z for c_0>0. In the actual own coordinates let

    C=[u,u+1] x [v,v+1],
    n_i=(a_i,b_i).

If F.f=0, then Z.f=0. One of the other two own-coordinate endpoints has absolute f-coordinate at least one, so the corner with the same e-coordinate and that f-coordinate has strictly larger norm than Z. This contradicts Z being a physical farthest corner. Thus F.f is nonzero.

Reflect f and the entire coordinate chart if necessary, so F.f>0. The force sum has F.e>0 as well. Since Z is the unique farthest corner and has positive e and f coordinates, independent farthest-coordinate maximization makes it the upper-right corner:

    Z=(u+1,v+1).

Compute each complete original pair moment about this same actual Z. There are three support types:

| Original direction | Actual support/application | Moment about Z |
| --- | --- | --- |
| b_i>0 | P_i=(u,v) | mu_i(b_i-a_i)<0 |
| b_i<0 | P_i=(u,v+1) | mu_i b_i<0 |
| b_i=0 | P_i=(u,t_i), v<=t_i<=v+1 | mu_i(t_i-v-1)<=0 |

The strict first inequality is exactly (1). The last row retains the full original mean and both endpoints. Every pair moment is nonpositive. Since F.f=sum_i mu_i b_i>0, at least one b_i>0, so at least one moment is strictly negative. The unique circle force acts at Z and has zero moment about Z. Full force balance permits the original torque equation to be taken about Z, but its terms now have strictly negative sum. This is a contradiction.

The F.f<0 case is its full reflection, which reverses all moment signs together and gives the same contradiction. This excludes every unique physical circle mask at any actual positive degree. No coincidence, concurrency or two-application hypothesis has been introduced.

## 4. The two physical corners have exactly the claimed radial direction

Only two adjacent physical circle corners remain. By Section 2, one center coordinate is zero. If c.e=0, the corners are

    +/-e/2 + sigma A f,
    A=sqrt(R^2-1/4)>1/2,
    sigma in {-1,1}.

For their unchanged nonnegative coefficients,

    |F.f| = A sum_j c_j > (1/2)sum_j c_j >= |F.e|,

contradicting (3). Thus c.f=0. The two physical corners instead have the form sigma A e +/-f/2. Since F.e>0, sigma=+1. The square's center is (A-1/2)e, proving its entire position (2).

This argument retains either individual zero coefficient. It also identifies the physical two-corner mask before any equation is written using radial-corner coordinates.

## 5. Useful exact full-star consequences

From (2) and the unchanged circle coefficients one obtains

    |F.f| <= (F.e)/(2A).                            (4)

This is a bound on the actual full resultant, not on each individual force. It does not require equal circle weights.

Let d=A-1 and retain the original pair applications on the actual minimum supports. In the radial frame (2), the original center-torque equation is exactly

    sum_{b_i>0} mu_i (d b_i+a_i/2)
  + sum_{b_i<0} mu_i (d b_i-a_i/2)
  - sum_{b_i=0} mu_i a_i t_i = 0,
    -1/2<=t_i<=1/2.                                (5)

Thus, when R>=sqrt(5)/2 so d>=0, the entire no-axis feature in which all b_i have the same strict sign is impossible. Every summand in (5) then has that strict sign. At an actual b_i=0 contact its real mean t_i must be retained; the no-axis corollary is not extended across such a contact without (5).

The theorem also recovers the loaded-two-endpoint step of the two-path argument: if one incoming direction is the own axis e and the other has dot product with e greater than 1/sqrt(2), both satisfy (1). The current theorem needs no such exact-axis contact and handles every original positive degree at once.

## 6. Boundaries and proof provenance

The strict inequality (1) is necessary for this statement. A unique-corner square centered on its own diagonal may support a radial diagonal load balanced at its opposite vertex, on the 45-degree boundary. No boundary case of (1) is claimed here. Radius R=1/sqrt(2) is also excluded explicitly because an origin-centered square has four physical circle corners.

Every actual force term must satisfy (1). Dropping a higher-degree star's other forces to make this cone condition hold would invalidate the theorem. No placement of any neighboring or completion unit follows solely from the radial conclusion.

The proof is elementary and complete above. The physical force/torque and mean convention agrees with `PHYSICAL_CONTACT_STRESS.md`, SHA256 `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5`. The construction was motivated by Section 3 of the separately authored `TRIANGLE_TWO_PATH_LENGTH_ORDER_AND_COMPLETE_D02_L014_EXCLUSION_2026_10_29_CONTINUATION.md`; the present arbitrary-degree, no-axis-premise theorem is a new root construction and needs its own independent review.

This source changes no original flag or count. It creates no numerical or computational packing certificate. The original global sharpness, equality and certificate-selection obligations remain separate.
