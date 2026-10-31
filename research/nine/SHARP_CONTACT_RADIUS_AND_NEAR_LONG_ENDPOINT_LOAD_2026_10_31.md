# Sharp contact radius and a near-long endpoint load theorem

October 31, 2026. Input commit: 8e8413d6abbb29663f70cf5511da45905b678763.

**Status: complete new hand derivation, self-checked; not independently reviewed or formally verified.** The contact theorem is force-free and sharp. The endpoint theorem uses only complete translational equilibrium. Neither assumes nine bodies, planarity, a generic normal, or a particular endpoint degree. No original fine/coarse flag changes.

## 1. An inward unit segment at every support point

Let S be a closed unit square, p a maximum support point in a unit direction n. Then

    p-n belongs to S.                                      (1)

Indeed, write S=c+[-1/2,1/2]u+[-1/2,1/2]v and n=a u+b v, with a^2+b^2=1. If a>0, p's u coordinate is 1/2 and subtracting a keeps it in [-1/2,1/2], because 0<a<=1. If a<0 the same calculation starts at -1/2. If a=0 that coordinate is unchanged. Apply the identical argument to b. This covers vertices, side interiors and both endpoints of a shared side. At a minimum support point, p+n belongs to S.

## 2. A sharp bound for every actual shared point

Let A,B be actual interior-disjoint unit squares in the disk D_R, and p any point of A intersect B. A supporting line separating their interiors passes through p. Let n be its unit normal from A to B. Thus p maximizes n on A and minimizes it on B. By (1), the actual points p-n and p+n lie in the respective squares. Containment gives

    |p-n|^2<=R^2,       |p+n|^2<=R^2.

Taking the larger of these two exact expressions proves

    |p|^2+1+2|p.n| <= R^2.                              (2)

In particular

    |p| <= sqrt(R^2-1).                                 (3)

This holds for every actual common point and every common supporting unit normal there, including a zero-force physical contact and an unchanged shared-side mean. No selected force is needed to choose the separator.

The radius in (3) is sharp. For any R>=sqrt(5)/2 put h=sqrt(R^2-1)>=1/2 and take

    A=[-1,0] x [h-1,h],     B=[0,1] x [h-1,h].

All their corners lie in D_R since |h-1|<=h. Their common point p=(0,h) attains (3). Thus the old universal radius 29/15 is not the sharp contact bound at Q=1105/256; the sharper one is sqrt(849)/16.

### Equality description at a contact

If equality holds in (3), (2) forces p.n=0 and both p-n,p+n lie on the circle. A point of a nondegenerate square on the boundary of a strictly convex containing disk must be a vertex: otherwise it is a nontrivial convex combination of two distinct contained points and lies strictly inside the disk. In the coordinates used in (1), the displacement of length one from p to that circle vertex can reach a square vertex only if n is an own side axis. Hence p too is a vertex, and the two frames agree with n and its perpendicular k.

The two squares extend from p in opposite n directions. Their tangential extensions must both point towards the origin. If one extended by +k, its far corner p+/-n+k would impose 2p.k+1<=0; extension by -k imposes -2p.k+1<=0. Both signs cannot occur. Therefore the squares share a whole unit side ending at p, and |p.k|>=1/2. Conversely the displayed construction realizes precisely this equality geometry, up to a common orthogonal transformation.

This is a two-square contact equality classification, not a classification of nine-square optimal packings.

## 3. Every endpoint of a gap at least 39/20 has a contact-free outward side

Put

    Q=1105/256,     M=91/60.

For every contained unit square S with center c, its farthest corner gives

    |c|^2+|c|+1/2 <= Q,

and M^2+M+1/2-Q=31/57600>0. Thus |c|<M.

Suppose two actual squares A,B in D_R, R^2<=Q, have a unit direction e with

    g_e(A,B):=e.(c_B-c_A)-h_A(e)-h_B(e) >= 39/20,       (4)

where h is the actual projection halfwidth. Write c_A.e=-X_A and c_B.e=X_B. Since h_A,h_B>=1/2 and both center norms are below M,

    X_A,X_B > 39/20+1-M = 43/30,
    h_A+h_B < 2M-39/20 = 13/12,
    h_A,h_B < 7/12.                                    (5)

At A choose its own side axis u directed towards -e with maximal absolute e component, and let v be its perpendicular own axis. Set a=-e.u, b=|e.v|, so a>=b>=0 and a^2+b^2=1. Equation (5) gives

    a+b=2h_A(e)<7/6,
    a-b>sqrt(23)/6>19/24.                              (6)

The last radical comparison follows from 23>361/16. The strict difference also makes the dominant own axis unique.

Every point p on the entire closed outward side c_A+(1/2)u+[-1/2,1/2]v satisfies

    p.e <= -X_A-(a-b)/2 < -43/30-19/48 = -439/240.     (7)

But every actual contact has, by (3),

    |p|<=sqrt(849)/16 <73/40=438/240.                  (8)

The exact squared reserve in the last comparison is

    (73/40)^2-849/256 =91/6400>0.

Thus the entire side in (7), including both corners, is disjoint from every other actual square. The same proof at B gives a contact-free outward dominant side directed towards +e. No square is rotated or moved; the two dominant axes are selected from their actual independent frames.

## 4. Full force-balance consequence

At an endpoint S retain every original positive pair force mu_j n_j, with outward normal n_j from S to its neighbor, and every original nonnegative circle coefficient. Its complete translational equation is

    sum_j mu_j n_j + 2 sum_z lambda_z z=0.             (9)

Let u be the outward own axis of the contact-free side proved above. Any normal n with n.u>0 exposes only that side, including its corners. It cannot be an actual positive contact normal. Consequently n_j.u<=0 for every original positive pair force.

If at least one of these scalar products is strictly negative, their full weighted sum is negative. Equation (9) therefore makes zero total circle load impossible. S has positive circle load.

In particular, under (4), a positive actual contact normal +e at A forces A loaded, and a positive actual contact normal -e at B forces B loaded. More generally any positive contact pointing strictly against that endpoint's dominant outward own axis suffices. Its other degrees, forces and actual applications are unrestricted. The other square in (4) is only a geometric witness and need not be adjacent to the tested endpoint.

This improves the gap-two endpoint theorem in UNIVERSAL_CONTACT_RADIUS_AND_POSITIVELY_LOADED_LONG_CHANNEL_ENDPOINTS_2026_10_30.md to the whole interval g>=39/20. Its original gap-two and true-long-channel callers remain valid. No inference about a short gap or a missing inward force is made.

## 5. Verification boundary

The proof consists of the inward-segment identity, two containment inequalities, the exact farthest-corner bound, and a dot product with the full unchanged force equation. Every rational and radical comparison is displayed. No numerical sampling, symbolic arithmetic program, mathematical script, Lean, Lake or CI was used. This source establishes its own theorems; it does not establish universal chain extraction, the complete nine-square theorem, or a new original gate closure.
