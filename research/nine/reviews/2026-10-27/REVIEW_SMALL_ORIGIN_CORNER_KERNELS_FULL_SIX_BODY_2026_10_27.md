# Independent full review of the small-origin-corner contact kernels

Date: October 27, 2026.
Reviewer: six-body-core independent review.

**Verdict: PASS for all stated geometric and two-force kernels.** I read the complete new `GENERAL_SMALL_ORIGIN_CORNER_CONTACT_KERNELS.md`, SHA256 `b977be65217728c0363e8bab030bdb3d11b1b8ef75cc32d295a8337c4ea01477`, and its complete operative dependency `ROOTED_SMALL_ORIGIN_CORNER_TWO_BOUNDARY_NEIGHBORS.md`, SHA256 `6ebda6299f692af6380ad36b98420aeb3155cf95a6b586e1df3848807d4cf467`.

The actual H contains O closed and has a real vertex P of norm below 1/40. In its inward axes H=[−a,1−a]×[−b,1−b], with a,b nonnegative and below 1/40. The signs are essential: neither source is exported to a small corner of an origin-free square. The statements concern original physical contact features and, where used, the two explicitly identified original forces. They impose no reduced degree or incomplete equilibrium at H.

## 1. Complete dependency and physical feature cover

The 6eb source's center bound follows from the actual farthest-corner inequality with strict reserve 31/57600. Its physical boundary-center bound exceeds 183/100 in squared norm already at the exact critical radius; its contact-point/circumradius bounds do not depend on positive circle weights.

I checked the complete wall calculation at height 39/40. Both square tilt signs are included. The width screen forces the small projection s<1/9, and the two upper-far-corner bounds have positive coefficients and constant excess 43/6400 over 1105/256. Reflection gives the lower-center bound. It needs no boundary hypothesis on that wall-contained unit.

For a strict southeast H contact, the actual contact-radius expansion gives the center x bound 10823/9600>9/8, and the real circumradius gives y>−11/15. The full neighbor feature cover then gives y<3/20. At a neighbor vertex its inward right-angle sector avoids H's northwest sector; either both inward edges have nonnegative x, which fails the far-corner containment bound, or both have nonpositive y, which immediately puts the center below zero. At a neighbor side interior the actual slider is retained, and the specified true corner violates containment if the center height is at least 3/20. Side endpoints belong to the vertex case.

The East axis uses the complete wall bound; the South axis uses physical boundary-center radius and the actual contact coordinate to choose the positive-x branch. Coordinate interchange covers Northwest and the remaining two axes. The small Southwest corner cannot belong to a boundary unit by its point-radius floor. The far Northeast corner has the explicit outward-unit-segment contradiction. Thus all actual separating normals, owners, physical circle masks and contact endpoints are covered by the two stated center rectangles.

Each rectangle has squared diameter 2689/2880<1, so it contains at most one actual unit center. This is a genuine physical statement and does not count only positively stressed or positively weighted corner contacts.

## 2. New opposite-corner and boundary-neighbor conclusions

For a minimum-support point z of any actual unit in inward unit direction n, z+n belongs to that same unit. At an own side it is the point one unit across; at a vertex the two nonnegative own components of n are at most one. This covers the normal-cone endpoints without changing n.

At the opposite H corner W=(1−a,1−b), a strictly exposing normal has both inward-axis components positive. The actual neighbor would contain W+n, whose squared radius is at least 2(39/40)²+1+2(39/40)=1105/256+3423/6400. Thus no actual neighbor, boundary or clear, can use that strict opposite-corner normal.

For a boundary center in the Southeast rectangle, x−y<=1 would imply 1/8<y<3/20 and x<23/20. Its squared radius would then be below 269/200, contradicting the already proved lower bound 183/100, with reserve 97/200. Hence x−y>1. In the Northwest rectangle, y−x>1. Any two distinct boundary neighbors must occupy the two different rectangles; their center difference has dot product greater than two with (1,−1), and therefore norm greater than sqrt(2). A real common contact of two units bounds their center distance by sqrt(2). Thus two distinct physical boundary neighbors of H cannot physically touch each other.

This conclusion permits two neighbors, one in each rectangle, with mandatory noncontact. It does not silently strengthen the theorem to at most one neighbor.

## 3. Exact two-force and cone-extraction scope

For two original positive forces mu*f and nu*g, if f belongs to the actual outward cone at P and their sum is strictly negative along both outward own axes, then g must be strictly negative along both of those axes. It would strictly expose the opposite H corner, already excluded. This uses no full equation or true-degree assertion at H; any other actual H forces may remain arbitrary. Both resultant signs must be strict, as the source states.

For the additional cone-extraction lemma, O is open in H, and the real contact has 0<h_H(f)<=epsilon. If f is H-owned, either far axis has support at least 39/40>epsilon; f is therefore one of the actual axes at P. If f is not H-owned, it strictly exposes its actual vertex p. The extra norm bound |p|<3/8 identifies p with P, because every other H vertex has norm at least 1−|P|>39/40. An endpoint-valued mean on an H-owned side stays in the first case. No incident normal is substituted for the original contact normal.

## 4. Limits and validation boundary

The exact critical radius, closed-origin side/vertex endpoints, actual shared-side means, both owners and zero individual circle weights are retained. The new geometric kernel is complete at its stated domain. It does not by itself close an original graph family, prove a statement for an origin-free small corner, or supply a missing positive force or concurrence premise.

Both mathematical sources were read in full; their elementary inequalities and entire feature scopes were independently checked. The original physical-packing setup is inherited. No Lean compilation, CI, numerical pose, remote operation or shared-ledger edit occurred.

