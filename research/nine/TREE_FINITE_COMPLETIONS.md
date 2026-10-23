# n=9: close TREE.12 and TREE.04 in the exhaustive six-case tree inventory

**Status:** new hand proofs of full physical completion bounds, allowing arbitrary rotations and oblique separators for every remaining square. Independent audit and Lean verification pending.

**Dependency:** TREE_RADIUS_QUANTIZATION.md proves that, within the declared radius window 79/40<=R<=sqrt(1105)/16, every chosen positive tree component has R^2=17/4 and belongs to one of six origin-incidence cases. This document closes **two complete cases**, not small angular subfamilies. The other four tree cases and the cyclic branch remain open.

Write q0=17/4 and place the disk center at zero. A unit square of center c in this disk satisfies

    |c|^2+|c|+1/2 <= q0,

so its center norm is at most 3/2. Any two physically interior-disjoint unit squares have center distance at least one, because their open inscribed disks of radius 1/2 are disjoint.

## 1. Cardinal cage theorem: four fixed outer squares leave capacity at most four

Let the packing contain the four axis-aligned unit squares centered at

    E=(3/2,0), W=(-3/2,0), N=(0,3/2), S=(0,-3/2).

**Theorem CAGE.** Every additional independently rotated unit square inside D_q0, physically disjoint from those four, has its center in [-1/2,1/2]^2. Hence **at most four** additional squares fit. In particular no ninth square fits this cardinal cage.

### 1.1 The inscribed disk leaves only central and diagonal center regions

By reflections, consider another square center (x,y) with x,y>=0 and x^2+y^2<=9/4. The radius-1/2 inscribed open disk about this center must avoid each outer-square interior.

If x>1/2 and y<=1/2, its distance to E's rectangle [1,2]x[-1/2,1/2] is <1/2; this is impossible. The symmetric case y>1/2, x<=1/2 is also impossible.

Suppose x,y>1/2. If x>=1 but y<1, its distance to E's rectangle is y-1/2<1/2. If y>=1 but x<1, use N. If both x,y<1, put u=x-1/2 and v=y-1/2, so 0<u,v<1/2. Distances at least 1/2 from the two inner rectangle corners (1,1/2) and (1/2,1) would require

    u^2+v^2 >= u,   u^2+v^2 >= v.

But u^2+v^2 < (u+v)/2 <= max(u,v), a contradiction. Boundary values x=1 or y=1 are included by the previous rectangle-distance cases.

Therefore every possible center is either in [0,1/2]^2, or in the diagonal region x>=1,y>=1. The other quadrants are symmetric. The diagonal regions must be excluded using the actual square geometry, not just its inscribed disk.

### 1.2 No square center can occupy a diagonal region

Suppose x,y>=1. The center bound gives x,y<=sqrt(5)/2<9/8. A square half-projection width is <=sqrt(2)/2<3/4, so all its points have both coordinates strictly between zero and two.

By square quarter-turn symmetry and, if needed, exchanging x and y (which preserves the cardinal cage), choose unit side axes

    u=(a,b), v=(-b,a),  a>=b>=0, a^2+b^2=1.

Set h=(a+b)/2 and k=(a-b)/2. The leftmost vertex is

    z_L=(x-h,y+k).

It has 1<=y+k<2. Avoidance of the upper outer square N=[-1/2,1/2]x[1,2] forces x-h>=1/2. For strict y+k>1 this follows immediately from physical nonoverlap. If y+k=1, then y=1,k=0 and the square has interior points arbitrarily near z_L with vertical coordinate >1, giving the same conclusion. Thus

    x>=1/2+h.

The upper-right vertex is z_U=(x+k,y+h). Both coordinates are positive, so

    |z_U|^2 >= (1/2+a)^2+(1+h)^2
             = 3/2+(2a+b)+(a^2+ab/2).

The following exact factorizations finish the estimate:

    2a+b-2 = b(1+a-2b)/(1+a) >= 0,
    a^2+ab/2-3/4 = (a-b)(a+3b)/4 >= 0.

The first can be an equality only when b=0; the second can be an equality only when a=b. They cannot both be equalities. Therefore

    |z_U|^2 > 3/2+2+3/4 = 17/4,

contrary to circle containment. This excludes all four diagonal center regions.

### 1.3 At most four remaining bodies

Every additional center lies in [-1/2,1/2]^2. Divide this box deterministically into its four sign quadrants, assigning axis points to the nonnegative side. Each cell has Euclidean diameter at most sqrt(1/2)<1. Pairwise center distances are at least one, so each cell holds at most one center. At most four additional squares fit. QED.

This theorem is sharp as an eight-square capacity: the four central axis-aligned squares centered at (+/-1/2,+/-1/2), together with the four outer cardinal squares, fit D_q0. No common-coordinate-separability premise was used for any additional square.

## 2. Central 2x2 block theorem

**Theorem BLOCK.** Four unit squares forming the central solid block [-1,1]^2 inside D_q0 can have at most four additional physical unit squares, regardless of their orientations. The only possible additional centers are (+/-3/2,0),(0,+/-3/2), and their frames must be axis-aligned. Hence the total is at most eight.

*Proof.* Let c=(x,y) be any additional center. Its norm is <=3/2. Its inscribed open radius-1/2 disk cannot intersect the interior of [-1,1]^2: the four internal seams cannot fill a nonempty open intersection. Thus dist(c,[-1,1]^2)>=1/2.

If |x|<=1 and |y|<=1, the distance is zero. If |x|>1 and |y|<=1, the distance condition forces |x|>=3/2, and the center-radius bound then forces |x|=3/2 and y=0. The vertically exchanged case is identical.

If |x|,|y|>1, the center-radius bound gives each |x|,|y|<sqrt(5)/2<9/8. Hence

    dist(c,[-1,1]^2)^2=(|x|-1)^2+(|y|-1)^2<1/32<1/4,

a contradiction. Only the four listed centers remain.

At any one of those centers, |c|=3/2. Exact containment requires equality in

    q0 >= |c|^2+1/2+|c.u|+|c.v| >= |c|^2+1/2+|c|=q0.

Thus one of c.u,c.v vanishes: a square axis is parallel to c, forcing the stated common coordinate alignment. Distinct squares cannot share a center because their inscribed disks would overlap. Therefore at most four additional bodies exist. QED.

## 3. Close the complete TREE.04 case

In TREE.04 all four unloaded bodies contain zero at vertices. Their four disjoint right-angle tangent cones exhaust the full angle 2*pi. They must therefore be consecutive coordinate quadrants in some rotated frame. Since the bodies are unit squares, their union is exactly [-1,1]^2 in that frame.

Theorem BLOCK applies to **every** physical completion, including all loaded and unstressed bodies outside the core. At most eight unit squares fit D_q0. Therefore:

> **TREE.04 CLOSED hand:** no nine-square packing at the target-window minimizing radius can have the selected positive tree component in case (s,v)=(0,4).

This is a whole-case exclusion with no angular subdivision.

## 4. Close the complete TREE.12 case

In TREE.12 one unloaded body has zero in the relative interior of a side, and two unloaded bodies have zero at vertices. Their tangent-cone angles pi+pi/2+pi/2 exhaust 2*pi. After rotation/reflection the side body is

    H=[-alpha,1-alpha] x [0,1], 0<alpha<1,

and the two vertex bodies are exactly [-1,0]x[-1,0] and [0,1]x[-1,0]. All three share the coordinate directions, though H can slide tangentially.

TREE.F2 says every loaded body is an S terminal with inward contact p=e of norm one. On H, the only such radial outward support point is (0,1), because its bottom vertices have norms alpha and 1-alpha strictly below one and its top corners have norms strictly above one. Every positive contact at zero on H has downward normal. H's force equilibrium therefore requires a loaded S terminal at (0,3/2).

On either lower vertex body, the possible unit-radius radial outward contacts are only its two axial endpoints. Consequently every loaded terminal of the tree is one of the four cardinal outer squares in Theorem CAGE.

Sum the force balances over the component. Internal pair forces cancel. Each S terminal's equal circle-vertex weights have mean 2e, so a positive total circle weight lambda contributes 4 lambda e. A positive weight in one cardinal direction requires a positive weight in its opposite direction. The upward terminal forces the downward terminal to occur.

If no horizontal terminals occurred, the component would have exactly two loaded bodies. The completed two-loaded tree theorem in SMALL_TREE_STRESS_CORES.md says that such a component consists of a four-square path with **exactly two** unloaded bodies. TREE.12 has three unloaded bodies, a contradiction. Therefore at least one horizontal loaded direction occurs, and force balance requires its opposite. All four cardinal outer squares are present.

Theorem CAGE permits at most eight total physical squares in the disk. Thus:

> **TREE.12 CLOSED hand:** no nine-square packing at the target-window minimizing radius can have the selected positive tree component in case (s,v)=(1,2).

Again all unstressed completions, arbitrary angles and oblique separators are included.

## 5. Live finite tree-case ledger

All six cases are defined and proved exhaustive in TREE_RADIUS_QUANTIZATION.md.

| Case | Completion status after this manuscript | Reason or remaining obligation |
|---|---|---|
| TREE.20: two side bodies | OPEN | All staggered four-square paths plus five other squares; only flat row closed previously |
| TREE.11: side + vertex | OPEN | Include nonaligned central frames and arbitrary physical completion |
| TREE.12: side + two vertices | **CLOSED hand** | Four cardinal loaded terminals; CAGE capacity <=8 |
| TREE.02: two vertices | OPEN | Include arbitrary relative cone angle and all loaded/free bodies |
| TREE.03: three vertices | OPEN | Include arbitrary gap angles and all loaded/free bodies |
| TREE.04: four vertices | **CLOSED hand** | Central 2x2 block; BLOCK capacity <=8 |

The positive graph **with a cycle** is not in this tree table and remains a separate global branch. No complete n=9 lower bound, Lean proof, CI success or independent full audit is claimed.