# n=9: exact radial-pocket capacities at squared radius 17/4

**Status:** complete hand arguments for the stated geometric pockets; independent audit and Lean verification pending. These are all-angle statements, not angle-grid checks. They will be applied to a full finite contact-type subcase of TREE.02.

Put q0=17/4. For a unit direction e, let S(e) be the radial side-normal unit square

    S(e) = { t e + u Je : 1 <= t <= 2, -1/2 <= u <= 1/2 }.

Its center is (3/2)e and its two outer vertices lie on the circle of squared radius q0. All extra squares below lie in the same closed disk, have arbitrary orientations, and are physically interior-disjoint from the fixed obstacles and each other.

## 1. Universal center bound and radial terminal screen

Every unit-square center has norm <=3/2, by the exact farthest-corner bound

    q0 >= |c|^2+1/2+|c|.

Distinct centers are at distance >=1, using their disjoint open radius-1/2 inscribed disks.

**Lemma P1.1 (outer-face screen).** If T is another unit square disjoint in interior from S(e), then every point of T satisfies e.x<2.

*Proof.* Its center c has e.c<=3/2<2. If some p in T has e.p>2, the segment from c to p crosses the chord e.x=2 at an interior point of the containing disk. That crossing has |Je.x|<1/2. Points of the segment immediately before the crossing belong to int(T) and int(S(e)), a contradiction.

If e.p=2 with |Je.p|<1/2, the same segment argument applies. The only remaining possibilities are the two outer circle vertices of S(e). Two interior-disjoint unit squares contained in a circle cannot share a point of that circle: such a point must be a vertex of each, and the two disjoint right-angle tangent cones would have to fill the inward tangent half-plane exactly, requiring a square edge along the circle tangent. A positive-length tangent edge cannot lie in the disk. Thus this remaining possibility is also impossible. QED.

Suppose now a central square has 0 as a vertex and one of its side segments is [0,e], while S(e) is present.

**Corollary P1.2 (no crossing of the whole positive ray).** The interior of any other square T avoids the ray {t e:t>=0}. Its portion 0<=t<=1 is blocked by the central square: an open ball around a point on that edge intersects the central square interior. The portion 1<=t<=2 is blocked by S(e), and t>=2 is excluded by Lemma P1.1. At t=0 the same open-ball argument applies.

Consequently, between two such screened rays with opening g<=pi, an extra square whose center is strictly inside that angular sector is **entirely contained in its closed wedge**. Its connected interior cannot cross either boundary ray; closure handles its boundary points. This conclusion is derived from physical obstacles, not assumed coordinate separability.

## 2. A right-angle pocket has exactly one possible unit square

**Lemma P2.1.** A unit square T contained in the first quadrant, contained in D_q0 and interior-disjoint from S((1,0)) and S((0,1)) must equal [0,1]^2.

*Proof.* Write its center (x,y), x,y>=0. Its inscribed half-radius disk avoids both fixed rectangles. The elementary center-region calculation of TREE_FINITE_COMPLETIONS.md, Section 1.1, uses only these two positive-axis obstacles and gives the alternatives

    0<=x,y<=1/2,  or  x>=1 and y>=1.

For completeness, if x>1/2,y<=1/2 the distance to S((1,0)) is <1/2. If both exceed 1/2 but one is >=1 and the other <1, the corresponding terminal is again closer than 1/2. If both lie between 1/2 and 1, put u=x-1/2,v=y-1/2. Avoidance would require u^2+v^2>=u and >=v, whereas u^2+v^2<(u+v)/2<=max(u,v).

The diagonal alternative is excluded using the actual square, not only its center. After a square symmetry and, if needed, exchanging coordinates, write its side axes as (a,b),(-b,a), a>=b>=0, a^2+b^2=1, and put h=(a+b)/2,k=(a-b)/2. Since x,y>=1 and |c|<=3/2, all square coordinates lie strictly between zero and two. Its leftmost vertex (x-h,y+k) has y+k>=1. Avoiding S((0,1)) forces x-h>=1/2. The limiting equality y+k=1 is covered by interior points approaching that vertex from above. The upper-right vertex then has squared radius at least

    (1/2+a)^2+(1+h)^2
      = 3/2+(2a+b)+(a^2+ab/2) > 17/4,

because

    2a+b-2 = b(1+a-2b)/(1+a) >= 0,
    a^2+ab/2-3/4 = (a-b)(a+3b)/4 >= 0,

and their equality conditions b=0 and a=b cannot both hold. Contradiction.

Therefore x,y<=1/2. Since T lies entirely in the first quadrant, both center coordinates are at least its equal coordinate halfwidth h>=1/2. Hence x=y=h=1/2, forcing axis alignment and T=[0,1]^2. QED.

## 3. No unit square fits an acute screened pocket

**Theorem P3.1.** Let two terminal rays make an opening 0<g<=pi/2, with S(e_1),S(e_2) fixed. An extra unit square T contained in their closed wedge and disjoint from both terminals exists only if g=pi/2. In that case it is the unique origin-vertex unit square filling the right-angle wedge.

*Proof.* Use the angular bisector as x-axis and write e_1,e_2 at angles +/-alpha, alpha=g/2<=pi/4. Widen the two rays to +/-pi/4, keeping T fixed and replacing the terminal squares by S at the widened rays.

T remains inside the wider wedge. It also remains disjoint in interior from each widened terminal. To see this, take any p in int(T) and consider the upper terminal. Its angular distance delta from the original upper ray and delta' from the widened one satisfy

    0<=delta<=delta'<=pi/2.

Thus its radial projection on the old ray is >= its projection on the new ray, and its absolute tangential projection on the old ray is <= that on the new ray. Lemma P1.1 also gives old radial projection <2. If p were in the widened terminal interior (new radial projection between 1 and 2 and tangential magnitude <1/2), it would therefore be in the original terminal interior. This contradicts physical disjointness. The lower terminal is symmetric.

Apply Lemma P2.1 after rotating the widened frame: T must be the unit square with vertex 0 filling the full right-angle wedge. It cannot be contained in an acute original wedge. At g=pi/2 Lemma P2.1 gives the asserted unique square. QED.

No movement of the packing is claimed: widening is a comparison with a pair of obstacles that cannot newly intersect the fixed T.

## 4. A moderately obtuse screened pocket holds at most two squares

**Theorem P4.1.** Suppose

    pi/2 <= g <= 2 arctan(2).

Let S(e_1),S(e_2) be the radial terminals on its two boundary rays. Then at most **two** independently oriented unit squares can lie entirely in that wedge, in D_q0, physically disjoint from both terminals and each other.

*Proof.* Let alpha=g/2, c=cos(alpha), s=sin(alpha). Then

    pi/4 <= alpha <= arctan(2),  s>=c>0.

Use the bisector x-axis; the boundary rays have directions (c,+/-s). The inward unit normals are (s,+/-c).

### 4.1 Every extra center has x>=3/(2 sqrt(5))

For any extra square with center (x,y), its containment in the wedge implies

    2 s x >= H((s,c))+H((s,-c)),

where H is its centered support function. By quarter-turn symmetry and reflection, write its side axes through a>=b>=0, a^2+b^2=1. The support sum is

    s a + max(s b,c a).

If s b<=c a, then a>=s and the sum is a(s+c)>=s(s+c). If s b>=c a, then b>=c,a<=s and the sum is s(a+b)>=s(s+c). The last comparison follows from

    (a+b)-(s+c)=(b-c)*(1-(b+c)/(a+s))>=0,

since a>=b and s>=c. Consequently x>=(s+c)/2. For s/c in [1,2], sc>=2/5, so s+c>=3/sqrt(5). Thus

    x >= m := 3/(2 sqrt(5)).

### 4.2 Every extra center satisfies |y|<5/9

Suppose y>=5/9. In the upper terminal's radial/inward-tangential coordinates put

    a_0=c x+s y,  b_0=s x-c y.

Because the square is wholly below the upper ray, b_0>=1/2. Fix this y and vary x on its possible interval

    x_min=(1/2+c y)/s <= x <= x_max=sqrt(9/4-y^2).

At x_min, b_0=1/2 and a_0=(y+c/2)/s>1/2. The center-radius bound gives a_0<=sqrt(2)<2 there. Hence its distance to the upper terminal rectangle [1,2]x[-1/2,1/2] is strictly below 1/2.

At x_max, b_0<1. Indeed b_0 increases with alpha and decreases as y increases, so its maximum in the stated domain is bounded by

    (sqrt(629)-5)/(9 sqrt(5)) < 1.

For an entirely rational check of the strict comparison, sqrt(629)<251/10 follows from 62900<63001, giving the upper bound 67/(30 sqrt(5))<1 since 4489<4500. Here b_0>=1/2 and a_0^2+b_0^2=9/4, so 1<a_0<2. Its terminal distance is b_0-1/2<1/2.

Squared distance to a convex rectangle is convex on a line (here it is the explicit sum max(1-a_0,0)^2+(b_0-1/2)^2). Both interval endpoints have squared distance <1/4, hence so does every intermediate center. The extra square's inscribed half-radius disk would meet the terminal interior. Contradiction. Reflection across the bisector excludes y<=-5/9.

### 4.3 Two small center boxes finish the count

Every additional center lies in

    [m,3/2] x (-5/9,5/9).

Split this box at y=0, assigning boundary points to one side. Each half has squared diameter at most

    (3/2-3/(2 sqrt(5)))^2 + (5/9)^2 < 1.

The exact comparison reduces to 1627/810 < 9/(2 sqrt(5)), whose squared sides compare as

    20*1627^2 = 52942580 < 53144100 = 81*810^2.

Distinct physical square centers are at distance >=1, so each half holds at most one. At most two squares fit the wedge. QED.

## 5. Minimum separation between two radial terminal directions

**Lemma P5.1.** Distinct physical S terminals have minor angular separation at least beta=2 arctan(1/2).

*Proof.* Express their directions as +/-theta around their bisector, theta=beta'/2. If tan(theta)<1/2, each terminal's vertical center magnitude is (3/2)sin(theta), smaller than its vertical halfwidth (sin(theta)+cos(theta))/2. Therefore its interior crosses the bisector line. The two squares are mirror images across that line and have the identical positive-length interior section there, giving physical overlap. Thus beta'>=2 arctan(1/2). QED.

In particular, for two complementary origin-cone gaps whose angles sum pi, if all four endpoint terminals are distinct and the smaller gap is g<=pi/2, then g>=beta and the larger gap is at most pi-beta=2 arctan(2). The acute/right and moderately obtuse capacities above apply to the entire angle range without subdivision.

## 6. Scope and validation boundary

These pocket theorems use actual full-square containment and nonoverlap, not only center separation. The auxiliary center-box constants are exact analytic inequalities, not a mesh over angle/position parameters. The barrier hypothesis must be derived when applying them: a unit square's center lying in a gap does not by itself put the whole square in that wedge.

No universal n=9 lower bound, independent full audit, Lean compilation or CI success is claimed by this manuscript.