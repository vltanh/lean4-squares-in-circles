# Triple caps need an outer center; no-double S2--S4 outer-center pruning

## Scope

Consider eight independently oriented unit squares with
pairwise disjoint open interiors in D_R, R²<=9789/2500.
The analytic central-square theorem supplies one unique
central square C. "Whole cap" refers to entire-square
containment beyond one signed side of C, not center signs.
An **outer center** has Euclidean norm >=1, and k is
the number of outer centers among all eight squares.

We prove a new cap center lemma and sharpen the
coarse outer-center classifications of the **all-seven-
single-side** branches S2,S3,S4 in
SINGLE_SIDE_SEVEN_BRANCHES.md. In those branches
every exterior square belongs to exactly one signed
central side: squares counted on perpendicular
sides are genuinely different labels.

None of the statements assumes a square frame or
an actual contact graph.

## 1. Three squares in any nonnegative cap cannot all have inner centers

**Triple-inner cap lemma.** Three pairwise interior-disjoint
unit squares cannot all lie in a closed half-plane
`n dot x>=h>=0` while all three of their centers
have Euclidean norm <1.

**Hand proof.** Let p_i be a square center with
r_i=|p_i|<1. Every unit square has half-width at
least 1/2 along the unit direction n. Therefore

    n dot p_i>=h+1/2>=1/2.                           (1)

In particular p_i is nonzero. Its polar direction
relative to n has signed angle theta_i satisfying

    cos(theta_i)=(n dot p_i)/r_i
       >=(1/2)/r_i>1/2.

Thus every center direction belongs to the
**open** angular sector

    -pi/3<theta_i<pi/3,                              (2)

whose total width is 2*pi/3.

On the other hand, any two of the center radii
r<=s<1 and smaller angular separation delta<=pi/3
would satisfy

    |p-q|²=r²+s²-2*r*s*cos(delta)
          <=r²+s²-r*s
          =s²-r*(s-r)<=s²<1.                        (3)

But the two open inscribed radius-1/2 disks
belonging to distinct packed unit squares
are disjoint. Their centers must therefore
have distance >=1. Hence *every pair* of
three center directions with norms <1
has angular separation strictly greater
than pi/3.

Ordering three rays inside sector (2)
would give two successive gaps, each
strictly greater than pi/3, so their
total span would exceed 2*pi/3.
That contradicts (2), proving the lemma. QED.

Consequently every side serving three
complete exterior squares includes at
least one square whose center norm is >=1,
regardless of the side's offset and
every square orientation.

## 2. The complementary two-square cap fact

Recall the elementary lemma in
HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md:

* If a complete unit square belongs to a cap of
  signed outward offset h>=1/2, its center has
  radial norm >=1, since n dot p>=h+1/2>=1.
* If two complete squares belong to a cap
  h>=2/5, **at least one** has center norm >=1.

For the second claim, if both centers had norm<1,
their n projections would lie in [9/10,1)
and their perpendicular projections in
(-sqrt(19)/10,sqrt(19)/10). Their distance
squared would be <1/100+19/25=77/100<1,
contradicting the inscribed disks.

We use these statements only for two-square
and one-square **whole cap memberships**.
They do not hold merely from center signs.

## 3. S2: a central strip forces k>=4

The all-single-side S2 type has opposite-side
pair populations

    (3+0, 2+2).

Let t be the signed central-center coordinate
on the **2+2** axis. Its two side offsets
are 1/2+t and 1/2-t.

Suppose

    |t|<=1/14.                                      (4)

The more distant cap has offset >=1/2
and therefore contains **two outer centers**.
The nearer cap has offset >=1/2-1/14=3/7>2/5.
Its two squares contribute **at least one
additional outer center** by section 2.
Since the two opposite cap memberships
are disjoint, these are three distinct labels.

The perpendicular 3+0 axis has a triple
whole-square cap. By section 1, at least
one of those three centers is outer.
Because **all seven statuses are single-side**,
this is a fourth distinct exterior square.

Thus

    S2 and |t|<=1/14 => k>=4.                      (5)

In particular the S2/k=3 macro-subcase
is impossible within the entire closed
central band (4). No conclusion is claimed
for the two remaining outer strips
1/14<|t|<5/24.

## 4. S3: a moderate double side forces k>=4

The all-single-side S3 profile consists
of opposite-side counts

    (3+1, 2+1).

The *far singleton* opposite the triple
has outward offset >17/24>1/2, by the
sharp three-square cap bound. Its center
is outer. The triple side contributes
a second, **different** outer center by
section 1.

Let h be the offset of the side serving
**two squares** on the other 2+1 axis.
Suppose

    h>=2/5.                                        (6)

If h>=1/2, both its square centers are
outer, giving two additional labels.
If 2/5<=h<1/2, its two squares contribute
at least one outer center by section 2,
while the *opposite singleton* is in the
side at offset 1-h>1/2 and is outer too.
Either way this axis supplies at least
**two distinct outer centers**.

All status groups are disjoint in the
all-single-side branch. Thus the total
has at least four distinct outer centers:

    S3 and h>=2/5 => k>=4.                         (7)

Consequently the S3/k=3 macro-subcase
requires the strict exceptional condition
h<2/5. It is **not** excluded outright.

## 5. S4: two complementary center-count implications

The candidate-bearing all-single-side S4 type
has opposite-side pairs

    (2+1, 2+2).

Let h be the offset of the side serving
two squares on the **2+1** axis. Let t
be the signed center coordinate on the
other **2+2** axis.

On the 2+2 axis, the more distant cap
has offset >=1/2; both of its squares
have outer centers.

If h>=2/5, the same two-case argument
as section 4 supplies at least **two
distinct** outer centers from the
perpendicular 2+1 axis. Since statuses
are exclusively single-side, these
four labels are different. Hence

    S4 and h>=2/5 => k>=4.                         (8)

If, in addition,

    |t|<=1/14,                                      (9)

the nearer side of the 2+2 axis has
offset >=3/7>2/5 and contributes
a **third distinct outer center** from
that axis. Combined with the two
outer centers from the 2+1 axis,
this yields

    S4, h>=2/5, |t|<=1/14 => k>=5.                (10)

The exact optimized Cantrell construction
belongs to S4, so (8)--(10) are **necessary
conditional center-count restrictions**,
not an exclusion of the entire S4 type.
They do not assert the sharp candidate's
central center coordinates satisfy the
extra bands (6) or (9).

## 6. Summary of actual cleared subcases

The finite taxonomy already allowed
k in {3,4,5,6,7}. The new hand proofs
eliminate precisely these intersections
of status, k, and central offset:

    S2, k=3, |t|<=1/14;
    S3, k=3, h>=2/5;
    S4, k=3, h>=2/5;
    S4, k=4, h>=2/5 and |t|<=1/14.

Separately, HUMAN_TYPE_C_FIVE_OUTER_MINIMUM.md
excludes **all** Type C cases k=3 or k=4,
without a central-offset subcondition.

These are genuine **continuous-region and
outer-center macro-branch** eliminations,
not merely new labels in the status ledger.
The remaining cases still require the
sharp global radius obstruction
R8>=Rhat; no equality proof is claimed.
