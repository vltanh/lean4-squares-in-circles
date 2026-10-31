# A boundary unit at a small side contains one fixed interior disk

Date: October 27, 2026.  
Author: topology_final.  
Original comparison head: `50c0cd616eb494ade100f055ad518cdbd33c7275`.

**Status: complete fresh physical theorem, pending independent full review.** This source is a new proof with new bytes, not a claimed restoration of the missing older small-side manuscript. It treats every actual square frame, a strict support vertex or the entire support-side interval, both signs of the small support level, every physical circle mask and arbitrary force degree. No force equation, selected normal, shared mean, numerical certificate or upper-radius bound is used in the local theorem.

## 1. Full local theorem

Let K be a physical unit square contained in the origin-centered closed disk D_R and touching its boundary, with

    R^2>=17/4.

Suppose its actual minimum horizontal support is x=h, where

    |h|<=1/60,

and K contains an actual support point

    T=(h,z), 0<=z<=1.

No assumption is made that T is the midpoint, a vertex, a force application rather than an arbitrary physical point, or a prescribed representative of a contact segment. Its actual value is kept.

Put

    F=(h+1/2,5/4).

**Theorem 1.1.** The entire closed Euclidean disk of radius 9/40 centered at F lies in the open interior of K.

In particular F is an interior point of K. The smaller closed radius-1/5 disk is included as well. No degree, circle-force positivity, unique physical circle corner or side-owner hypothesis is required. The point z=0, point z=1 and support endpoints h=+/-1/60 are included in the theorem's domain; a geometrically impossible endpoint may be eliminated by the proof rather than silently omitted.

**Corollary 1.2.** The same conclusion holds if the actual support point initially satisfies -1<=z<=1 and K has at least one physical circle point of positive height. Section 5 proves that these hypotheses force z>0, so Theorem 1.1 applies.

**Corollary 1.3 (whole-strip capacity one).** Every square in the entire family of Theorem 1.1 or Corollary 1.2 contains the same closed disk of radius 5/24 centered at (1/2,5/4) in its open interior. In particular two distinct squares in this family cannot be interior-disjoint, even when their actual support levels h differ.

Indeed the distance between (1/2,5/4) and F is |h|<=1/60, and `5/24+1/60=9/40`. The triangle inequality puts this complete fixed disk inside the disk from Theorem 1.1. The capacity consequence uses no force, common frame, common application point or common mean.

The circle origin is fixed. An orthogonal reflection gives the corresponding maximum-x statement, with F=(h-1/2,5/4), without any translation of the containing disk.

## 2. Every tilted frame: the actual circle corner and two uniform inequalities

If the minimum-x support is a strict vertex, its complete actual frame has the form

    K=T+[0,1]a+[0,1]b,
    a=(c,s), b=(s,-c),
    c,s>0, c^2+s^2=1.

These are the actual upper and lower inward axes. No bound on their angle is assumed.

The point T and both adjacent vertices are strictly inside D_R. Their exact squared norms are

    |T|^2=h^2+z^2,
    |T+a|^2=h^2+z^2+1+2hc+2zs,
    |T+b|^2=h^2+z^2+1+2hs-2zc.

Using |h|<=1/60 and 0<=z<=1, the largest necessary upper estimate among these is

    |T+a|^2<=4+1/30+1/3600=14521/3600<17/4,
    17/4-14521/3600=779/3600>0.

For the lower adjacent corner the corresponding estimate is at most 2+1/30+1/3600, and T is smaller still. A square contained in a disk and touching its circle has a circle vertex, since the squared norm at any convex combination is at most the corresponding convex combination of vertex squared norms. Therefore the actual opposite vertex is on the circle:

    Z=T+a+b=(h+c+s,z+s-c),
    R^2=h^2+z^2+2+2h(c+s)+2z(s-c).             (1)

This is a physical conclusion for the whole initial circle mask. No circle point was selected to suit a force equation.

The horizontal error term has the uniform bound

    E=h^2+2h(c+s)
      <=h^2+2|h|(c+s)
      <1/3600+(1/30)(17/12)
      =19/400,                               (2)

because c+s<=sqrt(2)<17/12.

If z<=3/4, then s-c<1 and (1)--(2) give

    R^2<2+9/16+3/2+19/400
       =411/100<17/4,
    17/4-411/100=7/50>0.

This is impossible. Hence the entire tilted domain satisfies

    z>3/4.                                   (3)

If s-c<=1/2, the whole interval 0<=z<=1 instead gives

    R^2<2+1+1+19/400
       =1619/400<17/4,
    17/4-1619/400=81/400>0.

Consequently

    s-c>1/2.                                 (4)

This also implies s>9/10. If s<=9/10, then c^2>=19/100>(2/5)^2, so c>2/5 and s-c<1/2, contrary to (4). The exact squared reserve is 3/100.

These bounds are uniform over every actual tilted frame and every allowed support point. They use only the physical radius and the original position of T.

## 3. All four faces contain the fixed closed disk in their open sides

Write

    q=5/4-z.

By (3) and z<=1, the actual interval is

    1/4<=q<1/2.

The own coordinates of the same fixed point F relative to the actual vertex T are

    A_F=(F-T).a=c/2+q*s,
    B_F=(F-T).b=s/2-q*c.                     (5)

No new placement of T is made. Equations (3)--(4) give the strict face margins

    A_F>=s/4>9/40,
    A_F<(c+s)/2<=sqrt(2)/2<17/24,
    B_F>(s-c)/2>1/4,
    B_F<s/2<1/2.                             (6)

Thus

    A_F>9/40,
    1-A_F>7/24>9/40,
    B_F>1/4>9/40,
    1-B_F>1/2>9/40.                          (7)

The exact supplementary reserves in (7) are

    7/24-9/40=1/15,
    1/4-9/40=1/40,
    1/2-9/40=11/40.

The axes a,b are orthonormal, so a Euclidean displacement of norm at most 9/40 changes either own coordinate by at most 9/40. Every point of the closed radius-9/40 disk about F therefore has both actual own coordinates strictly between zero and one. This proves that entire closed disk lies in int(K), with all four actual support faces retained.

## 4. Every aligned support side and its entire actual point interval

If the minimum-x support is not a strict vertex, K has the horizontal/vertical frame. Write its whole actual rectangle as

    K=[h,h+1] x [a,a+1].

The unchanged actual support point T=(h,z) belongs to its left side. Because 0<=z<=1,

    -1<=a<=1.

All actual side positions and both endpoints of T are included; no midpoint or selected force mean is imposed.

The two lower corners cannot touch the circle:

    (h+1)^2+a^2<=(61/60)^2+1<17/4,

and the other lower corner is no farther in the x direction. The upper-left corner also has

    h^2+(a+1)^2<=1/3600+4<17/4.

Therefore the actual circle vertex is the upper-right corner, with

    R^2=(h+1)^2+(a+1)^2.                    (8)

If a<=3/4, then -1<=a<=3/4 gives 0<=a+1<=7/4, so

    R^2<=(61/60)^2+(7/4)^2<17/4,
    17/4-(61/60)^2-(7/4)^2=277/1800>0.

Thus a>3/4. Since a<=1, the actual own coordinates of F in K are

    1/2, 5/4-a,
    1/4<=5/4-a<1/2.

Each of the four face distances is at least 1/4 or greater than 1/2, and hence strictly greater than 9/40. The entire closed radius-9/40 disk about F is again in int(K).

Sections 2--4 exhaust all possible minimum-x support features of a unit square. In particular an aligned vertex endpoint is part of this full aligned-side calculation, not an omitted limiting tilted case.

## 5. Full negative-height support extension with an upper circle point

Suppose instead that -1<=z<=1 and that K has an actual circle point Z with Z_y>0. Keep the same |h|<=1/60 and actual minimum-x support x=h.

Every point of a unit square has x projection between h and h+sqrt(2), because its horizontal width is at most sqrt(2). Therefore

    |Z_x|<1/60+17/12=43/30.

Since |Z|=R and R^2>=17/4,

    Z_y^2>17/4-(43/30)^2>2,
    17/4-(43/30)^2-2=44/225>0.

Thus Z_y>sqrt(2). If the unchanged actual support point had z<=0, the distance from T to Z would exceed sqrt(2) in its vertical coordinate alone, contradicting the unit-square diameter. Hence z>0.

The main theorem now applies to this same physical K and same actual T. This proves Corollary 1.2 with the entire initially allowed negative-height support interval, arbitrary circle masks and no force assumptions.

## 6. Exact original-use boundary

In the positive/nonparallel B-owned-HB chart of the fresh complete normal form, an H-owned singleton central contact has actual coordinates

    H=[x,x+1]v+[-y,G]u,
    0<x<=delta<1/60,
    n_HK=-v,
    T=xv+z*u, 0<z<G<1.

The same original K has a strict maximum-v vertex at T. Apply only the origin-preserving orthogonal map

    q -> (-q.v,q.u).

Its minimum horizontal support becomes h=-x, the same actual T becomes (h,z), and every hypothesis of Theorem 1.1 holds. Thus the actual K contains the fixed closed disk about `(h+1/2,5/4)`. No K force or physical-mask theorem is required for this conclusion, and no shared contact mean has been altered by the map.

This is exactly the physical K half needed in that remaining H-owned-central page comparison. To exclude an actual second square C by a common point, a separate proof must establish that C contains a point in this disk, or the same F, under its own complete actual hypotheses. This source does not assume that further C statement and does not close an original graph gate by itself.

The full normal form just used is

`POSITIVE_B_OWNED_ROOT_GENUINE_NEIGHBOR_NORMAL_FORM.md`,

SHA256 `93cbef188a875c95b56f51498ebb6b55633da09f34ce311740f370e1586849ce`,

with its separate complete acceptance

`REVIEW_POSITIVE_B_OWNED_ROOT_NORMAL_FORM_TOPOLOGY_INDEPENDENT_2026_10_27.md`,

SHA256 `705bad0d0719b4712af8e6ba8c20f02715d566ad0832a5b10122f2d5df86df3d`.

Its explicit positive/nonparallel B starting conditions and its separate HK-singleton premise are retained in this original application. Neither is claimed recovered from the older missing manuscript by recalling a hash. The local physical theorem itself is independent of those original reductions.

## 7. Verification and direct physical foundations

The local proof is self-contained in Euclidean unit-square geometry. It uses only the square's two orthonormal axes, its diameter sqrt(2), the maximum horizontal width sqrt(2), disk containment at its actual vertices, and the original actual support point. These elementary facts are proved or directly computed in Sections 2--5. The physical contact convention is consistent with the complete present source

`PHYSICAL_CONTACT_STRESS.md`, SHA256 `d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5`.

The independent reviewer should check every physical support type, the actual opposite-corner radius identity, both complete z/angle comparisons, all four strict face margins, the full aligned side interval, the negative-height extension and the exact origin-preserving original caller. Checking only that F lies in a sampled tilted square would not verify this theorem.

The separate exact author record `check_small_side_boundary_interior_disk_identities.py`, SHA256 `fefa4f7b86016b9e740bcd21281b5c79c69ad5b6650d6b81e2279466c6ac8402`, expands seven complete coordinate or norm identities and verifies twenty-two fixed rational values or reserves using only sparse polynomials and Fraction arithmetic. Its full replay passes. These checks validate displayed algebra and do not replace the whole physical proof or its required independent review.

No source bytes from an older manuscript are represented as restored. No K2, H3, C2, selected force normal, removed square, positive-load approximation, interval-box certificate, Lean invocation, CI workflow, ledger tick or remote edit appears in this proof. The whole physical result is analytic and introduces zero computational certificates.
