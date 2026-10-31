# Full independent review of the aligned-low LTAC.S upper-A placement

Date: October 28, 2026. Reviewer: triangle_bridges.

**Decision: ACCEPTED, unchanged, for the entire original A-upper/C-lower
placement and the complete scalar theorem used to finish it.** I read
the full physical source, the complete scalar manuscript and its exact
checker, and the operative portions of every direct physical input.
I independently derived the complete contact/frame cover and all new
force equations, reproduced the author certificate, and wrote a separate
exact continuous certificate over the whole stated enlarged domain.
No correction is requested.

| Reviewed artifact | SHA-256 |
| --- | --- |
| `HOUSE_LOWER_TAC_S_ALIGNED_UPPER_A_EXCLUSION.md` | `975b2ab626aa30b06decdf068fd0667c7badee83e6711ec489de0daab673c773` |
| `ALIGNED_LOW_S_LOWER_RETURN_HEIGHT_SEPARATION.md` | `93bb8e2d6dc3f2965c1a1868ba4a7552f63c5326cbe05cab5381950f4db765be` |
| `certificates/aligned_low_s_lower_return_height_separation.py` | `bd92d1895f240805a78ea5160b0b7ed56f6948a4ec6ce88ff870bb55a6472f15` |

Root's contribution to the initial continuous scalar argument is
explicit in both sources. This record is a separate full peer audit;
it does not count that contribution or the author's own reconstruction
as an independent acceptance. Hexagon has also separately accepted
the complete scalar and author code in cf5f5996. I read that entire
record after completing my own geometric derivation and independently
rebuilding the scalar cover. My conclusion includes the full physical
caller, which the scalar-only record correctly leaves separate.

## 1. Original graph, radius and exact local-input scope

The source retains precisely the original lower-root TAC.S graph

    AT, DT, AD, AB, BC, CD, BL.

The real S leaf is at B. B is genuinely clear and has exactly three
positive pair forces. A has its full loaded degree-three star, D its
full unloaded degree-three star, and C,T their original loaded
degree-two stars. The positive house loads are T,A,C; L retains
its original one force. All nine original physical units remain.
Nothing replaces A by a two-force tip or D by a transmitter.

The same-nine radius theorem supplies R>2, independently of this
graph or its forces. At the actual aligned strict-low root,

    2<R<sqrt(17)/2,
    d=sqrt(R^2-1/4)-1, 14/15<d<1,
    a=1-d, B=[-a,d] times[h-1,h].

The exact lower comparison follows from
15/4-(29/15)^2=11/900>0. The real leaf remains
[d,d+1] times[-1/2,1/2]. Vertical reflection changes the entire
physical configuration, preserving the original attachment labels;
this source then treats exactly the placement with A upper and C
lower.

I reread the complete local Sections 1--6 of the 02fd37d9 aligned-low
source. The normal cover and ratio use the true three-force root,
the real leaf and the physical boundary status of its two neighbors.
The finite singleton selector first proves the lower contact is an
actual vertex; its nonzero root determinant then makes the upper
normal a genuine neighbor side axis. Neither step uses degree two
at that neighbor. The all-boundary C5 path occurs only in the later
whole-C5 conclusion and is not imported here. Thus the literal local
exports are valid at the actual A3/C2 neighbors:

    29/50<h<2/3, g=1-h in(1/3,21/50),
    P_upper=(-a,h), n=(-c,s), c,s>0, c^2+s^2=1,
    P_lower=(x,-g), normal South, 3/10<x<=d,
    c/s=(x+a)/h.

The lower unit is genuinely tilted, and the upper unit owns n.
The selected normal was fixed before stress extraction and remains
compatible with the existing physical junction construction. No
new choice depends on an extracted force or mean.

I also read the full force-free Sections 1--3 of c32b99ad. They
exclude every other physical lower corner at arbitrary lower degree,
using the actual leaf crossing and the full tilt interval. Therefore

    C=(x,-g)+[0,1](b,-t)+[0,1](-t,-b),
    b,t>0, b^2+t^2=1,
    Z_C=(x+b-t,-g-b-t)=(X,-Y)

is the actual unique physical corner. The later boundary-neighbor
properness clause of that old theorem is not applied to D. Its
scope would not permit that substitution. The new source instead
establishes nonparallelity directly before invoking the conditional
loaded-two theorem, as checked below.

## 2. The new whole-square east-of-origin fact is sound

The proof that X>0 is force-free. If X<=0, then t>b and
|X|<t-b since x>0. The other actual circle coordinate is
Y=g+b+t. Using b^2+t^2=1 gives

    R^2<(t-b)^2+(g+b+t)^2
       =2+2g(b+t)+g^2
       <2+297/250+441/2500<4.

The last gap is exactly 1589/2500. The comparison
2g(b+t)<297/250 follows from g<21/50 and sqrt(2)<99/70.
Every squaring operation has its required sign, and the equality
X=0 is covered by the same strict inequality.

For the stronger x>t conclusion, suppose x<=t. Then
0<X<=b. The symmetric matrix for b^2+(b+t)^2 on b^2+t^2=1
has largest eigenvalue (3+sqrt(5))/2<21/8. Hence

    R^2<=b^2+(g+b+t)^2
       <21/8+297/250+441/2500
       =4-53/5000.

This is a contradiction at every tilt, including b<t; no later
properness conclusion was used prematurely. Since the minimum
horizontal coordinate of the actual lower square is x-t, the
whole square lies strictly east of O. I accept the stated physical
export to a lower degree-three body as well: this argument uses
only the actual physical corner and frame, not C2.

## 3. Conditional C2 properness and the exact original return mean

The full original C2 equation is

    mu*North+kappa*w+lambda*(X,-Y)=0,
    mu,kappa,lambda>0.

Since X>0, its horizontal component forces w_x<0. The two contact
normals are therefore nonparallel. The conditional Lemma 1.1 in
7d0c4092 now applies at its literal scope, without a boundary premise
at D. It places the positive radial concurrence in the actual unique-
corner C. The incoming vertical line fixes its horizontal coordinate
to x, so q_C=(x/X)Z_C. Its membership in the containing disk gives
x/X<=1, and consequently b>=t. No inside-concurrence assertion for
two physical corners has been used.

For the upper A, I rederived the physical frame

    A=P_upper+[0,1]n+[-rho,1-rho]j,
    j=(-s,-c), N=ac+hs, K=xs, W=K+rho,
    R^2=(N+1)^2+W^2.

The upper unique physical corner and this radius identity come from
the local geometry, independent of A's extra forces. The rho>7/8
proof in 843e9afc is before that source's first degree-two equation.
It uses N^2+K^2=a^2+h^2<101/225 and the radius triangle inequality
only. I checked the exact squared reserve 3666721 in its radical
comparison. Thus the source's arbitrary-degree transfer is legitimate,
and every actual A point has y>=h-(1-rho)c>91/200.

The complete outgoing C support cover is exhaustive:

* The left vertex and entire far-v side lie below -g-b<-31/30,
  using b>=1/sqrt(2)>7/10. Their vertical distance from any actual
  A point exceeds 893/600>sqrt(2), so the same unit D cannot meet
  both. The exact squared reserve is 77449/360000.
* The u side, -v side and right vertex have strictly positive
  horizontal normal component, incompatible with the already
  proved w_x<0.
* The top vertex P is in the relative interior of the root's bottom
  side, since the leaf screen excludes x=d and x>3/10>-a.
  B's upper half-plane sector and C's strict downward right-angle
  sector leave two gaps smaller than a right angle. A third square
  cannot occupy either. This is the actual tangent-sector statement,
  including all possible vertex/side endpoints.

The only remaining return is consequently the whole interior side

    w=-u=(-b,t), Q_CD=P+tau*v, 0<tau<1.

Both excluded endpoints were removed geometrically. The horizontal
force equation gives lambda=kappa*b/X. I independently took the
complete C2 torque about P and obtained

    tau=b(xY/X-g),
    tau-1=-(b-t)(1+bg-xt)/X.

The sparse exact identity check reduces the second equality to
b^2+t^2=1. Since 1+bg-xt>0 and tau<1, this forces b>t.
The formula retains the original mean; it does not select a point
on the side after extraction. The weak proper endpoint b=t is not
discarded earlier and is excluded here only because it would force
the already impossible tau=1.

## 4. All actual D orientations and means are covered

The strict inequality x>t gives Q_CD,x=x-tau*t>0. If D owns
the incoming -u axis, its actual frame in (u,v) coordinates is
[-1,0] times[z,z+1], with tau in the latter interval. For z<0,
the same interval contains zero in its interior because tau>0.
Then D contains P in its side interior and an inward -u segment
enters int(B), impossible. For z>=0, its maximum height is at
most -g+t<8/21<91/200. The exact height gap is 311/4200, so
it cannot meet A. This keeps the whole original z and tau means.

For a nonowned incoming normal, Q_CD is an actual strict minimum-
normal vertex. A strict Northwest vector can lie in the inward
orthogonal cone in exactly the two printed forms:

1. A bottom vertex with inward axes (q,p),(-p,q), p>0,q>=0,
   q/p<t/b. The strict cone condition gives p>b. Its actual
   first edge reaches y=-g at parameter tau*b/p in(0,1).
   The crossing x coordinate lies strictly between zero and x<d.
   Continuing that same edge enters the open root. Since an open
   neighborhood of a square boundary segment includes open square
   points, this is a true interior overlap. The axis q=0 is included.
2. A right vertex with inward axes (-p,q),(-q,-p), p,q>0.
   The additional strict cone condition q/p>t/b is retained; no
   invalid enlargement is used to exclude another frame. Its actual
   maximum height is Q_CD,y+q<1-g-tau*b.

Their common North/West axis belongs to the first case. If the
incoming vector itself is an axis, it is exactly the parallel-D
case already covered. Thus the two strict forms and the owned form
exhaust every possible D frame. No D2 equation, concurrence, circle
mask or force restriction is hidden in the cover.

## 5. The full scalar domain and every arithmetic guard

All premises of the enlarged scalar theorem are literal. In
particular x+b>3/10+7/10=1>d, so the actual leaf crossing is
mandatory. The unchanged screen yields t>2/25, while b>t gives
t<1/sqrt(2)<5/7. The original two circle equations, common d,
rho range and exact tau formula are all retained.

I read every author interval operation and every possible return.
The operations on Fraction endpoints are outward enclosures;
the zero-containing square convention, four-product multiplication
and positive-denominator reciprocal are correct. The 64-bit radical
floor/ceiling computed with integer square root encloses the full
real radical range, including exact squares. Clamping a negative
formal lower radicand to zero does not remove a real actual value.

The b and x contractions use only b>=t, x>=3/10, x>=t and
x<=d. The later X intersection uses the unchanged identity
X=x+b-t. Only a strictly negative screen upper bound excludes a
box; the true leaf-corner equality is kept. The W-radicand and
rho/tau intersections retain every actual real radical and both
original mean endpoints. A denominator not yet bounded away from
zero causes subdivision, not an inadmissible division or rejection.

The author's initial target test is positive rather than explicitly
above 1/25000. This is valid because the final code separately
checks that every positive terminal's lower bound exceeds that
claimed floor. I verified that final check and its exact minimum.
The bisection is by greatest normalized width, with deterministic
first-coordinate ties and both closed children. The independent
prefix-cover check retains all splitting-plane points.

My exact reproduction of the frozen author code gives every printed
count and the exact terminal digest:

| Author certificate quantity | Exact reproduced value |
| --- | ---: |
| Visited nodes | 3,135 |
| Terminal boxes | 1,568 |
| Actual leaf-screen exclusions | 374 |
| Strict target certificates | 1,194 |
| Maximum depth | 15 |
| Unresolved boxes | 0 |

The digest is
`3e16224eccf7d9f4b93cd98f0b49901d15ac6ff1aa0decfff4620c6e282f9662`.
The entire printed minimum fraction matches the reproduced value
and is strictly greater than 1/25000. Its full output is preserved
separately, not merely its counts.

## 7. A separate complete 128-bit continuous reconstruction

My independent checker imports no author code or peer interval
helper. It uses an immutable interval class, exact Fraction
arithmetic, 128-bit outward radical bounds, and a different normal
enclosure. For positive intervals w,h, the function

    w/sqrt(w^2+h^2)

increases with w and decreases with h. I therefore bound c using
the two corresponding corners of their interval rectangle, and
bound s by the reflected formula. Each radical is still outward
enclosed. This is a justified tighter enclosure; it does not identify
c and s or use a sampled correlation.

Starting from the entire closed printed rectangle, the new checker
rederives every screen, circle, mean and denominator guard. It stops
only at a strict target bound above 1/25000, or a rigorous necessary-
condition failure. Its separately generated complete result is

| Independent certificate quantity | Exact result |
| --- | ---: |
| Visited nodes | 2,583 |
| Terminal boxes | 1,292 |
| Actual leaf-screen exclusions | 326 |
| Strict target certificates | 966 |
| Maximum depth | 15 |
| Unresolved boxes | 0 |

A newly built binary trie rejects duplicate leaves, a leaf with
descendants, every missing sibling, and any incomplete internal
node. Every internal split has both actual rational midpoint
children. I also verify the exact Kraft sum is one and the node
identity 2583=2*1292-1. Thus this is a complete continuous cover,
not a replay of selected poses or only successful author leaves.

Every independent positive bound exceeds 1/15000, and hence the
claimed 1/25000. The full exact minimum and all terminal paths,
reasons and bounds are saved in the record below. The different
counts are expected from the independently tightened component
enclosures; they neither replace nor reinterpret the frozen author's
printed certificate. Both complete proofs establish the stated
whole enlarged domain, with all weak endpoints.

## 8. Final height contradiction and exact audit records

For the only remaining D frame,

    max_y D<1-g-tau*b.

The scalar theorem applies at the actual two means and gives
tau*b-delta*c>1/25000. Since g=1-h,

    max_y D<h-delta*c-1/25000<=min_y A-1/25000.

This contradicts the original AD contact. It does not assume a
generic square has height one above any contact: that height bound
was proved for the specific exhaustive surviving right-vertex frame.
All other D frames were excluded separately. Thus the complete
original A-upper/C-lower placement is accepted.

The independent exact record verifies all ten literal source pins,
ten rational comparisons/values and three sparse polynomial
identities. The operative files and records are:

| Review artifact | SHA-256 |
| --- | --- |
| `certificates/review_lower_tac_upper_a_height_triangle_bridges.py` | `cb248f5417d2c43b67291106f896ac97e9dae5cef23e56aac46316a2963f5654` |
| `checkpoints/triangle_bridges_lower_tac_upper_a_independent_scalar_2026_10_28.json` | `8f6c15e57acfdd998ccf753a45aa7c39efb9950316b3b36c7524d0ef3171e0a1` |
| `checkpoints/triangle_bridges_lower_tac_upper_a_physical_checks_2026_10_28.json` | `f0e18f8c188f058ce509ee73b31072870587564f2b85861ace29898c39c42680` |
| `checkpoints/triangle_bridges_lower_tac_upper_a_author_reproduction_2026_10_28.json` | `ce034bcdca30eb79e8ea0e1647885f71614af2da138ebf58d5856978e41d9470` |

The full source pin list is saved in the physical-check record and
was checked against readable current bytes. The opposite original
placement C-upper/A-lower is outside this record, as are any whole
LTAC.S parent or fine/coarse metadata changes. This review retains
all nine units, all original A3/D3/C2 forces and all zero-weight
physical corner possibilities before their proved mask reductions.
No normal reselection, canonical movement, Lean/CI, shared ledger
edit or remote mutation was used.
