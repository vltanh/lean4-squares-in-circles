# Independent review of the complete two-petal house and fan bouquet exclusions

Date: October 27, 2026.

**Verdict: ACCEPT without mathematical correction.** This accepts the
full degree-free unloaded-neighbor theorem and each of its three whole
original callers: roof-house, lower-house and endpoint-fan bouquets.
It is not merely an owner restriction or a selection of load masks.
The separate whole C3.335 assembly is reviewed in its own file.
No shared ledger or original gate is changed here.

Reviewed source:

    GLOBAL_NEXT_TWO_INTACT_PETALS_HOUSE_FAN_BOUQUETS_EXCLUSION.md
    SHA256 d7c7c69d2ac398b402d0dcfaa4e77864c83596e7a1e520db0db3c023f34f7298

## 1. Exact local statement and original force scope

The local theorem concerns actual distinct squares E,U in the same
containing circle. It assumes D_epsilon lies in int E,
dist(O,U)>sqrt(2)*epsilon, zero complete circle force at U, and the
strict original moment pattern in which U's force toward E has one
sign and every other original U force has the opposite sign. All
positive pair forces at U are retained. There is no degree restriction,
no assumed concurrence, and no boundary or equilibrium premise at a
different neighbor.

Reflecting the complete geometry first makes the E moment positive
and all others negative. This changes all determinants together,
preserves every physical support and full force equation, and does
not change an individual selected normal. The subsequent changes
of own frame have positive determinant and preserve these signs.

The universal actual-neighbor support bound h<=d follows directly
from the full farthest-corner inequality and the minimum half-width
one half. It is valid at arbitrary degree and physical circle mask.
It applies to every actual neighbor used in the kernel, without
requiring that neighbor to be a loaded degree-two unit.

## 2. The own frame and the complete root-normal screen

I independently reconstructed the frame argument. In the actual
own rectangle, the squared origin distance is the sum of the two
squared interval distances. The strict distance hypothesis implies
one interval misses zero by more than epsilon. A proper rotation
puts it at [a,a+1] with a>epsilon. If the other interval's upper
endpoint c is below -epsilon, the proper quarter turn x'=-y,
y'=x makes the new first lower endpoint -c>epsilon and the new
second upper endpoint positive. Thus the entire domain has

    U=[a,a+1] x [b,c], c=b+1,
    a>epsilon, c>=-epsilon, a+1>1+epsilon>=d.

No reflection that would reverse the fixed moment signs is hidden
in this reduction.

The actual common contact support satisfies

    h_U(n)=min_E n.x < -epsilon.

The strict inequality follows because the whole closed epsilon-disk
is in the open E, including the epsilon=0 case. It is retained at
every side mean and support-cone endpoint.

All n_x>=0 possibilities are excluded correctly. The upward axis
has support c>=-epsilon; the downward axis has strictly negative
moment because its point has positive x. For n_x>0,n_y>=0 the
support is at least -epsilon. For n_x>0,n_y<0, the positive moment
at the actual lower-right vertex forces b<0, which makes its
support positive. Thus the original root normal always has n_x<0.

## 3. Every nonpositive vertical root direction

For n=(-u,-v) with u,v>0, its actual lower-left point has moment
bu-av>0, so b>0 and c>0. For n=-e_x, its actual side mean has
positive y, which gives c>0 but does not falsely imply b>0.
The source explicitly keeps these two cases separate.

When c>0 the complete negative-moment feature cover is sound:

* The right axis requires actual neighbor support a+1>d.
* At the upper-right corner, negative moment forces
  (a+1)t<cs. For t>0 this gives support strictly larger than
  (a+1)/s>=a+1>d; the t=0 endpoint is the same forbidden right
  axis. All divisions have strictly positive denominators.
* The top side has positive moment because its x coordinates
  are positive. Every upper-left corner normal has nonnegative
  moment at (a,c).
* Every remaining actual feature has nonpositive vertical normal
  component, including the full left side and both lower cones.

The whole original force equation therefore has negative vertical
component when n_y<0. When n_y=0, balance makes every other force
horizontal. The positive horizontal axis is impossible, leaving
all forces in the negative horizontal direction. Both alternatives
are excluded without shortening U's star.

## 4. Every positive vertical root direction, including free vertices

For the remaining strict upper-left root cone, put

    n=(-u,v), u,v>0,
    p=(a,c), -au+cv<-epsilon, av+cu>0,
    w=(v,u).

The root force has zero w-projection. I checked every actual support
feature of a different negative-moment force g.

The right axis and top side are excluded as above. If c<=0, the
upper-right cone has nonnegative moment; if c>0, the preceding
strict support calculation excludes its negative moments. For an
upper-left g=(-s,t), negative moment gives c<0, s>0 and

    t/s < -c/a < v/u,

the last comparison coming from the actual positive root moment.
Thus w.g<0. The left side, bottom side and entire lower-left cone
have strictly negative w-projection directly, independent of their
actual means and of the sign of b. The c=-epsilon endpoint is kept.

For the lower-right cone g=(s,-t), the side-axis endpoints are
already covered. If s,t>0 and t/s<=v/u, write

    g=lambda e_x+mu(-n), lambda,mu>=0.

Both endpoint directions maximize at the actual lower-right vertex
(a+1,b), with that point also belonging to the side endpoint face.
Consequently the support is linear on their entire closed normal
cone. The two true endpoint heights satisfy

    h_U(e_x)=a+1>d,
    h_U(-n)=u+v-h_U(n)>1+epsilon>=d.

The second identity is the actual square width, not an inferred
force relation. Since g is unit, lambda+mu>=1. As d>0, every
unit direction in this closed cone has support strictly larger
than d, contradicting the existence of its actual contained
neighbor. Hence t/s>v/u and w.g<0 also in the last cone.

Thus every original force other than the E force has strictly
negative w-projection. Its positive coefficient cannot be cancelled
by the root force, whose projection is zero. This proves the entire
local theorem, including both strict root-vertex families left by
the previous axis-only result. No contact owner is presumed and no
normal, mean, point or circle weight is altered.

## 5. Exact two-petal distance and private-cycle transfer

I read the complete stronger two-petal disk proof and the full
original five-block root-neighbor reduction. Their current hashes
match the source:

    TWO_INTACT_PETALS_NO_UNLOADED_NEIGHBOR.md
    be227b05fbf23fd0e4e973f9f3c4ba4fe129116fc220a4c8fe2218a4c39fec77

    GLOBAL_CLOSURE_TWO_INTACT_PETALS_FIVE_BLOCK_ROOT_NEIGHBOR_REDUCTION.md
    653e4ea3bfd6d7ee5d1552c6bda26ab0519d3a6929083fb7f16b5496b60962a3

The stronger disk is closed D_(1/40) inside open E. A distinct
closed actual unit cannot meet int E: any such boundary meeting
would have nearby interior points of that unit still in int E.
Compactness therefore makes its origin distance strictly greater
than 1/40. The exact reserve

    (1/40)^2-2(1/60)^2=1/14400

gives the required strict distance above sqrt(2)*epsilon, including
epsilon=0. No mere open-disk exclusion is substituted for this
strict distance hypothesis.

The degree-free 8def789e input has my complete independent review
0773b4d8b038092f128da60a26b994a10b082fe6c9f1626a6e3235aa7202e3ee.
Its current full mathematical source still has the stated hash.
The current transfer uses its full local radial-contact and moment-
port results at their exact scope: every edge with both units
distinct from E is nonradial, and every strict directed-moment
private cycle winds O. The actual E-to-intact-tip path, together
with E's internal O-to-center path and the same compatible
physical embedding, excludes such a cycle. It does not require
the whole containing block to avoid E.

All private moments below are consequently nonzero. A private
simple cycle cannot have all its directed moments of one strict
sign; reversing the cycle handles the other sign. This conclusion
uses no degree reduction at a chorded or loaded higher-degree unit.

## 6. Whole original roof-house and lower-house joins

For the roof-house E, the two private root neighbors A,D have their
true degree three; B,C have true degree two. The original four
intact tips are distinct from all four house private units. The
complete physical no-six-neighbor premise makes at least one of
A,D physically clear. No private circle-load mask is otherwise
assumed.

The genuine B2,C2 moment equations give a common nonzero lower-path
moment l. The actual AD moment h is also nonzero. The private
four-cycle A-D-C-B-A has moments h,-l,-l,-l. Its forbidden
one-sign alternative forces h and l to have the same sign. The
complete A3 equation then makes the E moment -h-l opposite to
both remaining moments; the D3 equation gives the reflected pattern.
Whichever hub is physically clear meets the whole unloaded kernel.
This excludes both-clear and one-clear hub domains and every lower
load assignment, retaining the roof's full degree-six system.

For the lower-root house E=B, the original C2 neighbor is loaded
by the full two-petal true-two-force channel theorem. The four
intact tips plus C and a putatively boundary A would be six distinct
physical boundary neighbors of E. Hence the actual A is physically
clear at its true degree three. The Z2 equation makes the two roof
moments equal to a nonzero k; put h=m(A,D), also nonzero. The
private triangle A-Z-D-A has moments k,k,-h, so k,h have the
same sign. The original A-to-E moment is -k-h. This is the full
kernel pattern at the actual unloaded A. No load premise at D
is needed. Reflection covers the other lower root exactly.

## 7. Whole original endpoint-fan join

The complete unchanged-degree load reduction makes B,C,D genuinely
loaded at true degrees 3,3,2 and K physically clear at its true
degree four. The root E keeps all six actual pair forces. The
original private and root torque equations give

    h_i=k_i-k_(i-1), k_0=k_4=0,

including h_1=k_1 because each original intact petal contributes
zero aggregate origin moment at E. None of its four real petal
forces is omitted.

Orient the plane using the nonzero private moment k_3>0. Then
h_4=-k_3<0. The actual private K-C-D triangle has moments
h_3,k_3,-h_4; its last two are positive, so h_3<0. Thus k_2>k_3.
The K-B-C triangle then has moments h_2,k_2,-h_3, giving h_2<0
and k_1>k_2. All exclusions are strict because the private edges
cannot have zero moment. Therefore

    k_1>k_2>k_3>0,
    h_1>0, h_2,h_3,h_4<0.

The full actual K4 star has the required pattern and strict distance,
so the kernel excludes it. This sign proof needs no separate
boundary-center angular ordering and no virtual load at E. Both
strict K-vertex owner families and the reflected endpoint are
included.

## 8. Constants, accepted scope and remaining global obligations

Besides reconstructing the complete cone identities by hand, I
checked the following exact positive reserves with rational arithmetic:

    (1/40)^2-2(1/60)^2                         = 1/14400;
    (121/60)^2+1/4-1105/256                   = 31/57600;
    (79/40)^2-1/4-1                          = 4241/1600;
    41/40-61/60                              = 1/120;
    (67/120)^2-(1/40)^2-1/4                  = 11/180.

The original same-nine radius and complete physical no-six-neighbor
prerequisite chain is preserved as in the pinned accepted ten-domain
cover. No replacement packing or table-free version of an inherited
prerequisite is claimed. All three new exits are whole original graph
domains at that common selected-packing scope.

The reviewed source therefore excludes exactly the three remaining
common-root bouquets at full load/feature scope. The seven separate
middle-triangle chains use 8def789e and are joined in the separately
reviewed complete cell assembly. The unrestricted radius bound and
all original equality packings are not asserted proved by this review.

No numerical direction sample, physical motion, force redistribution,
Lean compilation, CI, workflow, remote mutation or shared-ledger
change is used.
