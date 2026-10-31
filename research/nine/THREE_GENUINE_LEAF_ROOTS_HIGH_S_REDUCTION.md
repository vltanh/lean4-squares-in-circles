# Three distinct genuine leaf roots force three high-radius S roots

Date: October 27, 2026.

**Status: accepted complete hand proof at its stated original scope
after full root and separate independent source/scope reviews.** See
REVIEW_C2_34_THREE_BRIDGES_NEW_UNIFORM_TOOLS_AND_COVER_ROOT_2026_10_27.md
and REVIEW_THREE_GENUINE_LEAF_ROOTS_HIGH_S_LEAF_PAIR_2026_10_27.md.
Their mathematical source pins precede this acceptance-only header.
No original ID or whole coarse-cell status is changed by this source.

Keep all nine original physical unit squares and the common selected
certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose three distinct actual units C_1,C_2,C_3, each of positive
degree at least two, each have a genuine positive degree-one leaf.
Their higher degrees, other forces, and contacts are arbitrary.
The genuine leaves are automatically distinct from one another and
from these three roots: a positive degree-one vertex is not one
of the stipulated roots, and one genuine leaf cannot have two roots.

**Theorem.** Every such original configuration has

    d>1 and all three genuine leaves are S.

All three actual roots meet the closed D_epsilon. No root is assigned
an unloaded equation, a prescribed frame, or a reduced degree.

## 1. Every D assignment is excluded at the original degrees

The actual root of each genuine S leaf has the inward radial unit
segment from d e to (d-1)e. Consequently it contains O when d<=1
and meets D_epsilon when d>1. A genuine D root contains O openly,
so it also meets D_epsilon at every radius.

If any of the three leaves were D, its original root and the other
two distinct original near units would satisfy the entire theorem
D_LEAF_TWO_DISTINCT_NEAR_ORIGIN_UNITS_EXCLUSION.md. That theorem
places no force, degree, leaf or frame condition on those other two
units and excludes the configuration. Hence all three leaves are S.

## 2. All d<1 configurations fail by actual origin tangent cones

For d<1 every C_i contains O. None can contain O in its open
interior, because either of the other actual closed units has interior
points approaching O.

If a genuine S direction is not an own side axis, its actual support
is a vertex and, in the own axes directed toward that vertex, its
square is

    [da-1,da] times [db-1,db],
    a,b>0, a^2+b^2=1.

Both da and db lie strictly between zero and one. This would put O
openly inside that root. Thus every surviving root is aligned with
its own S direction. Its radial interval [d-1,d] contains zero
strictly. To avoid an interior origin, zero must be an endpoint of
its transverse unit interval. Therefore O is in the relative interior
of an actual side of each root.

Two such nonoverlapping units have complementary open tangent
half-planes at O. Their union fills a whole neighborhood except the
common boundary line. No third unit square containing O can have
its nonempty open tangent cone there. This contradicts C_3 and
excludes the entire d<1 range.

## 3. The critical value d=1 has total capacity at most eight

Now R^2=17/4. Again every root contains O closed and none can
contain O openly. The same tilted own-frame calculation has
0<a,b<1 and would give an interior origin, so all three genuine
S directions are own side axes.

If O is a vertex of all three actual roots, apply the complete
physical THREE_VERTEX_ORIGIN_CAPACITY.md. It counts every other
original square with arbitrary orientation and gives total capacity
at most eight. This is the same accepted whole-configuration input
used with its full physical scope in
ROOTED_TRIANGLE_FOREST_OUTSIDE_FORK_EXCLUSION.md, Section 4.

Otherwise some C_i has O in a relative side interior. Its open
tangent half-plane leaves one complementary half-plane for the
other two actual roots. Neither of those can have a side-interior
origin, since its half-plane would leave no open sector for the
third root. Their two right-angle vertex cones must therefore
exactly fill the complementary half-plane. It follows that all
three actual root frames are parallel.

There are four directed side axes in their common frame. Each
genuine S direction belongs to this set. The three directions
are distinct: the physical genuine radial S leaf in a fixed
direction e is uniquely

    [1,2] e + [-1/2,1/2] Je.

Equal directions would repeat this same physical square as two
different actual leaves. Any three different directions among
four perpendicular directed axes contain an opposite pair.

Choose such a pair and rotate its directions to east and west.
Their actual S leaves are

    E=[1,2] times [-1/2,1/2],
    W=[-2,-1] times [-1/2,1/2].

Their actual roots have their radial support at e or -e and
contain O. With the common parallel frame, their full squares
are therefore exactly

    C_+=[0,1] times [t_+-1/2,t_++1/2],
    C_-=[-1,0] times [t_--1/2,t_-+1/2],
    -1/2<=t_+,t_-<=1/2.

These are the actual full closed side sliders, including every
vertex or side endpoint. No midpoint is imposed on a root's
pair-force application and no equation at either root is used.
The complete physical theorem P_ALL_COMPLETION.md excludes nine
units containing this four-square cage, throughout that entire
closed two-slider parameter domain.

The all-vertex and side-interior alternatives exhaust the
critical radius. Thus d=1 is impossible as well.

## 4. Exact remaining scope

Only d>1 with three genuine S leaves remains. Their three actual
roots contain the respective points epsilon e_i, by the original
inward unit segments, and hence meet D_epsilon. The theorem makes
no assertion that those roots contain O, have parallel frames,
or have any specified original force or circle equation at this
remaining high radius.

In particular the result applies simultaneously to every shared
C2.34.b3 three-direct-leaf attachment with three distinct roots,
without selecting a triangle interface or deleting another cyclic
block force. It also applies to other original graphs at exactly
the same stated physical scope. All nine units, every load mask,
zero weight, common normal and original side mean remain.

No new gate ID, pose sample, parameter certificate, Lean compilation,
CI run, remote action or shared-ledger change is made.
