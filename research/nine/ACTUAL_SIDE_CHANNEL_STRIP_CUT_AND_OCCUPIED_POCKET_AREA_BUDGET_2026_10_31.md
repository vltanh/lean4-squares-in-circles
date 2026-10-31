# Actual side-channel strips and a joint occupied-pocket area budget

Date: October 31, 2026 UTC.

**Status: complete hand geometric lemma and conditional area theorem.**
An actual width-one channel on a physical contact polygon contributes
its whole inward transverse strip as occupied area. If its actual
exterior pocket is occupied in the stated circle window, this additional
cut is strictly greater than 11/40. The cuts for distinct original
transmitters add, without changing their positions or force means.

The theorem is stated with its actual face-side hypothesis. It does not
turn an arbitrary graph path into an outer side channel, and it does not
subtract the same unit's occupied area twice. Section 6 records precise
ring consequences and the remaining short-seven-cycle limitation.

## 1. The physical polygon and its original side channel

Let P be a contact polygon of a noncrossing physical ring of actual
unit squares with pairwise disjoint open interiors. Its vertices are
the unchanged original contact applications; each polygon edge is a
chord of one original square. Retain the actual center/contact routing
and its bounded-side winding convention. In the weak limit, orient the
polygon so that its winding off its edges is zero or one, exactly as
in `CONTACT_RING_HOLE_AREA.md`, Section 1. Denote its winding-one
region by G.

Suppose one original ring square N has the width-one side-channel form
in an actual orthonormal frame (u,j):

    N=[a,a+1]*u+[h-tau,h+1-tau]*j,
    0<=tau<=1,
    U=a*u+h*j, T=(a+1)*u+h*j.                     (1)

UT is its original polygon chord. Assume the inward, bounded side of
this contact edge is j<h. This is a geometric face-side premise, not
a freely chosen sign: in an outer-channel caller it must be supplied
by the original physical exterior order and actual outer pocket.
Precisely, a regular subsegment of UT must have the winding-one side
immediately below it, or the inherited weak routing must supply that
same label at an actual point immediately below UT in int(N). A
fully cancelled retraced edge does not supply this premise by itself.

All other polygon edges lie in the other closed original ring squares.
No other edge crosses int(N). The endpoints, frame and tau in (1)
are the actual ones. For an unloaded full-positive-degree-two side
transmitter, its complete original force and torque equations supply
this form; no full-degree assumption is imposed on its neighbors.

## 2. The full inward strip has its exact area

**Lemma 2.1.** Under the preceding physical face-side hypotheses,
the open rectangle

    S_N=(a,a+1)*u+(h-tau,h)*j                     (2)

lies in G and has area tau.

If tau=0 the area claim is immediate. If tau>0, S_N is a connected
subset of int(N), also when tau=1. No edge of the other ring squares
can enter S_N. Indeed an interior point of N belonging to another
closed square would have a neighborhood meeting both open interiors.

A point of S_N immediately on the inward side of a regular part of
UT has the original bounded-side winding label by the stipulated
physical face side. Winding is constant throughout the connected
edge-free set S_N. This proves the inclusion and the exact area.

When tau=1, the contact chord UT may be a whole boundary side of N.
One must still use the same original inward label, rather than infer
it from an interior-chord argument. A regular point of UT establishes
that label whenever the selected polygon edge is isolated there.
For a weak boundary-side coincidence, the stated local-label premise
must be checked from the inherited physical center/contact routing;
neither support containment nor the word "outer" replaces that check.
Once its inward seed has been checked, constancy of winding throughout
S_N proves the full inclusion exactly as above. Compact subrectangles
of S_N stay a positive distance from the closed other ring squares and
retain that label under the same physical routing. Exhaustion recovers
the full area tau. This uses the actual center-to-contact homotopy and
compact-interior convention of the contact-ring theorem, not a motion
of any original unit or mean.

Equivalently, the lemma may be applied using an explicit isolated-edge
verification at tau=1. In the regular two-unique pentagon application,
the exact inequalities W.j,L.j,K.j<h prove that verification directly;
see the source cited in Section 5.

For several distinct actual transmitter squares N_i, their open strips
are pairwise disjoint because their unit interiors are disjoint. Any
occupied cuts taken in the other original ring squares are disjoint
from all these strips as well. Thus these strip areas add exactly.

## 3. An occupied exterior pocket forces a cut exceeding eleven fortieths

Now assume all original units are contained in the same centered disk,

    2<=R<=sqrt(1105)/16,

and N's two actual neighbors X,Y physically touch its circle. Keep the
actual width-one supports and original means from (1), with X and Y
on its two exterior support sides. The force-free channel theorem first
gives h!=0. Choose its one common reflection of the whole physical
chart so that h>0. In this same frame require the original exterior pocket
to be the opposite, upper bounded side of the actual occupied crosscut

    z_X -- U -- T -- z_Y

and its containing-circle closing arc. Here z_X,z_Y are the unchanged
actual exterior-spoke corners of the original caller. The complete
outer-gap join must be checked; it is not supplied merely by the words
"side channel." In particular, choosing the upper circle arc while
leaving h<0 is not an allowed entry. A positive outer-channel caller
with at least three loaded endpoints uses the complete component-balance
join in the source cited below to verify this agreement of signs.

The complete degree-free theorem
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md`
then gives, in the common frame whose original upper pocket is used,

    h>3/10.                                        (3)

It proves the nonzero port height, its common reflection, both strict
port signs, and the bound without any endpoint force or degree premise.
If an actual additional whole unit occupies this upper pocket, the
complete force-free theorem
`FORCE_FREE_OCCUPIED_SIDE_CHANNEL_ONE_FORTIETH_PROXIMITY.md`
gives

    dist(O,N)<1/40.                                 (4)

Both inputs allow every endpoint physical circle mask, every original
shared-side mean and arbitrary actual endpoint degree. Their common
upper-gap and weak-routing entry is the complete
`FORCE_FREE_BOUNDARY_SIDE_CHANNEL_OUTER_POCKET_CAPACITY_ONE.md`.

Every actual point of N has j-coordinate at least h-tau. A point
supplied by (4) therefore gives

    h-tau<1/40,
    tau>h-1/40>11/40.                              (5)

No coordinate of the origin is normalized by translation in this
inference. The original negative, zero and positive bottom positions
are all included.

## 4. The reusable area budget and the no-double-count rule

Let A_pre be any proved upper bound for the area of G after subtracting
specified occupied cuts in the other ring squares, but before
subtracting the inward strips of r distinguished actual transmitters.
Suppose all r actual exterior side pockets meet the full hypotheses of
Section 3 and are occupied. Lemma 2.1 and (5) give

    area(actual central free union)
        <= A_pre-sum_i tau_i
        < A_pre-(11/40)*r.                        (6)

In particular, if A_pre<=q+(11/40)*r for an integer q>=1,
the central free union has area strictly less than q and can contain
at most q-1 additional unit squares. For one occupied side pocket,

    A_pre<=51/40  ==>  no additional central unit. (7)

The phrase "before subtracting" is essential. A previously proved free
area bound that has already charged the same strips cannot have their
areas subtracted again without an audit of its proof. The complete
ring proof below has the required uncharged entries because each
distinguished channel chord has length exactly one.

## 5. The complete regular pentagon application

The source
`TWO_STRICT_REGULAR_PERPENDICULAR_CENTRAL_AND_SIDE_POCKET_MUTUAL_EXCLUSION_2026_10_31.md`
establishes the entire original D02.L135 regular two-unique chart and
checks the actual channel, sign, spoke order, weak winding and both
transverse endpoints. Its pre-strip free area obeys

    A_pre<(1+sqrt(2))/2<5/4.

The A and D cuts there lie in their own unchanged unit interiors; no N
area was already charged. Equation (6) therefore gives

    occupied N exterior pocket
        ==> central free area<5/4-11/40=39/40<1.

This is a whole chart theorem, not a restriction to the smaller angle
or side-coordinate region in a prior conditional central cover.

The same complete joint bound also applies to the unique-V A-only
two-unique side chart, by
`UNIQUE_V_A_ONLY_CENTRAL_AND_SIDE_POCKET_MUTUAL_HAND_EXCLUSION_2026_10_31.md`.
That source supplies its own full B moment proof of h>0, strict
isolation of the original port edge at both transverse endpoints,
and the correct inward A and D triangles. Its different original
geometry again gives an uncharged pre-strip area below 5/4. The
identical numerical threshold therefore excludes central/side-pocket
coexistence in both whole owner families without transferring an
unproved circle mask or changing either family's original means.

## 6. Exact contact-ring consequences and the short-C7 scope boundary

For a contact ring of k actual units, write l_i for its original chord
lengths. The complete area proof in `CONTACT_RING_HOLE_AREA.md`,
Sections 1--3, gives

    area(free union)
      <= A(P)-(1/2)*sum_i sqrt(max(l_i^2-1,0)),
    A(P)<=(1/4)*cot(pi/k)*sum_i l_i^2.             (8)

The first inequality subtracts no area at an edge of length at most
one. Each distinguished side-channel chord in (1) has length exactly
one. Its positive strip is therefore an additional, uncharged cut in
that very proof. Combining its winding localization with Lemma 2.1
gives the exact stronger expression

    area(free union)
      <= (1/4)*cot(pi/k)*sum_i l_i^2
         -(1/2)*sum_i sqrt(max(l_i^2-1,0))
         -sum_distinguished tau_i.               (9)

For 3<=k<=6, the same original continuous chord optimization in
Section 4 of that source bounds the first two terms by
(k/4)*cot(pi/k). Hence r occupied original side pockets give

    area(free union)<(k/4)*cot(pi/k)-(11/40)*r.    (10)

For example, a quadrilateral contact face with any one such occupied
exterior side pocket has central free area strictly less than

    1-11/40=29/40<1.

Thus a whole additional unit in a physical four-ring and an occupied
actual exterior side pocket at one of its boundary side transmitters
cannot coexist. This is independent of the other graph degrees,
provided the displayed original face-side and exterior-gap hypotheses
are supplied. In a chorded graph, it applies separately to each actual
quadrilateral face whose boundary contains that original transmitter.
It does not delete the chord or identify different face capacities.

Formula (9) remains valid for k=7 and larger because its polygon and
cut inequalities hold at those sizes. However the chord optimization
used to obtain (10) is proved only for 3<=k<=6; its coefficient is
already greater than one half at k=7. No k=7 substitution into (10)
is permitted without a separate full chord bound.

The existing whole short-C7 theorem supplies central *unit capacity*
one from the actual center-diameter argument; that statement does not
supply a pre-strip area bound of 51/40. Thus the generic lemma alone
does not exclude the remaining central-plus-one-side-pocket short-C7
allocation. A sharper actual polygon bound, an independent joint
geometry theorem, or a different complete allocation is still needed.

All results above are exact hand implications for the unchanged actual
units. No sampled poses, generated parameter proof, shortened positive
star, replacement means, new normals, Lean/Lake build or CI is used.
