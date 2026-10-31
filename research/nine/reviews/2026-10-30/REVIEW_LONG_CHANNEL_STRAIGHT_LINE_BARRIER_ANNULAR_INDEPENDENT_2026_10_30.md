# Independent review: the long-channel straight-line barrier

Date: October 30, 2026 UTC.

Reviewer: annular-capacity research agent, independent of the barrier
author.

**Result: PASS for the complete stated scope. No repair requested.**

## Frozen source and dependency

The complete 10,679-byte source
`LONG_CHANNEL_OUTER_STRIP_EXCLUSION_AND_STRAIGHT_LINE_BARRIER_2026_10_30.md`
was read and independently checked. Its SHA256 is

    dd1d91f8e49f4a5f507a70b53a75a30b299757f9f04a0976da3e674674ae7b05

The coupled-height input is equation (12) of
`TWO_ENDPOINT_EXPANDED_SQUARE_COVER_AND_LONG_CHANNEL_TRIANGLE_EXCLUSION_2026_10_30.md`,
whose recomputed SHA256 agrees with the imported pin

    78dfc5ed83b1538b2484007fc6d60d047c078b7f124944c0aef4dce6593558f6

That source was read, and the endpoint corner bound, tilt estimates,
triangle inequality and concave-square-root estimate deriving its
coupled-height budget were checked independently. The import applies
to the full support-gap premise with arbitrary actual endpoint tilts
and transverse positions; no circle-contact or force hypothesis is
needed for it.

## Outer-strip exclusion

The first theorem is genuinely force-free. A square meeting either
closed outer halfplane has its center within the stated narrow
horizontal cap. Its center is then at distance less than one from the
corresponding long-gap endpoint. Both horizontal and vertical estimates
are uniform over the full square, including its vertices, side
boundaries and the strip threshold itself. The exact squared-distance
bound is 565/576, with positive reserve 11/576. Thus closed strip
contact, including contact by an unstressed square, is excluded.

## Physical force line and original chords

The second theorem explicitly adds angular balance on both original
unloaded true-degree-two internal squares. Translation gives the same
signed normal and equal positive weights; torque gives collinearity
of the original application means. No line through a center is
assumed. The side/diagonal width classification follows from the
actual support points, with no genericity restriction. The center
diameter excludes even one diagonal transmitter, so both internal
pieces have unit length on the common actual line.

The inward-support-chord lemma is valid for every support point of
an arbitrarily oriented unit square. In its own side coordinates,
each nonzero normal component starts at its exposed endpoint and
changes by at most one over a unit inward step. Zero components do
not move. This includes side means and exposed vertices. Consequently
the two outer unit chords are actual subsets of the unchanged endpoint
squares, and the entire length-four segment is contained in the four
actual channel squares.

## Global barrier and boundary cases

The bound |s|<1/60 makes that segment extend strictly beyond both
outer-strip boundaries. Every completing square is in the open strip,
while its interior cannot meet any of the four other closed squares.
Its convex open interior therefore misses the entire force line and
lies in one open halfplane. Taking its closure gives exactly the
claimed closed-halfplane containment. This remains correct when the
force line runs along a channel-square boundary, when original means
are side endpoints, and when a completing square touches the barrier.

The two actual segment endpoints give

    (2+|s|)^2+t^2<=R^2<=1105/256,
    |t|<=9/16.

The aligned four-square witness at row height 1/16 proves sharpness of
this local line-height constant. Its actual application means at
height 9/16 give zero net force and moment on each internal unit; full
endpoint equilibrium is correctly not claimed by this local witness.

The completion count preserves all five squares outside the channel.
It correctly asserts only that one side has at least three, without
choosing that side or claiming that it already satisfies a sharp
three-square-cap floor condition. Translation alone is not used to
infer a straight line, and the source does not exclude multiple
channels with one common endpoint pair.

## Exact checks and verification scope

Direct rational recomputation verified 6789/10000, 73/300, 565/576,
the reserve 11/576, and Q-4=81/256=(9/16)^2, together with the strict
comparisons to 25/36, 1/4 and the diagonal-width threshold. The two
literal source pins were recomputed after the read.

This review checks the whole mathematical argument and its actual
physical scope. It is not a numerical pose certificate, Lean or CI
verification, a sharp nine-square closure, or a change to any original
ledger or remote state.
