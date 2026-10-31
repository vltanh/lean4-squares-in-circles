# Independent review: the zero-channel S123 hole and conditional slider

Date: October 27, 2026.

Reviewer: triangle_bridges, independently of the source author rooted_blocks.

**Decision: ACCEPTED in its complete stated physical and conditional scope.**
No mathematical or wording correction is requested. This is a full source
and dependency audit, not an inference from the source title or abstract.
Root review and any integration remain separate.

## 1. Exact reviewed source and dependencies

The entire reviewed source is

    S123_ZERO_CHANNEL_OWNED_RETURN_HOLE_EMPTY.md
    SHA256 02ddb17e3287ff203dd703a6e2333694ea0ca17a4cb9551bf65ce632a2915b17.

I read CONTACT_RING_HOLE_AREA.md in full, including the actual
center/contact homotopy, its nonnegative limiting winding and occupied
piece subtraction. I also read FOUR_CYCLE_SECONDARY_CONTACT_REDUCTION.md
in full, in particular its Section1 compact secondary minimizer choice,
and PHYSICAL_BODY_GRAPH_UNCROSSING.md in full. Only the global secondary
choice is imported from the four-cycle source; no four-cycle geometric
conclusion is transferred to this five-cycle.

The source keeps the original A--B--M--C--U--A, its genuine leaf, and
all three completion squares. The entire U slider, both original shared
side means and every physical M circle mask remain in the statement.
Its area argument does not need a M force equation or a unique mask.

## 2. Actual Jordan loop and subtraction

I checked every possible contact coincidence. E,D have height at most
zero and differ horizontally by one; P has height1/2; S,Q have height
at least F>1/2 and distinct horizontal coordinates -J<0<u. Thus the
five applications are distinct. The open center-to-contact strands lie
in their own disjoint square interiors. Within one square, two distinct
boundary points cannot lie on the same ray from its center. Consequently
the actual center/contact loop is simple, without any additional
assumption about other physical contacts.

The limiting contact polygon has the clockwise orientation displayed
in the source: its bottom edge D--E runs left and all other contacts are
strictly above it. The homotopy gives winding zero or minus one, so its
clockwise signed-area magnitude is an area, without cancellation.

For each of the three ABC triangles I checked the determinant of its
auxiliary corner relative to the actual oriented chord. It is on the
right, the inward side. A positive-area triangle has interior in its
actual square and cannot meet another polygon edge. The inward winding
jump is therefore one in magnitude throughout that triangle. A
degenerate triangle contributes zero and requires no jump assertion.
Their interiors are disjoint by the original physical packing.

The full shoelace expansion after these three subtractions is exactly

    T+(u-epsilon)F+(d-u)/2+(X-u)(Y-1/2)/2.

This identity does not require u>=epsilon, strict convexity, or absence
of limiting retracing. Winding subtraction precedes the algebra.

## 3. Every actual M frame and mean

If M owns East, the positive vertical component of its actual C normal
puts P on its bottom face at height1/2. The triangle through Q, the
bottom-left corner and P is inward and cancels the complete last term.
Its full original X remains; no endpoint is substituted.

For strict M, its inward axes v=(c,s), w=(s,-c) have c,s>0.
The actual C normal has h.w<0, so the exhaustive support form is
P=Q+w+lambda*v, 0<=lambda<=1. This covers both vertices and the full
shared-side mean. The inward M triangle has area lambda/2. I separately
expanded the remaining term as

    cs(1-lambda^2)/2-lambda*s^2 <= 1/4.

Both lambda endpoints are included. No circle or concurrence premise
enters this step. Combining the exact subtraction with T<=1-F gives
the stated upper bound

    5/4-(F-1/2)(W+epsilon).

## 4. Strict area reserve

I independently differentiated

    f(y)=(y-1/2)sqrt(R^2-(y+1)^2)

and obtained the displayed strictly negative second derivative.
The actual y=F lies in the interior of the comparison interval because
W<1 and F<1. The two endpoint values exceed1/4: the first uses
sqrt(13)/2-3/2>1/4, equivalently13>49/4; the second uses R^2>17/4.
Thus (F-1/2)W>1/4. With epsilon>0 the complete free-hole area is
strictly below one. An additional unit inside the actual Jordan loop
would contribute its full open area one, so it is excluded.

## 5. Conditional minimizer movement

I checked the full actual motion, including all other original units.
If U.top=b<1/2 and U has no physical M contact, a sufficiently small
upward translation avoids M by its positive compact-set distance.
A and C remain separated by the unchanged vertical support lines;
B starts above F>1/2. All new open interior points lie in

    (epsilon,d) times (b,b+small), with -T<y<1/2.

The whole larger open rectangle (epsilon,d) times(-T,1/2) has winding
one in magnitude: the polygon's left closing chain has x<=epsilon,
its right chain x>=d, its upper chain has y>=1/2, and its bottom is
the actual unit segment D--E. For points outside the core squares,
the contact homotopy equates this winding with that of the actual
center/contact loop. A connected extra-square interior cannot enter
that bounded region from the exterior without crossing a core square.
The hole theorem therefore protects the new strip against every
original extra and the genuine leaf, not merely the selected graph.

The translation moves the transverse U center b-1/2 toward zero,
strictly reducing both its maximum corner radius and its contribution
to the existing secondary objective. It yields the exact conditional
alternative U.top>=1/2 or physical U--M contact. It does not assign
a positive stress to such a contact.

For axis M, its actual bottom height1/2 and overlapping horizontal
interiors force U.top<=1/2, since U contains an application at height
-T<=0. There is no U--M contact below1/2. Hence U is centered
transversely exactly as claimed.

For strict M, the source correctly asserts only the alternative.
In particular an actual C mean X>d can leave its lower M edge above
height1/2 over x=d, so no centering follows from nonoverlap alone.
This endpoint remains outside the conclusion.

## 6. Exact accepted scope

The physical hole theorem, the conditional slider alternative, and
the axis-M centering consequence are each accepted in full. The
source does not claim an exterior completion bound, clearance from a
central1/8 disk, a centered arbitrary transmitter, or whole S123
closure. Those distinctions are necessary and have been preserved.

No sampled configuration, numerical optimization, altered normal,
deleted load, chosen side mean, compilation or remote action forms
part of this review.
