# Two real transmitter paths have strictly ordered lengths; the whole D02.L014 row is impossible

Date: October 29, 2026 UTC. Author: hexagon continuation.

**Status: complete proposed hand theorem and complete original-row join,
frozen for separate full independent review.** The main comparison is
radius-free and applies to arbitrary lengths of actual unloaded paths.
For one internal unit on each path it forces one side transmitter, one
diagonal transmitter, and an acute angle strictly below45 degrees. One
loaded-endpoint torque sign then eliminates every physical unique-circle
mask. The existing radial-diagonal theorem handles the physical two-corner
mask, giving an entire original load-row contradiction without an
extra-square allocation.

No original checkbox, count, ledger, source or review is changed by this
manuscript. The new whole-original conclusion, after independent review,
is exactly `M6.B6.HEXAGON.D02.L014` and its full-data reflected image.

## 1. Actual graph, complete equations, and exact path lengths

All units are actual closed unit squares with pairwise disjoint open
interiors. Retain all original force and torque equations, every positive
magnitude and unit normal, every actual application point and complete
shared-side mean. Zero circle load does not mean physical circle clearance.
No containing radius is assumed in Sections1--4.

Let U be unloaded true positive degree three, with its entire positive
neighborhood exactly V,W,T1. Assume V and W physically touch. They may
have arbitrary true degrees, other positive forces and circle loads.

There are two actual positive paths to the same actual endpoint C:

    U--T1--...--Tm--C,
    W--B1--...--Bk--C,             m,k>=1.

All displayed bodies are distinct except the common C. Every Ti and Bj
is genuinely unloaded true positive degree two with exactly its displayed
predecessor and successor. C has arbitrary degree and circle load here.
No positive force is removed to create either path. Every original
internal square remains present.

Let n be the original forward normal on the first path and l the original
forward normal on the second. The complete force and torque equations of
each unloaded true-two unit give its unchanged point translation

    outgoing application minus incoming application = w*n,
    w in {1,sqrt(2)},

or the same formula with l on the second path. Force balance gives one
common forward unit normal and one positive magnitude along each path;
torque puts the original applications on the same force line. A side
axis gives width1. Otherwise the supports are opposite vertices, and
their difference being parallel to the force forces the actual square
diagonal and width sqrt(2). This includes all original side means and
their endpoints.

Denote the exact path lengths by

    L_T=sum_i w_Ti(n),       L_B=sum_j w_Bj(l).

These are sums of physical widths, not graph distances or lengths of
virtual edges. Write h=h_U(n), where h_U is absolute maximum support.

## 2. The complete strict length-order theorem

The accepted full-star theorem
`UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md`
applies to this actual U3 and its physically touching returns V,W. It uses
the complete actual U force and torque, with no circle, normal-selection,
return-owner or return-degree premise. It gives

    n.z<h for every actual z in W.

Compactness of W therefore supplies the strictly positive actual gap

    Delta=h-h_W(n)>0.                              (1)

The first path ends at an actual minimum-n support point of C. Thus

    ell_C(n)=h+L_T.                                (2)

On the second path let X be the original application in W and Y its final
original application in C. The complete point transmission, retaining all
actual Bj, gives

    Y-X=L_B*l,      X in W, Y in C.                 (3)

Apply the original n projection to these actual points. Equations(1)--(3)
give

    h+L_T <= n.Y
           =n.X+L_B*(n.l)
           <=h_W(n)+L_B*(n.l).

Consequently

    L_T+Delta <= L_B*(n.l) <= L_B.                  (4)

In particular

    L_T<L_B,
    n.l>L_T/L_B>0.                                 (5)

The strictness comes from the original full-U3 support gap, not a
perturbation of a mean or deletion of an equality case. This proves the
whole two-path theorem for all original frames, circle masks and
applications. No equation at V,W,C has been shortened or assumed.

### 2.1. One real return transmitter forces the exact two widths

If k=1, then L_B is1 or sqrt(2). Since m>=1 and L_T>=m, equations(4)--(5)
force

    m=1,
    T1 is a side transmitter, L_T=1,
    B1 is a diagonal transmitter, L_B=sqrt(2),
    n.l>1/sqrt(2).                                 (6)

Thus the two original channel directions have angle strictly below pi/4.
This is a complete radius-free exclusion of all other width combinations,
including two side transmitters and a diagonal outgoing Ti.

### 2.2. Two unloaded triangle hubs cannot have such paths to one common endpoint

Suppose additionally that W is unloaded true positive degree three with
its entire positive neighborhood U,V,B1. The actual U,V contact is already
present. Apply the same full-star separation and path theorem with U,W
interchanged, retaining their respective real paths to C. It gives
`L_B<L_T`, contrary to(5).

Therefore the entire double-unloaded triangular junction is impossible,
for arbitrary positive path lengths and arbitrary degrees/loads at V,C.
This statement does not remove any extra force at a higher-degree U or W:
both displayed true-three hypotheses are essential. It is a local graph
shape exclusion usable in larger components after those exact stars are
checked. No new original case count is inferred from the graph shape alone.

## 3. A loaded two-force endpoint with acute incoming normals cannot have a unique circle corner

This separate lemma uses a circle center O=0. Let C be an actual contained
unit with positive total circle load and true positive degree two. Its two
original outward pair forces are

    -lambda*n at A,       -eta*l at M,
    lambda,eta>0,

where n,l are unit vectors, l is an own side axis of C, and

    n.l>1/sqrt(2).                                 (7)

The actual points A,M are respectively minimum-n and minimum-l support
applications of C, including original shared means. All physical circle
corners and their individual nonnegative coefficients remain.

**Endpoint lemma.** C cannot have exactly one physical circle corner.

To prove it, rotate the whole data about O so l=East. Reflect the transverse
axis if needed, so

    n=(a,b),      a>b>=0,      a^2+b^2=1.

Write C=[x,x+1]x[y,y+1]. Complete force balance is

    F_C=lambda*(a,b)+eta*(1,0).                    (8)

Suppose the physical circle corner is unique, say Z. Its positive total
coefficient makes F_C a strictly positive multiple of that same actual Z.

If b=0, equation(8) would give Z_y=0. This is impossible for a farthest
corner of a unit with own axes East/North: the greater absolute value of
its two y endpoints is at least1/2. Thus the unique-mask branch has b>0.

Now both coordinates of F_C are positive. The sole farthest physical
corner must therefore be the upper-right corner

    Z=(x+1,y+1).

This follows from independent farthest-coordinate maximization: a unique
farthest positive x coordinate is the right endpoint, and the identical
statement holds in y. Since both components of n are strictly positive,
its actual minimum support is the lower-left corner

    A=(x,y),
    M=(x,t),        y<=t<=y+1.

Take the entire original torque about Z. The only circle force acts at Z
and contributes zero. The two unchanged pair-force moments are

    det(A-Z,-lambda*n)=lambda*(b-a)<0,
    det(M-Z,-eta*l)=eta*(t-y-1)<=0.

Their sum is strictly negative, contradicting exact full torque balance.
Both endpoints of the original M mean remain in the weak second term.
No proper concurrence, boundary neighbor or virtual application is used.
This proves the entire endpoint lemma, including parallel n=l via the
separate b=0 argument.

At the current radius window a positively loaded contained unit has either
one physical circle corner or two adjacent physical circle corners.
Indeed farthest corner norms maximize the two own-coordinate signs
independently; a tie in both coordinates would center the unit at O and
give radius1/sqrt(2), outside the window. Therefore the endpoint lemma
forces exactly two physical circle corners. It does not assert equal
circle weights: one of the two original coefficients may be zero.

## 4. Broad high-radius exclusion of the actual six-unit motif

Retain the setting of Section1 with k=1. In addition assume

    sqrt(17)/2 <= R <= sqrt(1105)/16,

all actual units lie in the same disk, C is positively loaded true degree
two with exactly Tm,B1 as positive neighbors, and W physically touches
the circle. V retains arbitrary degree and circle load in this section.
Use the original compatible strict point-normal certificate with diagonal
avoidance chosen before multiplier extraction.

By(6), m=1, T=T1 is side, B=B1 is diagonal, and n.l>1/sqrt(2).
The original diagonal avoidance makes the two actual diagonal-B contacts
relative-side-interior contacts on W,C. A positive-length shared segment
cannot be supported at the uniquely exposed B diagonal vertex, and a
vertex/vertex singleton in that diagonal direction was excluded by the
common preselection. Consequently l is an own side axis of both actual
W and actual C. No normal is selected again.

At the actual C2 its two outward forces are exactly `-lambda*n` from T
and `-eta*l` from B, with their original positive magnitudes. Their actual
applications realize its two minimum supports. Section3 applies and
forces the actual physical-two-circle mask at C, including all individual
zero coefficient cases.

The real path C--B--W now has a genuine unloaded diagonal transmitter,
one physically radial endpoint C, and one physically boundary endpoint W.
The complete accepted degree-free theorem
`RADIAL_BOUNDARY_DIAGONAL_CHANNEL_RADIUS_RESTRICTION.md` therefore forces

    R^2<17/4,

contrary to the high-radius premise. It retains the actual application
mean, every endpoint degree and mask, and the already selected diagonal
avoidance. It includes its own critical equality argument. Thus the whole
six-unit motif is excluded at the printed high-radius scope.

For clarity, the operative radial-channel geometry is elementary. In the
radial endpoint frame C=[d,d+1]e+[-1/2,1/2]f with
`d=sqrt(R^2-1/4)-1`, the outward and tangential channel axes force an
endpoint beyond the disk and are impossible. The inner axis gives

    P_C=d*e+t*f, |t|<=1/2,
    P_W=(d-sqrt(2))*e+t*f,
    W's e interval=[d-sqrt(2)-1,d-sqrt(2)].

At d=1+epsilon>=1 its farther e coordinate is epsilon-sqrt(2).
Physical boundary of W gives its largest absolute f endpoint M through

    M^2=9/4+(4+2sqrt(2))*epsilon.

When epsilon>0 the entire unit f interval of W misses[-1/2,1/2], contrary
to the unchanged t. At epsilon=0 only t=+/-1/2 is possible, making the
radial endpoint application a vertex/vertex singleton with an own-axis
normal, contrary to the original strict convention. These are precisely
the complete physical masks of the imported theorem.

## 5. Entire original D02.L014 domain

Retain all nine original actual units and the full selected positive
six-body component with edges

    01,12,23,34,45,50,02,

and exactly the positive circle-load set

    {0,1,4}.

The true degree tuple is(3,2,3,2,2,2). Use the actual role map

    U=2, V=1, W=0, T=3, C=4, B=5.

Every original positive star is then exactly

| Body | Complete positive neighbors | Degree | Circle load |
| --- | --- | ---: | --- |
| U2 | V1,W0,T3 | 3 | zero |
| V1 | U2,W0 | 2 | positive |
| W0 | V1,U2,B5 | 3 | positive |
| T3 | U2,C4 | 2 | zero |
| C4 | T3,B5 | 2 | positive |
| B5 | W0,C4 | 2 | zero |

Thus U,V,W form the actual physical triangle; the outgoing path is the
real2--3--4 and the second path is the real0--5--4. The two internal units
are distinct actual unloaded true-two bodies. No 2--4 or0--4 edge is
invented. In particular the real W0 remains degree three throughout.

The original radius window is

    79/40<=R<=sqrt(1105)/16.

The complete corrected boundary-triangle chain theorem
`BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_CHAIN_COMPLETE_RADIUS_REDUCTION.md`
applies to this exact actual U3,V2, physically boundary V/W, and actual
unloaded T2 followed by C. It excludes the entire low and critical range
`R<=sqrt(17)/2`, independently of original axis count, owner, mask and
mean. The original lower endpoint and the critical equality are covered.
Equivalently the same-nine lower-window input may be applied first, but
it is not needed by this direct complete low/critical invocation.

Every remaining original configuration is in the strict high range. All
hypotheses of Section4 are literal: C4 is positively loaded true2, W0 is
physically boundary, B5 is unloaded true2, and the common diagonal-avoiding
certificate is the unchanged original one. That theorem excludes the
entire high range without any contact-owner subdivision.

Consequently

    M6.B6.HEXAGON.D02.L014 is excluded over its entire original domain.

The graph reflection `i -> 2-i (mod6)` sends the role map to
`U0,V1,W2,T5,C4,B3` and the load set to `{1,2,4}`. It transports every
actual normal, original application, full mean, true force equation,
physical mask and coefficient simultaneously. This is the full reflected
image of the same existing representative, not another counted row.

All three original extras remain arbitrary actual squares. No central,
channel or closing-pocket occupancy has been asserted. The contradiction
already occurs among the actual six core units; no completion square is
discarded from the nine-square packing.

## 6. Relationship to the earlier bypass theorems and exact limits

`UNIT_BYPASS_NORMAL_CHANNEL.md` assumes one actual unit directly touches
both endpoints of a normal channel. It proves that such a channel has one
side transmitter. In the present two-path geometry, W does not directly
touch C: the real B path intervenes. That older theorem's single-unit
bypass premise is not available and is not used as a replacement edge.

`UNLOADED_TRIANGLE_HUB_CHANNEL_BYPASS_EXCLUSION.md` assumes that one actual
return X of an unloaded U3 directly touches the far endpoint of U's
outgoing channel. It excludes that whole direct-bypass configuration.
Here the return W reaches C through genuine unloaded internal units.
Section2 supplies the stricter relation between both actual path lengths,
the two-channel direction inequality, and the reverse-hub contradiction.
The old direct-bypass result is not transferred after adding a force.

The high-radius theorem additionally uses the genuine C2 load/torque and
the physical boundary of W. It may be used in larger components with
arbitrary extra positive forces at V and W, provided U stays true3, T/B
stay true unloaded2 and C stays true loaded2. If U or C gains a positive
force, the source supplies no automatic extension.

Original D02.L0145 is different: B5 is loaded there and need not transmit
a common normal or the exact width1/sqrt(2). This source does not apply
the B-channel calculation in that row and gives it no whole-row credit.
The other three still-open D02 representatives with both triangle hubs
unloaded also lack the displayed unloaded-path hypotheses. Their flags
cannot be changed merely because Section2.2 mentions two unloaded hubs.

## 7. Exact reading, discovery and independent-review boundary

The new deductions are the full ordered-path inequality(4), its exact
one-return-transmitter alternative(6), the double-hub contradiction,
the loaded-endpoint torque lemma, and the complete high/low original join.
They were derived by hexagon continuation. Root was informed during
discovery but supplied no step, constant or repair to these deductions.
The earlier bridge-span discussion and the preserved support-separation,
diagonal-radius and chain-reduction proofs retain their own authorship.

The entire support-separation theorem, corrected chain-reduction source,
radial-diagonal source and full existing radial review were read, as were
the entire physical-stress source, actual graph/load cover and relevant
diagonal-selection construction. The full corrected chain review was
also read. The direct-bypass sources were compared at their complete
operative hypothesis/geometry scopes; they are historical comparisons,
not imported whole-theorem calls in this new proof.

The complete new source needs a separate full independent audit before
any original flag or parent accounting changes. No historical theorem or
review has been edited or silently repinned. No sampled orientation,
pose enumeration, new computational packing certificate, Lean/Lake,
build, CI, workflow, commit or remote write is part of this proof.

| Complete operative input or preserved review | SHA-256 |
| --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe |
| UNLOADED_THREE_FORCE_TOUCHING_RETURNS_STRICT_SUPPORT_SEPARATION.md | 406fce53d22cc20eec43a373a877798dab583a6bd93f684ff124293016c44c87 |
| REVIEW_GENERAL_THREE_FORCE_TOUCHING_RETURN_SEPARATION_THIN_D_2026_10_28.md | bc4a2c79adbdb2715df4f29da48c7cb432eef38efd1e4d55a051ec152bcafb1c |
| RADIAL_BOUNDARY_DIAGONAL_CHANNEL_RADIUS_RESTRICTION.md | a2fd0fd1a0096fed561b2e5da4f2eeafe884953e2e69bb324bb381985f4d686e |
| REVIEW_RADIAL_BOUNDARY_DIAGONAL_RADIUS_ROOT_2026_10_26.md | 6e5f83478fa89b49c8763ea8c8a7ec2a0c7b1b49417aef700622365ef9c91279 |
| BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_CHAIN_COMPLETE_RADIUS_REDUCTION.md | a967bb48602466727c2b28208f8884d50be96f03a553abaaa42d960661e9ee33 |
| REVIEW_BOUNDARY_TRIANGLE_UNLOADED_TERMINAL_COMPLETE_RADIUS_REDUCTION_REVIEW_RESUME_2026_10_29.md | f0493ed4912561f48f61a806d7ad20cb832a094a2ff1b43f0258a566bac04623 |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 |

All original mean endpoints, both physical circle masks, every individual
zero circle coefficient, all genuine stars and all nine actual units are
retained. The sharp global n=9 inequality and the other original gates
remain separate obligations.
