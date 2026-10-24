# Two parallel transmitters leave no third unit-square bypass

**Status: complete radius-free hand local theorem; root and separate
independent full hand audits passed.** Use the existing selected
strict point-normal convention: a positive singleton vertex/vertex
contact cannot carry a normal on a side-axis endpoint of either
square's common normal cone. No new normal is selected in this proof.

Let A,B be distinct unit squares. Let T1,T2 be two distinct unloaded
bodies of exact positive degree two, each with exactly the positive
neighbors A,B. Keep all of their actual application means. Other
positive forces and circle loads at A,B are unrestricted.

**Theorem.** No third distinct physical unit square C can touch both
A and B while all five squares have pairwise disjoint open interiors.
The C contacts need not have positive multipliers; C may carry arbitrary
additional positive forces, load or physical circle mask.

The theorem has no containing-circle premise. Its only certificate
hypotheses concern the two true transmitters and the already fixed
strict positive point-contact normals.

## 1. Both actual channels have width one and the same direction

Each T_i is a genuine normal transmitter by its two positive force
and torque equations. The other T_j is a physical unit bypass for
its channel. UNIT_BYPASS_NORMAL_CHANNEL.md, Sections 1--2, therefore
makes both transmitters side-normal, with reserve exactly1.

Lemma N.2 of PARALLEL_TRANSMISSION_AND_FOUR_CYCLES.md makes their
normal directions and reserves identical: both channels realize the
unique shortest displacement vector between the two endpoint units.
Rotate and translate, without altering any physical square, so that

    A lies in y<=0,   B lies in y>=1,
    T1 = I1 x [0,1],  T2 = I2 x [0,1],

where I1,I2 are closed intervals of length1. Their interiors are
disjoint. Relabel them so

    I1=[l,l+1],   I2=[r,r+1],   r>=l+1.

Each transmitter's actual lower and upper applications have the
same first coordinate. All their original permitted transverse
means remain; no midpoint condition is imposed.

## 2. Both endpoints must own the common channel axis

Suppose A did not own the upward side axis. Its maximum-y support
would then be one unique vertex. Both actual A-to-T_i applications
must equal that vertex. Thus I1 and I2 meet at that vertex's first
coordinate. Their disjoint interiors force r=l+1, and both
applications are lower corners of their respective transmitters.

Each A--T_i contact is consequently singleton vertex/vertex, and
its actual channel normal is vertical, a side axis of T_i. This
contradicts the existing strict point-normal convention. It is a
contradiction in the original certificate, not a change of that
normal after extraction.

Hence A owns the vertical side axis and is aligned with the two
transmitters. The identical maximum/minimum argument at B makes
B aligned as well. Write their horizontal support intervals as

    J_A=[a,a+1],   J_B=[b,b+1].

Each J_A intersection I_i has positive length. Otherwise the
actual positive A--T_i contact would again be singleton
vertex/vertex between aligned units, with forbidden vertical
axis normal. Likewise every J_B intersection I_i has positive
length. The actual weighted mean may be an endpoint of such a
positive-length intersection; all those endpoint values remain.

For A alone the two positive-length conditions give

    a < l+1,   a+1 > r.

In particular the gap between the two transmitter intervals obeys

    0 <= r-(l+1) < 1.

No strictness of an actual application mean was used in obtaining
this strict geometric gap.

## 3. A third physical bypass cannot occupy any transverse position

Suppose C physically touches both A and B. Apply the complete
transverse-separation corollary in UNIT_BYPASS_NORMAL_CHANNEL.md,
Section 4, to C and each actual side transmitter T_i. It says that
C and T_i are separated along the horizontal axis. This implication
allows an arbitrary tilted C and uses only its physical contacts to
the endpoint units; neither contact needs a positive force.

The horizontal projection of C is an interval of length at least1,
since every unit square has directional width at least1. It is
disjoint in interior from both ordered intervals I1,I2, so there
are exactly three possible positions.

* If C lies between T1 and T2, its horizontal width is at most
  r-(l+1)<1, impossible.
* If C lies to their left, max_x(C)<=l. But a+1>r>=l+1 gives
  a>l. Every point of A has x>=a>max_x(C), so C cannot touch A.
* If C lies to their right, min_x(C)>=r+1. But a<l+1<=r gives
  a+1<r+1. Every point of A has x<=a+1<min_x(C), again preventing
  its physical contact with C.

All three alternatives are impossible. This proves the theorem,
including every equality in the transmitter separation and every
shared-side endpoint mean.

## 4. Exact scope and immediate graph consequences

The result excludes any selected local K2,3 pattern in which two
of the three common neighbors are true unloaded degree-two
transmitters. The third neighbor needs only physical contacts to
the same endpoint bodies; it is not made into a transmitter.

In particular, in the two-spoke interior-pentagon graph with spokes
H--0,H--2 and outer chord03, the positive-load family024 is entirely
excluded. H and1 are true unloaded degree-two transmitters with
endpoints0,2. Body3 physically touches both endpoints through03
and23. The theorem applies with its actual degree three and all its
other forces retained. Every radius, physical mask, shared mean
and all three extra packing squares remain.

FIVE_BODY_BLOCK_LEAF_GRAPH_LOAD_COVER.md applies the same local
implication to both root orbits of K2,3, with all additional root
forces kept. It makes no statement about a
body of degree three obtained by deleting its third force, or a
zero circle multiplier at a body of higher positive degree.

No new generic choice, numerical sample, containing-radius bound,
completion motion, Lean compilation or CI is used.
