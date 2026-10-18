# Consequences of the analytic central-square theorem

Set Q=98/25. The input to this note is the fully analytical result in
HUMAN_GLOBAL_GEOMETRY_CLOSURE.md: every packing of eight unit squares in
D_sqrt(Q) has exactly one square containing zero in its open interior.
These corollaries require no marker certificate and no contact-graph
assumption.

## 1. A semicircle holds at most three units

**Theorem.** Four unit squares with pairwise disjoint open interiors cannot
all lie in

    D_sqrt(Q) intersection {x : n dot x>=0}

for any unit vector n.

Suppose they did. Reflect the four squares through the line `n dot x=0`.
Reflection preserves the disk and all pairwise interior disjointness within
the reflected set. Every original square has its open interior in the
strict half-plane `n dot x>0`, and every reflected square has its open
interior in `n dot x<0`. Thus the original and reflected collections together
form eight distinct interior-disjoint unit squares in D_sqrt(Q).

None contains zero in its open interior. This contradicts the central-square
theorem, proving the claim.

Consequently every cap `n dot x>=h` with h>=0 also has capacity at most
three in that disk. This is a three-unit capacity statement, not a sharp
formula for the least radius of three squares in a cap. It is weaker than
the two-unit capacity bound for the more restricted cap at h=1/2.

## 2. No line can separate an eight-square packing into four and four

Suppose a line separated all eight entire squares into two collections of
four, with no square interior crossing the line. One of the two closed
half-planes bounded by that line is contained in a closed half-plane whose
boundary passes through zero and has the same normal: choose the side
away from zero, with either side permitted if the original line passes
through zero. That side contains four squares in a semicircle, contradicting
section 1.

In particular every line through zero intersects the open interiors of at
least two packed squares. One is the central square C. If no other square
interior were crossed, the remaining seven would lie wholly in the two
closed half-planes; one half-plane would contain at least four of them.
Thus at least one exterior square must also cross every diameter line.

The statement is about whole squares and open-interior crossings. Counting
only center locations on the two sides of a line would not prove it.

## 3. A uniform positive central core exists analytically

**Theorem.** There is a single epsilon>0, depending only on Q, such that
in every eight-square packing in D_sqrt(Q), the closed disk D_epsilon is
contained in the open interior of its unique central square.

This theorem gives no particular rational numerical value for epsilon.
In particular it does not replace the old radius-1/12 certificate by an
analytical proof of that same numerical constant.

Here is the compactness proof. Describe a labeled square by its center p_i
and an oriented orthonormal frame `(e_i,Je_i)`, with `|e_i|=1`.
Its four vertices are continuous functions of these data. All centers lie
in the fixed compact disk D_sqrt(Q), and the eight choices of e_i lie in
a product of eight unit circles. Vertex containment is closed. Pairwise
disjointness of open square interiors is also closed: by the separating-axis
theorem it is equivalent to the maximum of the four continuous separation
margins being nonnegative for each pair. Hence the set K of labeled
packings is compact.

For a packing P define

    delta_i(P)=1/2-max(|p_i dot e_i|,|p_i dot Je_i|),
    delta(P)=max_i delta_i(P).                            (1)

These functions are continuous. A square contains zero in its open interior
exactly when its delta_i is positive. By the central-square theorem, exactly
one of the eight delta_i is positive, and consequently delta(P)>0 on K.
The set K is nonempty, for example by ANALYTIC_RATIONAL_CONSTRUCTION.md.
The positive continuous function delta therefore attains a strictly positive
minimum delta_min on K.

Choose epsilon=delta_min/2. In the central square, the distance of zero from
each side is at least delta(P)>=delta_min. If |x|<=epsilon, its projection
on either unit frame axis has absolute value at most epsilon, so its two
local coordinate distances from the central square's center are strictly
less than 1/2. Thus D_epsilon lies in that square's open interior.
This proves the uniform claim.

The proof does not simply infer a uniform bound from pointwise positivity:
compactness, the closed packing condition, and continuity of the maximum
in (1) are the essential steps.

## 4. The central label cannot change during a continuous deformation

Consider a continuous path of labeled eight-square packings, all within
D_sqrt(Q). For each label i the set of times at which square i contains
zero in its open interior is open, because delta_i is continuous. These
sets are disjoint and cover the time interval by the central theorem.
Connectedness of the interval implies that exactly one of them is nonempty.
Therefore the identity of the central square is constant along the path.

The same conclusion follows from the uniform positive margin in section 3:
a change of label would require losing open central containment at some
time. The open-set argument shows that a numerical value for the uniform
margin is not needed.

This is relevant when using continuous deformations to obtain a normal form.
One may rotate or translate the central square, but cannot transfer the
role of containing zero to another labeled square along a path within
this radius ceiling. A discrete reconstruction can instead give a different
packing; it must be justified as a reconstruction rather than as that path.

## 5. Use and remaining limitation

These results constrain whole-square occupancy and justify a uniform amount
of space around the origin. They do not give the sharp seven-square exterior
angle budget. In particular the semicircle capacity does not count squares
whose interiors cross the dividing line, and the abstract positive core
cannot be inserted into inequalities requiring the specific value 1/12.
The unrestricted sharp lower bound still needs the explicit geometric
reductions listed in SMALL_STEP_ROADMAP.md.
