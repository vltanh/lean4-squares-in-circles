# A seven-atom compatible certificate for the same eight-unit cross

Date: October 30, 2026 UTC.

**Status: complete proposed exact companion, awaiting independent
review. The frozen outer-face diagnostic is unchanged.**

Keep all eight actual unit squares and labels of
`EXACT_EIGHT_BODY_OUTER_FACE_CYCLE_WITH_UNLOADED_BRANCHING_VERTICES_2026_10_30.md`,
frozen SHA256

    d04ce78b5bb4656accbef54b0d19cbb94d5480b6e407d697399c0763a9632a4e

The four central centers are (±1/2,±1/2), and the outer centers are
E=(3/2,0), N=(0,3/2), W=(-3/2,0), S=(0,-3/2). Their exact containing
squared radius is 17/4. The original source proves physical
nonoverlap and also proves that no ninth unit can be added even in
the larger disk of squared radius Q=1105/256.

## 1. The explicit alternative has seven positive scalar atoms

Give coefficient lambda=1/4 to each of the four actual circle corners

    (2,1/2), (2,-1/2), (-2,1/2), (-2,-1/2).

They belong to E and W. All other circle coefficients are zero,
including those on the physically boundary-touching bodies N and S.
The total circle coefficient is one.

Keep exactly these three positive pair atoms:

| Directed pair | mu | n | Actual application p |
| --- | --- | --- | --- |
| E to NE | 2 | (-1,0) | (1,0) |
| NE to NW | 2 | (-1,0) | (0,0) |
| NW to W | 2 | (-1,0) | (-1,0) |

Each p is an endpoint of the original actual shared-side segment.
Its normal is the true common horizontal support normal. No square
or physical contact is moved. All other selected pair magnitudes
are zero. The seven positive scalar atoms are precisely these three
contact endpoint atoms and the four circle atoms.

## 2. Full force, torque and compatibility

At E, the circle contribution is

    2*(1/4)*[(2,1/2)+(2,-1/2)]=(2,0),

which cancels its contact force (-2,0). At W the signs reverse.
At each of NE,NW the two contact forces are equal and opposite.
The remaining four physical bodies N,S,SE,SW have zero selected
forces and zero selected circle load, so their equations are also
satisfied.

Every positive contact lies on y=0 and has a horizontal force.
Each therefore has zero origin moment individually. Every circle
force is radial and likewise has zero origin moment. Full force
balance then also gives zero moment about each actual body center.
All eight original physical units satisfy the complete equations.

The positive graph is the actual path

    E -- NE -- NW -- W.

Its original center-to-application route is strictly decreasing in
x, hence simple. At the central four-square junction it uses only
the adjacent pair NE--NW. It is therefore compatible with the
physical sectors and with the original E/W circle-access spokes.
No crossing pair or incompatible graph embedding is introduced.

Its endpoints E,W are positively circle-loaded; NE,NW are genuine
unloaded true-degree-two transmitters. This is also a literal
example of the positive-long-endpoint conclusion. It makes no
claim about the global minimum possible support size.

## 3. Twenty aggregate terms, thirty-two endpoint atoms, and seven chosen atoms

The frozen outer-face-C8 certificate has twelve positive aggregated
pair terms at their shared-segment midpoints, and eight positive
circle terms. Thus it has twenty displayed positive aggregate
terms.

Its stated actual endpoint representation replaces each magnitude
1/2 midpoint term by two magnitude-1/4 atoms at that segment's two
actual endpoints. That representation has twenty-four positive
contact atoms and eight positive circle atoms: thirty-two positive
scalar atoms in total.

Every atom of the new seven-atom certificate is already one of
those thirty-two actual atom types. The new certificate is an exact
sub-support reweighting of that finite physical atom family. Its
circle normalization and every body force and moment were verified
above, so no numerical sparse solver or minimization claim is
needed to establish this representation.

It is not obtained by deleting old aggregate-mean vectors while
keeping their application points fixed. For example the old
applications on E--NE, NE--NW, NW--W have respective heights

    1/4, 1/2, 1/4.

If only that positive path were kept at those old means, force
balance at NE would require equal horizontal magnitudes mu>0,
but its origin moment would be

    -mu/4+mu/2=mu/4>0.

Thus full moment balance fails. The new actual endpoint atoms
change those aggregate application means explicitly to height zero.

There is a stronger exact fixed-family check. If one allows arbitrary
nonnegative weights on only the original twenty displayed aggregate
vectors, with all twelve old means fixed, force balance at NE
makes its two horizontal magnitudes equal and its two vertical
magnitudes equal. Its torque equation then equates those horizontal
and vertical magnitudes. Hence all four incident magnitudes agree.
Rotation gives the same statement at every central body. The
connected central C4 therefore forces all twelve pair magnitudes
to one common value mu. At each outer body, vertical force balance
in its rotated frame makes its two circle coefficients equal;
horizontal balance gives lambda=mu/4. Normalization gives

    8*lambda=1, mu=1/2, lambda=1/8.

So the original normalized aggregate certificate is unique within
that fixed twenty-vector family. The availability of the much
sparser physical endpoint-atom certificate is entirely consistent
with this uniqueness: the two permitted vector families differ.

## 4. Scope for selection arguments

The outer-face example obstructs a universal cycle bound based only
on arbitrary physical force/torque balance and compatible planarity.
It is not a counterexample to a theorem that deliberately selects a
smaller physical certificate first. The explicit alternative here
already replaces the positive C8 by a four-body path while keeping
all eight physical squares.

Conversely, neither graph structure nor an old aggregate application
mean can be silently retained after the selection changes. A proof
using a selected certificate must verify all its required properties
on that same selection. This companion illustrates that distinction;
it does not close the original common-selection gate or characterize
minimum-support certificates globally.

No original source bytes, physical poses, ledger flags, Lean files,
CI state or remote state were changed. All displayed coefficients,
means and balance checks are exact.
