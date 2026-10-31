# Four-spoke no-chord pentagons: occupied pockets and compulsory long ports

**Status: complete necessary-domain hand reduction, submitted for independent
review. Neither original four-spoke load family is declared excluded.**

Keep the original nine physical unit squares, the unchanged circle origin,
the compatible original certificate, and

\[
                    79/40\le R\le\sqrt{1105}/16.
\]

The complete positive component has outer rim `0-1-2-3-4-0` and actual
interior hub `H`, with exactly the four spokes `H0,H1,H2,H3` and no outer
chord. All pair weights are strictly positive on those displayed edges.
The true degrees are `H4`, `0/1/2/3` each degree three, and `4` degree two.
All three additional actual units remain arbitrary and present.

The complete accepted load cover leaves exactly the two representatives

\[
 \texttt{M6.B6.PENTAGON.H4\_D0.L124},\qquad
 \texttt{M6.B6.PENTAGON.H4\_D0.L0124},
\]

with graph-preserving reflection `i -> 3-i modulo 5`. This reflection
exchanges `0,3` and `1,2` and fixes `4`. The original no-chord domain also
retains the complete physical restriction that `H` and `4` are
closed-disjoint; no zero-weight `H4` contact is added.

## 1. Every completion unit is exterior to the occupied rim

The physical theorem
`INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md`,
Sections 1--4, applies to this graph without any change. Its original
statement explicitly permits arbitrary interior hub degree and allowed
outer chords. In the present caller the hub is the actual degree-four
unit and there is no chord.

For clarity, its full whole-unit join is the following. The rim
center/contact loop has arbitrarily small compatible Jordan resolutions
with the unchanged cyclic sector order. The actual open hub has winding
one, and the entire open interior of any extra square has constant
winding zero or one, since it avoids every closed rim square. Contract
the rim centers to their respective original contact-chord midpoints
inside their real units. The limiting contact pentagon still has winding
only zero or one, even at coincident contacts and retraced weak edges.
The complete long-chord subtraction and polygon inequality give free
inner area at most

\[
             \frac54\cot(\pi/5)<2.
\]

The unchanged actual hub already contributes area one there. An entire
inner extra would contribute another unit area, a contradiction. Thus
every one of the three extras is exterior. No interior unit is replaced
by a point, and no local force equation is shortened.

Simultaneous actual circle spokes at the loaded rim bodies then assign
each whole open extra to one exterior pocket. The complete physical
boundary-pair pocket theorem excludes any pocket whose rim path is a
direct contact between two marked boundary bodies. This allocation
includes all weak contact junctions and all original shared means.

## 2. Exact pocket unions for both original load representatives

The literal paths are:

| Whole original family | Direct pockets containing no extra | Only allowed exterior union for all three extras |
| --- | --- | --- |
| `H4_D0.L124` | `1--2` | `1--0--4` and `4--3--2` |
| `H4_D0.L0124` | `4--0`, `0--1`, `1--2` | `2--3--4` only |

All paths name the actual cyclic rim arcs, and reversing a path names
the same pocket. The fourth spoke and every third rim force remain in
these descriptions.

For `L0124`, the zero-load body `3` is physically circle-clear. Otherwise
all five rim units would be physical boundary units, producing the
forbidden physical boundary five-cycle. Thus all three extra units lie
in the one actual two-edge pocket through this clear degree-three body.

For `L124`, the two unloaded bodies are exactly `0,3`, both of true
degree three. Neither or exactly one may physically touch the circle;
both cannot, by the same physical five-cycle exclusion. If one does,
insert its actual circle spoke in the existing simultaneous partition.
Its two incident boundary-pair pockets are empty, so the entire original
two-edge pocket through it contains no whole extra. In that case all
three extras belong to the other listed pocket. When both are physically
clear, the two-pocket union remains. A zero total multiplier was never
used as a substitute for physical clearance.

## 3. Three loads force at least one genuinely long contact pair

Consider `L124`. Sum the original force equations over the six-body
component. Every original pair force cancels at its two endpoints,
leaving exactly

\[
                          F_1+F_2+F_4=0.
\]

Each term is the actual nonnegative circle-corner resultant with
strictly positive total weight. The real rim contact `12` gives
`|c_1-c_2| <= sqrt(2)`. The full-window metric theorem
`GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md`
therefore forces

\[
 |c_1-c_4|>1+\sqrt2
 \quad\hbox{or}\quad
 |c_2-c_4|>1+\sqrt2.
\tag{1}
\]

Apply the graph-preserving reflection to the entire configuration if
necessary. It preserves this load set and every original degree, and
we may consequently retain

\[
                          |c_2-c_4|>1+\sqrt2.
\tag{2}
\]

For **every** pair of actual physical points
`P in 3 intersect 2` and `Q in 3 intersect 4`,

\[
 1+\sqrt2<|c_2-c_4|
 \le |c_2-P|+|P-Q|+|Q-c_4|
 \le\sqrt2+|P-Q|.
\]

It follows that

\[
                |P-Q|>1
 \quad\text{for every such actual pair }P,Q.
\tag{3}
\]

In particular (3) holds for the original aggregate means of the positive
`32` and `34` contacts. It holds also at any additional points of those
physical intersection segments. Compactness gives a strict separation
greater than one between the two entire physical contact sets.

## 4. Four loads force the same long pair without a reflection

In `L0124`, the loaded physical boundary path is exactly

\[
                            4--0--1--2.
\]

The complete original component force sum is
`F_4+F_0+F_1+F_2=0`. The full theorem
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` therefore gives (2), for
the actual endpoint centers and all physical radial masks. Body `3`
physically touches both endpoint units, so the identical triangle
inequality gives (3) at every pair of its actual endpoint contacts.

This application uses no equation at an internal path body. In
particular bodies `0,1,2` retain all three original pair forces, and
body `4` retains its genuine loaded degree-two equation. The other
unloaded body is the original `H4`, not a transmitter.

## 5. Precise surviving local star and remaining obligation

Both original families therefore retain, after the legitimate whole-graph
reflection for `L124` if needed, the actual unloaded degree-three body
`3` with the complete neighborhood

\[
                    \{2,H,4\},\qquad H\cap2\ne\varnothing,
\]

and with its two original boundary-neighbor contact sets more than one
unit apart, as in (3). The pair `H,4` remains physically closed-disjoint.
No normal-owner condition or proper-concurrence condition is asserted
at either loaded endpoint.

The two contact sets cannot meet a common side of `3`. If both original
applications are vertices of `3`, they must be opposite vertices:
the other vertex distances are zero or one. General side applications
remain in their complete intervals. These facts do **not** turn `3`
into a degree-two side or diagonal transmitter; its third original
`3H` force is strictly positive and remains in both its force and
torque equations.

To close `L0124`, one must still exclude three whole extras in its one
listed pocket, or derive an impossibility of the complete surviving
core. For `L124`, the joint capacity of its two listed pockets must be
at most two, with all physical zero-weight boundary refinements covered,
or the complete core must be excluded. No independent one-per-pocket
capacity has been proved here. Both whole fine gates and the whole
no-chord graph remain open.

## 6. Exact operative inputs

| Source | SHA256 |
| --- | --- |
| `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md` | `cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a` |
| `INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md` | `37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502` |
| `GENERAL_BALANCED_THREE_BOUNDARY_FULL_WINDOW_METRIC_EXCLUSION.md` | `5da69931a63ac7cbf93ec3ff494489dc05d2245017da1c4dcddf1b4a8a6c956e` |
| `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` | `164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f` |

The occupied-hub source in turn explicitly pins its complete
weak-embedding, long-chord area,
physical boundary-order and boundary-pair pocket inputs; all of those
operative hypotheses are retained. No new numerical certificate,
normal choice, force deletion, mean replacement, ledger change, remote
mutation, Lean compilation or CI enters this reduction.
