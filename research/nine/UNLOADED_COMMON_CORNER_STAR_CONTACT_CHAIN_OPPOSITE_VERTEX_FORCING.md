# A contact chain forces the opposite vertex in an unloaded common-corner star

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: complete proposed radius-free full-star theorem, frozen for
independent and root review.** The theorem permits arbitrary positive
degree and arbitrary original loads and degrees at every neighbor.
It keeps every original pair force and mean. No circle, torque
reduction, selected-normal perturbation, or graph-size bound is used.

## 1. Actual physical setting and the degree-free chain obstruction

Let U,A,B,C be distinct actual closed unit squares with pairwise
disjoint open interiors. U has original positive contacts to A,B,C,
with their unchanged separating normals. Assume that A touches B
and B touches C physically; those two additional contacts need
not carry positive forces. Normalize only the actual own chart
of U to [0,1]^2, with its own axes denoted x,y.

Suppose the unchanged U-to-A normal satisfies

    n_A,x<0, n_A,y>0,                                  (1)

so it strictly exposes the actual U vertex (0,1). Suppose also

    n_C,x<=0, n_C,y<0.                                 (2)

Thus C is either at the strict Southwest U vertex (0,0) or has
the U-owned South axis, with its full actual side mean retained.

**Physical chain lemma.** Necessarily

    n_B,x<=0.                                          (3)

This is a degree-free conclusion about the actual physical
A--B--C chain through three neighbors of the same unit U.

### Complete proof of the chain lemma

Suppose n_B,x>0. There are exactly three possible signs of
n_B,y.

If n_B,y<0, the original B support is the strict Southeast
U vertex (1,0), opposite the strict Northwest A vertex in
(1). Actual unit neighbors at opposite strict corners cannot
touch, contradicting AB.

If n_B,y=0, B uses the U-owned East axis. Its dot product
with the original A normal is negative by (1). The physical
U-A-B triangle and the owned-axis triangle theorem exclude
that contact, including every original B side mean.

If n_B,y>0, B is at the strict Northeast U vertex (1,1).
When n_C,x<0, C is at the opposite strict Southwest vertex,
contradicting BC. When n_C,x=0, C uses the U-owned South
axis. Its dot product with n_B is then negative, and the
physical U-B-C triangle gives the same contradiction.

All three signs and the closed axis endpoint have been
covered. This proves (3), using only actual physical
contacts and original support normals.

For clarity, the two geometric inputs used above apply
without any force or degree premise. An actual minimum-n
support of a unit has strict reach less than one in any
direction e with n.e<0. Consequently strict Southwest and
Northeast neighbors of U lie respectively in x<1,y<1 and
x>0,y>0; a common point would lie in int U, impossible
for another actual closed square. The other opposite
corner pair follows by reflection. For an owned axis,
normalize it to East: its neighbor lies in x>=1, while
a neighbor with strictly negative x normal lies in x<1
by that same reach bound. Such neighbors cannot touch.
These arguments include arbitrary frames and physical
side means of the neighboring units.

## 2. A full-star consequence, including the shared-axis return

Now U is genuinely unloaded and retains its complete
original positive star. Its neighbor set includes the
three units in Section 1 and may contain any number of
other actual neighbors. Write F_J=mu_J*n_J for every
original U-to-J vector, with mu_J>0.

Assume (1)--(2) and suppose every other original vector,
apart from the displayed A,B,C vectors, satisfies

    (F_J)_x<=0.                                        (4)

**Theorem 1.** This entire full-star domain is impossible.

Indeed, (1) gives (F_A)_x<0, (2) gives (F_C)_x<=0,
and (4) accounts for every other original force. The
unchanged full U force equation

    sum_J F_J=0

therefore forces (F_B)_x>0. This contradicts the physical
chain lemma (3). No original term has been discarded or
assigned a zero coefficient.

In particular the theorem includes the C-owned-by-U
South-axis case, with every original physical shared
interval and its actual mean. Its force has zero x
component, but remains positive and remains in the full
equations. U's torque equation is retained unchanged;
the contradiction simply does not need it.

## 3. Complete common-corner forcing at arbitrary original degree

Keep an unloaded U with its entire original positive
star. Choose distinct positive neighbors A,B,C such
that the actual contacts AB and BC exist. Assume:

1. The original C normal strictly exposes one actual
   U vertex P.
2. Every other original force except those toward A,
   B and C supports U at P. Equivalently, its direction
   lies in the closed outward normal cone of U at P.
   Such a force may be an own-axis direction with an
   arbitrary original mean elsewhere on that support
   side; its mean is not replaced by P.
3. The original A normal is not an own axis of U, so
   it strictly exposes one actual U vertex Q.

All pair magnitudes are the original positive ones.
Other neighbors have arbitrary actual degrees, loads,
masks and physical contacts.

**Theorem 2.** Q is the vertex opposite P.

Normalize P=(0,0), so the strict C vector has both
own components negative. Every remaining force named
in premise 2 has both own components nonpositive.

If Q=P, the A vector also has both components strictly
negative. Full force balance makes the B vector
strictly positive in both components. Thus B is at
the strict opposite U vertex (1,1), contradicting
the actual BC contact. This excludes the same-vertex
case using all original forces.

If Q is adjacent to P, exchange the two own coordinate
axes if needed so Q=(0,1). The A vector then has the
signs (1), while the C vector has the strict version
of (2), and all other forces satisfy (4). Theorem 1
excludes this entire alternative. The coordinate
exchange transforms the whole actual chart and does
not change a normal, application, or physical unit.

The four U vertices consist exactly of P, its two
adjacent vertices, and its opposite vertex. The first
three alternatives have now been excluded, proving
the conclusion. No assumption of distinct original
applications is required: the theorem explicitly
permits arbitrarily many forces at the common P.

## 4. Literal use and exact preservation boundary

The common-corner theorem applies, for example, to a
true unloaded H4 with positive neighbors A,B,C,D,
physical AB and BC, both HC and HD strict at the same
actual H vertex, and a non-H-owned HA normal. It forces
the actual HA support to the opposite H vertex. It does
not aggregate HC and HD into a fictitious third body or
give either loaded neighbor a smaller star.

If HC instead uses a South own axis and HA is strict
Northwest in the actual H frame, Theorem 1 applies
directly whenever all remaining original forces have
nonpositive horizontal components. This includes
an arbitrary original HC shared-side mean. These are
necessary full-star tools, not complete original-family
claims without a separately checked physical caller.

The theorem needs neither a containing disk nor a
radius or origin-clearance bound. It uses no special
normal-selection convention beyond each explicitly
stated strict vertex or owned-axis feature. The true
positive degree of U is unrestricted, and all actual
neighbor degrees and loads remain unchanged.

## 5. Exact source input

| Source | SHA256 | Exact use |
| --- | --- | --- |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Complete degree-free unit support-span and owned-axis physical triangle tools, also restated above |

No source, ledger, metadata, gate count, roadmap or
handoff is changed. No original force, shared mean,
physical contact, circle coefficient or completion
unit is removed. No numerical geometric exclusion,
Lean compilation, CI, commit or remote operation is
part of this manuscript.
