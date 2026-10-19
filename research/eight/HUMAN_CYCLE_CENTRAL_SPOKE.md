# A central actual spoke is forced by every exterior winding contact cycle

## Scope and main theorem

Assume eight pairwise interior-disjoint unit squares lie in the disk
D_R, centered at zero, with sqrt(2)+1/2<R<2 and a unique square C
containing zero in its open interior. Let J be any chosen collection
of **exterior** squares supporting a closed curve gamma contained in
their union such that gamma avoids zero and has nonzero winding about
zero. The positive-moment exterior cycles proved in
HUMAN_GLOBAL_CYCLE_CLOSURE.md satisfy these hypotheses.

**Theorem.** If C has any actual neighbor, it necessarily has an
actual neighbor **among J**. More precisely, any actual contact
between C and an exterior square S outside J occurs at a common
point of C, S, and the cycle curve gamma, hence at a three-way
(or higher) contact with some cycle square.

Furthermore, even if C is isolated, it may be translated without
rotation, keeping all other seven squares *fixed*, until it gains
an actual contact with a square of J. The disk radius does not
increase, no existing contact between other squares disappears,
and no interiors overlap. Therefore **there exists an attained
eight-square radius minimizer in which the central square has
a direct actual spoke into every previously chosen exterior
positive-moment cycle**. For any one chosen cycle, the adjustment
may be made while keeping that cycle and its chosen stress forces
unchanged.

This proves a central-spoke representative reduction, not a
positive-stress spoke: the new actual contact can have zero
multiplier in the original stress. It does not force two spokes,
a central two-force transmitter, or the sharp R8>=Rhat bound.

## 1. Every unused exterior square has winding zero

A unit square S other than C omits zero in its closed set, because
C contains zero in its open interior. Its center p_S has
|p_S|>1/2: otherwise the inscribed closed disk of radius 1/2,
which belongs to S, would contain zero.

The radial-escape theorem HUMAN_RADIAL_ESCAPE.md applies at
R<2. For every square T in J it gives

    T intersect {t p_S : t>=1} = empty.              (1)

Hence the outward ray from p_S to infinity avoids the entire
curve gamma, which lies in the union of the squares in J.
The winding number of gamma at p_S is therefore zero:
winding is constant along that ray and is zero at infinity.

The open interior of S is connected and avoids the closed squares
in J, hence avoids gamma. Winding is constant on int(S).
Consequently

    winding(gamma,x)=0   for every x in int(S).     (2)

On the other hand gamma winds nontrivially around zero,
and int(C) is connected, contains zero, and avoids gamma.
Thus

    winding(gamma,x)=w!=0 for every x in int(C).    (3)

Only the nonzero value, not its sign, is used below.

## 2. Contact points between unequal winding regions lie on gamma

Suppose C and S meet at a point z, where S is an unused
exterior square outside J. If z were not on gamma, there
would be an open disk around z disjoint from gamma (gamma
is compact). Winding would be constant on that disk.

But any point z of a closed unit square is a limit of
points of its open interior. Thus this disk contains
points of int(C) and int(S). Equations (2)--(3)
would give two different winding numbers inside a
connected disk missing gamma, a contradiction.

Therefore z belongs to gamma. Since gamma lies in
the union of the squares in J, z belongs to at least
one square T in J. Hence C and T share this actual
contact point z:

    C intersect S !=empty, S outside J
        => C intersect T !=empty for some T in J.    (4)

This is a **topological contact implication** that keeps
corner-only and multiple-square contacts; it does not
assume generic positions or a Jordan polygon. It is
valid for self-touching or repeatedly winding gamma.

If C has any actual neighbor, choose it. If it is in J
the main conclusion holds directly; otherwise (4)
supplies a neighbor in J. This proves the first part.

## 3. An isolated central square can be moved into contact

Suppose C is isolated. Write its center p and frame e,f.
Translate its center along p(a)=a*p for a decreasing from
1 to 0, keeping the frame fixed. The exact greatest
vertex squared norm is

    a^2 |p|^2+a(|p dot e|+|p dot f|)+1/2,              (5)

which does not increase as a decreases on [0,1].
The move preserves disk containment. If C meets any
other square along this path, stop at the first contact.
It has disjoint open interiors with every other square
by the first-contact argument, and (4) implies it has
contact with a square in J.

Otherwise C reaches center zero without touching
another square. Its closed inscribed disk of radius
1/2 is disjoint from the inscribed disk of every
other square S. Choose one of those squares with
center p_S, r=|p_S|>1, and u=p_S/r.

Move C's center along t*u for 0<=t<=r-1, frame fixed.
Since the entire inscribed radius-1/2 disk of S fits
in D_R, we have r+1/2<=R. Every point of the moved C
is within its circumradius 1/sqrt(2) of t*u, so

    |vertex of moved C| <= t+1/sqrt(2)
      <= r-1+1/sqrt(2)
      <= R-3/2+1/sqrt(2) <R.                         (6)

Thus this motion also preserves disk containment.
At t=r-1 the closed inscribed disks of C and S
touch, hence the whole closed squares touch.
Stop at the first actual contact, which must occur
by then. At first contact no square interiors
overlap, because a strict overlap would persist
immediately before first contact. Equation (4)
again implies a simultaneous actual contact
between C and a cycle square in J.

No other square moved in either motion; all old
actual contacts among the remaining seven remain.
We have constructed a feasible packing of the same
radius with a direct central spoke into the selected
cycle. The central square continues to contain
zero throughout: along the first motion it contracts
its center toward zero; along the second its center
norm is at most r-1<=R-3/2<1/2, so each of its
signed local coordinates remains less than 1/2.
Thus the winding identities used in section 2
remain applicable during both motions.

## 4. Consequences and limitations for the sharp n=8 proof

A positive-moment cycle not using C winds nontrivially
around C by HUMAN_GLOBAL_CYCLE_CLOSURE.md. The
present theorem implies that, after replacing an
isolated central square as above if needed, C must
have a *direct actual contact* with that cycle.
This removes the **central-isolated** alternative
for a representative selected to retain the
given exterior stress cycle. It does not remove
all globally isolated **exterior** square labels
or identify which cycle vertex is the contact.

Moreover, an exterior square outside the cycle
cannot be the sole contact-neighbor of C without
also producing a triple point on the cycle.
In particular, a speculative geometry in which
C touches only one of the unused exterior squares
without meeting the winding cycle is impossible.

The adjustment does not preserve the condition
'fewest actual contacting pairs among minimizers';
in fact it may increase the contact count. Thus the
theorem must not be combined automatically with
HUMAN_ACTUAL_BRIDGES.md's minimum-contact choice.
The actual new spoke need not be positively
weighted, and central stress degree one or more
than two is not resolved by this result.

The unrestricted sharp lower inequality
R8>=Rhat remains unproved.


## 5. A sharp consequence for central actual degree two

**Corollary.** Let a radius-minimizing packing be chosen
to have the fewest actual contacting pairs. Suppose its
central square C has actual contact degree **exactly two**,
and gamma is any exterior positive-moment contact cycle.
Then **both of C's actual neighbors belong to gamma's
cycle-square set J**. In particular, neither neighbor
may be an unused exterior square of winding zero.

**Proof.** The exact actual-degree-two theorem
HUMAN_CYCLE_ANALYSIS.md, section 8, applies to C:
it is strictly inside the containing disk, and
its two actual separating normals must be opposite
and owned by two opposite **sides of C**.
Consequently the two contacts occur on opposite
support lines of C, one unit apart. Their common
contact sets cannot have any point in common.

Suppose one neighbor S were not in J. Choose a
contact point z in C intersect S. Section 2
forces z to belong to gamma, and hence to some
square T in J. Therefore C also touches T
at the **same point z**. Since C has only two
neighbors, T must be its other neighbor.
But its two contacts then share point z,
contradicting their opposite-side support
lines. Thus both neighbors lie in J. QED.

If the two neighbor centers have norm at least
one and J is a full seven-outer contact ring,
HUMAN_STRICT_OPPOSITE_CENTRAL_ANGLE.md now
forces their center-ray separation above pi/2.
No two consecutive touching outer squares
can have so large a center-ray separation;
hence the two central neighbors are
**nonconsecutive vertices of that ring**.
Both circular arcs between them contain
at least one further ring square. This is
the candidate's B-T-D central routing
pattern at the level of cyclic order,
without asserting the number of vertices
on either arc or their orientations.

This is a genuine closure of the central
degree-two *attachment membership* subcase,
but not of the remaining sharp radius
inequality. It does not cover actual
central degree three or more, and it
must not be asserted for a representative
without the minimum-contact condition.
