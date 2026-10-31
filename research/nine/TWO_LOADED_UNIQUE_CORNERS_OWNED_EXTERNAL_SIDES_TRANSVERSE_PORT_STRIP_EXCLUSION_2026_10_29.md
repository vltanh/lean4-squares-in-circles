# Two unique-corner loaded units cannot join inside a transverse external-port strip

Date: October 29, 2026 UTC. Author: block_roots continuation.

**Status: complete proposed uniform hand theorem, frozen for a separate
full independent review.** The proof covers every owner, shared mean
and fixed-point alternative at the original joining contact. It uses
two actual loaded degree-two stars and their two actual external
side applications. No genuine-leaf, external-neighbor degree or
external-neighbor boundary premise is imposed.

## 1. Exact actual-star hypotheses

Retain all nine actual interior-disjoint unit squares in the same
circle about O=0, on the original window

    79/40<=R<=sqrt(1105)/16.

Use the same original compatible selected physical certificate,
including its already simultaneous fixed-tip normal selection.

Let P and Q be distinct actually loaded true-degree-two units with
original positive edge PQ. Their other actual positive neighbors
are A and C, respectively. A is distinct from P,Q, as is C; A=C
is allowed. No equation is assumed at A or C, and every original
force at those units remains.

Assume P and Q each have exactly one physical circle corner.
Their respective total circle coefficients are strictly positive.
A physical two-corner mask with an individually zero coefficient
is not reclassified as a unique physical corner and is outside
this explicitly stated hypothesis.

Suppose the actual intersections PA and QC are singletons at R0
and S0. Their unchanged outward unit normals, from P to A and
from Q to C, are N and M. They are genuinely owned by P and Q,
respectively, and their actual applications R0 and S0 lie in the
relative interiors of the corresponding actual sides. Thus

    max_P N=N.R0, max_Q M=M.S0.

Set J to be counterclockwise quarter rotation, and define

    U=J N, V=J M,
    beta=-M.U=N.V,
    D=R0-S0.

**Theorem.** The original configuration is impossible if

    beta>0,
    0<D.U<beta,
    0<D.V<beta.                                    (1)

In particular it is impossible whenever beta>eta>0, |D|<eta,
D.U>0 and D.V>0. These are tests on the unchanged actual points
and normals, not allowable movements or a choice of new means.

The direction convention is explicit. For either loaded unit K,

    F_circle + sum(original outward pair forces)=0.

Equivalently its circle resultant equals the sum of original
incoming pair forces. The proof below uses this convention.

## 2. A unique physical circle corner cannot give an own-axis resultant

Choose the actual own coordinates of P so that its unique physical
circle corner is Z=(a,b) and

    P=[a-1,a] times [b-1,b].

Containment of the two adjacent corners implies a,b>=1/2.
Uniqueness of the physical circle corner makes both inequalities
strict: equality in one would put that adjacent corner on the same
circle. Hence neither own coordinate of Z is zero.

The actual positive circle resultant is a positive multiple of Z.
It is therefore not parallel to any P side axis. The same statement
holds for Q. Consequently, if a loaded unit with this physical
mask has one original pair normal along an own axis, its other
original pair normal cannot be parallel or antiparallel to that
axis. Otherwise its full unchanged two-force sum, and hence its
circle resultant, would be along that axis.

This excludes both signs of the parallel alternative directly.
It does not infer physical uniqueness from a vanishing coefficient.

## 3. The original joining normal has an actual side-axis owner

If PQ has positive physical shared length, its unchanged pair normal
is perpendicular to that shared side and has an actual side-axis
owner at both units. Its entire original mean interval is retained.

Suppose instead PQ is a physical singleton, at its actual fixed
point F. We show that P's two actual applications are distinct.
If F=R0, the relative side-interior premise at R0 makes every
nonzero P outward support normal there the same direction N.
Its two original pair normals would then both be N. This is
impossible by Section 2. Thus F differs from R0.

The complete fixed-tip selection theorem now applies to the actual
P2: it has a unique physical circle corner, two distinct fixed
physical singleton applications, and its original neighboring
bodies A,Q are distinct. That existing simultaneous selection
forbids a free PQ normal. The actual joining normal must therefore
be owned by P or Q.

This call does not fix a shared-side mean. Shared PQ was handled
before the fixed-point selector. The coincident radial-D exception
cannot enter: R0 is in a genuine side interior and coincidence
already contradicts the unchanged force equation. No new normal
choice is made after extraction.

## 4. Every P-owned joining direction is impossible

Write n for the unchanged outward normal from P to Q. If P owns
it, n is one of N,-N,U,-U.

The two N-axis choices are excluded by Section 2. Suppose n=U.
The actual support equality at PQ and actual point membership give

    R0.U <= max_P U = min_Q U <= S0.U.

This contradicts D.U>0 in (1), including any endpoint of the
original PQ mean.

Suppose n=-U. Because M is the actual outward side axis of Q at
S0, the complete unit normal segment S0-[0,1]M lies in Q.
In particular the actual point S0-M belongs to Q. The original
support equality therefore gives

    R0.U >= min_P U = max_Q U
          >= (S0-M).U = S0.U+beta.

This contradicts D.U<beta. The translated point is an actual
point of the same occupied square; it is not a substituted
application or another unit.

These cases exhaust the entire P-owned joining feature.

## 5. Every Q-owned joining direction is impossible

Now suppose Q owns its unchanged outward normal toward P. It is
one of M,-M,V,-V. Section 2 excludes both M-axis alternatives.

For the direction +V, the actual point R0-N belongs to P by
its genuine owned side. Therefore the real support equality gives

    S0.V <= max_Q V = min_P V
          <= (R0-N).V = R0.V-beta.

Thus D.V>=beta, contrary to (1).

For the direction -V, the original support equality instead gives

    S0.V >= min_Q V = max_P V >= R0.V,

contrary to D.V>0. Every original mean and endpoint remains.
These are all Q side axes, so the whole Q-owned feature fails.

Section 3 supplied one of these actual owners. Sections 4--5
exclude both possibilities, proving the theorem.

## 6. Scope, exact inputs and preservation

| Complete input | SHA256 | Exact use |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Original full loaded2 force equations, actual support equalities, circle-corner geometry and unchanged shared means |
| GENERAL_FIXED_TIP_NORMAL_SELECTION.md | ef8ae8a219af9fa15a70698e485bbb337925e5caf2cd64b6b5c2619d9c4bd194 | Its complete distinct-fixed-application implication, after all physical premises are established in Section 3 |

The complete fixed-tip source was read. Its original radius and
pre-extraction simultaneous-selection contract are retained. The
generic parallel-star theorem is not needed: the narrower own-axis
parallel exclusion was proved directly in Section 2.

The theorem is independent of the signs of the two external support
heights N.R0 and M.S0. It uses no load or force equation at A,C,
and permits any actual shape or positive degree at those external
units. The exact-degree-two premise at each of P,Q is essential.

This is a uniform local obstruction, not yet a whole original graph
or coarse-cell exit. A caller must prove both physical unique masks,
both genuine external side interiors, the original application and
normal identities and all four strict tests in (1). In particular
a physical two-corner endpoint cannot be silently inserted here.

All nine actual units, every original pair force, true degree,
selected normal, original mean, physical corner and coefficient
remain. No pose sampling, angle mesh, numerical packing certificate,
new selection, Lean/Lake compilation, CI/workflow dispatch, remote
mutation, original-flag edit or merge was performed.

