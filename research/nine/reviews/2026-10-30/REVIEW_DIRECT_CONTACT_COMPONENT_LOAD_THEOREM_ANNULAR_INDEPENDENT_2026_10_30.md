# Independent review: direct-contact components contain positive loads

Date: October 30, 2026 UTC.

Reviewer: annular-capacity research agent, independent of the source
author.

**Result: PASS at the complete stated scope. No repair requested.**

## 1. Literal frozen source

The complete 10,397-byte manuscript
`DIRECT_CONTACT_COMPONENTS_OF_RETAINED_STRESS_CONTAIN_POSITIVE_LOADS_2026_10_30.md`
was read and independently reconstructed. Its recomputed SHA256 is

    5b91a3b7e7f55317c706bdc6c1b65fd2bd0e99ce823411d5cbe73378dc8e151d

The direct-contact component theorem, spanning-forest count and
arbitrary-group consequences are self-contained. The optional
comparison with positive long endpoints uses the correctly pinned
source

    d6adb49263e0c2ffb3c1dc58477bef25ed2d0ae83bde59089c33d76c2d23b705

which was also previously reviewed in full independently.

## 2. Retained scope and complete suppression bookkeeping

The retained vertex set is explicit and correct. It contains every
positively circle-loaded body and every unloaded body with a positive
incident pair force and true degree different from two. An unloaded
degree-one body cannot satisfy its full force equation, so unloaded
retained vertices have degree at least three. Unloaded zero-edge
physical squares are omitted only from this retained graph; they
remain present in the physical packing. This distinction is necessary
for the asserted load property of direct-contact components.

At each genuinely unloaded true-degree-two body, the two nonzero
forces are equal and opposite. The actual support normal and positive
magnitude propagate through the entire maximal transmission run.
An all-transmission cycle is impossible because its positive support
gaps would telescope to zero. The same positive-gap argument excludes
a run returning to its own retained endpoint, without requiring a
force equation at that endpoint. Thus every run in the finite graph
ends at two distinct retained vertices.

Every original positive edge belongs either to one such run or to a
direct contact between retained bodies. Distinct maximal runs have
disjoint internal vertices and are preserved as separate parallel
channels when their retained endpoints coincide. At a retained vertex,
each channel contributes its unchanged original first or last force.
No force at a branching vertex is removed by the suppression.

The exact endpoint gap identity includes both actual endpoint
halfwidths and every actual internal width. It implies g_e>=1+k_e,
and the strict center bound rules out k_e>=3. The operative argument
only needs g_e>=2 for non-direct channels; no discrete orientation
classification or torque equation is imported.

## 3. Complete force sum over an unloaded direct component

Let S be a hypothetical load-free component of the spanning direct-
contact graph. The sum of its center-dotted full retained force
equations is zero. Every internal channel contributes exactly

    -mu_e*g_e<0.

This includes direct channels, subdivided channels returning to S,
and each parallel channel separately. No returning path is lost by
calling S a direct-contact component.

Every channel leaving S is non-direct; otherwise its second endpoint
would be in the same direct component. Orienting it away from S gives
the original single endpoint term

    mu_e*n_e.c_i=mu_e*(n_e.c_j-g_e)
                   <mu_e*(M-2)<0.

The force sign and support-gap orientation agree with the original
outward-to-neighbor convention. Each vertex of S has a positive
incident force, so at least one internal or outgoing term occurs.
The full sum is strictly negative, contradicting zero. This proves
the theorem without plane geometry, endpoint torque or an endpoint
degree bound.

## 4. Count and arbitrary-group consequences

Each direct-contact component contains at least one positively loaded
vertex, so c_0<=b. A spanning tree in each component gives a forest
with b+h-c_0>=h edges. Hence the total number e_0 of direct retained
positive contacts satisfies e_0>=h. The argument remains valid for
parallel channels in the retained multigraph; only direct original
body pairs belong to the counted direct-contact graph.

An unloaded hub with no direct incident edge would form a load-free
singleton direct component. More generally, any nonempty all-unloaded
retained group with no direct edge leaving it contains an entire
load-free direct component. The stated arbitrary-group exclusion
therefore follows, whether its internal connections include direct
or subdivided channels. Every unloaded retained vertex also has a
direct-contact path to a positive load, with no hidden unloaded
degree-two body along a counted edge.

The empty retained graph is harmless, and a positively loaded isolated
vertex already satisfies the conclusion. The source does not confuse
either case with an unstressed physical completing square.

## 5. Exact checks and verification boundary

Direct rational recomputation verified

    M^2+M+1/2-Q=31/57600,
    M-2=-29/60,
    4-2*M=29/30.

Both source SHA256 pins were recomputed after the complete read.
The optional comparison with the independently reviewed long-endpoint
theorem is on the same unchanged retained stress and is valid.

This is a complete independent mathematical review of the suppression,
force-sum and graph-count arguments. No original manuscript bytes,
graph or ledger flags, or remote state were changed. No numerical
pose search, Lean compilation, CI run or finite certificate is a
premise or claimed verification.
