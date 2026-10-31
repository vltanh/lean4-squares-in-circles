# An intact root cannot bridge to another leaf root in a multi-triangle block tree

Date: October 26, 2026.

**Status: complete uniform central-disk lemma and whole all-triangle
block-tree exclusion; full root and separate independent audits
accepted.** The acceptance records are
REVIEW_INTACT_ROOT_BRIDGE_TO_LEAF_ROOT_ROOT_2026_10_26.md and
REVIEW_INTACT_ROOT_BRIDGE_TO_LEAF_ROOT_ROOTED_BLOCKS_2026_10_26.md.
This is an acceptance-status edit only; no ledger is changed.

Keep all actual physical units and the common compatible selected
certificate in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1,
    epsilon=max(d-1,0)<1/60.

Suppose H has an intact end triangle, whose two tips have their true
positive degree two and positive circle loads. Suppose HA is an actual
positive bridge, and A is the root of a genuine direct leaf L. A and H
retain every other original positive force and their full true degrees.

**Local theorem.** Every genuine leaf root in the entire component
belongs to {H,A}.

**Whole graph theorem.** If the entire original component has only
triangle cyclic blocks, at least two such blocks, and arbitrary bridges,
then this configuration is impossible.

This is not a reduction to a fictitious two-force A. In particular A
may initially belong to another cyclic block or carry further branches.
Their exclusion, when applicable, comes from the full original
block-cut tree after the local geometric theorem is proved.

## 1. The actual bridge is a small owned-side radial support of H

The intact-root origin theorem gives O in int H. Its actual common
petal side has height P<39/40 and actual port heights of strictly
opposite signs. One such height has magnitude at most 1/2. The physical
boundary-point bound gives

    P^2>(67/120)^2-1/4=889/14400>1/25.

Consequently

    1/5<P<39/40,
    every actual H vertex has norm greater than 1/40.      (1)

The last assertion uses the common-side own frame: every vertex has
longitudinal coordinate P or P-1, with both absolute values exceeding
1/40. All original forces at H remain.

The genuine leaf L cannot be D, because that would put O in int A.
Nor can it be S with d<=1, because its root would then contain O.
Both would overlap the actual origin-interior H. Hence

    L is S,       d=1+epsilon,       0<epsilon<1/60,
    epsilon v in A,                                        (2)

where v is its genuine radial direction and d v its actual outward
radial application.

The original radial-bridge theorem applies to HA without a degree
assumption at either endpoint. Let e be the actual normal from H to A.
Its unchanged common application is p=rho e. Since O lies openly
inside H,

    H subset {e.x<=rho},  A subset {e.x>=rho},
    p=rho e in H intersect A,       rho>0.

Apply this support to the actual point epsilon v in A from (2):

    0<rho<=epsilon(e.v)<=epsilon.                         (3)

By (1), p is not an H vertex. It lies in a relative side interior, so
e is an actual own side axis of H, with support height rho. Its opposite
side has height 1-rho.

The intact petal's actual common side cannot be e, whose height is at
most epsilon<1/5, or -e, whose height is at least
1-epsilon>59/60>39/40. It is therefore perpendicular to e. Its two
transverse side heights are P and 1-P, both strictly above epsilon
by (1). The opposite longitudinal height 1-rho is also above epsilon.

Thus all but the e-side inequality of H are strict throughout the
closed D_epsilon. For every x in that disk,

    x not in int H  implies  e.x>=rho.                    (4)

This statement retains the entire disk boundary and does not claim
that the e-side itself has height epsilon unless that follows later.

## 2. The complete genuine S-root geometry makes A parallel to that side

The point p=rho e is A's unique nearest point to the origin. Indeed
every point of A has e-projection at least rho and p attains norm rho.

Here is the complete radial S-root classification relative to that
actual nearest point.

If the leaf direction v is an A side axis, the full root form is

    A=[epsilon,d]v + [l,l+1]Jv,         -1<=l<=0.

Its unique nearest point is epsilon v. Hence

    rho=epsilon,          v=e,                             (5)

and A owns the actual bridge axis e.

Otherwise the leaf application d v is a strict A vertex. Choose its
outward own axes u,w so a=v.u>0, b=v.w>0, a^2+b^2=1. About the unchanged
circle origin the full A rectangle is

    [d a-1,d a] times [d b-1,d b].

Because A avoids O, one of its lower coordinates is strictly positive.
They cannot both be positive: that would give d^2>2, whereas
d<61/60<sqrt(2). Relabel the two own axes so d a-1>0. The other interval
contains zero strictly; its lower endpoint cannot equal zero for the
same d^2<2 reason.

The nearest point is therefore (d a-1)u. Its uniqueness gives u=e and
d a-1=rho. Choose the transverse sign accordingly and write

    A=[rho,rho+1] times [u_0-1,u_0],
    d v=(rho+1,u_0),            u_0=d b>0.                (6)

The exact radius identity and its consequences are

    (rho+1)^2+u_0^2=d^2,
    0<rho<epsilon,
    u_0^2<d^2-1<(61/60)^2-1=121/3600<1/25,
    0<u_0<1/5.                                           (7)

Thus A owns e in every actual leaf frame, including its side and
vertex endpoint alternatives. This conclusion does not use A's
other force equations.

## 3. A nonaxial leaf makes H and A cover the entire small disk

Assume the strict vertex alternative (6)--(7). Subtracting its radius
identity gives the exact relation

    rho^2+u_0^2=epsilon^2+2(epsilon-rho)>epsilon^2.          (8)

Let x=(x_1,x_2) belong to D_epsilon and not to int H. By (4),
x_1>=rho, while x_1<=epsilon<rho+1. Also

    x_2>=-epsilon>u_0-1.

If x_2>=u_0, equation (8) would give
|x|^2>=rho^2+u_0^2>epsilon^2, impossible. Therefore x_2<u_0.

If x_1>rho, these strict inequalities put x in int A. If x_1=rho,
the point lies in the relative interiors of the actual common H and A
sides: H's transverse margins exceed epsilon, and A's transverse
inequalities just proved are strict. A neighborhood of x is covered
by H and A on opposite sides of their original support.

Consequently no distinct third actual unit K, interior-disjoint from
H and A, can contain any point of D_epsilon. An open part of K near
such a point would lie in that union and, being two-dimensional, could
not remain on its single separating line; it would overlap int H or
int A. This handles every boundary equality in (4), without treating
a shared edge as a free passage.

Every genuine S-leaf root contains epsilon times its radial direction,
and every D-leaf root contains O. Hence there can be no genuine leaf
root K outside {H,A} in the strict vertex alternative.

## 4. The complete axial alternative retains its actual slider

Now assume (5). From the three strict H margins and h_H(e)=epsilon,

    D_epsilon minus {epsilon e} is contained in int H.

Let K differ from H and A and be a genuine leaf root. A D leaf would
give origin overlap with H. An S leaf of direction v_K gives the
actual point epsilon v_K in K. Disjointness forces that point to be
epsilon e and therefore v_K=e.

At the fixed radius the radial S leaf in direction e is exactly the
same actual square [d,d+1]e+[-1/2,1/2]Je as the existing L. Two distinct
bodies cannot occupy the same open square. Thus this would be the
same leaf body L, whose true positive degree one already has neighbor A.
It cannot also have root K.

No restriction on the axial A slider was needed. Sections 3--4 prove
the local theorem for every original orientation and mean:

    every genuine leaf root belongs to {H,A}.              (9)

## 5. Whole original all-triangle block trees are excluded

Assume now that the entire original positive component has only
triangle cyclic blocks, at least two of them, and otherwise arbitrary
bridges. Root the exact block-cut tree at H. The actual HA edge remains
a bridge, so its branch is the unique tree route from H to A.

Every terminal triangle has two private true degree-two vertices,
which are loaded by the touching-neighbor obstruction. It is an intact
petal, and its root must be H; otherwise its own origin theorem would
put O in two different open square interiors.

Every terminal bridge has a genuine leaf endpoint. By (9), its root
is H or A. These are the only allowable terminal roots.

There can be no triangle block away from H. Take any such block and
a terminal block descendant, allowing the chosen block itself when
it is terminal. A terminal triangle there has root different from H
and contradicts the preceding origin argument. A terminal bridge
would have root H or A by (9). It cannot return to the ancestral H.
If its root were A, the unique tree path from H to A would pass through
the chosen triangle block, whereas the actual bridge HA already is
that path. This is impossible as well. These exhaust the terminal
block types.

Thus every triangle block meets H directly. Neither of its private
vertices can have a further attached block: a terminal descendant of
that branch would give the same contradiction, and it cannot be A
because HA is a distinct bridge. Every such triangle therefore has its
two actual private tips of true degree two and positive circle load.

There are at least two intact petals at H, together with the unchanged
positive radial bridge HA whose actual application has norm rho<=epsilon
by (3). Section 3 of
GLOBAL_CLOSURE_COMMON_ROOT_INTACT_TRIANGLE_FORESTS_EXCLUSION.md excludes
precisely this combination. That local small-port theorem retains all
other root forces and requires no fictitious degree-two root equation.
It gives the final contradiction.

No minimum-support reduction of other bridge articulations is required
here. The terminal graph argument preserves every original branch and
uses only the real bridge HA, genuine leaf facts, and terminal degrees.

## 6. Scope of the completed family

This covers every direct intertriangle connector from an intact root
whose other endpoint has any genuine leaf, in all original C2.33 bridge
counts. Additional leaves or branches at either endpoint are not
deleted. The same whole theorem applies to all-triangle block trees
with three or four cyclic blocks under the original nine-body budget.

A bridge whose far endpoint is not a genuine leaf root, an intact root
with only a direct S leaf on itself, a graph with no intact petal, or
a nontriangle cyclic block remains subject to its separate original
obligation. No full coarse cell is declared closed by this source alone.

No physical pose, circle force, actual mean, or original normal is
changed. No sampled configuration, Lean compilation, CI, remote action,
or shared-ledger edit is used.

