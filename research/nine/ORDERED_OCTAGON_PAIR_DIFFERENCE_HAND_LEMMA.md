# Exact pair-difference bounds retained by ordered octagon children

This lemma supplies tighter proved difference intervals for the new
owner-free squared-distance secants. It introduces no branch and no new
geometric premise. It is not a claim that an original parent closes.

## 1. Named original pair and recorded rational rotation

Let `d=c_j-c_i` be the difference of the same two original centers named by
an existing `disk8_ordered` step. Write `w=R^T d`, with the exact rational
rotation reconstructed from that step's half-angle marker. Thus

    d_x = c*w_x-s*w_y,
    d_y = s*w_x+c*w_y,
    c²+s²=1.

The ordered octagon's first four escape alternatives are

    w_x>=12/13, -w_x>=12/13, w_y>=12/13, -w_y>=12/13.

The last four use signed diagonals `a*w_x+b*w_y>=17/13`, with
`(a,b)=(1,1),(1,-1),(-1,1),(-1,-1)` in that order.

## 2. Compact signed-coordinate intervals on diagonal children

On any child numbered `4,5,6,7`, all four first-axis predecessor
complements have been retained as closed inequalities. Hence

    -12/13 <= w_x,w_y <= 12/13.

The primary row is `a*w_x+b*w_y>=17/13` for its signed diagonal. Set
`u=a*w_x` and `v=b*w_y`. Both have upper bound `12/13`; subtracting each
upper bound from the primary inequality gives the other's lower bound:

    5/13 <= u <= 12/13,
    5/13 <= v <= 12/13.                                (1)

These inequalities include every boundary face. They are direct
nonnegative linear combinations of the child's primary and predecessor
rows; they do not use a numerical proposal or a strict complement.

Substitute `w_x=a*u`, `w_y=b*v` in the recorded rational rotation. For a
coefficient `p`, write

    low(p)=min(5*p/13,12*p/13),
    high(p)=max(5*p/13,12*p/13).

Equation (1) then proves exact original-coordinate bounds

    low(c*a)+low(-s*b) <= d_x <= high(c*a)+high(-s*b),
    low(s*a)+low(c*b)  <= d_y <= high(s*a)+high(c*b).    (2)

Every coefficient and endpoint is rational. Intersect (2) with any
previously proved intervals for this original pair, including intervals
from earlier ordered steps. A later step cannot invalidate an earlier
necessary interval on the same descendant.

More generally, a valid radius-scaled ordered octagon uses thresholds
`12*r/13` and `17*r/13`. The same argument gives
`u,v in [5*r/13,12*r/13]`. The radius must already be proved for the whole
caller; a radius inferred only from a proposed point is insufficient.

## 3. Exact difference propagation among original labels

For one coordinate, keep an upper bound `U[i,j]` on `z_j-z_i` for each
ordered pair of original labels. An interval `[l,u]` for `z_j-z_i` supplies
`U[i,j]<=u` and `U[j,i]<=-l`. A bound on an original center can be used to
initialize these differences by interval subtraction.

The identity

    z_j-z_i = (z_k-z_i)+(z_j-z_k)

proves every update

    U[i,j] := min(U[i,j], U[i,k]+U[k,j]).               (3)

Each update is an implication from already proved inequalities. A finite
sequence of such updates is therefore an acyclic proof, even if the
resulting graph has cycles. A negative bound on `z_i-z_i=0` is an exact
contradiction and requires its derivation to be retained. Otherwise the
interval for a difference is `[-U[j,i],U[i,j]]`.

The standard finite all-pairs shortest-path update order gives the strongest
path-sum bounds represented by the initial inequalities. For proof replay,
the checker may rerun this exact update schedule or record each improvement
and its two predecessor bounds. Both coordinate systems are handled
separately; all vertices remain the nine original labels.

## 4. Consequence for owner-free distance rows

On a proved interval `l<=d<=u`, the exact secant inequality is

    d² <= (l+u)*d-l*u.

Using the refined pair intervals (2)-(3) yields sharper upper secants for
`d_x²+d_y²` while retaining the same original physical predicate. They may
be combined with the independently reviewed signed or folded lower bounds

    ||d||² >= tau*(1+C+epsilon*S)-tau², tau>=0.

The result is the same row family as
`OWNER_FREE_RELATIVE_SUPPORT_HAND_PROOF.md`, with stronger, independently
proved interval inputs. This is a new derivation of its input bounds, not
a change to the existing v3 matrix or old row indices. Any certificate
that uses these strengthened rows needs an explicit additional context and
an exact replay of the bound derivation.

The three unclosed `negative-573078fc944ce553` domains retained after the
single-solve inspection contain diagonal ordered-octagon children, so this
lemma applies directly there. The four corresponding `negative-2f9ffd3df06e7c5f`
root-selector siblings have no octagon step yet; no extra difference bound
is inferred for them from this lemma alone.
