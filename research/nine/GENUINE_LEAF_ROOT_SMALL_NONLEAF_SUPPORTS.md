# Small nonleaf supports force a genuine leaf root to be aligned S

Date: October 27, 2026.

**Status: complete local hand theorem and one whole original adjacent-
root C4 mixed caller, submitted for full root and separate independent
review.** All original root forces and actual means are retained.
The local theorem makes no channel or boundary assumption at the
other neighbors once their stated actual support bounds are proved.

## 1. Full local hypotheses

Keep the original physical packing and compatible selected certificate,
with

    sqrt(17)/2<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1=1+epsilon,
    0<=epsilon<1/60.

Let A be an actual genuine radial-leaf root. Its other positive
neighbors form a nonempty finite collection. Write e for its actual
genuine leaf direction, alpha>0 for that force, and mu_i>0,n_i,p_i
for every other actual positive root force, unit normal and real
application. Assume the complete original supports satisfy

    h_A(n_i)=p_i.n_i<=epsilon       for every i.        (1)

The root is physically clear by genuine leaf geometry. Its full
force and origin-torque equations are

    alpha e+sum_i mu_i n_i=0,
    sum_i mu_i det(p_i,n_i)=0.                         (2)

The omitted leaf term in the second displayed sum is exactly zero,
because its unchanged real application is radial. No other positive
force is omitted.

**Theorem.** The genuine leaf cannot be D, and an S leaf must have
its direction along an actual own side axis of A.

The following proof is the support-only content of Sections 2--3
and 3.1 of `RADIAL_LEAF_TWO_BOUNDARY_CHANNEL_FORK_EXCLUSION.md`.
Those arguments use their channels only to establish (1). We state
the complete actual support argument here so this stronger local
scope is explicit rather than assigning a near neighbor a fictitious
transmitter equation.

## 2. Every genuine D-root alternative is impossible

Rotate the actual D leaf east. Its full root chart is

    A=[r-1,r] times [-b,a],
    r=R-sqrt(2),       a,b>0,       a+b=1.

Throughout this radius domain `1/2<r<3/4`, so both horizontal
origin margins exceed one quarter. For every actual normal n,

    h_A(n)>=|n_x|/4,

with strict inequality when n_x is nonzero. Equations (1) and
`epsilon<1/60` imply

    |(n_i)_x|<1/15,       |(n_i)_y|>14/15.             (3)

The full vertical equation in (2) has zero leaf component, so
there must be an actual upward and an actual downward nonleaf
force. If there were only one nonleaf force this already fails;
otherwise choose such an original pair i,j without deleting any
term from (2). Their true supports have sum

    h_A(n_i)+h_A(n_j)
       >=a(n_i)_y+b|(n_j)_y|
       >14(a+b)/15=14/15.

But (1) bounds that sum by `2epsilon<1/30`. This is impossible.
The root's genuine degree and every other original force remain.

## 3. Every tilted S-root alternative has a strict moment sign

Let the actual S-leaf point be p=d e. In the complete tilted root
chart choose its two inward own axes f_1,f_2, exchanging them if
necessary, so

    A=p+[0,1]f_1+[0,1]f_2,
    e.f_1=-a,    e.f_2=-b,
    a>=b>0,      a^2+b^2=1.

For a normal with these actual own coordinates (x,y), its support
from the unchanged origin is

    h_A(n)=-d(ax+by)+max(x,0)+max(y,0).                 (4)

The full radius bounds give `da>2/3` and `1-db>19/80`.
Therefore x<=0,y>=0 would give support greater than 19/80,
contradicting (1). This includes the two bounding axes.
If x,y>0 and y>=x, then y>2/3 and (4) is greater than

    (19/80-epsilon)y>53/360>epsilon,

another contradiction. Every feasible normal with y>0 thus has
`x>y>0`.

For an unchanged application `p+X f_1+Y f_2`, its signed own-frame
moment about p is `Xy-Yx`. The complete feasible support cover is

| Actual normal feature | Actual support feature | Moment |
| --- | --- | --- |
| x>y>0 | X=Y=1 | y-x<0 |
| x>0,y<0 | X=1,Y=0 | y<0 |
| x<0,y<0 | X=Y=0 | 0 |
| x>0,y=0 | X=1, any original Y in [0,1] | -Yx<=0 |
| x=0,y<0 | Y=0, any original X in [0,1] | Xy<=0 |

Every actual nonleaf term has nonpositive moment, including every
shared-side mean and both endpoints. The f_2 component of the
full force equation (2) is

    sum_i mu_i (n_i)_2=alpha b>0.

At least one original force therefore has y>0 and the strictly
negative first-row moment. The positive weighted sum of all
nonleaf moments is strictly negative. The physical determinant
differs only by the same nonzero orientation factor of f_1,f_2
for every term, while the real leaf applies at p and has zero
moment there. This contradicts the full root torque. It proves
the theorem without a force equation at any other unit.

## 4. Exact whole C4 adjacent-root mixed caller

Take the original C4 in cyclic order A--B--C--D--A. There is one
genuine leaf at A and another at the adjacent root B. Use the
exact positive block-load representative C: C is loaded, while
the unchanged D has true unloaded positive degree two. A and B
are physically clear genuine roots with true positive degree
three. All three other physical packing squares remain arbitrary
and present.

Consider the complete ordered mixed leaf family with D at A and
S at B. This ordering is essential: the fixed single-C load mask
does not identify it with the reverse assignment.

At d<=1, the D root A contains O openly and the S root B contains
O closed, giving immediate overlap. In the remaining domain d>1,
the original B contains its actual point `epsilon e_B`. Its real
separating support from A therefore satisfies

    h_A(n_AB)<=n_AB.(epsilon e_B)<=epsilon.             (5)

The actual D transmitter gives a normal channel A--D--C with
reserve w>=1, keeping its real means. If `h=h_A(n_AD)`, the
true far unit C lies beyond support h+w. The exact contained-unit
center bound and its directional halfwidth at least one half give

    h+w<=d,       h<=d-w<=epsilon.                     (6)

This uses no equation at C and does not remove its positive circle
load. The two actual nonleaf forces at A are exactly AB and AD;
(5)--(6) establish (1) for both. Section 2 contradicts A's full
genuine D3 equation.

This closes the entire original fine family

    M6.B4L2.C4.ADJACENT.LC.DA_SB.

The same actual support bounds show that any surviving S assignment
at A in the single-C load mask must have A aligned with its own
leaf direction at d>=1. That is a necessary reduction only; the
remaining S/S and reversed mixed families are not claimed closed
by this source. In particular no extra root force is suppressed,
and the clear near unit B is never called an unloaded channel.

No numerical pose, altered mean, normal reselection, Lean
compilation, CI, remote mutation or shared-ledger edit is used.
