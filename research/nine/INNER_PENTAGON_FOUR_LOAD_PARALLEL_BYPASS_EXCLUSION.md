# The four-load inner pentagon: complete parallel-bypass exclusion

Date: October 27, 2026.

**Status: complete fresh hand proof of the entire parallel-bypass
interface of H2_D0.L1234, saved for full independent and root review.**
The oblique-bypass interface is separate and is not claimed here.

## 1. Literal original graph, loads and unchanged forces

Keep the actual physical nine-square packing in the declared window

    79/40 <= R <= sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1 < 61/60.

The original outer pentagon is 0--1--2--3--4--0, with its actual inner
unit H joined to 0 and 2 and no outer chord. The positive circle-load
set is exactly {1,2,3,4}. Use the local labels

    A=2, B=1, V=0, C=4, Y=3, X=H.

Thus the complete positive graph is

    A--X--V--B--A,       A--Y--C--V,

with true degrees A3/B2/V3/C2/Y2/X2. X and V are unloaded. A,B,Y,C
are positively loaded physical boundary units, in the actual path
B--A--Y--C. In particular **Y is loaded degree two, not a transmitter**.
The other three original physical units remain arbitrary and present.

The common initial strictly exposing singleton convention is retained.
No selected normal, positive edge, application mean, physical circle
mask or individual zero circle weight is changed.

**Theorem.** The actual frames of B and X cannot be parallel.

This is a whole original interface, not a claim about a sampled frame.
We use the complete unloaded V3 equation and the complete loaded B2
equation. The circle forces of A,B,Y,C sum to zero by summing all six
original force equations. Consequently the full theorem
`FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` applies to their actual path:

\[
                         |c_B-c_C|>1+\sqrt2.
\tag{1}
\]

Its hypotheses retain both physical corner masks and all positive
degrees; it puts no false degree-two equation at A.

## 2. Exact parallel frame, with the circle origin still recorded

The actual unit B bypasses the true X2 channel. By
`UNIT_BYPASS_NORMAL_CHANNEL.md`, X has its actual side-normal width
one and its two original transverse application means agree.
Rotate and translate coordinates, recording the original circle
origin as O=(o_x,o_y). Put

\[
 X=[0,1]\times[y,y+1],\qquad
 A\subseteq\{x\le0\},\qquad V\subseteq\{x\ge1\}.
\tag{2}
\]

Under the present parallel-frame premise, B's horizontal interval is
exactly [0,1], since it physically touches both A and V. Reflecting
the transverse coordinate if necessary gives

\[
                       B=[0,1]\times[t,t+1],\qquad t\ge y+1.
\tag{3}
\]

Both A and V must also be parallel. For example, a tilted A has a
unique maximum-x vertex P. Its contacts with both X and B would both
be P=(0,t), with t=y+1. The positive AX contact would then be a
singleton vertex/vertex contact carrying an X side-axis normal,
contrary to the unchanged strict singleton convention. The same
argument works at V's minimum-x vertex.

The AX and XV contacts cannot be singleton endpoints for the same
reason. Their actual positive-length side intersections, together
with their physical B contacts, therefore give exactly

\[
 A=[-1,0]\times[a-1,a],\quad V=[1,2]\times[v-1,v],
 \qquad t\le a<t+1,\quad t\le v<t+1.
\tag{4}
\]

This is the complete physical frame argument of Section 2 of
`PARALLEL_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md`;
it uses no force equation or load assumption at Y. All its geometry
has been repeated here so that no transmitter premise at Y enters.
Every original side mean remains free within its actual intersection.

## 3. The entire shared V--B side would make B circle-clear

Suppose v>t. Then V-to-B and V-to-X are both West. V's complete
unloaded three-force equation forces V-to-C East, so C lies wholly
in x>=2. Its degree and physical frame are unrestricted here.

The sharp contained-unit support bound from Section 1 of
`END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` yields

\[
                              2-o_x\le d.
\tag{5}
\]

The two corners on A's actual side x=-1 are one unit apart. Their
containment gives (o_x+1)^2+1/4<=R^2, hence o_x<=d. Thus

\[
                    2-d\le o_x\le d,
                 \qquad d\ge1,\qquad o_x+1>119/60.
\tag{6}
\]

Both actual vertical endpoint coordinates of A relative to o_y have
absolute value strictly below 5/8, because

\[
 R^2-(o_x+1)^2<\frac{1105}{256}-\left(\frac{119}{60}\right)^2
                 <\frac{25}{64}.
\tag{7}
\]

The last reserve is 451/57600. By (4), B's bottom lies within A's
vertical interval and its top is at most one unit above A's top.
Every B point therefore has vertical distance from O less than 13/8.
Equations (6) bound its horizontal distance by d<61/60. Every actual
B corner consequently satisfies

\[
 |z-O|^2<\left(\frac{61}{60}\right)^2+\left(\frac{13}{8}\right)^2
            <\left(\frac{79}{40}\right)^2\le R^2.
\tag{8}
\]

The second reserve is 163/720. This contradicts B's actual positive
circle load. No C force, circle mask or application was replaced.

## 4. Full V3 at the remaining singleton interface

It remains that v=t. V and B meet at their actual singleton
P=(1,t). The original V-to-B force is strictly Northwest by the
selected vertex convention. Write the complete three forces at V as

\[
 V\to X=(-\lambda,0),\qquad V\to B=(-\beta,\gamma),
 \qquad V\to C=(\lambda+\beta,-\gamma),
 \quad\lambda,\beta,\gamma>0.
\tag{9}
\]

The unchanged VX application is (1,z), with t-1<=z<=t. The strict
Southeast VC normal has actual application P_C=(2,t-1). Taking V's
full moment about P gives

\[
 \lambda(z-t)+\lambda+\beta-\gamma=0,
 \qquad
 \gamma=\beta+\lambda\rho,\quad \rho=1+z-t\in[0,1].
\tag{10}
\]

In particular

\[
                          \beta\le\gamma\le\lambda+\beta.
\tag{11}
\]

Both mean endpoints rho=0 and rho=1 are retained. Normalize the
actual VC normal as n=(c,-s). Equation (11) gives c>=s>0.

We record a complete physical support observation. If P_C minimizes
this n on a unit C, then

\[
                             (c_C)_x\ge (P_C)_x=2.
\tag{12}
\]

For a strict minimum vertex, choose its inward orthonormal unit axes
u,v and write n=A_0u+B_0v, with A_0,B_0>0 and A_0^2+B_0^2=1.
The center displacement has n component (A_0+B_0)/2>=1/2 and
absolute Jn component |A_0-B_0|/2<=1/2. For an owned minimum side,
the complete actual mean gives displacement n/2+tau Jn with
-1/2<=tau<=1/2. In either case its x component is at least
(c-s)/2>=0. This proves (12), including all C owners, side means
and c=s.

## 5. The circle origin cannot have o_x<=1/2

Every contained unit center satisfies

\[
                         |c_S-O|\le d+1/2<91/60.
\tag{13}
\]

Assume o_x<=1/2. By (12), (c_C)_x-o_x>=3/2. Hence

\[
 |(c_C)_y-o_y|^2<\left(\frac{91}{60}\right)^2-\frac94<\frac1{16},
\tag{14}
\]

with reserve 11/900 in the last comparison. B's center is
(1/2,t+1/2), so its x coordinate relative to O is nonnegative.
Equation (12) also says (c_C)_x>(c_B)_x. Thus (13)--(14) give

\[
 \begin{split}
 0<(c_C)_x-(c_B)_x&<91/60,\\
 |(c_C)_y-(c_B)_y|&<91/60+1/4=53/30,\\
 |c_C-c_B|^2&<\left(\frac{91}{60}\right)^2+
                 \left(\frac{53}{30}\right)^2
                   <\left(\frac{12}{5}\right)^2.
 \end{split}
\tag{15}
\]

The last reserve is 1219/3600. Since 12/5<1+sqrt(2), (15)
contradicts the full balanced-boundary-path bound (1).
Consequently the only remaining possibility is o_x>1/2.

## 6. The actual B mask and its whole B2 moment contradict V3

For o_x>1/2, every B corner on x=1 is strictly nearer O than the
corner at the same height on x=0. Moreover the actual B bottom-left
corner (0,t) belongs to A by (4), and its bottom-right corner (1,t)
belongs to V. A physical circle point cannot belong to two distinct
packing units: the short inward radial segment lies in each unit's
open interior. This is also the explicit argument in
`PHYSICAL_BODY_GRAPH_UNCROSSING.md`, Section 6.

It follows that B has exactly one physical circle corner, its actual
top-left point Z=(0,t+1). This is a geometric mask conclusion, not a
choice of a positive weight among two physical corners. Put

\[
                    H_0=t+1-o_y,
                    F_B=\kappa(-o_x,H_0),\qquad\kappa>0.
\tag{16}
\]

Write the complete original B-to-A force and its actual mean as

\[
            (-\mu,-\nu)\quad\hbox{at }(0,t+\xi),
       \qquad\mu>0,\quad\nu\ge0,\quad0\le\xi<1.
\tag{17}
\]

Here a>t gives a positive-length vertical side with nu=0 and
0<=xi<=a-t<1. If a=t, the actual singleton normal is strictly
Southwest, nu>0 and xi=0. Thus (17) includes the entire actual
contact cover without resetting any mean.

The other actual B force is (beta,-gamma) at P=(1,t). Its complete
force equation, including (16), gives

\[
                 \beta=\mu+\kappa o_x,
               \qquad\gamma=\kappa H_0-\nu.
\tag{18}
\]

The B-to-A moment about P is nu+mu xi. The circle moment about P
is -kappa det(P-O,Z-O)=-kappa(H_0-o_x). The unchanged B2 moment
therefore reads

\[
                         \nu+\mu\xi=\kappa(H_0-o_x).
\tag{19}
\]

Subtracting the two identities in (18) and then using (19),

\[
 \gamma-\beta
   =\kappa(H_0-o_x)-\mu-\nu
   =\mu(\xi-1)<0.
\tag{20}
\]

This contradicts gamma>=beta from the complete V3 moment (11).
Both original stars, including the VX force and the complete AB
mean, are essential and have been kept. No concurrence or false
degree-two equation at V has been used.

## 7. Exact conclusion and complete prerequisite pins

The shared and singleton VB alternatives exhaust (4). The singleton
case retains both circle-origin half-planes, all C frames and masks,
both VX mean endpoints, and the entire shared/point AB interface.
Thus the whole parallel B/X interface of H2_D0.L1234 is excluded
throughout the original radius window, with all nine physical units
and every original positive force unchanged.

The direct sources used at their stated literal scopes are:

| Source | Exact SHA-256 | Used scope |
| --- | --- | --- |
| `SIX_BODY_INNER_PENTAGON_LOAD_COVER.md` | `fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434` | Original two-spoke graph and four-load set |
| `UNIT_BYPASS_NORMAL_CHANNEL.md` | `d6008ceb18b2c8921c1f3711e6babfea3a01761487352ef4dca60579a83353b8` | Actual X width one |
| `PHYSICAL_BODY_GRAPH_UNCROSSING.md` | `eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a` | Initial strict singleton convention; physical circle-point nonsharing |
| `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md` | `6f3459eaf4ca425ee2001ddb27e1ba7a1b5eb0003548498f48c610776554d3bb` | Degree-free Section 1 only: contained-unit support and center bounds |
| `FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md` | `6c38d162e1f2c435cf65a8b4a58a7001fe9489c65b3510159fee2687b9753708` | Full balanced actual four-boundary path |
| `PARALLEL_BYPASS_AT_UNLOADED_THREE_FORCE_ENDPOINT_EXCLUSION.md` | `0643b1ea0c6cd66724f2ad130c9cbd3fb2ffdbb53979e43170d7b58b2023e3be` | Section 2 physical frame argument only, repeated here |

The strict d<61/60 used above has squared reserve 31/57600 at the
maximum radius. The comparison sqrt(2)>7/5 has squared reserve1/25.
All six displayed rational reserves were recomputed by exact Fraction
arithmetic; none is a sampled premise.

The actual oblique B/X interface remains a separate obligation.
This file changes no finite cover, fine or coarse ledger, frozen
proof, Lean/CI state, remote repository or publication metadata.
