# The exact five-corner optimum has a seven-outer-center realization

**Theorem (hand proof, no root-isolating box).** Let
`q=R_hat^2` be the globally selected least five-corner
radius in HUMAN_FAMILY_CLOSURE.md. The eight-square
construction of ANALYTIC_EXACT_CONSTRUCTION.md can be
chosen so that its unique central square contains the
disk origin strictly, while **all seven other square
centers have Euclidean norm strictly greater than one**.

The circle radius is still **exactly R_hat**; the
five contact-bearing outer corners and all other
six standard-square centers remain unchanged.
No new interval certificate, sampled extremum,
orientation assumption or numerical root enclosure
enters this theorem. It is a property of the
fully analytical five-corner family itself.

## 1. The one-parameter displacement

Use exactly the notation and inequalities (2)--(5)
of ANALYTIC_EXACT_CONSTRUCTION.md. In particular

    (79/40)^2<q<9789/2500<4,
    1/2<v<u<1,   17/10<r,w,
    3/2<U<41/24,  c>49/50, 0<s<1/5,
    k1^2+k2^2=q,   k1>1, k2>1/2.

The side frame `e=(c,s),f=(-s,c)` is orthonormal.
Retain all six standard squares, including the central
square C with its slider `z_C=343/1000` and the
upper square T with `z_T=13431/10000`. Keep H at

    H=P5+(e+f)/2,

but replace the former small G slider by

    d=k1-1>0,
    eta=-d/2,
    G=H+e+eta*f.                                      (1)

The old proof already checks every pair at eta=0;
we recheck the inequalities affected by (1) below.

We first establish a useful upper bound on k1.
Since `r>17/10`, `c>49/50`, `s<1/5`
and `u<1`,

    k1=2-c*(r-1)+s*u
       <2-(49/50)*(7/10)+1/5
       =757/500<38/25<2.                            (2)

Thus `0<d<1`. Also `k2<sqrt(q)<2`.

## 2. The moved square stays strictly inside the sharp disk

In the tilted `(e,f)` frame the four vertex
coordinate ranges of G are

    e coordinate in [1-k1,2-k1],
    f coordinate in [-k2-d/2,1-k2-d/2].

Compared with `k1^2+k2^2=q`, the squared e-coordinate
loses at least

    delta=min(2*k1-1,4*(k1-1))
          =min(1+2*d,4*d)>3*d,                         (3)

since `0<d<1`.

As `k2>1/2`, the largest absolute f-coordinate
is `k2+d/2`. The greatest vertex squared norm
of the new G therefore obeys

    max_vertex |z|^2
       <=q-delta+(k2+d/2)^2-k2^2
       =q-delta+k2*d+d^2/4
       <q-3*d+2*d+d/4
       =q-3*d/4<q.                                    (4)

Thus **all four G vertices and its entire square**
lie strictly inside the same radius-R_hat disk.

No numerical margin is needed: (4) gives the
explicit symbolic reserve `3*(k1-1)/4`.

## 3. Every old pair separator survives

The six standard squares have not moved; their
fifteen pair checks in the original proof
are unchanged. The tilted pair G,H is still
separated along e, because

    e dot(G-H)=1+eta*(e dot f)=1.

The A,G contact separator is unchanged:

    e dot(A-G)=W,       W=(1+c+s)/2,

since moving G along f does not change its
e projection. The E,H, A,H separators are
unaffected because H has not moved.

The original horizontal separation of E from
G at eta=0 has **strict gap >1/4** by equation
(11) of ANALYTIC_EXACT_CONSTRUCTION.md.
When eta<0, the x-coordinate of G increases
by `-s*eta>0`; hence that horizontal gap
only increases.

Finally, at eta=0 both tilted squares are
strictly below all four squares B,C,D,T,
by equations (12)--(13) of the original proof.
Since `f_y=c>0` and eta<0, the entire
translated G moves strictly *downward*,
so those four vertical separations also
only increase. Every pair among the eight
squares is therefore interior-disjoint.
This proves the packing construction.

## 4. The tilted G center is now provably outer

From (1) its center coordinates in the
orthonormal `(e,f)` frame are exactly

    e dot G = 3/2-k1,
    f dot G = 1-k2-k1/2.                               (5)

We claim

    k2+k1/2>2.                                        (6)

To prove (6) without any tiny root box,
put `x=k1`, so `1<x<38/25`.
The convex quadratic

    P(x)=4-2*x+(5/4)*x^2

attains its maximum on `[1,38/25]`
at an endpoint. Direct fraction arithmetic gives

    P(1)=13/4,
    P(38/25)=481/125.

Therefore

    P(k1)<=481/125 < (79/40)^2 <q=k1^2+k2^2.

Rearranging gives

    k2^2>(2-k1/2)^2.

Both quantities under the square comparison
have positive square roots, because
`k2>0` and `k1<2`. Thus
`k2>2-k1/2`, proving (6).
By (5), `f dot G<-1`, so

    |G|>1.                                              (7)

This is a **whole-domain analytic** consequence
of the existing family bounds, not an observation
about rounded candidate coordinates.

## 5. The other six noncentral centers are also outer

The six standard centers from the original construction
are A,B,C,D,E,T. Among them C is central:
its signed frame coordinates have magnitudes
`U-3/2<5/24<1/2` and `z_C=343/1000<1/2`.
Hence the disk origin lies in the open interior of C.

For the other five standard squares:

* `|A|>1` since its x-coordinate is
  `r-1/2>6/5`.
* `|B|>1` since its x-coordinate is
  `U-1/2>1`.
* `|E|>1` since its x-coordinate is
  `1/2-w<-6/5`.
* `|T|>1` since its y-coordinate is
  `z_T=13431/10000>1`.
* For D, note `U>V` implies `V<3/2`.
  Hence

      (2-v)^2=q-V^2
             > (79/40)^2-9/4
             =2641/1600 >25/16,

  so `v<3/4`. Its coordinates
  `(U-5/2,3/2-v)` therefore satisfy

      |D|^2>(19/24)^2+(3/4)^2
             =685/576>1,

  using `U<41/24`.

The sixth noncentral square H has center
coordinates `(1/2-k1,1/2-k2)` in the tilted
frame. Cauchy--Schwarz gives

    |H|^2=q-(k1+k2)+1/2
         >=q-sqrt(2*q)+1/2
         >q-3+1/2>1,

because q> (79/40)^2>7/2 and q<4
imply `sqrt(2*q)<sqrt(8)<3`.
Together with (7), all seven centers
A,B,D,E,T,H,G are strictly outer.

## 6. Implication for an unrestricted optimality proof

A sharp five-corner construction of radius
**exactly R_hat** admits both a near-center
exterior-square realization (the original
slider eta=0) and a realization in which
**all seven exterior square centers are outer**.
The latter follows from the same analytical
stationary-family theorem and the displacement
(1); no candidate root-isolation certificate
is needed.

Consequently an argument which attempts to
prove R8>=R_hat by first showing that every
radius-minimizing packing at R_hat contains
a *second* center of norm less than one would
be false **if** R8=R_hat, since the displayed
eight-square packing would itself be a
radius minimizer with seven outer centers.
More generally, any geometric claim that
all packings of radius <=R_hat contain a
noncentral inner center is **unconditionally
refuted** by this exact construction.

The contact graph of this realization is not
asserted to be a full seven-outer ring.
A global proof must handle the outer paths
closed through the central square as well as
any surviving outer ring. The five-corner
construction establishes R8<=R_hat; the
opposite unrestricted inequality remains
an open obligation.


## 7. An entire analytically certified slider interval

The proof actually works for **every**

    -(k1-1)/2 <= eta <= 0,                             (8)

not only the selected endpoint.

Indeed every pair separation above is unchanged or becomes
stronger when eta decreases from zero. In the tilted
frame G's e-coordinate vertex interval remains unchanged,
while the largest absolute f vertex coordinate is
`k2-eta`, which increases as eta decreases.
The maximum squared vertex norm is consequently
largest at the negative endpoint (1), already
shown in (4) to be strictly below q. Thus all
intermediate choices preserve circle containment.

The f component of the center G is
`1/2-k2+eta<0`, and its e component is
independent of eta. Hence `|G|` **increases
strictly** as eta decreases throughout (8).
At the left endpoint it is greater than one,
by (7). This gives a macroscopic, analytically
certified slider of length `(k1-1)/2>0`
within the *exact* least-family-radius packing.

Unlike the earlier tiny independent slider
interval around eta=0, (8) permits
moving a square across the center-norm-one
boundary whenever its right endpoint
started below that boundary. No such crossing
is asserted without first checking the
starting center norm.


## 8. The seven outer squares actually form a contact cycle

**Strengthening.** At the negative slider endpoint
`eta=-(k1-1)/2`, the seven outer squares do not merely
fit: their **actual-contact graph is the entire
seven-cycle**

    A--B--T--D--E--H--G--A.                            (9)

Moreover the central square C has actual contacts with
B and D. Thus the full seven-outer **contact-cycle**
case is an exact sharp-family realization, not a
hypothetical branch to exclude at radius Rhat.

It is important to check *actual common points*:
a tight separating projection does not by itself
guarantee that the two supporting faces intersect.

The needed extra position facts are already proved
analytically in HUMAN_FAMILY_CLOSURE.md, Propositions
3--4, for the unique least-family-radius stationary
point:

    u>87/100,   v<589/1000,
    r<16/9,     w<48/25.                              (10)

The same proof above gave `k1<757/500`; also
`k1>3-r>57/50`.

### 8.1 The five contacts carried by the parallel columns and the tilted pair

The A top and B bottom share the line `y=1-u`.
Their horizontal projections overlap with positive length,
because A occupies `[r-1,r]` and B occupies
`[U-1,U]`, where `0<r-U<1`
from `r>U`, `r<16/9`, and `U>3/2`.
Thus **A-B is an actual edge contact**.

The B left and T right sides share the line `x=U-1`.
The B vertical interval is `[1-u,2-u]`;
the T interval is `[z_T-1/2,z_T+1/2]`,
with `z_T=13431/10000`.
Their interiors overlap along this line because
`1-u<1<z_T+1/2` and
`z_T-1/2=8431/10000<1<2-u`.
Thus B-T is an actual edge contact.

Similarly the T left and D right sides share
`x=U-2`. The D vertical interval is
`[1-v,2-v]`, with `1/2<v<3/4`.
It meets T's vertical interval with positive length:
`1-v<1/2<z_T+1/2` and
`z_T-1/2<1<2-v`. Thus T-D is an actual edge contact.

The E top and D bottom meet on `y=1-v`.
Their horizontal intervals are, respectively,
`[-w,1-w]` and `[U-3,U-2]`.
They overlap with positive length because
`2<U+w<4`: the lower bound follows from
`U>3/2,w>17/10`, and the upper bound
from `U<41/24,w<48/25`.
This proves D-E is an actual edge contact.

The H positive-e side and the G negative-e side
have the same e coordinate because `e dot(G-H)=1`.
Their f-coordinate center difference is
`eta=-d/2`, with `|eta|<1/2<1`.
Two unit-length side intervals translated by
less than one overlap with positive length,
so H-G is an actual edge contact.

### 8.2 The E-H tilted contact: the support vertex stays on its edge

The E support vertex in the negative-f direction is

    z_E=(1-w,-v).

From `k2=1+c*v-s*(w-1)` and
`f=(-s,c)`, its f coordinate is

    f dot z_E=s*(w-1)-c*v=1-k2.

But H has f-center coordinate `1/2-k2`, so its
positive-f side lies precisely on that same
support line. The H side's e interval is
`[-k1,1-k1]`. We must check that its
vertex `z_E` has an e coordinate inside.

Indeed, by (3)--(4), (10) and `0<s<1/5`,

    e dot z_E=c*(1-w)-s*v
      >-(w-1)-s*v
      >-23/25-589/5000
      >-57/50 >-k1,

whereas

    e dot z_E <-c*(w-1)
       <-(49/50)*(7/10)
       =-343/500
       <-257/500<1-k1.

Thus `z_E` lies in the **relative interior**
of H's positive-f supporting side. Hence
E-H is an actual vertex-to-edge contact.

### 8.3 The G-A tilted contact survives the larger slide

The A support vertex in the negative-e
direction is

    z_A=(r-1,-u).

It has `e dot z_A=c*(r-1)-s*u=2-k1`,
which equals G's positive-e support coordinate.
The G positive-e side has f-coordinate interval

    [1/2-k2-k1/2, 3/2-k2-k1/2].

Let `T_A=f dot z_A-f dot G`, the transverse
offset from that side's center. Substitution
of the k2 definition and eta=-d/2 yields

    T_A=1/2-c*(u-v)-s*(r+w-2)+d/2.                (11)

The upper bound uses `u-v>87/100-589/1000
=281/1000`, `c>49/50`, and
`d/2<(757/500-1)/2=257/1000`:

    T_A<1/2-(49/50)*(281/1000)+257/1000
        <1/2.

The lower bound uses `u-v<1/2`,
`r+w-2<16/9+48/25-2<17/10`,
`s<1/5`, and `d/2>0`:

    T_A>1/2-1/2-(1/5)*(17/10)
        =-17/50>-1/2.

Therefore `-1/2<T_A<1/2`. The A support
vertex lies in the **relative interior**
of G's positive-e edge. Consequently
G-A remains an actual contact after the
macroscopic negative-f slide.

The seven successive pairs in (9) now all
have proven actual contact points.

### 8.4 Central spokes and exact outer cycle

The central square C occupies the horizontal
interval `[U-2,U-1]`, meeting B along
`x=U-1` and D along `x=U-2`.
Its vertical interval is
`[z_C-1/2,z_C+1/2]` with `z_C=343/1000`.
It overlaps both B's interval `[1-u,2-u]`
and D's interval `[1-v,2-v]` in positive
length, because `u>87/100`,
`1/2<v<3/4` and `z_C+1/2=843/1000`.
Hence **C-B and C-D are actual central contacts**.

All seven noncentral square centers were
proved outer in sections 4--5. The private-ray
and outer circular-order theorem in
HUMAN_OUTER_CENTER_VISIBILITY.md says that
their induced actual-contact graph is a subgraph
of a simple seven-cycle. Since the seven
edges in (9) already form a Hamiltonian
seven-cycle, they must be the **entire
outer induced contact graph**, and their
order agrees with the actual circular center
order up to reversal.

This directly corrects a previously tempting
proof strategy: **the full seven-outer
actual-contact-cycle case cannot be
excluded at Rhat**, because the exact
conditional candidate realizes it. The
sharp global argument must recover the
five-corner support obstruction *inside
this contact-cycle case*, with equality
permitted, as well as cover the centrally
closed outer-path case.

No unrestricted theorem `R8=Rhat` is
claimed from this construction: it is
an equality **candidate** for the
missing global lower bound.


## 9. The exterior actual-contact cycle persists along the entire slide

The seven actual contact edges in (9) remain present for
**every** eta in the full interval (8). Only the H-G
edge overlap and the G-A vertex-to-edge contact depend
on eta; all other five edges are fixed.

For H-G, the f-center difference is eta, and
`|eta|<=d/2<1/2<1`, so the supporting
unit intervals retain positive overlap.

For G-A, the transverse vertex-to-edge offset
is the affine function

    T_A(eta)=1/2-c*(u-v)-s*(r+w-2)-eta.

It increases as eta decreases. At the left
endpoint `eta=-d/2`, section 8.3 proves
`-1/2<T_A<1/2`. At the right endpoint
eta=0 the lower estimate is

    T_A(0)>1/2-1/2-(1/5)*(17/10)
           =-17/50>-1/2,

while its upper bound is even smaller than
at the left endpoint. Affinity now puts
`-1/2<T_A(eta)<1/2` throughout (8).
Thus the A support vertex always belongs
to the **relative interior** of G's supporting
edge, and G-A remains an actual contact.

Consequently the full seven-square *exterior*
contact cycle A-B-T-D-E-H-G-A is preserved
throughout this macroscopic deformation,
even though the radial norm of the G center
changes strictly. The two central spokes
C-B,C-D also remain actual contacts.

This illustrates why classifying the ring
solely by which of its square centers have
norm above one is not a topological or
contact-graph invariant: the center norms
can change while every actual edge of the
exterior cycle stays present.
