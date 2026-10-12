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
