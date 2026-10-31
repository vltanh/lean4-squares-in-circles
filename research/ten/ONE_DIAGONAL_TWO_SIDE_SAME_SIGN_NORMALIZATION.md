# The two side paths beside a loaded diagonal pair point to the same side

**Status:** exact whole-signature normalization; root and independent full
mathematical reviews of the assembled note passed on 2026-10-31. This is
not a whole-signature exclusion or a completion-capacity bound.

Use the selected physical certificate and `79/40<=R<=3/sqrt(2)`.
Suppose a three-loaded component has a D path A--B and single S paths
A--C and B--C: the whole signature is `LSLSLD`. All three loaded bodies
have degree two. Use the reviewed
[D-endpoint direction theorem](DIAGONAL_ENDPOINT_NONEMPTY_PATH_DIRECTION.md)
to put the parallel loaded endpoints in the frame

```text
A=[−u,1−u]×I_A,       B=[v−1,v]×I_B,
u+v=K=2+sqrt(2),
H_A=sqrt(R²−u²)>=1/2, H_B=sqrt(R²−v²)>=1/2.
```

Each loaded interval is either `[−H_i,1−H_i]` or `[H_i−1,H_i]`.
They coincide precisely when H_i=1/2, the radial-side case with two
geometric circle vertices. The common D force height h belongs to the
relative interior of both intervals. Its positive force magnitude is mu.

**Theorem.** The two S directions have nonzero vertical components with
the same sign. After a possible vertical reflection they can be written

```text
n_A=(p,q),       n_B=(−r,s),
p,r>=0,         q,s>0,
p²+q²=r²+s²=1.
```

Both unique-circle endpoints then have their circle vertex on their
lower outer corner. At most one D endpoint is radial. If an endpoint is
radial, the radius satisfies `R²<17/4` and the other endpoint has
`5/4<H<3/2`. Arbitrary nonnegative radial circle-load splits are retained.

## 1. Opposite directions with two unique-circle endpoints

Suppose A's circle vertex is lower and B's upper. Vertical force balance
and the direction theorem give outgoing S directions `(p,q)` and
`(−r,−s)` with p,r>=0 and q,s>0. Strict overlap of the D force height gives

```text
H_B−1<h<1−H_A,       H_A+H_B<2.                    (1)
```

If p>0, A's S support is its upper inner corner
`P_A=(1−u,1−H_A)`. Torque about its circle vertex `Z_A=(−u,−H_A)` gives

```text
mu(h+H_A)=sigma_A(q−p)>0.
```

Hence q>p and q>1/sqrt(2). If p=0, the contact may be anywhere on the
upper horizontal side, but q=1 gives the same strict bound. At B the
reflected torque equation is

```text
mu(H_B−h)=sigma_B(s−r)>0
```

when r>0; when r=0, s=1. Thus s>1/sqrt(2) in either case.

The two far S contacts are points of the same unit square C. Their
heights are `1−H_A+q` and `H_B−1−s`, so (1) makes their difference

```text
2−H_A−H_B+q+s > sqrt(2).
```

A unit square has vertical width at most sqrt(2), a contradiction.
Reflection handles the other ordering of opposite unique circle signs.

## 2. At most one endpoint can be radial

A radial endpoint has

```text
u=sqrt(R²−1/4)>19/10.
```

Indeed `(79/40)²−1/4=5841/1600>(19/10)²`. If both endpoints were
radial, then `u+v>19/5`, whereas `u+v=2+sqrt(2)<7/2`, impossible.

Suppose henceforth that A is radial and B has a unique circle vertex.
The direction theorem makes A's S direction a strict inner-corner
direction with nonzero vertical component. Reflect so it is `(p,q)`
with p,q>0, at `(1−u,1/2)`.

The neighboring endpoint has the useful strict bound

```text
v=2+sqrt(2)−u < 2+57/40−19/10 =61/40,
H_B²=R²−v² > [(79)²−(61)²]/1600
             =63/40>25/16,
H_B>5/4.                                           (2)
```

## 3. Radial torque fixes the sign, without choosing a circle split

Every circle force has zero torque about the origin. On radial A, the
outgoing D force is `mu(1,0)` at `(1−u,h)` and the outgoing S force is
`sigma_A(p,q)` at `(1−u,1/2)`. Origin torque balance therefore gives

```text
mu h=sigma_A[(1−u)q−p/2]<0,
h<0.                                                (3)
```

This calculation is independent of the two circle coefficients and
remains valid when either coefficient is zero.

If B's S direction pointed downward, vertical force balance at its
unique circle vertex would make B upper-loaded. Its D height would then
satisfy `h>H_B−1>1/4`, contradicting (3). Thus B's S direction also
points upward. Horizontal reflection covers radial B. Along with
Sections 1–2 this proves the same-sign assertion in all cases.

## 4. Exact radius and height bounds for the radial survivor

The common D height belongs to `(−1/2,1/2)` on radial A and to the
relative interior of a loaded interval on B. This is possible only if
`H_B<3/2`, regardless of which loaded interval B uses. Since
`R²=u²+1/4` and `v=K−u`,

```text
H_B²−9/4 = u²+1/4−(K−u)²−9/4
          =2K(u−2),
```

where `K²+2=4K`. Hence `u<2` and `R²<17/4`.
After the upward normalization, B is lower-loaded, and (2) gives

```text
5/4<H_B<3/2,
−1/2<h<1−H_B<−1/4.                                 (4)
```

This radius conclusion also follows from the already reviewed loaded-D
endpoint clearance argument in
[SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md](SS_PATH_RADIAL_SIDE_DIAGONAL_EXCLUSION.md),
Section 3; the direct identity above makes explicit that no SS hypothesis
is needed here.

## 5. Exhaustive surviving endpoint supports

After upward reflection the remaining support possibilities are:

| Endpoint circle feature | S contact on that endpoint | Direction |
| --- | --- | --- |
| Unique lower outer vertex | Upper inner corner | Strictly inward and upward |
| Unique lower outer vertex | Upper horizontal side, endpoints included | Vertical upward |
| Two outer circle vertices | Upper inner corner | Strictly inward and upward |

For a unique endpoint with a strict corner S direction, torque shows its
vertical component is strictly larger than the horizontal component.
The same inequality holds for its vertical side-normal alternative.
No such steep-direction assertion is made for a radial endpoint.

All supports and all circle multiplicities at the common loaded endpoint
C remain unrestricted. Both transmitter slide parameters remain free.
The remaining whole-case task is to bound completion capacity uniformly
over these surviving cases; the normalization alone does not exclude
the LSLSLD signature.
