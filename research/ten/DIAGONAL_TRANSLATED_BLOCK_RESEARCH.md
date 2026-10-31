# Unreviewed completion lead for an outward diagonal two-by-two block

**Status: UNREVIEWED research handoff, 2026-10-31.** This records a proof
derivation reached before the user's handoff request. It has not received
root or independent review and is not a proved exclusion or ledger input.
In particular the quadrant lemma and its separating-axis coverage need
full review before any use. No fixed family is declared closed.

The on-ray row of
[LOADED_DEGREE_TWO_VV_SUPPORT_TABLE.md](LOADED_DEGREE_TWO_VV_SUPPORT_TABLE.md)
has a loaded square `C=[a,a+1]^2`, with

```text
0<a<1/2,       R^2=2*(a+1)^2,       P=(a,a).
```

If P is a geometric four-square junction, the four unit squares tile

```text
K=[a-1,a+1]^2.
```

This block is outside the scope of the published translated-block theorem:
its upper-right constituent has center norm greater than one. The proposed
argument below would bound its completion by five further squares. It
does not handle the on-ray contact when only three squares meet P.

## 1. Candidate quadrant lemma

**Proposed lemma.** Two unit squares whose interiors avoid the open
quadrant `{x>0,y>0}` and which each have `max x>0` and `max y>0` must
overlap in their interiors.

Here is the algebraic proof candidate. For each such square, a
separating-axis argument should give a northeast-facing side normal
`n=(c,s)`, with c,s>0 and c^2+s^2=1. The coordinate axes cannot separate
the square from the quadrant because it straddles both lines. Write
`v=(-s,c)` and express the square as

```text
S={-u*n+z*v : d<=u<=d+1, t<=z<=t+1},       d>=0.
```

The two strict straddling conditions become

```text
-d*c-t*s>0,       -d*s+(t+1)*c>0.
```

They imply

```text
-1<t<0,       d<c*s<=1/2.                           (1)
```

For two squares S_1,S_2, test every separating axis of S_1. Along its
mixed-sign direction `v_1=(-s_1,c_1)`, both squares have projection
intervals containing zero strictly. Indeed a point with x>0 must have
y<=0 because the square avoids the open quadrant, and gives negative
v_1 projection; a point with y>0 analogously gives positive projection.
Thus that axis cannot separate them.

For its positive direction n_1, the projection interval of S_1 is
`[-d_1-1,-d_1]`. Put

```text
A=n_1 dot n_2>0,       B=n_1 dot v_2.
```

Since the interval [t_2,t_2+1] contains zero, the minimum n_1 projection
of S_2 is at most `-(d_2+1)*A<=-A`, and its maximum is at least `-d_2*A`.
Moreover

```text
A=c_1*c_2+s_1*s_2 > min(c_1,s_1) >= c_1*s_1 > d_1,
-d_2*A > -1/2 > -d_1-1.
```

Thus the two projection interiors overlap along n_1 as well. Exchange
the squares to check both axes of S_2. The rectangle separating-axis
theorem would then prove overlap of interiors.

The crucial coverage detail to audit is the first paragraph: passing
from avoidance of an unbounded open quadrant plus strict straddling to
one of the square's own positive side normals, with d>=0. One possible
route is the separating-axis theorem applied to a sufficiently large
first-quadrant rectangle. The coordinate separation alternatives are
excluded, and a square-axis separator must have positive coordinates.
The remaining projection argument uses only strict inequalities.

## 2. Candidate application to the diagonal block

Take any additional unit square in the radius-R disk, disjoint from K.
As in
[GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md](GENERAL_TRANSLATED_BLOCK_OBSTRUCTION.md),
a separating axis either places it beyond a coordinate side of K or
gives an oblique side normal of the additional square supporting a corner
of K. In the oblique case one can translate inward to contact at that
corner without increasing vertex norms; the corner lies on the inner
edge segment, unless there was already coordinate separation.

The coordinate caps above or to the right of K have width

```text
R-(a+1)=(sqrt(2)-1)*(a+1)<1,
```

so contain no unit square. The upper-right corner is on the containing
circle and cannot belong to another square.

At the upper-left corner `q=(a-1,a+1)`, the general corner estimate from
the translated-block manuscript gives, for an oblique contact square,

```text
max_vertex |z|^2
  > (1-a)^2+(1+a)^2+2*(1-a)+1
   = 2*a^2-2*a+5.
```

Subtracting `R^2=2*a^2+4*a+2` gives `3-6*a>0`, a contradiction.
Reflection gives the same obstruction at the lower-right corner.
Only the lower-left corner `(a-1,a-1)` remains.

An additional square obliquely separated there avoids the open northeast
quadrant based at that corner. If it is not coordinate-separated from K,
it straddles both of that quadrant's coordinate lines. The proposed
quadrant lemma would permit at most one such square.

Every other additional square lies wholly in one of the two caps

```text
x<=a-1<-1/2,       y<=a-1<-1/2.
```

The reviewed sharp three-square cap theorem permits at most two squares
in either strict cap: its three-square equality case requires the sharp
boundary at distance 1/2. Therefore the proposed total is

```text
2 + 2 + 1 = 5 additional squares.
```

If all the coverage and strictness details pass review, this would exclude
the four-junction part of the on-ray loaded-VV residual for a ten-square
packing. The three-square junction and other irreducible branching
structures would still remain.
