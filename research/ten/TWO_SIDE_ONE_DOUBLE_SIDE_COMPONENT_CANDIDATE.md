# A numerical seven-body LSLSLSS component

**Status:** exploratory numerical construction, not an exact existence
certificate and not a ten-square packing. It closes no whole-case ID.
Its practical consequence is to avoid trying to exclude this component
using only its internal force, torque, and contact equations: completion
capacity must be addressed unless this numerical candidate is disproved.

The signature is `C20-M07-L03-B02-T01 LSLSLSS`. The seven positive edges
form the cycle `A–U–V–B–T–C–S–A`; exactly A, B, C carry circle loads.
U and V form the SS path. S and T are single side transmitters.

Run the self-contained high-precision reconstruction with:

```sh
python research/ten/explore_two_side_one_double_side_component.py \
  --output research/ten/two_side_one_double_side_candidate.json
```

The script requires `mpmath`. Its saved output records all vertices,
physical contact points, positive forces, circle coefficients, body force
and torque residuals, contact membership and support margins, and all
21 pairwise separating-axis margins. It uses numerical root finding;
80-digit arithmetic does not replace an interval or algebraic proof.

## 1. A one-parameter symmetric construction

Put `c=cos(theta)`, `s=sin(theta)`, and define

```text
e=(c,s), f=(-s,c),
r=(1+(c+s)/2)/c,
R=sqrt((r+1/2)^2+1/4).
```

Choose theta as a root near 0.102 of

```text
R = 2 sqrt(2)+c-r(c+s).                              (1)
```

A is the unit square centered at `−r e` with frame `(e,f)`, and B is
its reflection in the vertical axis. Their two outer vertices are on
the containing circle; both circles atoms receive positive weight below.
The rightmost vertex Q of A has x-coordinate −1. Its upper adjacent
vertex is P. Thus

```text
Q=−r e+(e−f)/2,
P=−r e+(e+f)/2.
```

C is the diamond with vertices

```text
(0,R), (1/sqrt(2),R−1/sqrt(2)),
(0,R−sqrt(2)), (−1/sqrt(2),R−1/sqrt(2)).
```

Write `n=(1,1)/sqrt(2)` and `t=(−1,1)/sqrt(2)`. Set

```text
S=P+[0,1]n+[−1/2,1/2]t,
T=the vertical-axis reflection of S,
U=[−1,0]×[−3/2,−1/2],
V=[0,1]×[−3/2,−1/2].
```

Equation (1) puts `P+n` on C's lower-left side. The SS force line is
`y=Q_y`; it passes from Q through U and V to the reflected Q.

The numerical solution is

```text
theta = 0.102044961939244...
R     = 2.116341817652994934065...
R^2   = 4.478902689146782459928... < 9/2.
```

The centers, rounded here only for orientation, are

| Body | Center |
| --- | --- |
| A | (−1.548333, −0.158550) |
| B | (1.548333, −0.158550) |
| C | (0, 1.409235) |
| U | (−0.5, −1) |
| V | (0.5, −1) |
| S | (−0.748315, 0.743336) |
| T | (0.748315, 0.743336) |

## 2. Positive forces and circle atoms

Give each single S path force magnitude 1. Give the SS path magnitude

```text
mu=(P_y−P_x)/(−sqrt(2) Q_y)=1.743354721260428... > 0.
```

The forces into A are `−mu(1,0)` at Q and `−n` at P. The displayed
choice of mu makes their total torque about the origin zero.
Let `Z_-=−r e−(e+f)/2` and `Z_+=−r e+(−e+f)/2` be A's outer vertices.
Solve

```text
lambda_- Z_- + lambda_+ Z_+ = −mu(1,0)−n.
```

The coefficients are approximately 1.064024 and 0.156414, both positive.
These are the circle coefficients on A; B uses their reflected copies.
C uses its upper vertex with coefficient `sqrt(2)/R≈0.668235`.
All circle forces point inward. Unloaded transmitters have equal opposite
forces on a common line, so their force and torque balance is automatic.
All coefficients may be divided by their positive circle-coefficient sum
if the certificate normalization requires that sum to equal one.

At this solution A and B have two circle contacts each. Replacing those
two atoms by the lower one alone produces a false negative-force
obstruction; that single-circle assumption must not enter a purported
whole-case exclusion.

## 3. Numerical checks and generic-normal compatibility

The 80-digit reconstruction has maximum equation, body-force, or
body-torque residual below `5×10^−81`. All seven positive graph edges
have zero separating-axis gap to numerical precision. The fourteen
nonedges have strictly positive separating-axis margins, with minimum
greater than 0.05827. All vertices lie in the disk to the same numerical
precision; only the five stated loaded vertices have zero circle slack.

At A–U and B–V, the contact is a loaded vertex in the relative interior
of a transmitter side. The analogous statement holds at A–S and B–T.
U–V, S–C, and T–C share side segments, and their force applications are
valid points of those segments. There is no point-only vertex/vertex
positive contact. Hence the candidate does not evade the reviewed
generic-normal selection rule through a forbidden normal.

This is evidence for a realizable small component, not a counterexample
to the n=10 lower bound. Three more unit squares would be needed. No
capacity theorem, classification of all realizations of this signature,
or whole-case promotion is claimed here.
