# An exploratory six-body component survives the one-D/two-S equations

**Status:** high-precision numerical research candidate, not a proof.
There is no exact-root or interval existence certificate, and no
ten-square completion has been constructed. No finite case is closed
by this note.

The remaining signature

```text
C20-M06-L03-B02-T02: LSLSLD
```

has three loaded bodies, two S transmitters, and one D transmitter.
The current evidence suggests that a proof must use the four further
squares in a ten-packing, rather than trying to exclude every isolated
six-body stress component.

The [reproduction script](explore_one_diagonal_two_side_component.py)
solves three equations at 80-decimal precision. The saved
[candidate and residuals](one_diagonal_two_side_candidate.json) include
all six squares, contacts, positive force magnitudes, positive circle
loads, and every pairwise separating-axis check. The radius is

```text
R ≈ 2.0325299468783518576,
R^2 ≈ 4.131177984957317.
```

The unloaded squares have squared-radius slack exceeding 1.46. Every
noncontacting pair has a positive separating projection gap, the smallest
exceeding 0.14. Force and torque residuals are below `5e-80`; the tiny
reported contact/support errors are floating-point residuals. These
figures are reproducibility diagnostics, not certified error bounds.

## 1. Exact equations used by the numerical model

Let d=sqrt(2), and take three unknowns R,u,z. Define

```text
v=2+d-u,
H_A=sqrt(R^2-u^2),       H_B=sqrt(R^2-v^2),
t_A=[u*z-H_A*(u-1)]/[H_A*(1-H_A+z)],
t_B=[v*z-H_B*(v-1)]/[H_B*(1-H_B+z)],
q=1/sqrt(1+t_A^2),       p=t_A*q,
s=1/sqrt(1+t_B^2),       r=t_B*s.
```

The two parallel loaded endpoint squares are

```text
A=[-u,1-u] x [-H_A,1-H_A],
B=[v-1,v] x [-H_B,1-H_B].
```

Their circle vertices are `(-u,-H_A)` and `(v,-H_B)`. A horizontal D
transmitter joins their facing sides along `y=-z`. The above expressions
for t_A,t_B enforce the endpoint force and torque equations when the
two S paths leave their upper inner corners.

Put

```text
n_A=(p,q),         e_A=(q,-p),
n_B=(-r,s),        e_B=(s,r),
P_A=(1-u,1-H_A),   P_B=(v-1,1-H_B),
P=P_A+n_A,        Q=P_B+n_B,
W=Q-e_A+n_A.
```

C has a side contact at P, a vertex contact at Q, and candidate circle
vertex W. Its proposed square is

```text
C=Q+[-1,0]e_A+[0,1]n_A.
```

Normalize the D contact magnitude to one, and define

```text
sigma_A=1/(u*q/H_A-p),
sigma_B=1/(v*s/H_B-r),
g_C=sigma_A*n_A+sigma_B*n_B.
```

The three root equations are

```text
n_A dot(Q-P)=0,
|W|^2=R^2,
W cross g_C=0.
```

The numerical root has positive dot product `W dot g_C`, positive force
magnitudes, and P strictly inside the designated C side. The resulting
circle coefficients are approximately 0.794, 1.015, and 0.992 on A,B,C.
All contact forces and circle coefficients can be divided by their
positive circle-coefficient sum to obtain the usual normalization.

## 2. The transmitter placements have actual interior clearance

The D square is fixed by its two horizontal diagonal endpoints. For the
two S squares, the force line can slide transversely within the square.
The reproduction uses the rational choices

```text
S_A=P_A+[0,1]n_A+[-7/9,2/9]e_A,
S_B=P_B+[0,1]n_B+[-1/7,6/7]e_B.
```

The D contacts occur in relative side interiors of A and B, compatible
with the generic normal selection. At A--S_A and B--S_B, a loaded vertex
meets a relative transmitter side interior. At S_B--C, a C vertex meets
a relative transmitter side interior. S_A and C have a positive-length
shared side segment, with their force application inside that segment.
There are no point-only vertex/vertex active contacts in this candidate.

The script constructs the exact formulas for all vertices and uses both
square frames for every pairwise separating-axis check. It also checks
the displayed contact points' square coordinates, support inequalities,
circle containment residuals, and body-by-body force and torque residuals.
Those checks are evaluated numerically at the approximate root.

## 3. What this does and does not settle

The candidate does not establish an exact six-body physical stress;
that requires an exact algebraic or interval root certificate and
validated inequalities. Even if that certification is completed, it
would not be a ten-square packing. Four further squares would have to
fit in the same disk, and that is a separate capacity question.

The candidate is retained to prevent an unsupported claim that local
three-load force balance alone excludes LSLSLD. A useful next step is a
completion obstruction for the resulting six-body cores, retaining the
actual two S slide parameters and the remaining contact-ownership cases.
