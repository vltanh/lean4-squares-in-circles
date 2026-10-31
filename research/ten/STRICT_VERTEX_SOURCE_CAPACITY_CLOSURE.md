# Complete source closure when both LSLSLD D endpoints have unique circle vertices

**Status:** complete branch argument in the selected-certificate radius
window 79/40<=R<=3/sqrt(2). Two exact arithmetic backends checked the
finite tables in this single-agent session. No independent agent review
or Lean verification is claimed.

Together with [the strict side-source closure](STRICT_SIDE_SOURCE_CAPACITY_CLOSURE.md),
this excludes every LSLSLD realization whose two D endpoints each have
one geometric circle vertex. The separate radial-D-endpoint branch
remains open, so the fixed master ledger stays 276/336 closed and 60 open.

## 1. Exhaustive scope

The [common-edge classification](ONE_DIAGONAL_TWO_SIDE_COMMON_SOURCE_EDGE.md)
and [completed vertical exclusion](RADIAL_VERTICAL_SOURCE_EXCLUSION.md)
give strict directions n_A=(p,q), n_B=(-r,s), with
0<p<q, 0<r<s, p^2+q^2=r^2+s^2=1. Both transmitter slides retain their
whole intervals. The common source edge has direction e=(a,b) and inward
normal m=(-b,a). In row V_V its contacts are its two endpoints and

```text
a = sqrt(2)-p-r,       b = H_A-H_B+s-q,
a^2+b^2=1,            a>0,
p*a+q*b>0,           -r*a+s*b<0.
```

Consequently -p/q<b/a<r/s, so |b|<a and a>1/sqrt(2).
C has either a unique upper-left vertex, a unique upper-right vertex,
or its two upper vertices on the circle. The E_A/E_B rows are already
excluded by the preceding side-source theorem.

## 2. Neither unique-circle V_V source can balance torque

Write p=sin(theta_A), q=cos(theta_A), r=sin(theta_B),
s=cos(theta_B), with both angles in (0,pi/4). Since

```text
p+r = sqrt(2)-a < 1/sqrt(2),
sin(theta_A+theta_B)=p*s+q*r < p+r,
```

and theta_A+theta_B is in (0,pi/2), their sum is strictly below pi/4.
In particular

```text
p/q < (s-r)/(s+r),       r/s < (q-p)/(q+p).
```

For a unique upper-left circle vertex W=Q_A+m, the two outgoing S
torques about W sum to

```text
-sigma_A*(p*a+q*b)
-sigma_B*((s-r)*a+(s+r)*b).
```

The first parenthesis is strictly positive. The support inequality
b>-(p/q)*a and the angle bound make the second parenthesis strictly
positive too. Thus the torque is negative, a contradiction.

At the unique upper-right circle vertex W=Q_B+m, the sum is

```text
sigma_A*((q-p)*a-(p+q)*b)
+sigma_B*(r*a-s*b).
```

Both parentheses are strictly positive, using b<(r/s)*a and the
second angle bound. The torque is positive, again impossible.
These contradictions use only positive S force magnitudes and actual
contact positions; no guessed contact point or transmitter slide is used.

## 3. A radial V_V source reduces to two variables

The remaining source has both upper vertices on the circle, retaining
every nonnegative circle-load split, including a zero coefficient. Put

```text
L=sqrt(R^2-1/4)-1,       9/10<L<17/16,
Q_A=-e/2+L*m,           Q_B=e/2+L*m,
c_C=(L+1/2)*m,          R^2=(L+1)^2+1/4.
```

The L bounds follow directly from the imported radius window.

Use x=p/(1+q) and t=b/(1+a). Both variables lie in
0<x<sqrt(2)-1 and |t|<sqrt(2)-1. Then

```text
p=2*x/(1+x^2),         q=(1-x^2)/(1+x^2),
a=(1-t^2)/(1+t^2),     b=2*t/(1+t^2),
r=sqrt(2)-a-p,         s=sqrt(1-r^2)>0.
```

Actual points also have 0<r<1/sqrt(2) and the two strict source
support inequalities from Section 1.

Set

```text
A_X=1+a/2+p,           A_Y=1+b/2+q,
B_X=1+a/2+r,           B_Y=-1+b/2-s.
```

Endpoint geometry gives

```text
u=A_X+L*b,             v=B_X-L*b,
H_A=A_Y-L*a,           H_B=-B_Y-L*a.
```

The outer circle vertices are L*m-(A_X,A_Y) and
L*m+(B_X,B_Y). Equating each squared norm with (L+1)^2+1/4 gives

```text
L_A=(A_X^2+A_Y^2-5/4)/(2*(1-b*A_X+a*A_Y)),
L_B=(B_X^2+B_Y^2-5/4)/(2*(1+b*B_X-a*B_Y)).
```

Both denominators exceed two at every actual point:
a*(1+q)-b*(1+p)>0 and b*(1+r)+a*(1+s)>0, by |b|<a,
q>p and s>r. There is no lost zero-denominator case.
Set L=L_A and impose G=L_A-L_B=0.

The remaining endpoint torque equation is, as before,

```text
D_A=u*q-H_A*p>0,       D_B=v*s-H_B*r>0,
N_A=H_A*((u-1)*q-(H_A-1)*p),
N_B=H_B*((v-1)*s-(H_B-1)*r),
E=N_A*D_B-N_B*D_A=0,       h=-N_A/D_A.
```

These conditions are necessary. Ignoring further circle-load or
nonoverlap conditions only enlarges the family to which the capacity
bound will apply. In particular no choice of the radial circle-load
split is excluded without proof.

## 4. Complete finite parameter classification

The full table in
[strict_vertex_source_closure_certificate.json](strict_vertex_source_closure_certificate.json)
bisects [0,27/64] x [-27/64,27/64] along its longer side, with x first
on ties. Closed child cells share their bisecting boundary. Let
S=2^44=17592186044416.

| Leaf rule | Number |
| --- | ---: |
| Impossible source support | 5 |
| G has strict nonzero sign | 108 |
| L outside (9/10,17/16) | 6 |
| Interval Newton excludes a zero | 81 |
| E has strict nonzero sign | 3 |
| r outside (0,1/sqrt(2)) | 11 |
| Retained interior rectangle T | 2 |
| **Total** | **216** |

Maximum binary depth is 33. The paths are a full prefix-free binary
frontier and cover the whole closed initial rectangle. There are no
unresolved leaves or removed boundary neighborhoods. The two retained
leaves both lie in

```text
T:
x in [1841550035129/S, 1841901878851/S],
t in [-175921861/S, 175921861/S].
```

All operations use outward-rounded integer intervals. Square roots use
integer square roots of the scaled endpoints, with an upper endpoint
increment when the radicand is not a perfect square. The only constant
radical is bracketed by the same strict integer-square comparisons as
in the side-source proof. Forward derivative intervals and each row's
rational preconditioner (denominator 1024) verify the mean-value
Newton exclusion. The elementary identity proving that test is stated
in Section 2 of the side-source proof; no root existence is a premise.

The verifier checks every listed strict inequality, every path and all
coverage. Thus all actual radial V_V source configurations lie in T.

## 5. A 120-cell physical capacity cover on all of T

The four relevant centers are

```text
c_A=(1/2-u,1/2-H_A),
c_B=(v-1/2,1/2-H_B),
c_D=((v-u)/2,-N_A/D_A),
c_C=(-(L+1/2)*b,(L+1/2)*a).
```

The certificate's four center boxes, ordered A,B,D,C, are exact outward
interval evaluations on T. The same evaluation gives

```text
R^2 <= 3.999896816067974 < 4.
```

The decimal merely presents the exact integer upper bound checked
against four. Every square center c obeys
R^2>=|c|^2+|c|+1/2. Since

```text
(23/16)^2+23/16+1/2=1025/256>4,
```

every center has norm strictly below 23/16.

The second full binary tree covers [-23/16,23/16]^2 by 120 closed
rectangular leaves, maximum depth 14. Its assignments are:

| Assignment | Count |
| --- | ---: |
| Outside center disk | 15 |
| Expanded physical square A | 14 |
| Expanded physical square B | 10 |
| Center-distance exclusion from D | 28 |
| Center-distance exclusion from C | 24 |
| Slot 1 | 12 |
| Slot 2 | 2 |
| Slot 3 | 3 |
| Slot 4 | 6 |
| Slot 5 | 6 |
| **Total** | **120** |

The five slots are disks of radius 9/20, centered at the following
integer pairs divided by 1000:

```text
(-1130,779), (1223,404), (544,340), (997,825), (-605,425).
```

An outside leaf has minimum squared norm greater than (23/16)^2.
A center-distance leaf has maximum squared distance less than one
from every point in its assigned core center box.

The two physical-square assignments use the known axis-aligned
orientations of A and B. For a leaf rectangle X and its center box K,
let M_i=max{|z_i-c_i|: z in X,c in K}. The exact test is

```text
max(M_x-1/2,0)^2 + max(M_y-1/2,0)^2 < 1/4.
```

It implies every candidate center is within distance strictly less than
1/2 of the actual closed physical square. Its open inscribed disk of
radius 1/2 would then meet that square's interior, which is impossible.
This uses the full known endpoint squares, rather than just their
inscribed disks. Corner tests compute all maxima exactly.

Every additional center therefore belongs to one of the five slot
disks. Each has diameter 9/10<1 and contains at most one further
unit-square center. Total packing capacity is at most 4+5=9,
including both S transmitters over their entire slide intervals.

This proves the radial V_V source exclusion. Section 2 proves both
unique-circle V_V exclusions, and the earlier side-source theorem proves
E_A/E_B. Every source feature in the both-unique-D-endpoint LSLSLD
branch is now covered.

## 6. Verification and the remaining branch

```text
node research/ten/check_strict_vertex_source_closure.mjs
node research/ten/check_strict_vertex_source_closure_60bit.mjs
```

Both arithmetic bodies were executed successfully in the session's V8
runtime, verifying all 216 parameter leaves and all 120 capacity leaves.
The separate backends use 44-bit direct division intervals and
quotient differentiation, and 60-bit reciprocal intervals and Jet
differentiation. Coverage uses prefix/Kraft arithmetic and a full binary
trie respectively. The logical Newton and capacity predicates are shared.
The unavailable execution workspace prevented running the Node entry
points. This is not independent agent review or a Lean check.

The only remaining LSLSLD endpoint-circle class has at least one radial
D endpoint. Neither this theorem nor the earlier E_A/E_B theorem applies
that endpoint normalization to it. No whole-signature or new master
closure is asserted.
