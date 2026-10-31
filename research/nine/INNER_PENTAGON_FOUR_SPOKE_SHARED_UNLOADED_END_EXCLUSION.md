# The unloaded end of the four-spoke pentagon cannot share its hub side

Date: October 28, 2026.

**Status: complete new radius-free hand interface and necessary-domain
reduction, frozen for full independent and root review.** No whole
four-spoke load family or graph-parent flag is changed.

## 1. Original local scope and input

Retain the exact six-body local scope of
INNER_PENTAGON_FOUR_SPOKE_BOTH_END_AXES_EXCLUSION.md, Section 1:

    HA, HB, HC, HD, AB, BC, CD, DE, EA;
    H unloaded with its full positive neighborhood A,B,C,D;
    D unloaded with its full positive neighborhood H,C,E.       (1)

All bodies are actual interior-disjoint unit squares. The degrees,
loads and physical circle masks of A,B,C,E are unrestricted. Keep
the original strict point-normal convention, every shared-side mean
and every positive force; no normal is subsequently selected anew.

**Theorem.** HD cannot be a positive-length shared side.

In each original H4_D0 load representative 124 or 0124, substitute
(A,B,C,D,E)=(0,1,2,3,4). This is a whole interface in both families.
In the three-load family both end units are unloaded, so reflection
also excludes a positive-length shared H0 side. In the four-load
family the exclusion is applied only at its actually unloaded end;
the loaded end is not falsely given a zero-load equation.

We use the complete radius-free both-end-axis theorem at SHA-256
e1106b043b8b6b61899177a7e68121fce49c65e3ebf86273ef332cf451f437bf.
Its Sections 2--3 also supply the strict whole-unit coordinate reach
argument reproduced in the next section. All nine original units
and all physical circle-corner and zero-weight possibilities remain.

## 2. Adjacent physical hub neighbors cannot occupy opposite strict corners

Normalize H=[0,1]^2. If an actual H neighbor T has a strictly
northeast normal, its H application is (1,1), and the minimum-support
span calculation gives T subset {x>0,y>0}. A strictly southwest
neighbor S at (0,0) satisfies S subset {x<1,y<1}. Thus any common
point would belong to int(H), impossible. Reflections give the same
conclusion for the other pair of opposite strict corners.

The span statement used here is exact: at a minimum-n support point
P of a unit, n dot u<0 implies max u dot (x-P)<1. It holds for
vertices and every side mean. A point of another closed unit in
int(H) would force an open-interior overlap.

We also use the degree-free physical triangle implication: when
H owns a normal n to one triangle neighbor, its dot product with
the normal to the other triangle neighbor is nonnegative. This is
UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md, with all axis endpoints
retained.

## 3. A full H4 sign reduction whenever the unloaded end is H-owned

Suppose H owns n_D. Rotate so n_D=North. The both-end-axis theorem
excludes every H-owned n_A; hence n_A strictly exposes an H vertex.
We claim

    n_A,y<0.                                                   (2)

The actual triangle HCD gives n_C,y>=0. If n_A,y>0, the full
unchanged hub force equation

    a_A n_A+a_B n_B+a_C n_C+a_D North=0,
    all a_i>0,                                                (3)

forces n_B,y<0. Reflect horizontally if necessary so n_A is
strictly northeast.

The actual AB contact now forces n_B to be strictly southeast.
Indeed its negative y component leaves only southwest, South or
southeast. The southwest case is excluded by the opposite-corner
argument of Section 2. The South case is H-owned and contradicts
the triangle HAB dot-product implication with n_A,y>0. Therefore
n_B,x>0.

Next n_C,y>=0 and the actual BC contact force n_C,x>0. If n_C,x<0,
it is either strictly northwest, excluded by the opposite-corner
argument with the southeast B, or West, whose H-owned triangle
dot product with n_B is negative. If n_C,x=0, it is North, whose
triangle dot product with n_B is likewise negative. This exhausts
all zero-component endpoints.

The x coordinate of (3) is now strictly positive from A,B,C and
zero from D, a contradiction. The horizontally reflected case
has a strictly negative x coordinate and is identical. Since the
strict H-vertex normal n_A has nonzero y component, this proves (2).

Thus A's actual H application lies at a bottom H vertex, with
y=0. Section 2's support span, applied in the North direction to
the actual A minimum-support point, gives the entire-unit bound

    max_A y<1.                                                (4)

This argument did not use D's frame, either inner body's degree,
any circle equation or any component of the H torque equation.
It retained all four original terms of (3).

## 4. A shared HD side contradicts the actual AE contact

Suppose HD is a positive-length shared side. Its common outward
normal from H is North, and D is aligned with H:

    D=[s,s+1] x [1,2],                                        (5)

with its complete actual side overlap and mean retained. In
particular the normal from D to H is its own South axis.

Apply the physical triangle theorem at the actual unit D in DHC.
It gives n_DC,y<=0. The complete original D3 force equation is

    gamma South+mu n_DC+nu n_DE=0,
    gamma,mu,nu>0.                                            (6)

Its vertical coordinate gives n_DE,y>0. Every actual support of
the aligned D for such a normal has y=2: it is a top-side mean or
one of its two top vertices. Let P be that unchanged DE application.
At E it is a minimum-n_DE support point. Since n_DE dot South<0,
the strict unit-support span gives

    min_E y>P_y-1=1.                                         (7)

Equations (4) and (7) contradict the actual AE physical contact.
The pure North n_DE endpoint is included; its stronger direct
half-plane bound min_E y>=2 is not needed. The top-side mean may
take either endpoint. The C normal may be horizontal, vertical or
strictly oblique. No C2, E2 or surrogate H3 equation has been used.

This proves the entire shared-unloaded-end interface.

## 5. Exact H-owned-end residue, with all means and frames retained

Combining Sections 3--4 with the both-end-axis theorem gives the
following complete necessary statements in the class where H owns
its normal to the actual unloaded end D:

* The other end normal n_A is not H-owned and has strictly negative
  y component in the chart n_D=North. It is supported at one of
  H's two bottom vertices, and the entire A satisfies max_A y<1.
* D is not aligned with H. Its minimum-y support is one fixed actual
  vertex P=(p,1). The H contact is a singleton at an H-side interior,
  so 0<p<1 under the original strict point-normal convention.
* With its actual tilted frame one may write

      D=P+[0,1](a,b)+[0,1](-b,a),
      a,b>0,              a^2+b^2=1.

  No ordering between a and b is imposed. All DC and DE owners,
  all their true applications and means, and the full original D3
  force and torque equations remain.
* The original triangle HCD still gives n_C,y>=0. The complete H4
  equation (3), with its actual HB and HC forces, remains in force.

These statements do not yet exclude that tilted D residue. In the
other original end-owner classes, including an H-owned loaded end
with a non-H-owned unloaded end, the complete original obligations
remain separate. No reflection is used to exchange unequal load
roles without recording the resulting graph labels.

## 6. Literal dependency pins and limits

| Direct input | SHA-256 |
| --- | --- |
| INNER_PENTAGON_FOUR_SPOKE_BOTH_END_AXES_EXCLUSION.md | e1106b043b8b6b61899177a7e68121fce49c65e3ebf86273ef332cf451f437bf |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | ee865704904a8b2a5cab7649bdfd928008c253631abf1eb346d4950411c3afac |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | eb26f19b27dc7327f80a64ccfd1febb542c5915aadcf95227e35765b20d3509a |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | fa877c9d7d25c57a7c8cf438a429465b5952cb8db6628c57d9d93695b33dd434 |

The shared-side theorem and the precise tilted-end necessary domain
are the only new conclusions. This is not a proof of either entire
H4_D0 load family or of its graph parent. There is no change to a
frozen source, metadata, body, normal, mean, force or circle weight;
no numerical pose, late selection, Lean or CI is a premise.
