# Exact geometry of a genuine length-three pendant arm

Date: October 26, 2026.

**Status: accepted complete theorem after full-source root review in REVIEW_LONG_ARM_GEOMETRY_AND_TWO_EDGE_ROOT_2026_10_26.md and separate review in REVIEW_LENGTH_THREE_ARM_GEOMETRY_GLOBAL_2026_10_26.md.** The original cycle-root load is explicitly unrestricted. This
source supplies geometric facts for the remaining long-arm triangle
families; it does not assign a circle-clear or degree-two equation to their
root.

## 1. Original graph and force scope

Keep all nine physical squares in

    79/40<=R<=sqrt(1105)/16,
    d=sqrt(R^2-1/4)-1<61/60, r=R-sqrt(2)<7/10.

Suppose A--U--V--L is an actual pendant path of three positive bridges,
with U,V genuinely unloaded of exact positive degree two, L a genuine
radial S/D leaf, and all four bodies distinct. A may have arbitrary other
positive forces and any original circle load. Its circle mask, zero
weights, actual means and all original normals remain unchanged.

Let e be the actual radial leaf direction. The unchanged transmitter
equations give widths w_U,w_V in {1,sqrt(2)}. The leaf radius is r_L=d
for S and r_L=r for D. Thus the original root application is

    p_A=(r_L-w_V-w_U)e,
    A subset {e dot x<=r_L-w_V-w_U}.                       (1)

These equations do not use any force or torque equation at A.

Every contained unit center satisfies the exact bound

    |c|<=d+1/2<91/60.                                    (2)

This follows from the farthest-corner inequality
R^2>=|c|^2+|c|+1/2.

## 2. Only an S leaf and two side widths survive

The supporting half-width of A in direction e is at least 1/2. If either
transmitter width were sqrt(2), (1) would give

    c_A dot e <= d-(1+sqrt(2))-1/2
               < 61/60-3/2-7/5 = -113/60,

contradicting (2). Hence both original widths are one. If L were D,

    c_A dot e <= r-2-1/2 < 7/10-5/2 = -9/5 < -91/60,

again impossible. Thus L is S and the complete original applications are

    p_A=(d-2)e,  p_UV=(d-1)e,  p_VL=d e.                 (3)

Both U,V are side-aligned to e, with projected intervals

    U: [d-2,d-1],        V: [d-1,d].                      (4)

Each original transverse interval has length one and contains zero,
because its unchanged radial applications do. Every slider and endpoint
mean is retained.

## 3. The critical and lower radii are excluded by a full physical P

Equations (2)--(3) give

    -(d+1/2) <= c_A dot e <= d-5/2.

Therefore d>=1. At d=1 all inequalities are equalities. The original
center is c_A=-3e/2 and A's supporting half-width in direction e is
exactly 1/2. Thus its frame is side-aligned to e and its actual square is
the physical radial S(-e), whether or not its circle weights make it a
positive leaf in the graph.

The four actual bodies A,U,V,L then are precisely a physical P skeleton:
the two radial terminals S(-e),S(e), and the two side-aligned inner units
on longitudinal intervals [-1,0] and [0,1]. Their independent transverse
intervals still contain zero, including every endpoint slider. The complete
physical capacity theorem `P_ALL_COMPLETION.md` excludes all five other
original squares from completing this skeleton to nine at R^2=17/4.
It makes no graph-degree assumption on A.

Consequently every remaining genuine length-three arm has

    d>1,   R^2>17/4.                                     (5)

## 4. The full original root is side-aligned with an exact small slider

Put rho=2-d>0. By (3), A lies in e dot x<=-rho and contains p_A=-rho e.
Hence p_A is its unique nearest point to zero.

That nearest point cannot be a vertex, including an endpoint of a
side-axis support. If it were, write A=p_A+[0,1]u+[0,1]v with inward
orthonormal axes satisfying u dot e<=0 and v dot e<=0. Put
a=-u dot e, b=-v dot e. Then a,b>=0, a^2+b^2=1, a+b>=1, and

    |c_A|^2=rho^2+rho(a+b)+1/2
             >=rho^2+rho+1/2.

The excess of this lower bound over the square of (2) is exactly

    rho^2+rho+1/2-(d+1/2)^2 = 25/4-6d > 3/20.             (6)

This contradicts (2). Thus p_A is in a relative side interior and A is
side-aligned to e.

In the actual orthonormal frame (e,Je), write its full square as

    A=[d-3,d-2] times [t-1/2,t+1/2].                     (7)

Since 1<d<61/60, the left face has larger absolute first coordinate than
the right face. Its farthest corner has squared norm
(d-3)^2+(1/2+|t|)^2. With R^2=(d+1)^2+1/4, containment is exactly

    |t|<=h(d):=sqrt(8d-31/4)-1/2,
    0<h(d)<1/8.                                          (8)

For the last bound, 8d-31/4<23/60<25/64. This retains every admissible
original root slider and does not infer that A is loaded.

The physical boundary mask is also exact. If |t|<h(d), A is physically
circle-clear. If |t|=h(d), it has exactly one physical circle corner,

    z=(d-3, sign(t) sqrt(8d-31/4)).                       (9)

Indeed h(d)>0, so the opposite left corner has strictly smaller radius,
as do both right corners. If A has positive circle weight, its resultant
is the original positive multiple of this z. That force is retained; it
is not absorbed into the pendant leaf's radial ray or omitted from the
triangle equation.

## 5. Two touching roots cannot each have such a length-three arm

Suppose two physically touching distinct roots A_1,A_2 have two such
pendant paths with disjoint body sets. Their respective first internal
units U_1,U_2 have the side-aligned intervals in (4). Since d>1,

    d-2<0<d-1.

Each U_i therefore contains zero strictly between its two longitudinal
faces. At zero it is either interior or relative side interior; it cannot
be a vertex. Because U_1,U_2 are distinct physical units, neither can
contain zero in its open interior. Their two tangent half-planes must be
opposite, so their longitudinal side axes are parallel. Consequently the
actual leaf directions satisfy e_2=e_1 or e_2=-e_1.

Equal directions repeat the same physical radial S leaf, impossible. In
opposite directions, (3) puts the roots beyond opposing supports:

    A_1 subset {e_1 dot x<=-(2-d)},
    A_2 subset {e_1 dot x>= +(2-d)}.

Their supporting half-planes are strictly separated; in particular the
roots cannot physically touch. For a quantitative reserve, the intervening
gap is 2(2-d)>59/30>sqrt(2). This contradicts the assumed root contact.

Thus at most one vertex of a positive triangle can carry a length-three
pendant path. The conclusion also holds for any pair of mutually touching
roots satisfying the displayed original path hypotheses.

## 6. Exact use and limits

The complete sole-triangle forest reductions already prove that every
outside nonleaf is genuinely unloaded and that the surviving branches are
simple paths. Hence this source applies directly to every remaining
length-three triangle arm, without discarding a root circle force.

Its conclusions are: d>1; the actual leaf is S; both original transmitter
widths are one; the root is exactly the aligned chart (7)--(8); any
physical boundary root has the unique actual corner (9); and at most one
triangle root has a long arm. The other triangle roots and their positive
branches still require their full equations. No entire length-three
multi-root family, larger coarse cell, sharp lower bound or equality
classification is asserted here.

No numerical pose sampling, Lean compilation, CI or remote action is used.
