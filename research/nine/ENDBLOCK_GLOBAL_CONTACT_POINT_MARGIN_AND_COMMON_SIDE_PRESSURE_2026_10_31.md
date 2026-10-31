# A universal contact-point margin and a common-side endblock pressure theorem

October 31, 2026. Read base: a965eb1133fb31e1b685da49e619d8fe8f6ef274.

**Status: complete new hand arguments; independent review passed in REVIEW_ENDBLOCK_GLOBAL_CONTACT_MARGIN_AND_COMMON_SIDE_ANNULAR_2026_10_31.md. No original fine or coarse gate is declared closed.** These results apply to the original nine actual unit squares, with every physical unit and original contact retained. They require no Lean, CI, mathematical script, angle mesh, or generated exclusion table.

The first result is entirely geometric. The second applies the first to the actual original cut forces and origin moments, at arbitrary cut degree and arbitrary degrees inside the endblock. Its hypotheses distinguish a whole interface on one actual root side from a general mixed-side interface.

## 1. Every actual contact with a boundary square is in front of the contacted square's center

Let nine closed unit squares with pairwise disjoint open interiors lie in the disk of radius

    2 <= R <= sqrt(1105)/16.

Put

    t = 401/100 - (9/5)R,
    rho = R - sqrt(2),
    delta = 11401/4155200.

Let H be any one of the actual squares, with center c. Let B be an actual square which physically touches the containing circle, and let p be any actual point in H intersect B. It may be a vertex, a relative side-interior point, an endpoint of a common segment, or any original shared-contact mean.

**Theorem 1.**

    c dot p > delta.                                    (1)

There is no force, degree, normal ownership, positive circle weight, origin-containment, or orientation premise.

### 1.1. The three exact geometric inputs

The accepted force-free central-disk theorem in

    NINE_SQUARE_CENTRAL_DISK_AND_SIX_BOUNDARY_NEIGHBORS_EXCLUSION.md,
    Sections 1--2,

proves that every actual square center satisfies

    |c| > t > 0.                                        (2)

Its radius-dependent disk is h=(9/5)R-351/100 and t=1/2-h. It applies to all nine actual squares and includes the closed-disk endpoint. This is the only non-elementary geometric input in the present theorem.

Choose any actual circle corner z of B. Because both z and p lie in the same unit square B,

    |z-p| <= sqrt(2),
    |p| >= |z|-|z-p| >= rho > 0.                        (3)

The unit circumradius of H gives

    |p-c|^2 <= 1/2.                                     (4)

An individual zero circle coefficient does not affect (3); only the physical corner is used.

### 1.2. A single rational completed square, valid over the whole radius window

The identity

    2 c dot p = |c|^2 + |p|^2 - |p-c|^2

and (2)--(4) imply

    2 c dot p > t^2 + rho^2 - 1/2.                     (5)

We now give one exact uniform lower bound for the right side. Since

    sqrt(2) < 99/70,
    (99/70)^2 - 2 = 1/4900,

and R>0,

    t^2 + rho^2 - 1/2
      = (106/25)R^2 - (3609/250 + 2 sqrt(2))R
          + 175801/10000
      > (106/25)R^2 - (30213/1750)R + 175801/10000
      = (106/25)(R - 30213/14840)^2
          + 11401/2077600
      >= 11401/2077600.                                (6)

For a direct arithmetic check of the constant in the square completion,

    30213^2 = 912825369,
    175801 * 5194 = 913110394,
    913110394 - 912825369 = 285025,
    285025/51940000 = 11401/2077600.

Equations (5)--(6) prove (1). The complete original continuous radius interval is covered by this one comparison.

### 1.3. Geometric interpretation and an exact endpoint check

For each actual H, all of its physical contacts with circle-touching squares lie strictly inside the same open half-plane

    {p : c dot p > delta}.

The vector c is nonzero by (2). This statement is about the actual contact points, not the contact normals or the remote circle corners. It does not itself assert c dot n>0 for every contact normal.

The sharp two-stack packing in TWO_STACK_SHARP_EQUALITY_WITNESS.md is consistent with (1). An origin-containing square in that packing has center (31/64,0), whereas the left face is at x=-1/64. No point on that face can be a contact with a physical boundary square: its scalar product with c is negative. The nearby squares on that side are physically circle-clear. The theorem therefore retains the known equality construction and its free sliding positions.

## 2. Every genuine endblock has the original cut force and origin-moment identities

Let U be the vertices on one side of a genuine articulation cut at H. The only positive pair edges from U to its complement meet H. Each such edge e has its original physical application p_e in H and a positive force f_e directed from H into U. For a shared side, p_e remains the original aggregate mean in the actual shared segment.

Summing all original force equations on U gives

    F := sum_e f_e = sum of all original outward circle resultants in U.
                                                                  (7)

Use the source convention consistently; an overall factor two in the circle resultants can be retained without changing any conclusion here.

Summing their origin-moment equations gives

    sum_e det(p_e,f_e) = 0.                              (8)

Every internal pair torque cancels at its actual common application. Every circle force is radial and has zero origin moment. Arbitrary internal chords, branching, true degrees, physical masks, and zero individual corner coefficients are allowed. No root equation is shortened.

The following theorem only uses the actual f_e and (8). It does not replace U by a fictitious leaf or claim that a selected pair of cut forces is itself a physical certificate.

## 3. A whole interface on one actual root side has nonnegative pressure

Assume additionally:

1. O belongs to the actual closed H;
2. every actual U-neighbor of H on this cut is physically circle-touching;
3. every cut application p_e belongs to one fixed actual closed side L of H.

The third condition includes both side endpoints. An endpoint contact normal may be oblique or even tangent to L. No common normal direction, proper-concurrence sign, private degree, load count, or resultant-slope bound is imposed.

**Theorem 2.**

    c_H dot F >= 0.                                    (9)

Moreover equality in (9) is possible only when

    F = 0.                                             (10)

Thus every nonzero cut resultant has strictly positive root-center pressure.

### 3.1. Exact side coordinates and the complete moment identity

Let n be the outward own-side unit normal of L and k=Jn. Write

    L = {a n + y k : Y-1/2 <= y <= Y+1/2},
    c_H = (a-1/2)n + Y k,
    0 <= a <= 1,     -1/2 <= Y <= 1/2.                 (11)

The last bounds follow from O in closed H. Write the unchanged forces as

    f_e = alpha_e n + beta_e k.

The exact normal cone of H on this side gives alpha_e>=0. A force with alpha_e=0 is nonzero and is a positive k force at the upper endpoint, or a negative k force at the lower endpoint. These alternatives include all tangential endpoint normals.

Let

    A = sum_e alpha_e = F dot n >= 0,
    B = sum_e beta_e = F dot k,
    p_e = a n + y_e k.

The full original moment equation (8) is

    a B = sum_e alpha_e y_e.                            (12)

Every cut port is a contact with an actual boundary square, so Theorem 1 gives

    c_H dot p_e > delta.                               (13)

### 3.2. Positive normal component

Suppose A>0. Multiply the desired scalar pressure by the actual signed side height a. Using (12),

    a(c_H dot F)
      = a(a-1/2)A + aYB
      = sum_e alpha_e [a(a-1/2)+Y y_e]
      = sum_e alpha_e(c_H dot p_e)
      > delta A > 0.                                  (14)

Since a>=0, equation (14) first proves a>0, including the exclusion of a=0. Dividing now by that proved positive number yields

    c_H dot F > delta (F dot n)/a > 0.                 (15)

All tangential forces are retained in B and in (12); none was removed to obtain (14).

### 3.3. Zero normal component, positive side height

Suppose A=0 and a>0. Every alpha_e=0, and (12) gives aB=0, hence B=0. Therefore F=0, and (9) is equality. This establishes precisely the allowed zero-resultant exception, rather than assuming it away.

### 3.4. Zero normal component, zero side height

Suppose A=0 and a=0. Every force is tangent to L. The root side contains O, and (13) becomes

    Y y_e > delta > 0.                                (16)

A positive k force occurs only at y_e=Y+1/2>=0, while a negative k force occurs only at y_e=Y-1/2<=0. Thus any positive k force requires Y>0 by (16), and any negative k force requires Y<0. Both signs cannot occur.

There is at least one cut force. Consequently every beta_e has the same strict sign as Y, and

    c_H dot F = Y B > 0.                               (17)

This includes origin-at-vertex and origin-in-side-interior cases without assigning a positive height to the side.

The three alternatives exhaust all genuine cut interfaces and prove (9)--(10).

## 4. Consequences for arbitrary terminal-block interiors

### 4.1. Any negative-pressure endblock must use genuinely different root sides

Suppose an original argument has already established c_H dot F<0 for a genuine endblock and O in H. If every root neighbor in that cut is physically circle-touching, Theorem 2 excludes the entire domain in which all applications lie on one actual root side.

Therefore a surviving negative-pressure interface either has a physically circle-clear neighbor at its original true degree, or its original applications cannot all be placed on one root side. This distinction concerns actual side membership, not the number of independently selected force directions.

For example, the accepted intact-root normal form supplies O in int H, at least two physically circle-touching root neighbors, and strict negative pressure for the other complete cyclic block. Whenever all neighbors of that block at H are physically boundary and their actual ports share a side, the present theorem gives an immediate whole-interface contradiction. It permits arbitrary private stars and chorded block interiors and covers every resultant slope simultaneously.

This does not say that every original marked C5/C6/C7 block satisfies the common-side premise. The remaining mixed-side interfaces and any clear root neighbor must still be treated.

### 4.2. Two genuine endblocks with common-side interfaces

Suppose a physically circle-clear origin-containing articulation H has exactly two positive branches, each satisfying the boundary-neighbor and common-side premises separately. The two sides need not be the same. Its full unchanged force equation gives F_1+F_2=0.

Both scalar pressures are nonnegative by Theorem 2, so both are zero, and then both F_1 and F_2 are zero.

If the original certificate has been chosen support-minimal on this same unchanged packing, this is impossible. Indeed retaining H and just one branch gives a nonzero physical certificate: its cut force is zero, its cut origin moment is zero by (8), and all its private equations are unchanged. The branch has positive total circle weight by the existing no-unloaded-appendage theorem, so the retained certificate can be normalized. It has strictly smaller positive support than the original two-branch certificate, contradicting the stated support-minimality. No new normal or mean is chosen. Without support-minimality, only the exact conclusion F_1=F_2=0 is claimed.

The same argument works with further genuine root branches whose nonnegative pressure and zero-pressure rigidity have separately been proved. A strict-pressure branch, such as an intact petal at its accepted scope, already contradicts the sum without any support-minimality hypothesis.

## 5. A finite witness-pair reduction for the mixed-side remainder

This algebraic reduction is valid for arbitrary true cut degrees and preserves the full original system. It is a witness extraction, not a license to delete forces.

For each actual cut atom put

    tau_e = det(p_e,f_e),
    pi_e = c_H dot f_e.

Partition the cut atoms into P={tau_e>0}, N={tau_e<0}, and Z={tau_e=0}. Equation (8) says

    T := sum_(i in P) tau_i = sum_(j in N)(-tau_j).

If T=0, all moments vanish. If T>0, define the positive weights

    w_ij = tau_i(-tau_j)/T,       i in P, j in N.

A direct finite summation gives the exact pressure decomposition

    c_H dot F
      = sum_(e in Z) pi_e
        + sum_(i in P,j in N)
            w_ij [pi_i/tau_i + pi_j/(-tau_j)].           (18)

For instance sum_j w_ij/tau_i=1, and likewise for every j. Each bracket is the pressure of the algebraic moment-balanced pair

    f_i/tau_i + f_j/(-tau_j),

at the same two original applications. Its origin moment is 1-1=0.

At an origin-containing H, every radial zero-moment contact to a physical boundary neighbor has strictly positive pressure: tau_e=0 means p_e=s_e f_e for a real s_e; root support and O in H imply p_e dot f_e>=0. The contact is nonzero by |p_e|>=R-sqrt2>0 and has positive root support, so s_e>0. Thus

    pi_e = (c_H dot p_e)/s_e > 0                       (19)

by Theorem 1. No nonradial-normal convention is needed for (19).

Consequently, if every cut neighbor is physically boundary and c_H dot F<=0, then T>0 and at least one actual opposite-moment pair has

    pi_i/tau_i + pi_j/(-tau_j) <= 0.                    (20)

If its two applications belong to one actual side of H, Theorem 2 applies to these two positive vectors at the unchanged ports. It forces their algebraic resultant to be zero. If the pressure is strictly negative, at least one pair in (18) has strict negative pressure, and its applications therefore cannot share any actual root side.

This is a genuine finite structural witness statement at arbitrary cut degree. The rescaled pair is never asserted to satisfy the other bodies' force equations. A complete mixed-side exclusion must use the whole original branch in addition to the identified pair.

## 6. Scope matrix and remaining obligations

| Original structural family | Directly usable new implication | Premises still needing proof for full closure |
| --- | --- | --- |
| Intact triangle plus any order-5/6/7 cyclic block at the same root | A strictly negative other-block resultant cannot have a wholly boundary, common-side interface | All possible root sides/clear neighbors; no general common-side theorem is claimed |
| Two arbitrary cyclic endblocks at an origin-containing common articulation | Common-side boundary interfaces both have nonnegative pressure; a support-minimal two-branch star cannot consist of two such interfaces | Origin containment and the actual interfaces; bridge-bearing layouts keep all bridge forces |
| Chorded or branching terminal block at any root degree | The contact margin and exact cut identities remain unchanged; negative pressure has an actual mixed-side witness pair when all neighbors are boundary | The witness pair is not an isolated physical subgraph |
| Any of the nine physical squares, regardless of stress | Every physical boundary contact lies in c_H dot p>delta | This statement alone is not a bound on c_H dot z or c_H dot n |

The universal contact-point theorem and common-side pressure theorem are established above with one rational square completion. They do not by themselves establish the missing interface premises across all ten open two-block parents. No original fine/coarse closure, unrestricted n=9 radius theorem, or equality classification is claimed.

The separate annular review reconstructs the radius-dependent margin, all side-height and tangential-force alternatives, support-minimality scope and mixed-side witness-pair identity. No formal verification is claimed.

