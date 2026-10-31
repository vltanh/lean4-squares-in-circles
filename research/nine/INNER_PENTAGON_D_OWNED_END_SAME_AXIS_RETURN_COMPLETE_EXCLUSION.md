# The same-axis return is impossible at a D-owned unloaded pentagon end

Date: October 28, 2026 UTC. Author: pentagon_uniform continuation.

**Status: new complete proposed original-feature theorem, frozen for full
independent and root review.** This excludes the entire D-owned HD,
same-D-axis DC interface whenever A,B,C,E are physically boundary.
It holds throughout the full original radius window and preserves every
CD and DE side mean. Neither C nor E is assumed to own its D contact.
No whole original fine or coarse family is declared closed.

## 1. Original graph, loads, actual geometry and precise feature

Retain the original no-chord H4_D0 component with all nine actual units,
the full positive graph

    HA, HB, HC, HD, AB, BC, CD, DE, EA,

and the unchanged actual circle origin. Its original radius range is

    79/40<=R<=sqrt(1105)/16.                              (1)

H is unloaded with true positive degree four, D is unloaded with true
degree three, and C and E are loaded with true degrees three and two.
A and B retain all their original positive forces and circle equations.
Assume A,B,C,E physically touch the circle. This is automatic in
H4_D0.L0124, and is exactly the physical-boundary mask of zero-load A
in H4_D0.L124. No positive circle weight is assigned to A in that latter
family. All physical zero-weight contacts, individual zero corner
coefficients, and the three completion units remain.

The actual H lies inside the occupied physical rim A-B-C-D-E-A.
Assume D owns the original D-to-H side-axis normal and that D-to-C
uses that **same** actual D axis. The full shared-HD exclusion removes
every positive-length HD contact. Under the retained strict singleton
normal convention, HD therefore has an actual relative D-side-interior
point and the genuinely nonparallel H has a unique vertex there.

Normalize the unchanged D chart by a rigid motion to

    D=[0,1]^2,
    D->H=(-gamma,0), D->C=(-mu,0), gamma,mu>0,
    P_H=(0,t), 0<t<1,
    P_C=(0,s), 0<=s<=1.                                 (2)

Vectors in (2) include their original positive force magnitudes. The
whole actual H and C lie in x<=0 and have maximum x coordinate zero.
P_C is the original actual application, including its full possible
shared-side interval and either endpoint. No strict CD ownership or
singleton condition is inferred.

## 2. The original two left applications are distinct

We first prove s!=t without changing either mean. If s=t, then the
actual point P=P_H belongs to D,H,C. At P, the D interior tangent
sector is the right half-plane, of angle pi, because 0<t<1. The
H tangent sector is a right angle strictly inside the left half-plane:
P is its unique maximum-x vertex and both actual inward axes have
strictly negative x components.

The actual C tangent sector has angle at least pi/2 and lies in the
left half-plane because C lies in x<=0. To avoid open-interior overlap
with H and D, it would have to fit into one of the two angular gaps
between H's strict interior sector and the boundary of that left
half-plane. Each gap has angle strictly less than pi/2: H's sector
has angle pi/2, and it is separated strictly from both half-plane
boundary rays. No unit tangent sector of angle at least pi/2 fits
into either gap. This contradiction excludes s=t.

This tangent-sector argument permits P to be a C vertex, side point,
or endpoint of the original common segment. It uses the actual common
point implied by equality of the two unchanged applications.

Reflect the entire actual configuration vertically if necessary. This
does not change graph labels, load roles, or the same-West normals, and
allows us henceforth to write

    t<s.                                                  (3)

The reflected force and circle data are all transformed together. The
other inequality s<t is thus included in the complete theorem.

## 3. The entire D3 force and torque equations

Full original D force balance makes its E vector exactly

    D->E=(gamma+mu,0).

Its actual D application is therefore on the full right side,

    P_E=(1,u), 0<=u<=1,
    E subset {x>=1}.                                     (4)

The original torque about the local lower-left D corner gives

    gamma*t+mu*s-(gamma+mu)*u=0.

Consequently

    u=(gamma*t+mu*s)/(gamma+mu),
    t<u<s.                                                (5)

The strict middle placement follows from the two original positive
magnitudes and (3). It is a consequence of the complete D3 equation,
not an assigned midpoint. Both the original CD mean and original DE
mean remain exactly their given values in (2), (4), (5). The whole
external units retain arbitrary orientations and circle masks.

Let N be the unchanged original unit normal from H into C. At its
actual application, the real supporting half-planes give

    N.P_H<=N.S<=N.P_C,
    (s-t)*N_y>=0.

Thus N_y>=0. In fact it is strict. If N_y=0, a horizontal normal
would vertically separate H and C. Both have maximum x coordinate
zero and positive horizontal width. An East H-to-C normal would force
the minimum x coordinate of C to be zero; a West normal would force
the minimum x coordinate of H to be zero. Either conclusion contradicts
that unit's positive width and maximum x coordinate zero. Hence

    N_y>0.                                                (6)

This uses only their actual whole supports. It permits a full shared
HC contact and every original HC application mean.

## 4. Restore the original circle origin and every coordinate bound

Let the unchanged circle origin have local D coordinates (xi,zeta).
Translate the coordinate chart back to that origin, keeping the same
horizontal and vertical directions. Define

    X_C=xi, X_E=1-xi,
    h_C=s-zeta, h_E=u-zeta.

The exact original points and whole supports are now

    P_C=(-X_C,h_C), C subset {x<=-X_C},
    P_E=(X_E,h_E),  E subset {x>=X_E},
    X_C+X_E=1,
    h_C-h_E=s-u>0.                                      (7)

No sign of a height is inferred from the local D chart. Their signs
will be proved from the original-circle torque equation in Section 6.

For completeness put d=sqrt(R^2-1/4)-1. The farthest-corner center
bound and the unit halfwidth bound give every actual minimum support
height at most d. Apply them to C in the West direction and to E in
the East direction. They give X_C<=d and X_E<=d, so (7) implies

    X_C,X_E>=1-d>-1/60>-1/2.                             (8)

Here d<61/60 throughout (1), by squaring the positive quantities
sqrt(R^2-1/4)<=sqrt(1041)/16<121/60. The support bound does not assume
that East or West is an own side axis of C or E. Both may have tilted
vertex supports or arbitrary aligned side means.

## 5. The actual occupied rim fixes the boundary order and moments

At the real D center, the two rays to P_C and P_H point left. By
t<s, their actual angular order is the ray to C followed by the ray
to H when turning counterclockwise through that left half-plane.
The ray to P_E points right. Thus the original H spoke lies in the
counterclockwise sector from the C rim ray to the E rim ray. All
three applications are distinct, so this local sector order is strict.

The occupied-hub theorem places H in the bounded side of the actual
rim. Therefore its counterclockwise exterior-rim orientation is

    D -> C -> B -> A -> E -> D.                           (9)

This is the actual physical sector order, including a possible reflex
rim angle at D. It does not assume convexity of the center polygon.
The compatible weak-junction resolutions elsewhere preserve (9).

The simultaneous real circle accesses in the occupied-rim theorem
carry (9) to the counterclockwise physical boundary order C,B,A,E.
The actual center directions have that same order. Explicitly, every
physical circle corner is within pi/12 of its own center direction,
while distinct physical boundary centers are separated by more than
pi/5. Those disjoint angular intervals prevent a reversal when passing
from the protected corner accesses to their center directions.

The physical angular-neighbor theorem makes C->B, B->A and A->E their
counterclockwise minor center traversals: the reverse minor arc would
contain the other two boundary centers. These three original contacts
therefore form the exact increasing center lift required for the short
boundary-path theorem, with total advance less than 2*pi and each
successive advance less than pi.

The complete arbitrary-degree boundary-contact moment theorem gives,
for the actual original applications and directed unit normals,

    det(P_CB,g_CB)>0,
    det(P_EA,g_EA)<0.                                    (10)

The second direction is E toward A, opposite to the last traversal
A->E in (9). All determinants in (10) use the unchanged circle
origin. Full original side means and every physical boundary mask
are covered; A's physical boundary status suffices even if its total
circle coefficient is zero.

## 6. The genuine E2 proves its height and full circle-resultant sign

The true E2 force equation retains its original force -mu_DE East
toward D, its original positive force mu_EA g_EA toward A, and its
full nonnegative circle resultant F_E. Every actual circle atom has
zero origin moment. Its unchanged torque equation consequently gives

    det(P_E,East)
      =(mu_EA/mu_DE)*det(P_EA,g_EA)<0.

Since det(P_E,East)=-h_E, this proves

    h_E>0, h_C>h_E>0.                                   (11)

The second inequality is the already proved actual height difference
in (7). Both signs are now established about the original origin.

The complete genuine two-force properness theorem applies to E,
because its actual neighbor A physically touches the circle. It gives
the actual concurrence q_E=t_E F_E, t_E>0, and

    q_E=P_E+ell*East, ell>=0.

No claim that q_E lies inside E is used. Its y coordinate is h_E,
so the full actual circle resultant satisfies

    (F_E)_y=h_E/t_E>0.                                  (12)

This uses only E's true degree two. No two-force equation is assigned
to C, A, or H, and no physical two-corner mask or zero individual
weight is removed.

## 7. The complete C3 obtains its sign without side ownership

Keep all three original C pair forces. Its exact full equation is

    F_C-mu_CD*(-East)-mu_CH*N+mu_CB*g_CB=0.                (13)

Its two incoming directions have y components zero and the strictly
positive N_y in (6). Its only outgoing direction in (13) is the actual
C-to-B direction, whose original moment is strictly positive by (10).

C has its actual maximum-x support point (-X_C,h_C), with X_C>-1/2
and h_C>0 by (8), (11). R>sqrt(2) holds in the full original window.
Apply the arbitrary-degree full-star consequence of
`BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md` to the
entire original equation (13). It yields

    (F_C)_y>0.                                          (14)

In detail, if (F_C)_y<=0, that source's reflected force-free theorem
would give (g_CB)_y<=0 from the actual positive moment in (10).
The exact y projection of (13) would then be

    (F_C)_y=mu_CH*N_y-mu_CB*(g_CB)_y>0,

a contradiction. This sign uses the true C3 and original HC force;
it does not require CD to be a C side axis or give C a concurrence.

## 8. The full-radius short-path contradiction and complete owner cover

Apply `SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md`
to the actual counterclockwise boundary path C-B-A-E. Its two original
opposite parallel support points and full actual half-planes are (7).
Their horizontal coordinates satisfy (8) and have exact sum one. Both
heights are positive by (11), both full endpoint resultants have
positive y components by (12), (14), and the actual center lift was
proved in Section 5. The four path units are physically boundary.

Every hypothesis of that theorem has therefore been established on
the full original domain (1). It forces X_C+X_E>1, contradicting (7).
This excludes the entire same-D-axis DC feature under a D-owned HD,
including all aligned or tilted C/E frames, all original CD/DE means,
their closed endpoints, every HC owner and mean, and all circle masks.

For H4_D0.L0124 this is the complete displayed contact-feature exit.
For H4_D0.L124 it is the same complete exit whenever zero-load A is
physically boundary. It supplies no conclusion on the separate
physical-clear A mask by itself.

There is a useful exact assembly with the preceding frozen H4 sources.
Their entire H-owned-HD strict-northeast and East-HC proofs also use
only the physical boundary status of A, not a positive A circle weight
or a two-force law at A. Their uses of A are its boundary-contact
moment signs, its position on the physical boundary path, and its
boundary status in the genuine E2 properness theorem. Therefore their
complete H-owned-HD union applies unchanged to L124's physical-boundary
A mask as well as to L0124. Every original zero A coefficient remains.

The already complete D-owned-HD nonaxis-DC theorem explicitly has the
same physical-boundary-A extension. Joining that nonaxis exit with the
present same-axis exit, the D-owned-HD residual among these four-boundary
configurations has only the perpendicular D-axis DC cases. The opposite
axis East is excluded by the degree-free owned-axis D-H-C triangle
lemma, since D-to-H is West. Thus, after reflecting vertically as needed,
the sole remaining D-owned normal pattern is

    D->H=West, D->C=North.

The original perpendicular contact means and endpoint cases remain
untouched. Free HD also remains outside these owner exits. For L124,
its physical-clear A mask retains its separate full obligations. This
assembly is not a complete original-family exclusion and gives no
whole fine or coarse gate credit.

## 9. Exact operative inputs and preservation

| Source | Current SHA-256 | Exact use |
| --- | --- | --- |
| BOUNDARY_SUPPORT_POINT_HALF_PLANE_MOMENT_MONOTONICITY.md | c1694bb4265871e2f2c499e16a2e7ac01173b436966558a90e245e79856fbe9b | Full arbitrary-frame force-free moment theorem and full-star strict sign |
| SHORT_BOUNDARY_PATH_ARBITRARY_FRAMES_FULL_RADIUS_OPPOSITE_SUPPORT_EXCLUSION.md | 34c9a02388146c9e085f66831eb3be49bd577cf1ec47ff7948f7306c0f4c24f1 | Complete full-radius arbitrary-frame opposite-support path theorem |
| INNER_PENTAGON_FOUR_SPOKE_SHARED_UNLOADED_END_EXCLUSION.md | ab1882057cc4d5bc0be2929c0c926543a92fbbbc4f8f74598c2238707d17f9f6 | Complete positive-length HD exclusion |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Original strict singleton convention and compatible physical routing |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Complete original normal, application and torque conventions |
| INNER_PENTAGON_OCCUPIED_HUB_AND_EXTERIOR_POCKET_LOCALIZATION.md | 37fad266560ea5e2bca29723f4db00617c35a67be2e82b70fbf743b75006a502 | Actual occupied rim, strict H interior, simultaneous physical circle accesses |
| CIRCLE_CONTACT_ANGULAR_ORDER.md | e54df61d3134c5709bee5ac1a250fdd51084828da114d896f14c7e6337c4e8c5 | Physical boundary center gaps and minor contact order |
| FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md | 164d08bb2c4dfe8510247e44298d309920cb88a780221252d833f51aa654225f | Only Section 1 physical corner/center direction intervals |
| BOUNDARY_CONTACT_ORIGIN_MOMENT_ORIENTATION.md | 851417d7fcd12ccb93a6f7f09ba7d7b2bf9bccc61c82fee3457b5ee4cee47e9a | Actual CB and EA moment signs, arbitrary degrees and original means |
| TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md | 29e38d3f641fe16c6db587e51245f92ad4c447f9536db7d14c221f56b5357e82 | Complete proper two-force Lemma 2.1 for true E2 with actual boundary neighbor A |
| SIX_BODY_INNER_PENTAGON_LOAD_COVER.md | cfe85a201b09182200d5270f0dcdc0e590bf99eded19aaf6d56f86830e959c0a | Literal original graph, load orbits, true degrees and interior H |
| UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md | b4c0a2895debb403a52603e4243351dbb9a98f04bc2d051c54c33ce6cacf9207 | Only the complete owned-axis triangle implication for the final opposite-axis residual |
| INNER_PENTAGON_FOUR_BOUNDARY_H_OWNED_END_STRICT_NORTHEAST_EXCLUSION.md | d35d1d95347becdf45f4381db0f2d7cd16ff8dac92a525ff1979bb3c76e4759f | Existing complete H-owned strict-northeast interface and its literal physical-boundary-A extension |
| INNER_PENTAGON_H_OWNED_END_EAST_RETURN_TANGENT_AND_COMPLETE_FOUR_LOAD_EXCLUSION.md | 413a3ba7229f4685dff19253337d86bc89c0d30b18d8cda7a9f0bcc51f720c6a | Existing complete H-owned union and its literal physical-boundary-A extension |
| INNER_PENTAGON_D_OWNED_END_NONAXIS_C_RETURN_EXCLUSION.md | 74013228a4c4d762938fa5f7fe72c1c9d447508bbfae14b11c7f9902220bffd0 | Existing complete D-owned nonaxis interface, with the same physical-boundary-A scope |

All three original higher-degree H4, C3 and D3 systems remain intact.
The only proper two-force application is to genuine E2. No application,
normal, physical square, circle corner or coefficient is replaced.
No historical source is edited or silently repinned; existing terminal-LF
reconciliations retain their exact current recovery scope.

No pose sample, numerical exclusion, force deletion, selected mean,
Lean compilation, CI, workflow, shared metadata change, commit or
publication is used. This full new caller and its explicit owner/mask
assembly require their own complete independent and root reviews.
