# Independent review of the force-free boundary side-channel theorem

Date: October 28, 2026 UTC. Reviewer: pentagon continuation.

**Verdict: PASS, without source repair.** This is a complete independent review of the exact current manuscript identified below, including its whole continuous geometric theorem, the original width-one channel join, and its expressly limited consequences. It does not approve any exterior-pocket capacity, occupied-transmitter proximity, or original graph/load closure.

## 1. Exact target and review boundary

Target:

    FORCE_FREE_BOUNDARY_SIDE_CHANNEL_CENTER_HEIGHT_AND_PORT_MARGIN.md

SHA256:

    1a40004509d14eaa228ab52a4eb3280ed0f96df60e3891666f380124b5cacf9c

The reviewed target has 16,323 bytes. I read the entire target and every complete direct source listed in Section 10 below. I independently rederived the endpoint estimates, the nonpositive-center contradiction, the port-margin argument, and the literal graph join, and checked every displayed rational reserve by exact fraction arithmetic.

I did not contribute to the discovery of the new force-free endpoint estimates or the strict endpoint-center theorem. The surrounding discussion of the remaining D02 channel obligation supplies context only. This review does not transfer an earlier review of the old simple-cycle port theorem or the old proximity theorem onto the new bytes.

The new theorem concerns unchanged actual units X,H,Y in the same disk, with X,Y physically boundary, and the actual support configuration

    H=[-a,b] times [v,v+1], a+b=1,
    P_X=(-a,h), P_Y=(b,h), v<=h<=v+1,
    X subset {x<=-a}, Y subset {x>=b},
    2<=R<=sqrt(1105/256).

There is no assumption about endpoint degrees, forces, concurrence, positive individual corner weights, or the position of any completion unit. The proof uses actual support points throughout, including original shared-side weighted means at either endpoint.

## 2. Both universal endpoint estimates are complete

The lower estimate

    R^2 >= (a+1)^2+h^2

for a,h>0 follows from containment alone. In the side-axis case, P-(1,0) is an actual point of the unit for every original support mean. The proof does not silently require a vertex or midpoint.

In the nonaligned exposed-vertex case, the actual inward axes can be written

    u=(-c,s), w=(-s,-c), c,s>0, c^2+s^2=1.

I re-expanded both vertex deficits (5) and (6). The threshold h=as/(1+c) is retained in the first branch. Below that threshold, the split according to D=c-s exhausts the remaining orientations. The exact identity used in the positive-D branch is

    (c+s-1)-s(c-s)/(1+c)=s/(1+c).

Its numerator follows from c^2+s^2=1, so the strict lower deficit in (7) is valid for every exposed-vertex frame. The separate axis argument covers the missing c=0 or s=0 frame endpoints.

For the upper estimate

    R^2 <= (a+1)^2+(h+1)^2,

the extra premise h>=a is used exactly where required, in the coefficient a-h of the opposite-corner comparison. The axis support gives the whole actual coordinate box even when the original application lies at either end of its side. In the exposed-vertex case, all four actual corner norms are bounded. Physical boundary supplies an actual corner attaining R; the proof never identifies a positively weighted corner with the entire physical mask. Consequently physical two-corner ties and zero individual corner weights are all retained.

Reflection supplies the corresponding estimates for the right endpoint without changing the actual origin or either application.

## 3. The port line and horizontal signs are established without circularity

The contained-unit center bound is proved from the actual farthest own-frame corner:

    max_vertex |z|^2
      =|c|^2+1/2+|c.e_1|+|c.e_2|
      >=|c|^2+|c|+1/2.

The exact reserve at M=91/60 is 31/57600. Hence all actual centers have norm strictly less than M. True horizontal halfwidths are at least 1/2, so the actual support identities give

    -1/60<a,b<61/60,

before their signs are known. The endpoint-center separation is at least two, which then gives the strict horizontal signs

    (c_X)_x<-29/60, (c_Y)_x>29/60.

These deductions do not use h>0 or the theorem's later center-height conclusion.

When h=0, the smaller of a,b lies in (-1/60,1/2], so the norm of an actual endpoint application is at most 1/2. Its actual boundary unit has diameter sqrt(2), giving R<2. This correctly excludes h=0 even if that smaller coordinate is negative. A reflection of the whole unchanged configuration can therefore arrange h>0.

For a<=0, the right coordinate b>=1 makes the reflected lower endpoint estimate applicable. It gives h^2<=81/256. Together with -1/60<a<=0, the actual left application has squared norm strictly below 1/3600+81/256. The subsequent strict diameter contradiction has reserve 803/57600 at 23/40, and the chosen bound sqrt(2)<57/40 has reserve 49/1600. The reflected proof excludes b<=0.

Only after these sign conclusions does the proof use the smaller positive coordinate, at most 1/2, to show h>3/10. Here

    23/4-4(283/200)=9/100

is an exact equality, and strictness comes from sqrt(2)<283/200, whose squared reserve is 89/40000. There is no unjustified positive rational remainder at this step.

## 4. The whole nonpositive-center domain is covered

For an exposed-vertex support with (c_X)_y<=0, the actual axes imply

    D=c-s>=2h>0, D<=1,
    C=c+s=sqrt(2-D^2).

The three comparisons in (16) are correct. In particular, the first lower bound is exactly

    s^2+cs+2as,

which is positive in the open nonaxis frame. The other two comparisons are also strict. The target deliberately retains the weak comparison where it discusses the aligned limit; it does not derive an unsupported unique-mask assertion at that endpoint.

Thus physical boundary contact gives the actual largest-corner identity

    R^2=a^2+h^2+2+2a sqrt(2-D^2)-2hD.

For fixed a,h>0, its derivative in D is strictly negative throughout the closed admissible interval [2h,1]. The denominator sqrt(2-D^2) stays positive there, including D=1. Substitution of the actual lower endpoint D=2h proves the first inequality in (15).

The separate axis treatment is necessary and correct. With the actual aligned square

    X=[-a-1,-a] times [v_X,v_X+1],

the unchanged support mean and nonpositive center give

    h-1<=v_X<=-1/2, 0<h<=1/2.

Its farthest vertical magnitude is -v_X, including the physical tie v_X=-1/2. The upper comparison to (a+1)^2+(1-h)^2 is valid for every mean. This expression is the same continuous formula at D=1, so the monotonic comparison down to D=2h remains valid. In particular, h=1/2 and center-height zero are included.

The final strict inequality in (15),

    R^2 < (a+sqrt(2))^2,

follows from h>0 and a>0. The proof has therefore obtained one uniform bound on the complete nonpositive-center domain, with no omitted aligned case, application endpoint, physical mask, or corner-weight endpoint.

## 5. The continuous contradiction from that bound is valid

The strict radius bound yields

    b<1+sqrt(2)-R<=sqrt(2)-1<5/12.

If h<=b, the actual right application and its unit diameter imply

    R<2+2sqrt(2)-sqrt(2)R,

which contradicts R>=2. This is a direct exact rearrangement, and no endpoint-center properness is used. Thus h>b, so the reflected upper endpoint estimate is now licensed.

Combining that estimate with h<=1/2 gives b>3/10 and hence a<7/10. Combining it with b<5/12 gives h>2/5. The exact radical and square reserves are positive as printed.

Substitution into the uniform nonpositive-center bound gives

    R^2<49/100-12/25+2+42/25
        =369/100<4.

The cross term is controlled by sqrt(2-4h^2)<sqrt(34)/5<6/5. Every comparison is continuous over the original domains. The contradiction is strict even when the assumed endpoint center has height zero or the support is at an aligned mean endpoint.

Horizontal reflection proves the other endpoint-center conclusion. The resulting statement is precisely that both actual centers have positive height relative to the line through O parallel to the port line. It does not claim that either center or either far physical corner has height at least h.

## 6. The port-margin strengthening is valid at the full new scope

The Section 6 proof retains the old exact port-margin algebra, but its entry is now completely force-free.

For 0<a<=7/100, the actual application diameter immediately excludes h<=a. Hence the upper estimate at X and lower estimate at Y can both be used:

    (2-a)^2+h^2 <=R^2<=(a+1)^2+(h+1)^2.

Expansion gives h>=1-3a, with the latter positive on the entire interval. The decreasing quadratic then yields

    R^2>=5-10a+10a^2
        >=4349/1000>1105/256,

with exact final reserve 1043/32000. Reflection yields the same strict lower bound for b.

Every actual H vertex has first coordinate -a or b. Its norm is therefore greater than 7/100 independently of the original transverse slider v and independently of the position of either original actual mean. No completion placement or capacity argument has entered.

## 7. Exact arithmetic record

These calculations verify the displayed rational comparisons; they are not numerical pose tests or a finite geometric exclusion certificate.

| Comparison | Exact value |
| --- | ---: |
| (91/60)^2+91/60+1/2-1105/256 | 31/57600 |
| (23/40)^2-1/3600-81/256 | 803/57600 |
| (57/40)^2-2 | 49/1600 |
| (283/200)^2-2 | 89/40000 |
| 23/4-4(283/200)-9/100 | 0; strictness supplied by the preceding radical bound |
| (17/12)^2-2 | 1/144 |
| 7-(13/5)^2 | 6/25 |
| 287/144-49/25 | 119/3600 |
| 36-34 | 2 |
| 4-369/100 | 31/100 |
| 2-(3/2)(107/100) | 79/200 |
| 5-10(7/100)+10(7/100)^2 | 4349/1000 |
| 4349/1000-1105/256 | 1043/32000 |

The two vertex-deficit expansions, the identity in (7), the opposite-corner comparisons, both monotonicity derivatives, and the quadratic expansion in (24) were also independently checked algebraically.

## 8. The original channel and D02.L0134 joins are literal

At a genuine unloaded degree-two transmitter H, its complete original positive force equation makes the two pair forces equal and opposite. In the width-one alternative, those directions are the opposite actual side axes of H. Its original torque then makes the two unchanged application means share one transverse coordinate. This gives exactly the displayed geometric chart after one common rigid change of coordinates. The contact support half-planes are actual pair supports, so the endpoint containment conditions in the geometric theorem follow without a normal reselection.

Neither endpoint's force equation is used in the new theorem. Consequently an endpoint can retain its true degree three, other positive spokes, physical corner mask and complete original means.

For the original D02.L0134 graph, I checked the positive rim

    01,12,23,34,45,50

and the original positive chord 02 against the complete graph/load cover. With loaded vertices 0,1,3,4, the actual channel is

    W=0 -- H=5 -- B=4.

Here H=5 is unloaded degree two, W=0 is loaded degree three, and B=4 is loaded degree two with its boundary neighbor 3. The theorem applies to the actual width-one alternative without replacing W by a two-force tip, deleting chord 02, or discarding any original endpoint force.

The diagonal-width alternative remains outside this theorem. No original fine or coarse flag is changed by this local join.

## 9. The distinction from occupied-cap proximity is essential and correctly preserved

I read the complete older occupied-cap proximity source, including its actual opposite-corner escape comparison. That comparison uses the endpoint's genuine proper concurrence to force its relevant far corner to lie on the outward side of the port line. This information is not supplied by a positive center height alone and is not automatically available at the true degree-three endpoint W.

The new source explicitly does not infer any of the following:

- every physical boundary corner has height at least h;
- proper radial concurrence at W;
- the entire closing pocket lies in y>=h;
- an occupied pocket forces dist(O,H)<1/60;
- a pocket-capacity bound or an original graph/load exclusion.

Those limitations are correct. The new force-free theorem removes the center-height and port-margin entry gap, but it does not remove the separate actual routing and proximity obligation. This review gives no credit for an implication beyond the stated theorem.

## 10. Complete direct-source audit

All four complete sources were read, and their current exact hashes match the target's table.

| Source | Current SHA256 | Audited role |
| --- | --- | --- |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Actual applications, full original force/torque conventions, degree-two width-one channel entry |
| SIDE_CHANNEL_PORT_MARGIN_AND_NEAR_ORIGIN_THREE_UNIT_EXCLUSION.md | 0fa62f59c2b228d235a3e1539f9bbf8c3e53f7f128052064b8157819dcf06b4c | Earlier margin argument, now reprinted after a broader geometric entry; no unproved transfer of its stronger near-origin conclusion |
| FOUR_C6_SIDE_OCCUPIED_CAP_TRANSMITTER_PROXIMITY.md | d227307250320a41e00e54e8aaa2c2475c2a3180a89bb23d52f4e6e1746a74ad | Full scope audit only; its properness-dependent stronger conclusion is not invoked |
| SIX_BODY_OUTER_HEXAGON_GRAPH_LOAD_COVER.md | cd5fa69e4257898360f0d740d26369bdab51828c49d61d831e6ecb6646fafcc1 | Original D02.L0134 graph, loaded set and actual degrees |

The new geometric proof is self-contained beyond these physical conventions and the literal graph join. No Lean compilation, CI, numerical scan, force deletion, selected-normal change, new physical contact, remote write, or shared-ledger mutation was used in this review.

**Final disposition:** accept the exact 1a400045 manuscript as a complete force-free width-one boundary-channel center-height and port-margin theorem, with all stated endpoints and masks retained and with its explicit capacity/proximity limitations unchanged.

