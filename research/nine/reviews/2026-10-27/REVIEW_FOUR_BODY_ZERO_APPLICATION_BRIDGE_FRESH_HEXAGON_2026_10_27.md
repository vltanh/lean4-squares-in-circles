# Full independent review: zero-application bridge at a four-body block

Date: October 27, 2026.  
Reviewer: hexagon.  
Verdict: **ACCEPTED in full, with no correction.**

The unchanged target is `FOUR_BODY_BLOCK_ZERO_APPLICATION_BRIDGE_FRESH_EXCLUSION.md`, SHA256

```
5e9f44b9ae62fd5c81e4b7c347bdee06d6000ca2ecbe5cf8ac7afe8a5cd72c57
```

I read the whole target and reconstructed its complete geometry, private-force reductions, winding comparison and original fork callers. I also read the complete adjacent-, opposite- and three-load C4 local sources and the full hub-diamond source, checking exactly which portions precede their old middle-triangle/ray assumptions. The closed-origin treatment below is new mathematics in the target; it is not imported by continuity from those strict-ray sources. No complete zero-application source lost in the earlier rollback is assumed.

## 1. Full original scope and the correct strict-ray statement

The actual root H and the distinct outside bridge neighbor U both contain the unchanged origin. H is physically circle-clear because its diameter is sqrt(2), below every allowed radius. Thus summing the real private equations and then using the full H equation gives exactly `M=-beta*n`, with beta positive. The bridge support is zero, so H lies in `M.z>=0`, contains O, and misses only the **strict** negative M ray.

The target never substitutes the stronger absence of O from H. Its use of the actual H center D is legitimate: a nonzero linear functional nonnegative on a full-dimensional square is strictly positive at its center, hence `M.D>0`. Both H and U have O on their boundaries; an interior occurrence in either would overlap the other's interior. No root circle force or outside U force is deleted by these observations.

## 2. Complete height-one proper-port cap

I independently rederived the purely geometric export in Section 2. Because O belongs to the root rectangle and the strict negative N ray misses it, an active own-coordinate side through O points against that ray. After an origin-preserving orthogonal map the actual square is `[0,1] x [b,b+1]`, with `N_x>0` and `q_x<0`. This argument includes an origin vertex: if every active coordinate were inward or tangent, a sufficiently short negative-ray segment would belong to the square.

Both proper coefficients are strictly positive since q lies outside the square. Thus both actual normals have positive x component and expose the far side x=1. The actual origin moment gives a positive weighted mean k of their unchanged port heights. The concurrence slope is a convex combination of the corresponding height and k. At an upper port its positive vertical component has slope at most the upper height; at a lower port the inequality reverses before multiplication by its negative component. Consequently the displayed bound `h_i>=1/(n_i)_x>=1` holds for both signs and for a zero vertical component, including a full actual side mean.

The local support and center bounds require only a contained neighbor, not a triangle, load or force equation. They give `n_x>60/61`, `|n_y|<11/61`, center normal projection at least 3/2, and center norm below 91/60. The resulting common rectangle has squared diameter

```
52124381/53582400 < 1,
1 - 52124381/53582400 = 1458019/53582400.
```

The cap therefore remains strict at height exactly one. The parallel companion also retains this closed endpoint: origin containment and strict-negative-ray avoidance force the actual owned face height to equal one, and the center rectangle has squared diameter `29/144`, leaving reserve `115/144`.

No nonzero triangle-moment premise was exported from `TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md`. In that source it is used to obtain the geometric concurrence hypotheses. Here those hypotheses are supplied by the actual private block equations or, in the final diamond subcase, by explicit positive auxiliary coefficients at unchanged normals and ports.

## 3. Every C4 private load mask is retained

There are eight private load subsets before the A/B reflection. Three consecutive unloaded true degree-two bodies contradict the actual root diameter. A sole adjacent load gives a two-unit normal channel despite an actual endpoint contact. Neither uses a root equation of reduced degree.

For the sole opposite load, the two actual transmitters have width one and the same direction; the endpoint-owner proof uses the original strict point convention and retains their independent means. The loaded parallel-star equation supplies only their actual weighted average. Its inward unit segment contains `(r_C-2)e`, a strict negative M-ray point since `r_C<=d<2`. This excludes both radial S/D possibilities without replacing either mean by that average.

For adjacent private loads, the cited local Sections 1--3 use the real bypass, private equations and complete support cover only. The original later middle triangle is not needed. Their equal normals have strictly opposite port heights, while their nonparallel case has a negative actual concurrence and both proper root ports. The new height-one caps exclude exactly these alternatives. The same-nine radius-lower-bound prerequisite supplies the original `R>2` requirement where used in the local geometric channel calculation.

For opposite private loads, I reread the conditional positive-concurrence proof without a boundary-neighbor premise. Its preceding parallel S/D exclusion uses the real width-one channel and the other endpoint's actual boundary status. The common nonzero channel height then makes the endpoint resultant directions independent with spread less than pi. The nonparallel root coefficient comparison gives `q=-tau*M` before any forbidden-ray use. The all-three-load source similarly uses the actual full boundary-path cone and all three genuine degree-two equations. Its middle circle force remains in the cone and auxiliary polygon.

In each mask the target supplies the new strict-ray premise itself, excludes zero root coefficients, excludes two negative coefficients by nearest-point uniqueness, and applies the height-one cap to two positive coefficients. Equal parallel root normals are handled by the separate closed cap, and opposite parallel normals are excluded by the original private equations. Exactly one positive and one negative coefficient remains, with no discarded zero private proper length.

## 4. Both correction triangles avoid the allowed origin

For that last C4 alternative I independently expanded the two determinant identities:

```
det(M,P_1) = -b_1*mu_2*det(n_1,n_2),
det(M,P_2) =  b_2*mu_1*det(n_1,n_2).
```

They have the same strict sign. The port chord avoids O, and the triangle through q and the two ports meets the M line only at its nonzero vertex q. Hence the whole triangle avoids O, not merely its edges.

For the actual-root triangle through D and the same ports, `M.D>0` and `M.P_i>=0` imply that any representation of O would have zero coefficient at D. It would lie on the excluded port chord. Thus this whole triangle also avoids O. Their signed boundary sum is exactly the correction loop, whose winding is zero. This proof does not assert that the root square itself avoids O and does not manufacture a positive-M point on its axis.

The private-center homotopies have the full physical scope claimed. Every actual boundary-square point and its positive radial concurrence lie in the strict half-plane determined by its full circle resultant; two-corner concurrences need not belong to their squares. In the opposite-load case the real unloaded channel has nonzero height, so its chord avoids O. If that transmitter contains O, it does so only on its boundary because the distinct U contains O. Its center/chord triangle therefore avoids O by the same supporting-face argument. All representative strands consequently have positive distance from O, allowing sufficiently small original junction routings.

The auxiliary triangle or polygon has winding one by the exact strict angular lifts in the local source. Adding the zero-winding root correction proves the same for the actual physical ring. Interior points of U approach O from within a winding-one neighborhood; its connected open interior avoids all occupied ring strands. Therefore the unchanged U lies on the bounded free side, including all weak contacts. The four-ring area/equality theorem applies. Three boundary members exclude a central unit directly; two opposite boundary members force the aligned cross and then `R^2=5/2`, contrary to the radius window. No third boundary load is invented in that latter case.

## 5. The hub-diamond keeps its full K3 equation

The two private tips are loaded by their exact degree-two touching-neighbor obstruction; the private hub K is loaded by its exact degree-three theorem. The complete physical-triangle coefficient lemma applies with every original central force and both physical pages retained. Its parallel and all-coincident cases were reread. In particular the all-coincident exclusion uses the actual boundary K, rather than a nonexistent two-force law at K.

The full K3 equation implies that a belongs to the closed positive cone of u,v. In the nonparallel case this can also be checked directly from the original coefficient formulas: if `a=A*F_A+B*F_B`, then the coefficients of a in the u,v basis are `A*c_W/Delta` and `B*c_U/Delta`, both nonnegative. Adding u and v gives the strict positive coefficients of M used in the target. The determinant expansion and both numerator identities were checked independently as formal rational polynomials.

The actual root-line intersection is a strict negative combination of u and v. Hence neither whole root line passes through O, including any actual zero proper endpoint. If their chord contained O, both ports would lie on the exposed H face `M.z=0`. This is an actual side, because the two ports are distinct. All outward normals there, including at its endpoints, have nonpositive M component. The strict positive representation of M by u,v then contradicts `|M|^2>0`. This proves the target's new chord-origin exclusion with full K3 retained.

The actual-root triangle now avoids O. If the other correction triangle does too, the unchanged private boundary path and its center homotopies give winding one and the same three-boundary ring-capacity contradiction. If O lies strictly inside that triangle, its positive coordinates in the u,v basis force both actual root lengths positive. An actual own side of H through O then puts Q strictly across that side; `N=-Q` is a positive auxiliary combination of the unchanged u,v normals. The complete height-one geometric cap applies. Those coefficients are used only to establish its hypotheses; they do not replace the original stress or any K3 load.

The parallel hub case is covered by the same height-one parallel cap. The tip-root diamond has two true private degree-three hubs and is excluded by the arbitrary-tip hub-pair theorem. The positive K4 profile has its unchanged independent obstruction. This is the full four-body block/root-orbit cover.

## 6. Entire original three-edge fork callers

The outside U is an actual unloaded degree-three articulation: its three incident edges are bridges, and the original common certificate excludes a loaded all-bridge nonleaf. Its two actual leaf moments are zero, so its full moment makes `P_HU=rho*n`.

I reread the complete force-free central-disk/critical feature cover for two genuine leaves. For `d!=1`, U contains O openly and hence its actual incoming support has `rho<0`. The corrected negative-bridge theorem retains the root circle resultant until justified at each mask and applies to precisely that original bridge. At `d=1`, the only noninterior possibility is the actual own-axis square `[0,1]u+[0,1]v` with both genuine S leaves. The full U3 force equation gives `beta*n=lambda*u+mu*v` with both coefficients positive. Its actual incoming support is its unique origin vertex, so the new zero-application theorem applies.

Thus all original fork placements F1/F2/F3 are excluded across all radii and leaf types, with all seven positive bodies and both additional physical squares retained. No positive edge is dropped to create a smaller degree, no actual mean is changed, and no outside subtree equation is substituted.

## 7. Exact present prerequisite pins and independent arithmetic

| Source read at its stated local scope | SHA256 |
| --- | --- |
| `TRIANGLE_NONZERO_MOMENT_EXTERNAL_RAY.md` | `a9cd82e70331f0ceea763807005224d2a4dee557842d7fe1d8bf32ea97ffb1fb` |
| `ROOTED_C4_ADJACENT_LOAD_ORIGIN_TRIANGLE_EXCLUSION.md` | `020d5807780d21c5fa8274fc2e89b500b21cbb6e1265a7ee42153e914b5f4f3d` |
| `ROOTED_C4_OPPOSITE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md` | `c93c6b5bef9cc46d686c06e722ada47595c0c87996d13c71a9a154fea1f56e60` |
| `ROOTED_C4_THREE_BOUNDARY_NEGATIVE_CONCURRENCE.md` | `7fb6437698bcbfedc696d74cc718198115b5cd81c22b6dd67f3cc78509b1b801` |
| `ROOTED_C4_THREE_LOAD_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md` | `267617c29d251390ce5d4e5ed31cae57e2610a681a1a1ca935272a0f086dcfa5` |
| `ROOTED_HUB_DIAMOND_ORIGIN_TRIANGLE_COMPLETE_EXCLUSION.md` | `c9d06aef6dd21548fb7d1e380ef6f97d44527ac20934e57f441fd9aaf55032d1` |
| `FOUR_CYCLE_THREE_BOUNDARY_HOLE_EMPTY.md` | `7331e02af561c8194fd666a83ea3f9e3d89624ddde494f8a06cf26519edcf1b9` |
| `TWO_PARALLEL_TRANSMITTERS_NO_THIRD_BYPASS.md` | `2722fa3b4483d741acb4de927b3178ff9bd913c2584ec1ca6199b513fabde6eb` |
| `TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md` | `71bcdeddbb272f17f2842c54b7d304abf3288436ef01e8faef1ffb9d29c20521` |
| `FOUR_BODY_BLOCK_NEGATIVE_BRIDGE_WITH_FULL_ROOT_LOAD_EXCLUSION.md` | `f2b3b0fc1c41fced68a7f2196ae6261e87b7b2f03d5bfda171da157c5c7887fe` |
| `GLOBAL_CLOSURE_ARTICULATION_STRESS_SPLITTING.md` | `6498d915c83118b06270962f340c300cf52791a1ba6e144e2d7d24c3f25be962` |

The contained-unit support theorem, radial parallel-star theorem, original normal-channel theorems, arbitrary-tip diamond-hub-pair theorem and positive K4 theorem were checked at their literal uses. The new proof does not extend a local theorem beyond its actual degree, load or physical boundary premise.

Independent exact Fraction arithmetic recovered the transverse square `181/3600`, the radical upper reserve `1/2880`, the two rectangle values and reserves above, the opposite-cross radius reserve `2241/1600`, and the conditional endpoint reserve `149/2880`. An independent sparse polynomial reexpansion verified both determinant identities and all three hub coefficient identities. These computations verify the printed exact continuous proof; they are not a sampled geometric certificate.

The target mathematics remains unchanged at its exact pin. No source correction, normal reselection, force deletion, mean replacement, remote mutation, compilation, CI or shared metadata edit was made in this audit.
