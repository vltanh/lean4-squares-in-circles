# A.2: a wider sharp terminal that retains the sliding equality family

**Scope.** This extends `SHARP_NEIGHBORHOOD_THEOREM.md` strictly: the same
quantitative conclusion now permits substantially larger internal vertical
slides. It is a conditional seven-square theorem, not a proof that every
remaining nine-square configuration enters this chart. No original positional
root is marked closed solely because this theorem exists. A.2 remains OPEN.
No Lean, Lake, CI, separate human review, or global equality classification is
claimed. All arithmetic certificates use Python integers and Fraction.

## 1. Exact domain and conclusion

Put Q=1105/256. Use seven independently oriented, pairwise interior-disjoint
unit squares with centers

    M_i=(-3/2+i+dx_i, 1/16+z_i),          i=0,1,2,3,
    B_j=(-1+j+dx_(4+j), -15/16+z_(4+j)),  j=0,1,2.

They are contained in the disk centered at zero of squared radius q. In ONE
common orthonormal coordinate system, assume:

| Quantity | Closed interval |
|---|---|
| Every horizontal deviation dx_i | [-1/8,1/8] |
| Anchor vertical deviations z_0,z_3,z_4,z_6 | [-1/8,1/8] |
| Internal middle-row deviations z_1,z_2 | **[-1/8,11/16]** |
| Internal bottom-row deviation z_5 | **[-19/32,1/8]** |

Write the frames as u_i=(a_i,t_i), v_i=(-t_i,a_i), with a_i>=0,
a_i^2+t_i^2=1 and |t_i|<=1/64. Normalize the common coordinates by u_0=(1,0).
No other orientation is fixed. Frame quarter-turns only change a square's
representation, not its physical pose.

Define

    V_M=|t_1|+|t_2-t_1|+|t_3-t_2|,
    V_B=|t_5-t_4|+|t_6-t_5|,
    V_C=|t_4|+|t_3-t_6|,             V=V_M+V_B+V_C.

Let w_0=w_3=23/64 and w_4=w_6=9/64. Then

    q-Q >= V/256 + (1/2) sum_(i in {0,3,4,6}) w_i(dx_i^2+z_i^2).       (T)

In particular, q>=Q. This is uniform arbitrarily close to equality, not a
bound at Q-epsilon. Two additional physical squares are permitted without
any new pose restrictions; their constraints are simply not needed by (T).

Every configuration in the former [-1/8,1/8] vertical neighborhood is included.
For example, the new chart also permits internal middle-row centers at height
3/4 and bottom-middle centers nearly as low as -91/60.

## 2. The horizontal separator argument still covers every owner

Set b=1/64, c=(1-4b)/2=15/32. The relative-frame estimate of the preceding
manuscript is unchanged:

    (1+u_i.u_j+|det(u_i,u_j)|)/2 >= 1+c|t_i-t_j|.             (1)

For a consecutive horizontal-chain pair, its x-displacement is in [3/4,5/4].
The maximum vertical displacement is now 13/16 in M and 23/32 in B. On a
v-axis the absolute projection is therefore bounded by the following values:

| Row | Wrong-axis upper bound | Correct u-axis positive lower bound |
|---|---:|---:|
| M | b(5/4)+13/16 = 213/256 < 1 | (1-b)(3/4)-b(13/16) = 743/1024 > 0 |
| B | b(5/4)+23/32 = 189/256 < 1 | (1-b)(3/4)-b(23/32) = 1489/2048 > 0 |

Since the required halfwidth is at least one, a v-axis cannot separate the
pair. The u-axis projection is positive for either possible owner. The full
separating-axis theorem consequently implies

    Delta x >= 1+c|t_j-t_i|-t_owner(z_j-z_i),                (2)

where the owner is whichever of the actual two squares supplies a separator.
No contact equality is assumed.

The two vertical anchor pairs have exactly the old bounds: an unavailable
u-axis has magnitude at most 197/256<1, while the correct v-axis projection
is at least 93/128>0. Their derivation and all four owner combinations are
unchanged. Thus none of the widened internal slides invalidates an axis or
sign case in the proof.

## 3. Recenter each row before telescoping

This is the mathematical improvement. Consider any chain whose height
deviations z_i lie in [L,U]. Put m=(L+U)/2 and h=(U-L)/2. For an edge i--j,
if i owns its separating axis,

    -t_i(z_j-z_i)
      =t_i z_i-t_j z_j + m(t_j-t_i)+(z_j-m)(t_j-t_i).

If j owns the edge, replace z_j in the last term by z_i. In both cases the
last term is at least -h|t_j-t_i|. Summing (2) over the entire chain yields

    span - number_of_edges
       >= (c-h)V_chain + t_start z_start-t_end z_end
          +m(t_end-t_start).                              (3)

This identity uses the true owner on every edge. It does not require parallel
squares, equal heights, or a presumed common separator.

For the present two rows, the complete height ranges, including their anchors,
are

| Row | L | U | Midpoint m | Half-range h |
|---|---:|---:|---:|---:|
| M | -1/8 | 11/16 | 9/32 | 13/32 |
| B | -19/32 | 1/8 | -15/64 | 23/64 |

Let W_M=23/16, W_B=27/64 and k=207/512. Compared with the old telescoping
bound, (3) adds the endpoint terms

    W_M m_M t_3 + W_B m_B(t_6-t_4),

while replacing c-1/8 by c-h_M or c-h_B in the two variation coefficients.
These signed endpoint terms must be retained. Estimating the enlarged height
ranges solely by their absolute magnitudes would discard this improvement.

## 4. The four-corner identities and displacement costs are unchanged

The old proof uses only the four anchors in its exact weighted corner
expansion and displacement grouping. Their neighborhoods are unchanged, so
both polynomial identities remain valid verbatim. The explicit weights and
selected corner signs are in Sections 4-5 of `SHARP_NEIGHBORHOOD_THEOREM.md`.
The new checker re-expands both identities through that separate verifier;
neither is inferred from a numerical example.

Completing the four displacement squares retains

    (1/2) sum_anchors w_i(dx_i^2+z_i^2)

and bounds all negative quadratic tilt terms by C_3 t_3^2+C_4 t_4^2+C_6 t_6^2,
where

    C_3=2623909/524288,
    C_4=484929/262144,
    C_6=1647099/524288.

No enlarged internal-height term enters these coefficients. Internal heights
were eliminated by the exact telescoping in Section 3. The only changes to
the old three-endpoint expression are

    A'=851/2048-W_M m_M = 23/2048,
    B'=225/2048+W_B m_B = 45/4096.                          (4)

Here X=t_3,Y=t_4,Z=t_6. Subtract lambda V, lambda=1/256, from the derived
radius lower bound. The coefficients of V_M and V_B are positive, so minimize
V_M>=|X| and V_B>=|Z-Y|. Bound t_i^2<=b|t_i|. The remaining expression is

    F(X,Y,Z)=(W_M(c-h_M)-lambda)|X|-A'X
       +(W_B(c-h_B)-lambda)|Z-Y|+B'(Z-Y)
       +(k(c-1/4)-lambda)(|Y|+|X-Z|)
       -b(C_3|X|+C_4|Y|+C_6|Z|).                          (5)

Proving F>=0 completes (T).

## 5. Complete finite sign table

The positive/negative level-set decomposition used in the preceding proof
applies to (5): every absolute coordinate, every absolute difference and each
linear term decomposes exactly into signed indicator layers. Hence it suffices
to check F(1_S),F(-1_S) for all seven nonempty subsets S of {X,Y,Z}. This is a
complete real-domain argument, not sampling of possible tilts. Repeated levels
and zero coordinates simply contribute zero-length layers.

The following entries are exactly 2^25 F at the indicated layer:

| Nonzero coordinates S | Positive layer | Negative layer |
|---|---:|---:|
| X | 2,719,323 | 3,472,987 |
| Y | 2,915,198 | 3,652,478 |
| X,Y | 5,634,521 | 7,125,465 |
| Z | 2,975,237 | 2,237,957 |
| X,Z | **21,600** | 37,984 |
| Y,Z | 3,056,003 | 3,056,003 |
| X,Y,Z | 102,366 | 856,030 |

All values are strictly positive; the smallest is 675/1048576. Therefore (5)
is nonnegative for every real triple. Retaining the four anchor squares proves
(T), including its exact sharp boundary. As a further algebra check, the
verifier independently checks all 126 signed indicator layers of all six free
tilts before reducing the two chains to three endpoint variables. Their minimum
reserve is the same. Neither table restricts actual physical tilts to +/-1;
these are homogeneous test directions.

## 6. The downward guard is automatic for subcritical packings

For a contained unit square, the maximum corner norm gives

    q >= |c|^2+|c|+1/2.

At |c|=91/60 the right side exceeds Q by 31/57600. Thus q<=Q implies
|c|<91/60. For the bottom-middle square,

    z_5 = y_5+15/16 > -91/60+15/16
                        = -19/32+7/480 > -19/32.           (6)

Accordingly, a global caller excluding q<Q need not prove the lower vertical
guard on B1 independently: it follows from the original physical constraints.
This does not establish its upper guard, any other chart guard, or the global
existence of the seven-square subsystem. For the unrestricted quantitative
statement (T) at arbitrary q, the displayed chart hypotheses are retained.

## 7. Equality within the widened seven-square chart

If q=Q, (T) forces all four anchor deviations to vanish and V=0. The variation
graph is connected to t_0=0, so every frame aligns. Physical horizontal
nonoverlap and the fixed endpoint spans force all seven x-coordinates to their
base values. The three remaining slides have exactly these ranges:

    M1=(-1/2,1/16+s_1),   M2=(1/2,1/16+s_2),
    B1=(0,-15/16+r),

    0<=s_1,s_2<=11/16,
    (23-sqrt(1041))/16 <= r <= min(1/8,s_1,s_2).             (7)

Necessity of s_1,s_2>=0 follows from their horizontal overlap with the fixed
outer B squares. The bottom-middle square overlaps both middle M squares,
forcing r<=s_1,s_2. The opposite vertical order is impossible in the chart's
height ranges. Circle containment of the bottom-middle square gives the exact
lower endpoint in (7). It lies above -19/32, as 4*1041<65^2.

Conversely, every choice in (7) gives an interior-disjoint seven-square packing.
The two internal M squares have maximum squared corner norm at most 41/16<Q.
For B1 the lower endpoint in (7) is exactly the circle-containment limit:
1/4+1041/256=Q. The four fixed anchors attain Q. Every other pair is separated
horizontally or satisfies the listed vertical inequalities.

This is a necessary-and-sufficient equality description for these seven squares
within this chart. It is not a parametrization of all possible eighth and ninth
squares, or of every unrestricted optimal nine-square packing. Their original
physical constraints remain mandatory.

## 8. Exact replay, caller integration, and remaining scope

Reproduce with Python's standard library only:

```sh
python make_wide_slide_certificate.py
python verify_wide_slide_certificate.py --negative-controls
```

The checker imports no new producer. It rechecks the two physical polynomial
identities, four telescoping owner cases, all axis/sign margins, all 14 endpoint
layers, all 126 full-tilt layers, and the automatic downward bound. Sixty-four
rational equality controls pass, 52 outside the former vertical neighborhood.
Eight deliberately corrupted certificates are rejected. The universal proof is
Sections 1-7; these finite controls are supplementary tests, not its premise.

A global branch may use this terminal only after establishing its entire chart
in one common frame. The accompanying guarded-model emitter expresses those
conditions in the ORIGINAL coordinates using the chosen M0 square's frame;
it does not rotate only some squares or reset a fixed hex-cell root's frame.
That interface is a way to apply the theorem to a verified leaf, not an
assertion that every remaining root or assignment satisfies the guards.

### Explicit original-coordinate guard interface

Let the selected M0 square have original first axis (a_0,b_0), and choose
eta in {-1,+1}. For every selected square i, define

    X_i=a_0 x_i+b_0 y_i,
    Y_i=eta(-b_0 x_i+a_0 y_i),
    A_i=a_0 a_i+b_0 b_i,
    T_i=eta(a_0 b_i-b_0 a_i).

The common matrix is orthogonal. It preserves the disk and every intersection.
When eta=-1 it reverses orientation; reversing the transformed second frame
axis then represents the same physical square with positive frame determinant.
The unit equation for M0 gives A_0=1,T_0=0. Thus the 49 emitted inequalities
are precisely the x, y, half-frame and tilt guards of Section 1 in one common
coordinate system. All their expressions are quadratic in the original
variables. No square position or frame variable is eliminated or reassigned.

`emit_sharp_terminal.py` appends these guards to the original nine-square
model, optionally to one fixed hex-cell root. Seven distinct selected IDs
are required; the other two square poses retain all original constraints.
The default or reflected chart is a sufficient refutation terminal for q<Q,
not a global symmetry reduction or an exhaustive choice of seven squares.
No UNSAT solver was called or is needed for the conditional implication.

`test_sharp_terminal_emitter.py` parses the emitted text and evaluates it in
Q(sqrt(3)). Ninety-six transformed/relabelled physical witness models and 24
models with fixed hex-cell assignments pass their exact closed/strict controls.
The downward-slide witnesses lie outside the old neighborhood. All 36 corner
and 36 pair constraints remain, and no new independent real is introduced by
the guards. All fourteen vertical guard endpoints, invalid ID choices, a wrong
reflection choice and an escaped-height control are checked. These are finite
regression controls; the orthogonal-coordinate argument supplies universal
interface soundness. Proving that EVERY remaining packing meets some guarded
terminal remains a separate missing global implication.

**No new original roots are closed by the local theorem alone.** The accepted
5,838 excluded / 2,077 open count remains unchanged until a complete caller or
additional exact full-root exclusion is produced. A.2, global A.3, B.2/B.3 and
the final global hand/table manuscript remain OPEN.
