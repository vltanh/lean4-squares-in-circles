# Independent audit of the fixed-ceiling sharp-radius transfer

**PASS.** I independently checked the continuous outer-expansion argument,
the retained-witness boundary reduction, the subsharp contradiction and the
original-center equality pullback in
`HAND_FIXED_CEILING_TRANSFER_WITH_AUTOMATIC_TERMINAL.md`.
No correction to that frozen manuscript was needed.

The conclusion is still conditional on completing the universal capture
at \(Q_1\), including \(S\le1/1000\). This audit does not treat that
remaining global input as already proved.

## 1. Radius order and uniformity

The previously proved sharp bracket has endpoints
\(q_c-2\cdot10^{-16}\) and \(q_c+10^{-16}\), where
\(q_c=3.91553413751747532652\). Exact rational comparisons give

\[
\frac52<\frac{7831}{2000}
<q_c-2\cdot10^{-16}<q_*<q_c+10^{-16}
<Q_1<\frac{9789}{2500}<4.
\]

Thus \(\bar q=\max(q,7831/2000)\) is inside the expansion range and
strictly below \(q_*\) whenever \(q<q_*\). Enlarging only the containing
disk to \(\bar q\) does not move any square. The central-core theorem
remains applicable under the coarse ceiling.

The ordinary boundary-reduction proof is uniform at every such
\(\bar q\): its radius and angular estimates use upper containment
bounds at the coarse ceiling, while its compact outer center body can be
formed at the actual smaller radius. The exact arithmetic comparison
giving a gap greater than \(3/5\), and the six-other-gaps argument
excluding a gap of \(\pi\), remain unchanged. Nonneighbor overlap is an
explicit relaxation and does not affect either part of the transfer.

## 2. Every feasible signed axis survives outer expansion

For fixed center ray and true square frame, implicit differentiation of
\(r^2+Br+1/2=q\) gives the stated
\(r_q=(B^2+4q-2)^{-1/2}\). Since \(1\le B\le\sqrt2\), the
uniform bounds are \(4/5<r<3/2\) and \(1/4\le r_q\le1/3\).
A core-boundary center has radius less than \(4/5\); for example,
\(\sqrt2<10/7\) gives
\(\sqrt2/2+1/12<67/84<4/5\).

For any initially feasible signed SAT axis, its normal and support width
are fixed during expansion, and the width is at least one. In an
outer–outer pair with nonnegative projection coefficients, feasibility
forces their sum greater than \(2/3\), giving derivative greater than
\(1/6\). They cannot both be nonpositive. With opposite signs, write
the projection as \(ur_A-sr_B\), where \(u,s\ge0\). Feasibility gives
\(u>2/3+(8/15)s\) and \(s<5/8\), so

\[
P'\ge u/4-s/3>1/6-s/5>1/24.
\]

For a core–outer pair, \(ur_O+vr_C\ge1\) forces
\(u>2/15\), giving derivative greater than \(1/30\). A core–core
projection is unchanged. These estimates apply wherever that axis is
feasible, including at its feasibility threshold. Continuity and the
positive derivative at a hypothetical first downward crossing prove
preservation. This reasoning holds separately for **every** initially
feasible signed axis; it is stronger than preserving one chosen axis.

Core avoidance also survives: core centers stay fixed, and each outer
center moves outward along a fixed ray outside the bounded rounded-square
forbidden center body. Containment at the new radius is its defining
outer-boundary equality.

## 3. Exactly which quantities are retained

| Operation | Retained information used later |
|---|---|
| Enlarge the containing disk to \(\bar q\) | All centers, frames and pair witnesses |
| Boundary deformation at \(\bar q\) | Cyclic label order, true frames and the seven initially selected signed witnesses |
| Outer expansion to \(Q_1\) | Every previously feasible signed axis, each center ray, true frame, relative tangent and radial type |
| Return to the stored \(\bar q\) representative | Its already established feasibility and the capture's identical ray/frame data |

The boundary deformation is not asserted to preserve individual center
rays or relative tangents. Retaining the initially chosen seven witnesses
is nevertheless valid by induction: every move uses precisely its two
incident selected halfplanes, whose common recession direction keeps both
inequalities valid. Other selected inequalities are unchanged by that
move. The same signed witness assignment therefore survives the entire
seven-step construction.

In contrast, the subsequent outer expansion fixes each ray and true
frame, so the captured canonical tangents, quarter offsets and frame
differences are identical on its two endpoints. Returning to the smaller
representative invokes its prior feasibility, not a claim about arbitrary
inward motion.

## 4. Capture at the larger radius applies at the smaller one

The necessary quantifier on the axis results is used correctly. The
universal angular theorem excludes the other signed axes, and the owner
theorems exclude every forbidden feasible retained axis, including ties.
Each witness already feasible at \(\bar q\) survives to \(Q_1\), so
it must belong to the captured allowed set there. Its normal and true
frames are fixed, so it is the same allowed witness on returning to
\(\bar q\).

The recovered representative therefore has the captured tilt and total
mismatch, the required owners, containment at \(\bar q\), and core
avoidance. These are the hypotheses of the automatic-slider terminal.
Its slider projection bounds are conclusions from containment and core
avoidance; no center-distance comparison with the expanded cycle is
needed. The terminal gives \(\bar q\ge q_*\), contradicting the
strict radius order in Section 1.

## 5. Equality is pulled back to the original centers

At \(q=q_*\), the same argument obtains the terminal on a boundary
representative at \(q_*\). Its positive angular remainder forces
\(S=0\), and its positive tilt term forces \(t=t_*\). The original
physical square frames are those same frames. Applying the captured
labeling and rigid normalization to the original packing preserves the
original selected signed witnesses.

At zero error, either allowed owner on an aligned edge has the same
normal: axes 1 and 3 coincide at zero quarter difference, while axes 3
and 4 coincide at one quarter difference. The remaining two mixed normals
are fixed uniquely. Thus the exact stationary dual can be evaluated
directly on the original centers, with their original nonnegative
separator gaps. Its identity is

\[
\mathcal D=q_*+
\sum_{i=A,B,D,E,H}\mu_i|p_i-p_i^0|^2.
\]

Containment and the positive contact weights also give
\(\mathcal D\le q_*\). It follows that the five original anchors
are fixed and every selected original contact gap is zero. The two
slider forces vanish identically at these stationary directions, so
this reapplication needs neither original slider bounds nor original
canonical tangent or center-proximity assumptions.

Only the zero-error identity from
`EQUALITY_PULLBACK_TO_ORIGINAL_SQUARES.md` is needed in this final step;
its earlier, narrower capture thresholds are not reintroduced. The new
automatic terminal supplies the required frame conclusion. The actual
original eight-square packing still satisfies all nonneighbor and
central-square constraints, so the necessary-and-sufficient parameter
domain in `COMPLETE_EQUALITY_PARAMETER_DOMAIN.md` applies. No equality
branch is lost through the relaxed boundary cycle, and no extra freedom
is inferred from that cycle.

## 6. Exact companion and binding

`verify_fixed_ceiling_transfer_arithmetic.py` independently checks 29
fixed rational comparisons, the exact radius order, the quarter-offset
word, all 32 allowed owner assignments and the five zero-error normal
identities. It also reconstructs the two frame clusters
\(\{H,G\}\) and \(\{A,B,T,D,E\}\). The terminal angular reserve
is checked exactly as \(10293/5000000>0\).

The report `fixed_ceiling_transfer_independent_audit.json` binds the
unchanged transfer manuscript, the cited bracket and broad estimates,
the committed boundary reduction, the current capture and automatic
terminal, and the original-center equality and complete parameter-domain
notes. It records the checker hash and unchanged-input status. All paths
support a flat repository layout.

The reviewed transfer manuscript hash is

```
09c574dbcad7353057ef247341424e2f6bc158c2ed1329bd7a125223ab062265
```

The continuous transfer and equality implications are complete under the
explicit universal fixed-ceiling capture input.
