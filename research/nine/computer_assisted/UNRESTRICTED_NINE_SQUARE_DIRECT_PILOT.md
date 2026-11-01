# First computer-assisted direct pilot — unrestricted nine-square model

**Current active gate: `D.1.a`.** The equations below describe the full, independent-orientation nine-square packing problem, not a positive-force graph or local three-/four-cut module. **The global impossibility is not proved.**

For i=1,...,9 take independent real center `c_i=(x_i,y_i)` and orientation variables `a_i,b_i` with `a_i²+b_i²=1`. Let `u_i=(a_i,b_i)`, `v_i=(-b_i,a_i)`. Vertices are `p_i(s,t)=c_i+(s u_i+t v_i)/2` for each s,t∈{-1,+1}.

**Containment:** all 36 inequalities `p_i(s,t)·p_i(s,t)≤q` with `q=R²`.

**Interior disjointness:** for all 36 pairs i<j, require some axis n chosen from `u_i,v_i,u_j,v_j` to satisfy
`|n·(c_j-c_i)|≥(|n·u_i|+|n·v_i|+|n·u_j|+|n·v_j|)/2`.
This is the exact weak separating-axis theorem for rectangles. Split every absolute value into finitely many exact signed cases. Contact/tangency and zero-projection faces must remain.

**Sharp goal:** prove nonexistence for the entire open semialgebraic domain `q<1105/256`, `q≥0`. Do not prove only at some fixed `q≤Q-ε`. Keep the known equality construction feasible at `q=Q`.

**Sequence:** (1) deterministic exact polynomial formula emitter and hand proof of equivalence; (2) signed-root proof of union coverage; (3) exact equality positive control and known-invalid overlap/outside controls; (4) symmetry reduction with inverse maps; (5) independently proof-producing exact solver on a nontrivial root; (6) GO or explicit pivot to structural stress route. A timeout, numerical sample, missed sign face, or unknown terminal is OPEN, not a proof.

Useful previous source: [full-nine specialized triangle emitter](FULL_PHYSICAL_TRIANGLE_SYSTEM_2026_11_01.md) and [implementation](emit_full_triangle_system.py). Its all-nine geometric constraints may be reused **only after** the selected triangle-specific stress hypotheses are removed. The [three-cut theorem](../ADOPTION_COMPLETE_DIRECT_TRIANGLE_AND_THREE_CUT_FOREST_2026_11_01.md) is a conditional source for the alternate stress route, not an assumption here.
