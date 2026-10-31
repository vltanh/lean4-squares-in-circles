# Two genuine parallel transmission channels force an actual transverse two-square strip

Date: 2026-10-31. PR #11 hand-only physical geometric lemma.

**Status:** complete source-level hand proof conditional on the existing **original full-torque two-force-transmitter theorem** and **unique closest-displacement parallel-channel theorem**. Not independently reviewed. This is an actual new geometric condition on distinct unit squares, but **not** a complete nine-square physical exclusion.

## Domain and theorem

In one packing of nine actual, interior-disjoint, arbitrarily oriented unit squares, retain **one original physically supported positive force/torque certificate**, the original body-pair graph and real contact application points/means. Let $A,B,U,V$ be **four distinct actual squares**. Suppose the original selected positive graph contains two internally disjoint two-edge channels
\[
             A-U-B,\qquad A-V-B,
\]
where $U,V$ are selected-circle-unloaded **true full-positive-degree-two** squares: their only positive body-pair contacts are the two edges shown. (The end squares $A,B$ may have arbitrary further original positive edges, and arbitrary circle loads.) No other original force, non-stress touch or external physical square is removed.

The original two-force/torque theorem says each middle square transmits one oriented unit normal $n_U$ or $n_V$ and has **full actual normal width** $w_U,w_V\in\{1,\sqrt2\}$: the normal is either a side normal, giving width $1$, or a diagonal normal, giving width $\sqrt2$.

The existing parallel-channel unique-displacement lemma (Sections 2–3 of [the three-port unicyclic proof](THREE_PORT_UNICYCLIC_UNLOADED_MODULES_HAVE_AT_MOST_FIVE_BODIES_2026_10_31.md)) shows that the two channels have the **same** signed unit normal $n$ from $A$ to $B$ and the same true closest distance $d(A,B)=w_U=w_V$. We do not reselect any force direction.

**Theorem (transverse strip).** Let $t$ be either perpendicular unit direction to $n$. Then:

1. $w_U=w_V=w\in\{1,\sqrt2\}$; **both transmitter squares have the same physical orientation modulo square symmetry**, namely side-normal to $n$ if $w=1$, diagonal-normal to $n$ if $w=\sqrt2$.
2. Their centers have the **same** longitudinal coordinate, $n\cdot c_U=n\cdot c_V$, and
   \[
       |t\cdot(c_U-c_V)|\ \ge\ w.
   \]
3. Thus the **actual** union $U\cup V$ has transverse projection span at least **$2w$**, hence at least $2$, and at least $2\sqrt2$ in the diagonal-transmitter case. No fictitious compressed edge or virtual area is used.

These are necessary conditions. They do not bound where the other seven squares can fit and do not by themselves exclude any of the H1–H5 or K1–K6 families.

## Hand proof

Let $s_A^+(n)=\max_{a\in A} n\cdot a$ and $s_B^-(n)=\min_{b\in B} n\cdot b$. Since the original positive force at $A-U$ uses $n$ outward from $A$ and the force at $U-B$ uses $n$ outward from $U$, the physical support contact equalities at **unchanged actual applications** read
\[
 s_A^+(n)=\min_{u\in U} n\cdot u,\qquad
 \max_{u\in U} n\cdot u=s_B^-(n).
\]
The same statements hold with $V$ in place of $U$ because the unique-distance parallel-channel theorem fixes the same signed $n$. Hence
\[
 \min_{u\in U}n\cdot u=\min_{v\in V}n\cdot v=s_A^+(n),
 \quad
 \max_{u\in U}n\cdot u=\max_{v\in V}n\cdot v=s_B^-(n). \tag{1}
\]
Subtracting gives $2h_U(n)=2h_V(n)=s_B^-(n)-s_A^+(n)=w$, and adding gives $n\cdot c_U=n\cdot c_V=\frac12(s_A^+(n)+s_B^-(n))$.

The full original two-force/torque classification gives $w\in\{1,\sqrt2\}$. For any unit square, a prescribed side-normal $n$ determines its actual unoriented side frame, up to changing signs or exchanging the two axes. Likewise a prescribed diagonal normal $n$ determines that frame up to the same square symmetries. Because $U,V$ have the **same** transmitted normal and normal width type, their square shapes are identical up to translation: there is no free independent tilt between them.

Now use the common coordinates $(n,t)$. For the *side-normal* case, each square is a unit axis-aligned square; its open slice at its own center longitudinal coordinate is the open tangential interval of length $1=w$. For the *diagonal-normal* case, each is the same square tilted by $45^\circ$; its open slice at the center longitudinal coordinate is the open tangential interval of length $\sqrt2=w$. In either case, by (1) the two squares have the **same** longitudinal center coordinate. If their tangential center separation were strictly below $w$, those two open central slices would overlap in an open interval. As the slices lie in the same longitudinal line and within each square's interior, this would violate disjointness of open square interiors. Hence
\[
             |t\cdot(c_U-c_V)|\ge w. \tag{2}
\]
Conversely, (2) is sufficient for nonoverlap of these two same-oriented transmitter squares by a separating support line perpendicular to $t$; only necessity is needed here.

Each square has transverse projected width $w$ in both the side and diagonal cases. Two length-$w$ tangential projections whose centers are separated by at least $w$ have union span at least $2w$. This proves 1–3.

The original physical touches and all nine actual bodies remain; no center has been moved and no force direction has been replaced. The lemma is compatible with both possible support-face corner ties, since it uses only true physical support extremes and open interiors.

## Disk-center corollary (actual farthest corners, no virtual width)

Let $m=n\cdot c_U=n\cdot c_V$, with the actual containing disk centered at $O=0$. The two transmitters' transverse center coordinates differ by at least $w$, so at least one transmitter $T\in\{U,V\}$ has $|t\cdot c_T|\ge w/2$.

- **Side-normal $w=1$.** In its actual side-aligned $(n,t)$ square frame, $T$ has a farthest actual corner with squared radius
  \[
  (|m|+\tfrac12)^2+(|t\cdot c_T|+\tfrac12)^2
  \ge (|m|+\tfrac12)^2+1.
  \]
  Disk containment therefore forces $(|m|+\tfrac12)^2+1\le R^2$.
- **Diagonal-normal $w=\sqrt2$.** In $(n,t)$ coordinates, one actual vertex of $T$ is the tangentially outer diamond vertex
  \[
  (m,\ t\cdot c_T+\operatorname{sgn}(t\cdot c_T)\,\tfrac{\sqrt2}{2}),
  \]
  with the sign chosen arbitrarily if its transverse center coordinate vanishes. Its squared norm is at least
  \[
  m^2+\left(\tfrac{\sqrt2}{2}+\tfrac{\sqrt2}{2}\right)^2=m^2+2.
  \]
  Thus $m^2+2\le R^2$.

These are real radius constraints shared by both parallel-channel transmitters. They hold independently of the endpoint hubs' orientations and any other contacts. They still do **not** exclude a complete nine-square configuration without a joint bound involving the other seven bodies.

## Scope boundary and next use

This lemma applies to the **compulsory two genuine parallel $AB$ transmitters** in *each* of the five H1–H5 three-hub rank-two cases, and to the analogous pair in any other original positive graph satisfying this same two-channel premise. It supplies a real transverse width reserve rather than a made-up projection gap. A next theorem would have to combine this reserve with the **actual** neighboring hub square(s), the external loaded squares and all the nine-square completion geometry at radius $R^2\le1105/256$. The lemma alone cannot close any canonical coarse/fine cell, any M29 physical case, or G4.2.c.

No Lean/Lake, CI, external scripts, computer-assisted mathematical exclusions or numerical pose certificates were used.
