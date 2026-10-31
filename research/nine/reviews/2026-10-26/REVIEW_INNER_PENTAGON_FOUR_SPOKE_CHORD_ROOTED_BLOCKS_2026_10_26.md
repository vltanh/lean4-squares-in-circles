# Independent rooted-block review of the four-spoke chorded pentagon exit

Date: October 26, 2026.
Reviewer: separate rooted-block agent, independent of the proof author and first reviewer.

**Verdict: PASS, complete source and both original load domains.**

I read INNER_PENTAGON_FOUR_SPOKE_CHORD_EXCLUSION.md in full and checked
its local geometric comparisons, the embedded wheel restriction, and the
necessary load cover in SIX_BODY_INNER_PENTAGON_LOAD_COVER.md.
The direct cross equality input was checked against the degree-free
four-ring equality argument in FOUR_CYCLE_LEAF_HOLE_EMPTY.md and the
cross comparison reproduced in LEAF_ANYWHERE_TWO_BOUNDARY_FOUR_RING_EXCLUSION.md.
Only their geometric equality parts are used; no leaf premise is imported.

The opposite-arm calculation is valid: opposite boundary arms give one
center coordinate zero, and containment of the more distant perpendicular
arm forces the other zero. This gives radius squared 5/2, outside the
specified interval. Adjacent boundary arms therefore give the full t,t
cross chart. The strict interval 3/10<t<2/5 has the stated exact reserves
33/1600 and 663/6400.

For the additional unit T, the two physical contacts give its actual
center in [-w,w]^2, with w the common horizontal/vertical halfwidth of
a unit square. Its center cannot lie in any of the three occupied closed
squares, so it is in the strict southwest quadrant. No unsupported claim
that T lies wholly in that quadrant is made. Every vertex offset has
absolute coordinates w,d in some order. The complete bound
(a+b)^2+a^2 <= (3+sqrt(5))/2 <25/9 is valid for every frame, including
side-aligned endpoints. Translating back by P gives every actual vertex
norm <59/30<79/40, with strict reserve 1/120 in the final comparison.
Thus the local lemma genuinely proves physical circle clearance.

The embedded wheel restriction keeps H inside the actual 0123 ring.
The chord03 cannot cut the H0123 sector away from H without crossing
H1 or H2; it lies in the other H0340 sector. The enclosed-unit equality
therefore applies to the actual H and all four original ring bodies.
In the forced cross, loaded1 and2 are adjacent boundary arms, and
physical4 touches both other arms0 and3. Its required load contradicts
the local clearance lemma. This covers optional load0 as well as its
absence, every physical corner mask and all actual means.

The exact ready-to-close IDs are M6.B6.PENTAGON.H4_D1.L124,
M6.B6.PENTAGON.H4_D1.L0124 and M6.B6.PENTAGON.H4_D1_EXIT.
No broader pentagon parent or coarse C1.6.b0 follows. All nine actual
units and the true fourth spoke at H remain. No scalar packet, numerical
pose, force deletion, Lean compilation or CI was used in this review.
