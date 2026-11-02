# The good-central position lemma uses only the original endpoint rectangle

November 2, 2026. Independent physical transfer audit of the completed
6,302-leaf local position theorem. This is a transfer of an already
replayed finite proof, not a new finite exclusion or a whole-mask claim.
No Lean, Lake, or CI.

## 1. The precise weaker statement proved by the existing table

Put Q=1105/256, l=29/60, u=13/12. Let L,P be two original independently
oriented unit squares in the closed Q-disk, with disjoint open interiors.
Suppose

    -u<=x_L<=-l, y_L>=0,
    |x_P|<=l, y_P-h_P>=1/10,
    x_P-x_L>=|y_P-y_L|.

Let K be the fixed rectangle centered at (-3/2,0), with horizontal
halfwidth 217/480 and vertical halfwidth 221/600. Suppose L and K have
disjoint open interiors. Then

    x_P>-1/10.                                      (1)

No inner main square occurs in this statement. An original left
endpoint containing K is sufficient to derive the last nonoverlap
hypothesis, but the proof does not require any four-chain comparison
after that containment has been established.

This is exactly the physical subsystem evaluated in Sections 2-6 of
`UPPER_SIDE_GOOD_CENTRAL_POSITION_HAND_TABLE.md`. Its original statement
assumed an actual four-chain to obtain K. The following audit makes
explicit why its same completed table proves the weaker statement above.

## 2. Complete transfer of the physical reduction

Assume (1) fails and write x_L=-z, x_P=-v. The physical half-unit disks
and the cone comparison give x_P-x_L>=1/sqrt(2)>7/10. Thus

    4/5<=z<=13/12, 1/10<=v<=29/60.

These are the existing position roots. Put D_E=3/2-z and
s=D_E-217/480. Then

    -17/480<=s<=119/480,
    D_E+217/480>=139/160.

The rectangle's horizontal separating axis fails because s<1/2<=h_L.
Every downward L-owned axis also fails. If its horizontal component is
nonpositive, its projection on (D_E,y_L) is nonpositive. Otherwise,
after subtracting the support of K, its projection is bounded above by

    max(0,D_E-217/480)<1/2.

The maximum with zero is necessary when D_E-217/480 is negative. The
older sentence bounding that projection by D_E-217/480 itself was
incorrect in that sign case. Replacing it by the displayed bound proves
the same strict exclusion and changes none of the evaluated finite
expressions or root intervals.

The surviving upward coordinate and original L-owned axes give exactly
the three thresholds independently reconstructed by the existing verifier.
Their complete two-sign reduction is the loss in Sections 3-4 of the
position manuscript. It includes t_L=0 through the coordinate facet and
the two closed slope charts [0,1/4], [1/4,1]. It forces y_L>31/50.

All later quantities use only the same original signed L and P frames,
their circle caps, the good whole floor of P, their original physical
separating axes, and the cone truncation of y_P-y_L. In particular,
neither an inner-main halfwidth nor an actual middle comparison occurs.
The inset-sum lower bound for their horizontal gap is a consequence of
their own physical cone pair; it is not a main-chain condition.

Consequently the five necessary expressions, eight signed/chart roots,
and their complete midpoint partition are unchanged. The original
independent replay proves (1) on the entire weaker physical subsystem,
including every contact and boundary face.

## 3. The endpoint resource in the weak-middle domain

`OUTER_ACTUAL_LINK_ENDPOINT_RESERVE_HAND_PROOF.md`, pinned at
ddadfdd3bd2ef39a2e698680f9a2f3b7d73876ab, proves for the original left
endpoint E of a completed four-chain with actual outer links

    -91/60<x_E<-89/60,
    g_E>15/32,
    g_E-|y_E|>221/600.

Its original aligned inset therefore contains K. The two horizontal
endpoints of K are -937/480 and -503/480, and the last displayed
inequality supplies its entire vertical interval. The proof retains
the two independent inner frames through h_i<13/20; no old 31/60
inner-width bound is imported.

Thus L's original physical nonoverlap with E supplies its required
nonoverlap with K, even when the middle main link is weak. All other
original pair constraints remain present. This justifies the position
lemma's use in the 010/11 high-floor caller.

## 4. Exact acceptance record and limits

The preserved certificate is
`computer_assisted/low_endpoint_central_position_cover.json`, SHA-256

    794ddb292c0914e2aa5f097fd68f2abea037bcc7bba08cba659de9630cbc8028.

Its completed independent replay checked 12,596 nodes, 6,302 strict
leaves, eight closed roots, and maximum depth 29. The largest replayed
upper bound is

    -87402506829127/18446744073709551616<0.

The standalone verifier independently reconstructs the three original
endpoint facet thresholds, rather than importing the producer's loss
formula. The position manuscript records all fifteen rejected damaged
or false certificate controls and the exact reproduction commands.
The downward-axis wording correction above does not change the
certificate or the verifier, and no numerical optimization is used to
justify this transfer.

This is independent exact arithmetic replay and an analytic agent audit,
not a formal-kernel or human verification claim. The completed local
position bundle was not present at the pinned remote ddad commit; it is
a preserved local proof input to be integrated explicitly if the new
010/11 proof uses it. No whole-mask closure follows from this audit alone.
