# A side-interior singleton cannot have a shared support axis

**Date:** October 31, 2026 UTC. **Complete hand proof.**
**Input:** PR #11 at `d896360d49bbdae72567ebe43fee939366ab2c20`.
No numerical search, external computational certificate, Lean work or CI is used.

## 1. A uniform physical contact lemma

Let X,Y be actual closed unit squares with disjoint interiors. Suppose
their physical intersection is the singleton {W}. Assume that W belongs
to the relative interior of a side E of X. A support line through E
separates X and Y; write n for the directed unit normal from X to Y.

**Lemma.** The normal n is not an own side axis of Y.

**Proof.** Suppose it were. Because W belongs to Y and is on the common
support line, the minimum-n support face F of Y is a whole unit side
containing W. E and F lie on the same line.

Choose a unit tangent t along this line. Since W is in the relative
interior of E, some eta>0 satisfies

    W+[-eta,eta]*t subset E.

The side F has length one, contains W, and is nondegenerate. Therefore
for one sign sigma in {+1,-1} and some zeta>0,

    W+[0,zeta]*sigma*t subset F.

It follows that the nondegenerate segment

    W+[0,min(eta,zeta)]*sigma*t

is contained in E intersect F, hence in X intersect Y. This contradicts
the stipulated singleton intersection. The argument includes W at either
endpoint of F. QED.

The conclusion is purely physical. It does not depend on any force,
circle contact, vertex coefficient, degree, load or choice of aggregate
contact mean. In particular, a genuine side-interior singleton between
two squares cannot occur when their frames are parallel. Conversely,
parallel support sides meeting at a side-interior point necessarily have
positive shared physical length; an endpoint-valued mean cannot change
that length into a singleton.

## 2. The singular perpendicular AD feature is impossible

Use the exact original chart and premises of
[TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md](TWO_STRICT_PERPENDICULAR_AD_REGULAR_ANGLE_TORQUE_REDUCTION_2026_10_30.md).
In particular, the actual A-to-V roof direction h is an A own axis, the
actual D-to-V roof direction k is a D own axis, and AD is a **genuine
A-owned singleton**. Its original application W lies in the relative
interior of A's side with outward normal g=-e. Write

    h=(c,-s), e=(s,c), k=(C,S), v=(-S,C),
    c,s,C,S>0,
    c^2+s^2=C^2+S^2=1,
    H=s*C+c*S, J=c*C-s*S.

Suppose the alleged singular alternative J=0 holds. The positive unit
vectors k,e then agree: H=1 and

    k=e, C=s, S=c, v=-h.

Thus g=-e is also a D own side axis. The physical support line of AD
contains A's minimum-e side and D's maximum-e side. W is in the relative
interior of the former and belongs to the latter. The lemma in Section 1
forces positive shared physical AD length, contradicting the unchanged
genuine-singleton premise. Therefore

    J != 0.

This proof uses no B,C,N equation, no physical circle coefficient and no
radius bound. It applies without change to the stated feature of **both
D02.L135 and D02.L1345**, as well as any larger configuration retaining
the same actual singleton/support premises. Every other unit and every
original force remains; none is suppressed.

## 3. Correct strengthened angle conclusion

The prior angle manuscript establishes, from its full original hub stars
and support geometry, that

    0<alpha+beta<pi/4 OR alpha+beta=pi/2.

Section 2 removes the second alternative by the actual singleton
condition. Consequently the complete original genuine A-owned
perpendicular feature satisfies

    0<alpha+beta<pi/4,
    0<H<J,
    s/H<rho<1,
    0<ell=c-J*rho<1.

All the regular full-star equations of that manuscript remain valid,
including

    nu*(1-rho)=gamma*(J-H),
    mu*(1-ell)=gamma*(1+s-H*rho),
    mu*(d*s+c/2)=nu*(d*S+C/2).

The side-mean torque identity previously recorded at J=0,

    (nu+gamma)*lambda=gamma*rho,

is an algebraically compatible equation for a relaxed shared-axis
support model. It does not establish a physically genuine singleton.
There is no need to force lambda to an endpoint or to replace a side by
a vertex. The missing geometric singleton condition itself supplies the
contradiction.

## 4. Shared interfaces and exact accounting

A physical AD segment with J=0 belongs to the separate shared-interface
row, with its entire original side mean retained. It is never relabeled
a singleton. For L135 with both roofs hub-owned, that whole shared row is
already excluded by
[TWO_STRICT_OWNED_ROOFS_SHARED_HUB_EDGE_COMPLETE_BRIDGE_EXCLUSION_2026_10_30.md](TWO_STRICT_OWNED_ROOFS_SHARED_HUB_EDGE_COMPLETE_BRIDGE_EXCLUSION_2026_10_30.md).
That earlier bridge theorem has an unloaded-N premise; it is not extended
here to loaded N. The **genuine-singleton** exclusion in Section 2 has no
such premise and does extend to loaded N.

This proves the whole singular feature and closes a genuine geometric
branch of the perpendicular argument. The regular narrow-angle feature,
the free-roof/nonfree-interface family and the complete original row join
are separate obligations. This manuscript by itself changes no original
fine or coarse gate flag and does not assert the full n=9 theorem.
