# A side-normal S arm cannot feed an adjacent-loaded C4

**Status: accepted complete hand argument after independent full source
and dependency review in REVIEW_SIDE_S_ARM_ADJACENT_C4_2026_10_25.md.**
Use the common selected physical certificate and the full radius window
\[
              79/40\le R\le\sqrt{1105}/16.
\]
Let the exact six-body positive component be
\[
                  A-B-C-D-A,\qquad A-U-L,
\]
where \(L\) is a genuine radial S leaf, \(U\) is its true unloaded
side-normal transmitter, and exactly \(B,C\) among the block vertices
are positively circle-loaded. Thus \(A\) has true degree three;
\(B,C,D,U\) have true degree two; \(L\) has true degree one.
Every physical mask, individual zero corner weight, original positive
force, shared application mean and all three completion squares remain.

**Theorem.** This entire component is impossible. Consequently the
existing full gate **M6.B4L2.C4.CHAIN.LBC.S_SIDE** is closed after
independent review. The reflected block-load set
\(CD\) is included by the original attachment symmetry. No new gate
or computational certificate is introduced.

## 1. Two actual channels and the sharp center bound

Put
\[
 T=\sqrt{R^2-1/4},\qquad d=T-1,\qquad\delta=d-1.
\]
Rotate the genuine radial leaf direction to the unit vector \(e\).
The complete leaf and arm formulas in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md and
FOUR_BODY_BLOCK_TWO_BRIDGES_LOAD_COVER.md give
\[
 L=[d,d+1]e+[-1/2,1/2]Je,
 \qquad p_{AU}=\delta e,
 \qquad A\subseteq\{x:e\cdot x\le\delta\}.
 \tag{1}
\]
The application in (1) is the actual mean on \(AU\). No application
has been replaced by a midpoint.

The other unloaded body \(D\) is a true degree-two transmitter
between \(A,C\). Its physical unit bypass is \(B\), so
UNIT_BYPASS_NORMAL_CHANNEL.md gives actual reserve one. There
are a unit vector \(n\), actual endpoint applications \(p_A,p_C\),
and support value \(\alpha\), with
\[
 p_C-p_A=n,\qquad
 A\subseteq\{x:n\cdot x\le\alpha\},\qquad
 C\subseteq\{x:n\cdot x\ge\alpha+1\}.
 \tag{2}
\]
In particular \(n\cdot p_A=\alpha\). No degree-two equation is
assigned to \(A\).

For every contained unit square \(S\), the exact farthest-corner
bound gives
\[
 |c_S|\le d+1/2.
 \tag{3}
\]
Its projection halfwidth in every unit direction is at least \(1/2\).
Applying both facts to \(C\) in (2) gives
\[
                 \alpha+3/2\le n\cdot c_C
                    \le |c_C|\le d+1/2,
 \qquad \alpha\le\delta.
 \tag{4}
\]

## 2. The entire lower radius interval forces a repeated physical leaf

Suppose \(\delta<0\). The real point \(\delta e\in A\) from
(1) yields
\[
             \alpha\ge\delta(n\cdot e)\ge\delta.
 \tag{5}
\]
Together with (4), all inequalities in (4)--(5) are equalities.
Since \(\delta<0\), equality in the second inequality of (5)
forces \(n\cdot e=1\), hence \(n=e\). The equalities in (4)
force
\[
           c_C=(d+1/2)e,\qquad H_C(e)=1/2.
 \tag{6}
\]
Here \(H_C(e)\) denotes the unit square's projection halfwidth.
For a square, halfwidth \(1/2\) occurs only at a side axis.
Equation (6) therefore determines the entire physical square:
\[
                    C=[d,d+1]e+[-1/2,1/2]Je=L.
 \tag{7}
\]
The two differently labeled physical units \(C,L\) would have the
same open interior. This is impossible. No load weight or force
magnitude equality was assumed.

## 3. The entire upper interval is the existing boundary-detour theorem

Suppose \(\delta\ge0\). Throughout the radius window,
\[
                         0\le\delta<1/60<1.
\]
A unit square containing a maximum-support point \(p\) in direction
\(e\) contains the inward normal segment
\(p-te\), \(0\le t\le1\).
This is the support-segment lemma in
RADIAL_BRIDGE_AND_LEAF_REDUCTION.md; it includes vertex
applications, side-interior applications and side endpoints.

Apply it at the genuine point \(p=\delta e\) in (1), with
\(t=\delta\). It follows that \(O\in A\). In particular
\[
              \operatorname{dist}(O,A)=0
                \le\max(\delta,0).
 \tag{8}
\]

The complete physical theorem
FOUR_CYCLE_ADJACENT_LOAD_EXCLUSION.md, Theorem 4.1, says that
a unit square satisfying (8) cannot be the initial endpoint of a
normal channel of reserve at least one whose other endpoint has a
common circle-touching unit neighbor. Its far endpoint need not
itself be loaded; its bypass needs only physical circle contact,
and all endpoint degrees are unrestricted.

Instantiate that theorem with the actual channel \(A-D-C\) in
(2) and the actual common neighbor \(B\). The positive edges \(AB\)
and \(BC\) are physical contacts, and \(B\)'s positive circle load
makes it physically circle-touching. The theorem gives a
contradiction.

This includes the critical value \(\delta=0\), without a limit,
motion, or deletion of a force. In particular it does not require
the arm at \(A\) to be a direct radial leaf.

## 4. Exact original-case impact and limits

The two intervals \(\delta<0\) and \(\delta\ge0\) exhaust
the original full gate **M6.B4L2.C4.CHAIN.LBC.S_SIDE**. The
original finite cover already includes the reflected \(CD\)
block-load set under this ID.

The proof does not close the S/diagonal or D/side arm alternatives,
the \(BD\) or \(BCD\) load sets, a whole C4-arm parent, or the entire
C1.4.b2 cell. All three other units stayed present; the argument
excludes the core itself and hence needs no separate completion
capacity bound.

The only arithmetic used is the established exact radius-window
bound and equality in the standard square-center estimate. No
orientation grid, polynomial certificate, Lean compilation, or CI
is used.

