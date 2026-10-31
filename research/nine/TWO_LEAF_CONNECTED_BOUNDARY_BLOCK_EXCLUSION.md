# One cone obstruction excludes both SS and SD connected boundary blocks

**Status: complete hand theorem; independent full-source and direct-
dependency review accepted October 27, 2026.** See
REVIEW_TWO_LEAF_CONNECTED_BOUNDARY_2026_10_27.md. Its named diamond
applications were already closed by the stronger block-pressure theorem;
this alternative proof changes no original checkbox or coarse-cell count.

Pinned prerequisites: `4c8584155ba0b4f5a59375d7140e3a38f95eecfa`.
This manuscript does not use the new high-radius triangle-tip proof, either
parallel-HK exclusion, any Bernstein table, or an equation at a designated
boundary-block body.

Work with the original nine independently oriented physical unit squares,
the common selected necessary certificate, and

\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-1/4}-1,\qquad r=R-\sqrt2.
\tag{1}
\]

## 1. Uniform theorem and exact hypotheses

Let H be a body of one positive component. Suppose L1,L2 are two
distinct genuine positive leaves at H, with **at least one of type S**.
Label an S leaf L1. The other leaf may be S or D. Their unchanged radial
circle resultants are

\[
                  F_i=\lambda_i e_i,\qquad\lambda_i>0.
\tag{2}
\]

For an S leaf the actual unit and radial application are
\([d,d+1]e_i+[-1/2,1/2]Je_i\) and \(p_i=d e_i\), with
\(h_H(e_i)=d\). For a D leaf its unique outer and inner vertices are
\(R e_i\) and \(r e_i\), and the original selected leaf theorem makes
\(e_i\) an H side axis with \(h_H(e_i)=r\).

The actual leaf moment fixes each radial application; none is a freely
chosen midpoint. A genuine S leaf has equal positive circle weights by its
own degree-one equation. No equal-weight premise is imposed on any other
radial body.

Assume there is a connected **physical-contact graph** K, excluding L1,L2,
whose vertices are physical circle-touching neighbors of H, and which
contains every other positively circle-loaded body of the component.
K may include zero-circle-load boundary bodies. Its edges and its contacts
with H may have zero stress. H and every member of K retain all their
actual positive degrees, all selected normals and all original means.

**Theorem.** Such a positive component is impossible throughout (1).
The other physical squares, including every completion square, remain
arbitrary and unmoved.

The two ingredients are a physical support estimate for H and the existing
sign-propagation statement for connected boundary neighbors of the S leaf. Their combination
uses only the genuine whole-component force sum.

## 2. One support bound for the entire opposite cone

Define

\[
 \mathcal C_- =\{-\alpha e_1-\beta e_2:\alpha,\beta\ge0\}.
\]

**Support lemma.** The two distinct directions are not antipodal. For every
unit vector w in the closed cone \(\mathcal C_-\),

\[
                         h_H(w)<14/25<r.
\tag{3}
\]

The complete radial-support classification is
TRIANGLE_THREE_BRIDGES_DOUBLE_LEAF_ROOT_EXCLUSION.md, Sections 1.1--1.2.
It concerns the two original radial points, permits every original
side-mean endpoint, and uses no equation at another neighbor of H.
Up to an orthogonal transformation and exchange of leaf labels as indicated,
the four SS rows and three SD rows below are exhaustive. They are continuous
geometric types, not sampled configurations. All inequalities are given here.

First record the strict whole-window bounds

\[
 91/100<d<61/60,\qquad r>14/25.
\tag{4}
\]

For the lower d bound, square \(\sqrt{R^2-1/4}>191/100\) at
R=79/40. For the upper one, square
\(\sqrt{R^2-1/4}<121/60\) at the upper endpoint in (1).
For r use \(\sqrt2<283/200\) and
\(79/40-283/200=14/25\).

### 2.1. SS: two adjacent side applications

Here \(d\le1\),

\[
 H=[d-1,d]^2,\qquad e_1=(1,0),\qquad e_2=(0,1).
\]

Every w in the opposite cone has both coordinates nonpositive. Thus

\[
 h_H(w)=(1-d)(|w_x|+|w_y|)
       \le\sqrt2(1-d)<\sqrt2/10<14/25.
\]

This includes d=1 and the actual origin-vertex endpoint.

### 2.2. SS: one side and one distinct vertex application

Here \(d\le1\), and, writing \(Y=\sqrt{2d-1}\),

\[
 H=[d-1,d]\times[Y-1,Y],\quad
 e_1=(1,0),\quad e_2=(d-1,Y)/d.
\]

One has \(Y>8/9\), \(0\le1-d<1/10\), and \(0\le1-Y<1/9\).
Every w in the opposite cone satisfies

\[
 w_y\le0,\qquad w_x\le\frac{1-d}{Y}(-w_y).
\tag{5}
\]

When \(w_x\le0\), Cauchy--Schwarz gives

\[
 h_H(w)=(1-d)|w_x|+(1-Y)|w_y|
       <\sqrt{1/100+1/81}<1/4.
\]

When \(w_x\ge0\), (5) and \(d\le1\) give

\[
 h_H(w)\le\left(\frac{d(1-d)}Y+1-Y\right)(-w_y)
       <9/80+1/9=161/720<1/4.
\]

The cone boundary and d=1 are included. Both bounds are below 14/25.

### 2.3. SS: two adjacent vertex applications

Here

\[
 H=[a-1,a]\times[-1/2,1/2],\qquad
 a=\sqrt{d^2-1/4},\qquad e_1=(a,-1/2)/d,\quad e_2=(a,1/2)/d.
\]

The complete window (4) implies \(3/4<a<1\). Every vector of the
opposite cone has nonpositive first coordinate. In fact the following
bound holds on that entire closed half-plane, not just the cone:

\[
 h_H(w)=(1-a)(-w_x)+|w_y|/2
       \le\sqrt{(1-a)^2+1/4}<\sqrt5/4<14/25.
\tag{6}
\]

The last squared reserve is
\(196/625-5/16=11/10000>0\).
This row includes every d>1 possibility as well as its low-radius part.

### 2.4. SS: two opposite vertex applications

Here put \(c=1/\sqrt2\), \(b=\sqrt{d^2-1/2}\). The actual body and
leaf directions are

\[
 H=\{(X,Y):|X|+|Y-b|\le c\},\qquad
 e_1=(c,b)/d,\qquad e_2=(-c,b)/d,
\]

with \(d\le1\), \(11/20<b\le c<3/4\). A unit vector in the
opposite cone satisfies

\[
 v=-w_y>0,\qquad z=|w_x|\le(c/b)v,\qquad v^2+z^2=1.
\]

The support is exactly

\[
                         h_H(w)=-bv+c\max\{z,v\}.
\]

If \(z\le v\), this is at most \(c-b<1/5\).
If \(z\ge v\), it is at most

\[
 \frac{c^2-b^2}{b}v=\frac{1-d^2}{b}v
       <\frac{19/100}{11/20}=19/55<14/25.
\]

The endpoint d=1 gives a zero numerator and remains included.

### 2.5. SD: complete root form and a coupled radius inequality

For the SD calculation, rotate the D direction east and reflect vertically
so the S direction has positive second coordinate. This is a coordinate
choice, not an exchange of the physical leaf types. Put \(s=1-r\).
The full D-root theorem gives

\[
 H=[-s,r]\times[Y-1,Y],\qquad 0<Y<1,
 \qquad 14/25<r<7/10,
 \qquad 0<s<11/25.
\tag{SD1}
\]

The S radial support point must be either on the top support side,
or the top-right vertex, or the top-left vertex. The east/west side
alternatives would require \(d=r\) or \(d=s\), both impossible from the
bounds above. The bottom possibilities are their reflected versions.
This is the complete Section 1.1 radial-support cover, also valid below
d=1. The three top alternatives have respectively

\[
 (Y,e_S)=(d,(0,1)),\quad
 (\sqrt{d^2-r^2},(r,Y)/d),\quad
 (\sqrt{d^2-s^2},(-s,Y)/d).
\tag{SD2}
\]

For the right-vertex row we need the coupled, full-window estimate

\[
                             d^2-r^2>1/2.
\tag{SD3}
\]

Indeed the left side is

\[
 f(R)=-5/4+2\sqrt2R-2\sqrt{R^2-1/4},
 \qquad f'(R)=2\sqrt2-\frac{2R}{\sqrt{R^2-1/4}}>0,
\]

where the derivative sign follows by squaring from \(R^2>1/2\).
At the lower endpoint use \(\sqrt2>24/17\) and
\(\sqrt{(79/40)^2-1/4}<153/80\). This gives

\[
 f(79/40)>-5/4+(79/20)(24/17)-153/40
         =341/680=1/2+1/680.
\]

Thus (SD3) is a single monotonicity argument on the entire original window,
not separate bounds treating d and r as independent variables.

### 2.6. SD: the top side and top-right vertex

For the S top-side row, \(Y=d\le1\). Both components of a vector w in
the opposite cone are nonpositive, and

\[
 h_H(w)=s|w_x|+(1-d)|w_y|
       <\sqrt{(11/25)^2+(1/10)^2}<1/2<14/25.
\]

For the S top-right vertex, (SD3) gives \(Y>1/\sqrt2>7/10\).
The opposite cone is contained in the southwest quadrant, so

\[
 h_H(w)=s|w_x|+(1-Y)|w_y|
       <\sqrt{(11/25)^2+(3/10)^2}
       =\sqrt{709}/50<14/25.
\tag{SD4}
\]

The squared reserve in (SD4) is exactly \(3/100>0\).

### 2.7. SD: the top-left vertex, including the southeast part of the cone

Now \(Y=\sqrt{d^2-s^2}>7/9\), since
\((91/100)^2-(11/25)^2>(7/9)^2\).
Every w in the opposite cone satisfies

\[
                     w_y\le0,\qquad
                     w_x\le(s/Y)(-w_y).
\]

For \(w_x\le0\),

\[
 h_H(w)=s|w_x|+(1-Y)|w_y|
       <\sqrt{(11/25)^2+(2/9)^2}<1/2<14/25.
\]

For \(w_x\ge0\), use \(rs\le1/4\), which follows from r+s=1:

\[
 h_H(w)\le\{rs/Y+1-Y\}(-w_y)
       <9/28+2/9=137/252<14/25.
\tag{SD5}
\]

The last reserve is \(103/6300>0\). Thus the entire cone, not only
its southwest part, satisfies the same support bound.

In every SS row the directions are distinct and lie in an open semicircle:
the opposite-vertex row has b>0, the adjacent-vertex row has a>0, and the
side rows are immediate. Every SD row has an east D direction and an S
direction with Y>0. Hence no pair is antipodal. Sections 2.1--2.7 establish
(3) for the full SS and SD domains, including d=1 and every mean endpoint.

## 3. No circle corner of a neighbor can lie in the opposite cone

Let B be any original unit touching H, let p be any point of its physical
intersection with H, and let z be any physical circle corner of B.
If z belonged to \(\mathcal C_-\), put \(w=z/R\). Then (3) gives

\[
 \sqrt2\ \ge |z-p|\ \ge w\cdot(z-p)
 =R-w\cdot p\ \ge R-h_H(w)\ >R-r=\sqrt2.
\tag{7}
\]

The first bound is the diameter of the actual unit B. This contradiction
is independent of B's frame, loads, positive degree, contact owner and
mean. It covers both physical circle masks and every individual zero
weight. In particular **no physical circle corner of any neighbor of H
lies in the closed opposite cone**.

## 4. One S-leaf sign propagation contradicts the entire force sum

Sections 1--2 of S_LEAF_CONNECTED_BOUNDARY_NEIGHBORS.md prove the following
geometric statement before that source uses any component force equation:

> For a genuine radial S leaf with direction e and root H, every connected
> physical-contact graph of circle-touching neighbors of H, excluding the
> leaf, has all its physical circle corners on the same strict side of the
> line through O parallel to e.

In particular the sign of \(\det(e,z)\) is nonzero and constant over all
those corners. This includes zero-circle-load vertices and unequal radial
weights; it does not require every member of that graph to be a positive
neighbor of H. Rotating or reflecting the geometric statement changes no
physical unit, selected normal or original application.

Apply this statement **only to the S leaf L1**, with direction e1. No
analogous statement for a D leaf is assumed. Let M be the sum of all the
original component circle forces other than those of L1,L2. H is
circle-clear by the genuine leaf/root theorem. The sum of all true
component force equations gives

\[
                  M=-\lambda_1e_1-\lambda_2e_2.
\tag{8}
\]

If there were no other positive circle load, (8) would already contradict
non-antipodality. Otherwise K contains at least one positive circle atom.
Choose coordinates, reflecting if needed, so that e1,e2 have directions
0 and \(\theta\in(0,\pi)\). The S leaf remains L1. Equation (8) gives

\[
 \det(e_1,M)=-\lambda_2\sin\theta<0,\qquad
 \det(e_2,M)=\lambda_1\sin\theta>0.
\tag{9}
\]

By S-leaf sign propagation, every physical circle corner z of K satisfies
\(\det(e_1,z)<0\), so its direction is in \((\pi,2\pi)\).
Section 3 excludes the entire closed opposite sector
\([\pi,\pi+\theta]\). Therefore every such corner has direction
\((\pi+\theta,2\pi)\), and consequently

\[
                              \det(e_2,z)<0.
\tag{10}
\]

All nonleaf positive atoms are in K, so their positive weighted sum has
\(\det(e_2,M)<0\). This contradicts (9). The argument applies unchanged
when L2 is S or D, and proves the theorem on the whole closed interval (1).

No local pair force was discarded. No result for an isolated smaller
component was imposed on a larger-degree body. The only force operation
was the sum over all original bodies in the actual component.

## 5. Several complete original families follow at once

### 5.1. The entire SS and SD diamond-hub families

Take the positive diamond HK,HA,HB,KA,KB and two genuine leaves at H,
at least one S.
A and B are loaded by their true degree-two triangle-tip equations. K is
loaded by NO_UNLOADED_DIAMOND_HUB.md: its true three neighbors are H,A,B,
and H physically touches both A and B. Thus A--K--B is a connected physical
graph of circle-touching neighbors of H containing all other loads.
The theorem excludes the **entire** family, for every one-/two-corner mask at K,A,B,
every original weight and mean, all HK owners, and the full radius window.
H keeps degree five and K degree three. All three extra squares remain.

This covers both whole existing gates
`M6.B4L2.DIAMOND.SAME_HUB.LKBC.SS` and
`M6.B4L2.DIAMOND.SAME_HUB.LKBC.SD` (with tip names B,C in those gates).
It is not merely its high-radius or parallel-HK subset.

### 5.2. Every same-root path fan with SS or SD leaves

Let H be positively joined to all k bodies of a positive path
V1--V2--...--Vk, and also to two genuine leaves of types SS or SD.
There are no other positive edges, and \(2\le k\le6\), so the component has \(k+3\le9\) bodies.
H has its genuine degree k+2.

The two path endpoints have true degree two and physically touching
neighbors, hence are loaded. Each inner path body has true degree three;
its neighbor H touches both its other neighbors, so the same unloaded-hub
obstruction makes it loaded. The path is therefore a connected physical
graph of boundary neighbors of H containing every other load. The theorem
excludes all these components simultaneously.

The k=3 case gives both preceding diamond families. The k=4 and k=5 cases
give both full SS and SD seven- and eight-body families in C1.5.b2 and C1.6.b2, respectively, with
two and one arbitrary extras. The k=2 triangle case was already excluded;
k=6 also violates the established boundary-count restriction. These latter
two cases are not counted as new progress. Other rooted layouts in these
coarse parents remain open.

### 5.3. Physically chorded fully loaded C4 with SS or SD leaves

Take H--A--K--B--H with two genuine leaves of types SS or SD at H
and all three A,K,B positively circle-loaded. If the original packing has physical HK contact,
even with zero multiplier, the same graph A--K--B meets the theorem.
This excludes its whole physical-chord feature without altering true
H4/K2 degrees or introducing a positive HK edge. The physical-noncontact
C4 residue is not covered.

### 5.4. Degree-independent connected-block formulation

More generally, any selected component satisfying Section 1 is excluded,
regardless of its positive graph inside or outside K. A physical contact
used for connectivity need not carry a positive force. This includes
additional zero-weight boundary bodies joining the graph. Conversely,
a circle-loaded body outside K, a member of K not touching H, disconnected
loaded groups, or replacement of a genuine leaf by a formal aggregate
must not be silently admitted. Those are explicit remaining obligations.

## 6. Verification and accepted-roadmap status

The support estimates are elementary and table-free. The companion
TWO_LEAF_CONNECTED_BOUNDARY_CHECK.py verifies their exact rational endpoint
reserves with Python's standard-library Fraction type; it is not a proof of
the geometry or an independent reviewer. No numerical search or angle grid
is a premise. The earlier exploratory searches of low-radius triangle
coordinates played no role in this proof. The DD leaf assignment is not
covered: this proof deliberately requires an actual S leaf and its geometric
sign-propagation theorem.

Author checks cover all four SS and all three SD radial-support rows, the
coupled radius derivative, d=1, both physical masks,
zero atom weights, shared mean endpoints, the sign-propagation scope, and
the true-degree applications in Section 5. The independent full saved-source and direct-dependency review is now
accepted in REVIEW_TWO_LEAF_CONNECTED_BOUNDARY_2026_10_27.md. The named
diamond applications and DD sibling were already closed at the current
head by DIAMOND_ROOT_PRESSURE_AND_MIXED_BOUQUET_CLOSURE.md. Thus this
alternative theorem changes no original checkbox or coarse-cell count;
the earlier full global prerequisite-chain audit remains a separate gate. No Lean
compilation or CI was run. The unrestricted theorem and original equality
classification remain open.

