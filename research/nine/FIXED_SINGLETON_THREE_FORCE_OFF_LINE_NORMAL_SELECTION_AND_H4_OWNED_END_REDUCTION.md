# Compatible off-line selection at three fixed singleton ports and the H4 owned-end residue

Date: October 28, 2026.

**Status: complete proposed pre-extraction normal-selection theorem and
necessary-domain join, frozen for full independent and root review.**
This is an existence statement for the common selected physical
certificate. It is not an impossibility claim for every arbitrary
choice of point normals after an equilibrium has been extracted.
No complete original H4 family is closed.

The geometric H4 reduction used below is selection-free and remains
unchanged. The present source is the explicit additional compatible
preselection step needed to strengthen its remaining two-return owner
cover. It keeps every actual square, contact, frame and application.

## 1. A general fixed-port selection rule

Fix the actual physical packing before choosing free vertex/vertex
normals or obtaining multipliers. Consider an ordered physical
quadruple U,V0,V1,V2 for which all three U contacts are actual
singletons at the fixed points P0,P1,P2. Suppose:

1. The normal n0 from U to V0 is geometrically fixed, independently
   of the free normal parameters at the other contacts.
2. Both P1 and P2 lie off the line P0+R*n0.
3. Whenever a contact UVi, i=1,2, is a free vertex/vertex contact,
   its allowed strict normal interval is parametrized at its
   own contact point. P0,P1,P2 are distinct; in particular the
   two possible free parameters are not identified by the
   four-square junction matching rule.

All these predicates concern actual physical singletons, contact
features, frames and a fixed axis. None concerns an unknown
multiplier, load, true positive degree, circle-weight split or
shared-side application mean.

**General selection theorem.** The common compatible physical
certificate can be selected so that no unloaded true positive
degree-three U with exactly the three positive neighbors V0,V1,V2
can realize such a prelisted pattern if either UVi, i=1,2, is free.

The theorem permits arbitrary original degrees, loads and physical
circle masks at all three neighbors. Additional zero-weight
physical contacts at U remain. It makes no assertion at a loaded
U, at a higher-degree U, or when a contact application is a
variable shared-side mean.

## 2. The full force-and-moment determinant

Translate only the coordinate origin of this local calculation to
P0. Do not move the physical packing or its circle. For a unit
direction n at the fixed point Pi define the three-coordinate vector

\[
                   w_i(n)=(n_x,n_y,P_i\times n),                 \tag{1}
\]

where the translated P0 is zero. The original full force and torque
equations of an unloaded U3 are exactly

\[
        \mu_0 w_0(n_0)+\mu_1 w_1(n_1)+\mu_2 w_2(n_2)=0,
                  \qquad \mu_0,\mu_1,\mu_2>0.                   \tag{2}
\]

The torque equation about P0 is equivalent to the original torque
equation because the full force sum is zero. No force has been
discarded. The positive numbers in (2) are the original unit-normal
magnitudes; no sign, scale or circle coefficient is changed.

Consequently a necessary condition is

\[
                         \det(w_0,w_1,w_2)=0.                   \tag{3}
\]

Suppose first that the contact at P1 is free. Its possible vectors
fill an open circular arc in the two-dimensional linear plane

\[
          W_1=\{(v_x,v_y,P_1\times v):v\in\mathbb R^2\}.          \tag{4}
\]

The fixed vector \(w_0=(n_0,0)\) does not lie in W1: membership
would say \(P_1\times n_0=0\), contrary to the off-line premise.

For every fixed nonzero n2, the vectors w0 and w2 are independent.
Indeed \(w_2=\lambda w_0\) would give \(n_2=\lambda n_0\) with
\(\lambda\ne0\), and then
\(0=P_2\times n_2=\lambda(P_2\times n_0)\), again contrary to the
off-line premise.

The plane spanned by w0,w2 is therefore two-dimensional and cannot
equal W1, since it contains w0. Hence (3), as a linear functional
of \(w_1\in W_1\), is nonzero. On the free unit-normal interval it
has the form

\[
                            A\cos\theta+B\sin\theta
\]

with \((A,B)\ne(0,0)\). It vanishes at at most two directions on
the full unit circle, and cannot vanish on any allowed open
strict interval.

The argument for a free P2 is identical, interchanging indices.
If both return contacts are free, fix any allowed n2 and vary n1.
The preceding proof still applies. Thus the determinant is not
identically zero on their full independent product of strict
normal intervals. No eventual force magnitude enters this
nonidentity proof.

## 3. One finite selection before extracting any certificate

For the fixed physical packing, prelist all ordered quadruples
and fixed singleton patterns satisfying Section 1, regardless of
which edges will later have positive multipliers or which units
will eventually be unloaded. There are only finitely many actual
units, contacts and feature choices. Include (3) as a forbidden
condition for each prelisted pattern having at least one free
return contact.

The compatible strict point-normal domain is the one already
used by PHYSICAL_BODY_GRAPH_UNCROSSING.md. At a four-square
junction an opposite-pair parameter is matched with the other
opposite pair at that same point. Distinct singleton points
P0,P1,P2 cannot share that junction parameter. Matching may
simultaneously determine the normal of a different edge at
Pi, but does not remove the open interval at Pi or identify
it with a parameter at another contact point.

Each determinant condition is a proper real-analytic zero set
in this common allowed parameter domain, by Section 2. More
explicitly, after fixing every other parameter, varying the
designated free return parameter leaves a nonzero sine-cosine
expression on every allowed open subinterval. Its complement
is open dense. A finite intersection with the other already
proved compatible strict, matched, nonradial and generic
conditions is therefore still open dense and nonempty.

Choose the free point normals once in that intersection, then
apply the existing physical branch and multiplier theorem.
This order matters: no normal of an already extracted
equilibrium is changed. The new determinant conditions depend
on no unknown mean or multiplier and so are legitimate
conditions at this pre-extraction stage.

The existing planar uncrossing preserves surviving point
normals and adds only actual shared-side forces. A contact in
the present prelist is physically a singleton and cannot turn
into a positive-length shared side under that operation.
Thinning only deletes atoms; it does not change the surviving
singleton application or its selected normal. Consequently
every final unloaded positive U3 matching a prelisted
singleton pattern still has exactly the columns in (3).
Its full equilibrium (2) contradicts the selected nonzero
determinant whenever either return contact was free.

This proves the general selection theorem. An arbitrary
positive equilibrium outside this selected domain is not
claimed impossible by this argument.

## 4. Literal application to the H-owned unloaded H4 end

Retain the original six-body contacts

    HA, HB, HC, HD, AB, BC, CD, DE, EA,

the full unloaded H4 and unloaded D3, and all original degrees
and loads at A,B,C,E. Assume H owns its normal toward D.
The complete selection-free source

    INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md

at SHA256
bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c
proves the entire necessary domain

\[
\begin{gathered}
H=[0,1]^2,\quad P=(p,1),\quad 0<p<1,\\
D=P+[0,1]u+[0,1]v,\quad
u=(a,b),\quad v=(-b,a),\quad a,b>0,\quad a^2+b^2=1,\\
D\cap H=\{P\},\qquad
D\cap C=\{P+u\},\qquad D\cap E=\{P+v\}.                         \tag{5}
\end{gathered}
\]

All CD-owned-at-D, DE-owned-at-D, shared-side and other vertex
alternatives have been excluded by that geometric source using
their complete original means and forces. They are not silently
omitted in order to apply the present selector.

In the D frame the fixed D-to-H unit normal is

\[
                        n_0=(-b,-a).
\]

The three fixed points are \(P_0=(0,0)\), \(P_1=(1,0)\),
\(P_2=(0,1)\). The exact off-line tests are

\[
                   P_1\times n_0=-a\ne0,\qquad
                   P_2\times n_0=b\ne0.                         \tag{6}
\]

The first normal is geometrically fixed by the actual H-side
interior contact in (5); it is not another free parameter.
The two return points are distinct opposite D vertices, so
any matched junction parameters there are independent.

For complete transparency, the same nonidentity proof here
can be read directly in the three-coordinate vectors:

\[
 w_0=(-b,-a,0),\quad
 w_C=(x,y,y),\quad
 w_E=(z,t,-z).
\]

The free-C plane is torque=y and does not contain w0 because
a>0. The free-E plane is torque=-x and does not contain w0
because b>0. The other two columns are independent in each
case, exactly as proved in Section 2. No positive-force
normalization or determinant coefficient is being inferred
from a partially solved stress.

The general prelist can include these physical quadruples
(D,H,C,E) before any H4 or D3 positive degree is known. If
a final selected certificate later falls in the H4 domain,
the selection-free reduction proves (5), so it was one of
those prelisted fixed physical patterns. There is no
post-extraction choice of a new prelist.

Therefore the entire remaining H-owned-HD interface of the
common selected certificate satisfies

\[
                \boxed{\text{CD is C-owned and DE is E-owned.}} \tag{7}
\]

Indeed the reduction already makes both original normals
strict at their D vertices. A nonfree singleton normal
cannot then be D-owned; it must be the other unit's own
side axis. Under the strict singleton convention its
application is relative-interior on that actual external
side. A side endpoint would be a point-only vertex/vertex
contact, whose permitted normal strictly exposes both
vertices and is precisely the free alternative just removed.

Thus there are actual external tangent parameters
\(\ell_C,\ell_E\in(-1,0)\) such that, for the unchanged unit
normals \(n_C,n_E\) from D and a chosen ninety-degree rotation J,

\[
\begin{aligned}
 C&=P+u+[0,1]n_C+[\ell_C,\ell_C+1]Jn_C,\\
 E&=P+v+[0,1]n_E+[\ell_E,\ell_E+1]Jn_E.                         \tag{8}
\end{aligned}
\]

Choosing the signs of the tangent axes merely changes the
names of these two full intervals; it changes neither unit
nor contact application. Both intervals and all external
force equations remain.

## 5. Exact surviving force table and original-family scope

The full original D3 force and moment equations from the
selection-free source remain, with actual \(\gamma,\eta>0\):

\[
\begin{array}{c|c}
\text{neighbor}&\text{D-frame force vector}\\ \hline
H&(-\gamma b,-\gamma a)\\
C&(\eta+\gamma b,-\eta)\\
E&(-\eta,\gamma a+\eta).
\end{array}
\]

Conclusion (7) now fixes the external side frames to these
actual directions, without replacing either tangential
interval in (8). The whole H4 force and torque, the original
loaded E2 equation, the remaining physical rim contacts and
every circle coefficient are still required to close the
domain. No two-force equation is assigned to C or D.

For each original load representative H4_D0.L124 and
H4_D0.L0124 use \((A,B,C,D,E)=(0,1,2,3,4)\), retaining all
nine actual packing units. This source removes the free-CD
or free-DE alternatives in the H-owned H-to-3 interface of
the common selected certificate. In L124 the graph-preserving
reflection also gives the corresponding statement at its
other unloaded end when that end normal is H-owned. In
L0124 it does not assign an unloaded equation to the loaded
end 0.

The non-H-owned end domains and the full external-owned
residue (5)--(8) remain. No whole original fine family,
graph parent or coarse cell is declared closed.

## 6. Exact operative inputs and limits

| Source | SHA256 | Use |
| --- | --- | --- |
| INNER_PENTAGON_H_OWNED_UNLOADED_END_FIXED_OPPOSITE_RETURN_VERTICES.md | bc1b08bc93401e25891f1307139c465409e4a3e260670513087b658c210e0f8c | Complete selection-free H-owned-end physical reduction, all original shared means excluded before the selector |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Allowed strict normals, matched four-square parameters, common physical certificate and preserved point normals under uncrossing |
| PHYSICAL_CONTACT_STRESS.md | d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5 | Physical branch before multipliers and the full unchanged force/torque equations |

The determinant proof is complete in this source. It does
not import the historical diamond selector or its old
generic-selection premise; the selection-free diamond
replacement remains independently valid.

There is no change to an already selected normal or force,
no unknown-mean predicate, no movement of the packing,
no numerical pose or angle mesh, no Lean run or CI, and
no ledger or metadata edit. This manuscript records one
explicit compatible extension of the necessary common
certificate and its exact limited original-family use.

