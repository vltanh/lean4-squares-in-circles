# A parallel bypass is impossible in every opposite-load four-cycle

**Status: complete uniform hand exclusion; root and separate independent
full hand audits passed.** Work in the common selected physical
certificate and radius window
\[
             \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
             \qquad d=\sqrt{R^2-\frac14}-1.
\tag{1}
\]
Suppose the positive graph contains the four-cycle
\[
                         H-A-U-C-H,
\]
where A,C have exact positive degree two and positive circle load,
and U has exact positive degree two and zero circle load. The unit H
may have arbitrary additional positive neighbors and forces. If H is
parallel to U, this entire family can be excluded by one compatible
pre-certificate normal selection.

Every physical circle mask, individual zero corner weight and genuine
shared-side application mean is retained. In particular H is not
assumed to have a radial leaf, to meet a small disk about the origin,
or to satisfy a degree-two force equation. All other packing squares
remain unchanged.

## 1. The complete parallel-frame domain

UNIT_BYPASS_NORMAL_CHANNEL.md makes U a side-normal transmitter of
reserve one and separates H,U transversely. Since their frames are
parallel and H's channel projection contains U's unit projection,
those projections coincide. Rotate and reflect about the circle
origin so that
\[
 \begin{split}
 H&=[X,X+1]\times[Y,Y+1],\\
 U&=[X-g-1,X-g]\times[Y,Y+1],\qquad g\ge0,\\
 A&\subseteq\{y\le Y\},\qquad
 C\subseteq\{y\ge Y+1\}.
 \end{split}
\tag{2}
\]
The two genuine channel applications have the same first coordinate
x and the same positive magnitude \(\gamma\), by U's torque and force
equations. No application is replaced by a midpoint.

If A were oblique to U, its unique top vertex p would be its only
possible contact with both U and H. Thus
\[
                         X\le p_x\le X-g.
\]
This forces g=0 and p=(X,Y), also a vertex of U. The vertical channel
normal is a U side axis, so it does not strictly expose U's vertex at
this point-only vertex/vertex contact. That violates the common strict
selection. Therefore A is parallel to U. Reflection gives the same
conclusion for C.

Both AU and UC have positive shared length: a point-only aligned
vertex contact cannot carry their side-axis channel normal. Since A
touches U, the left endpoint of its top side is strictly less than X.
Its H contact is consequently either a positive horizontal shared
segment, or the sole point (X,Y), in which case
\[
                         A=[X-1,X]\times[Y-1,Y].
\tag{3}
\]
The corresponding alternatives for C are a positive shared segment
with H, or the sole point (X,Y+1), in which case
\[
                         C=[X-1,X]\times[Y+1,Y+2].
\tag{4}
\]
These are all physical H interfaces, including every actual mean.

## 2. One shared H interface already forces the other tip clear

Suppose HA is shared; vertical reflection handles HC instead. Both
pair forces on A point downward. Its actual circle resultant is
therefore vertical downward. The parallel-force radial classification,
with A's physical frame already fixed, gives
\[
               A=[-1/2,1/2]\times[-d-1,-d],\qquad Y=-d.
\tag{5}
\]
The two physical circle weights are equal and positive as a consequence
of the genuine force equation. Their equality is not an extra mask
assumption. If HC were also shared, C would similarly be the upward
radial S square, giving Y+1=d and hence 2d=1, impossible since d>9/10.

Thus HC is point-only and (4) becomes
\[
                         C=[X-1,X]\times[1-d,2-d].
\tag{6}
\]
Positive AU overlap gives X-g>-1/2 and hence X>-1/2. Positive AH
overlap gives X<1/2. Consequently
\[
                 -\frac12<X<\frac12,\qquad
                 \max_{z\in C}|z|^2
                    <\frac94+(2-d)^2
                    <\frac94+\frac{121}{100}
                    =\frac{173}{50}<\frac{15}{4}<R^2.
\tag{7}
\]
Here 9/10<d<61/60 implies that 2-d is the largest absolute vertical
endpoint in (6). This contradicts the positive circle load of C.
Every actual shared mean survived this geometric argument. Neither
shared H interface is possible.

## 3. Two point interfaces force the exact two unique circle corners

We are left with (3)--(4). Write
\[
              f(X)=\max(|X-1|,|X|),\qquad
              h(t)=\max(|t-1/2|,|t+1/2|)=|t|+1/2.
\]
Equality of the two maximum corner radii gives
\[
                   |Y-1/2|=|Y+3/2|,
                   \qquad Y=-1/2.
\tag{8}
\]
Put
\[
                  m=\sqrt{R^2-\frac94}.
\tag{9}
\]
Then f(X)=m. The radius window gives
\[
                      \frac54<m<\frac32.
\tag{10}
\]
If X>=1/2, then f(X)=X=m. But H contains a point of first coordinate
X+1=m+1>R, because
\[
                  m^2-(R-1)^2=2R-\frac{13}{4}>0.
\]
This contradicts H's containment. Therefore
\[
                 X=1-m<0,
                 \quad z_A=(-m,-3/2),\quad z_C=(-m,3/2).
\tag{11}
\]
Both tips have exactly one physical circle corner. This conclusion
was derived from their entire physical masks, not postulated.

## 4. The actual channel means force equal circle scales

The two actual H applications are
\[
                    P_A=(X,-1/2),\qquad P_C=(X,1/2).
\]
Their freely selectable strict point normals, directed out of H, have
the forms
\[
               n_A=(-a,-b),\qquad n_C=(-c,e),
               \qquad a,b,c,e>0.
\tag{12}
\]
Let their positive magnitudes be \(\mu,\nu\), and write the true circle
forces as \(k_Az_A,k_Cz_C\), with k_A,k_C>0. The common channel
applications are (x,-1/2) and (x,1/2). Set u=X-x; the physical interval
gives 0<=u<=1. The exact lower force equation is
\[
                       k_Az_A=\mu n_A-\gamma e_y.
\]
Taking its origin moment at the genuine application P_A and using
the lower torque equation yields
\[
                 \gamma u=k_A(3/2-m).
\tag{13}
\]
For example,
\(\det(P_A,z_A)=m-3/2\), and
\(0=\det(P_A,k_Az_A)+\gamma(X-x)\).
The reflected upper calculation gives
\[
                 \gamma u=k_C(3/2-m).
\tag{14}
\]
Since m<3/2, these equations force u>0 and k_A=k_C=:k. They use
neither a force equation at H nor any resultant direction of H's
other neighbors.

The two exact tip force equations now give
\[
                 \mu a=km=\nu c,\qquad
                 \mu b=\frac32k-\gamma=\nu e.
\tag{15}
\]
Hence a necessary condition for this positive four-cycle is
\[
                              bc-ae=0.
\tag{16}
\]

## 5. One simultaneous selection and the complete conclusion

Prelist every physical assignment of H,A,U,C with the stated actual
degrees and loads, every possible transmitter axis and the complete
parallel-frame alternatives. Sections 1--3 either exclude the candidate
or fix (11). For the last candidate the two point contacts are at
distinct physical junctions, separated vertically by one. Their strict
normal parameters vary independently through nonempty open intervals.
The bad equation (16) has empty interior on their product. Choose
the normals outside its zero set, together with all previous finite
open-dense conditions before applying the physical multiplier theorem.

At a four-square junction keep the already required matched opposite-pair
parameter; this does not couple the two distinct junctions in (12).
The exact choices are prelisted before multipliers, without freezing a
shared mean. Uncrossing preserves a surviving point normal and adds
only physical shared interfaces already covered by Section 2. Thinning
only deletes atoms. Thus every possible final candidate remains within
the complete cover above.

The parallel H/U family is impossible in this common selected
certificate. This theorem is uniform in every additional force at H
and every other physical square. In particular it excludes the entire
parallel-bypass part of C2.34.b0's opposite-load AC orbit, with the
actual attached triangle and all three extra units retained.

The oblique H/U domain remains outside this theorem. No complete AC,
C4-attachment, C2.34.b0, or unrestricted radius closure is asserted here.
No Lean compilation, CI, numerical sample or completion motion is used.
