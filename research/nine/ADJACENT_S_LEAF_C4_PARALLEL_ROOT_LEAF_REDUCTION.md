# Adjacent S leaves with parallel roots: the complete genuine-leaf cover

Status: complete original-domain reduction, awaiting independent review.
No whole high adjacent-C4 gate is claimed here. The remaining boundary
squares may be tilted, and retain their true degree-two equations.

Keep the exact strict-high unique/unique domain of
`ADJACENT_TWO_S_LEAF_C4_HIGH_DOMAIN_AND_SINGLE_CORNER_SELECTION.md`:
\[
 AB,BC,CD,DA,AL,BM,
 \qquad A3,B3,C2,D2,L1,M1,
\]
with both actual roots owning the original \(AB\) axis. All nine physical
units remain present. Put
\[
 d=1+\varepsilon,\quad0<\varepsilon<1/60,
 \qquad R^2=(2+\varepsilon)^2+1/4\le1105/256.
\]
Normalize the actual \(AB\) normal to east and its nonzero common cycle
moment to be positive. Thus
\[
 A_x=[h-1,h],\quad B_x=[h,h+1],\quad |h|\le\varepsilon,
 \qquad P_{AB}=(h,-k),\quad k>0.                   \tag{1}
\]
The mean in (1) may be any original side mean, including either endpoint.

## 1. A force-free height bound at a shallow vertical support

Let \(T\) be any actual physical boundary unit contained in the same disk,
with \(T\subseteq\{x\ge-\varepsilon\}\) and an actual point
\(Q=(-\varepsilon,y)\in T\), where \(y\ge0\). Then
\[
 y\ge\sqrt{13/4+6\varepsilon}-1>4/5.               \tag{2}
\]
There is no force, degree, mask or orientation hypothesis on \(T\).

If \(T\) owns the east axis, it is an actual axis-parallel unit with
x interval \([-\varepsilon,1-\varepsilon]\) and a unit y interval
containing \(y\). Every corner therefore satisfies
\[
 |Z|^2\le(1-\varepsilon)^2+(y+1)^2.                \tag{3}
\]
Otherwise \(Q\) is its minimum-x vertex and its full actual frame is
\[
 T=Q+[0,1](c,s)+[0,1](s,-c),
 \qquad c,s>0,\quad c^2+s^2=1.
\]
For its opposite corner,
\[
\begin{split}
 |Q+(c+s,s-c)|^2
 &=\varepsilon^2+y^2+2-2\varepsilon(c+s)+2y(s-c)\\
 &\le\varepsilon^2+y^2+2-2\varepsilon+2y
  =(1-\varepsilon)^2+(y+1)^2.
\end{split}
\]
Here \(c+s\ge1\), \(s-c\le1\), and \(y\ge0\). The two adjacent
corners have strictly smaller upper bounds: subtracting their squared
norms from the right side of (3) gives respectively
\[
 1-2\varepsilon(1-c)+2y(1-s)>0,
 \qquad1-2\varepsilon(1-s)+2y(1+c)>0.
\]
The same bound for \(Q\) is immediate. Thus (3) holds for every actual
corner in both cases. Since \(T\) is physically boundary,
\[
 (y+1)^2\ge R^2-(1-\varepsilon)^2=13/4+6\varepsilon>(9/5)^2,
\]
proving (2). Reflection gives exactly the same conclusion for an actual
boundary unit in \(x\le\varepsilon\) containing \((\varepsilon,y)\).
All side means and vertex/side endpoint limits are included.

## 2. The upper genuine-leaf features are excluded at both roots

Apply Sections 1--2 of
`ADJACENT_S_LEAF_C4_UPPER_AND_NEAR_SIDE_OWNER_LEAF_EXCLUSION.md`.
They exclude the upper-left genuine leaf at \(A\) with arbitrary actual
\(B\) frame, every side mean and every boundary mask. Their hypotheses
are exactly (1), the true adjacent-C4 component and the original common
positive cycle moment. The proof uses the original circle order
\(L,M,C,D\) and the broad force-free shallow-S screen; it does not need
a nonparallel force pair at \(B\).

An east own-axis leaf at \(A\) would require \(h=d\), which is impossible.
A north own-axis leaf puts \(A\) entirely above height \(\varepsilon\),
contradicting \(P_{AB,y}<0\). An upper-right vertex leaf has height
\(\sqrt{d^2-h^2}>1\), more than a unit side length above the same actual
AB point, and is also impossible.

Reflect horizontally and interchange \(A,B\), \(C,D\), and \(L,M\).
The reflected \(AB\) normal is again east and the actual mean still has
negative height, so its positive-cycle convention is unchanged. This
excludes all corresponding upper and outer-wrong-axis features at \(B\).
Before considering the lower features, the only possibilities at \(B\)
are its strict lower-right outer vertex, its lower-left near vertex,
an owned south leaf, or an owned east leaf. The reflected list holds at
\(A\).

## 3. Every proposed near-south leaf at A forces \(k<13/50\)

Suppose \(A\)'s real leaf is its strict lower-right vertex or its owned
south side. Write its genuine application as
\[
 (\eta,-v),\qquad v>1,\quad0\le\eta\le h\le\varepsilon.
\]
For a strict vertex \(\eta=h>0\); for the owned side \(\eta=0\) and
\(v=d\). Retain each possibility at \(B\) from Section 2.

If \(B\)'s leaf is its strict lower-right outer vertex, write it as
\((1+h,-w)\). Since \(h\ge0\),
\[
 0<w^2=d^2-(1+h)^2\le d^2-1<121/3600.
\]
The actual mean (1) belongs to \(B\), whose lower side is at \(-w\),
so \(k\le w<11/60<13/50\). The weak mean endpoint is retained.

If \(B\)'s leaf is near-south, its actual geometry requires \(h\le0\).
Together with \(h\ge0\) this gives \(h=0\). Both actual leaf
applications are then \((0,-d)\), so the two real radial S leaves would
be the same physical unit. They are distinct, a contradiction.

Finally suppose \(B\)'s genuine leaf is owned east. Its actual frame has
\(h=\varepsilon\), \(B_x=[\varepsilon,d]\), and a vertical interval
containing zero. The complete B3 equation makes \(BC\) horizontal.
East would put the whole contained unit \(C\) beyond support \(d\),
whose sharp equality case is precisely the actual radial S leaf \(M\).
This is impossible for distinct units. Therefore the actual \(BC\)
normal points west. This uses the degree-free sharp contained-unit
support equality from `END_TRIANGLE_RESULTANT_SUPPORT_BOUND.md`, Section 1.

Let its original mean be \((\varepsilon,y)\) and magnitude \(\nu>0\),
and keep the original \(AB\) magnitude \(\mu>0\). The full B3 moment is
\[
 \nu y=\mu k>0.
\]
The actual \(C\) lies in \(x\le\varepsilon\) and is physically boundary.
The reflected version of (2) gives \(y>4/5\). Both actual means belong
to the same unit side of \(B\), so \(k+y\le1\), and
\[
 k<1/5<13/50.                                          \tag{4}
\]
This argument permits arbitrary \(C\) orientation. It does not use an
all-cycle owner selection in this parallel-force case.

## 4. The owner-free near-radial tip theorem closes all near-south cases

The full true A3 force and torque put its actual \(AD\) force strictly
northwest at the actual vertex
\[
 Q=(h-1,1-v)=(-X,-a_0),\qquad X=1-h,\quad a_0=v-1.
\]
Indeed the other two original forces have nonnegative horizontal and
negative leaf vertical components. Writing the original incoming unit
normal as \((-a,b)\), with \(a,b>0\), the unchanged equations give
\[
 a(k-a_0)=b(X+k\eta/v).
\]
All hypotheses of Section 2 of
`NEAR_RADIAL_LOADED_TWO_FORCE_PORT_EXCLUSION.md` now hold: Section 3
proved \(k<13/50\); the actual \(D\) is a unique-corner loaded true D2
with its actual boundary neighbor \(C\). That theorem gives a
contradiction whether the original \(AD\) normal is D-owned or a
strict D-vertex normal. Thus no nonparallel-pair selection premise is
needed, even in the horizontal-B exception.

Horizontal reflection and the original relabeling exclude the corresponding
near-south genuine leaf at \(B\).

## 5. Exact exhaustive remaining parallel-root frames

Every actual genuine-leaf support is one of four vertices or four own-axis
sides. The preceding sections leave exactly the following full physical
domains.

### Both genuine applications are outer lower vertices

For \(-\varepsilon<h<\varepsilon\),
\[
\begin{split}
 A&=[h-1,h]\times[-v,1-v],& (1-h)^2+v^2&=d^2,\\
 B&=[h,h+1]\times[-w,1-w],& (1+h)^2+w^2&=d^2,
\end{split}
\]
where \(0<v,w<13/50\), \(v^2-w^2=4h\), and the original common
AB mean satisfies \(0<k\le\min(v,w)\). Equality at either side endpoint
is retained. Neither \(C\) nor \(D\) has been assigned an orientation.

### A has an owned west leaf

Here \(h=-\varepsilon\), \(A_x=[-d,-\varepsilon]\), and its actual
vertical unit interval contains zero. The other root is
\[
 B=[-\varepsilon,1-\varepsilon]\times[-w,1-w],
 \qquad w=2\sqrt\varepsilon.
\]
The full A3 equation makes \(AD\) horizontal. West would duplicate the
actual radial S leaf \(L\) by the same sharp support equality, so it is
east. If its actual mean is \((-\varepsilon,y_D)\), the full A3 moment
is \(\nu y_D=\mu k>0\). Section 1 gives
\[
 y_D>4/5,\qquad0<k<1/5,\qquad k\le w.
\]
The actual A interval contains both \(-k\) and \(y_D\). No midpoint,
endpoint, D alignment or shortened D equation is inferred.

### B has an owned east leaf

This is exactly the reflected preceding domain. Both horizontal genuine
leaves cannot occur together, because they would require
\(h=-\varepsilon\) and \(h=\varepsilon\) with \(\varepsilon>0\).

These three domains retain all original A3/B3/C2/D2 forces and torques,
all actual means, both real leaves, and all three arbitrary completion
squares. The entire subdomain in which \(C,D\) also have parallel frames
is excluded separately by
`ADJACENT_S_LEAF_C4_ALL_PARALLEL_FRAMES_COMPLETE_EXCLUSION.md` and its
same-nine capacity argument. The remaining tilted-boundary domains are
not counted as closed by this reduction.
