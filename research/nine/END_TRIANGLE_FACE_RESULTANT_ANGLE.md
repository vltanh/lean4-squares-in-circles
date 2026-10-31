# An end triangle attached to one positive side has a quantitative outward resultant

**Status: complete hand implication; root and separate independent full
audits passed.** Work in the common selected certificate and the window
\[
 \frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},\qquad
 d=\sqrt{R^2-\frac14}-1<\frac{61}{60}.
\tag{1}
\]
Let H,C,E be an actual positive triangle. C,E have exact positive
degree two and positive circle load; H may have arbitrary additional
forces. Suppose both actual HC,HE applications belong to one side of H
with outward unit normal N and support height P. Put
\[
                         M=F_C+F_E,\qquad e=M/|M|.
\]
All physical circle masks, individual zero corner weights, contact
owners and actual shared-side means are retained.

**Theorem.** The following two whole-domain implications hold:
\[
 \boxed{\quad P\ge\frac45\quad\Longrightarrow\quad e\cdot N>\frac12,\quad}
\tag{2}
\]
\[
 \boxed{\quad P\ge\frac{29}{30}\quad\Longrightarrow\quad e\cdot N>\frac45.\quad}
\tag{3}
\]
The theorem makes no claim that an arbitrary end triangle has its two
applications on one side. That premise must be proved in each use.

## 1. The entire non-free interface has a uniform center projection

The proofs of Sections 1--3 of END_TRIANGLE_HIGH_FACE_EXCLUSION.md
use only P>0 until the final numerical cap estimate. We recall exactly
the inequalities that remain valid here.

For nonparallel root normals, their intersection is a negative
multiple of M, and lies behind both actual applications. Every root
normal at the side in question has strictly positive N-component.
A root-owned normal is therefore N itself. Otherwise its application
is an endpoint of that side.

For a strict endpoint normal n choose its transverse direction v
toward the exterior endpoint, as in that source, so that
\[
 N=c n-bv,\qquad c,b>0,\qquad
 p_n=p\cdot n>0,\quad p_v=p\cdot v>0,
 \qquad P=c p_n-bp_v.
\tag{4}
\]
The sharp contained-unit support bound gives
\[
                              P\le p_n\le d.
\tag{5}
\]
If the contact is owned by the tip and the tip has a unique physical
circle corner, its center and corner in this frame are
\[
 z=(p_n+\tfrac12,Y-\tfrac12),\qquad
 Z=(p_n+1,Y),\qquad Y>0.
\]
The proper loaded-tip concurrence at p+ell n gives
Y<=((p_n+1)/p_n)p_v. Consequently
\[
 \begin{split}
 z\cdot N
 &\ge P+\frac12(c+b)-\frac{bp_v}{p_n}\\
 &=P+\frac{P}{p_n}-\frac c2+\frac b2
 \ge P+\frac Pd-\frac12.
 \end{split}
\tag{6}
\]
For a physical two-corner tip the same source's all-mask argument
forces its radial axis to be n, gives p_n=d, and proves the identical
bound. A root-owned N contact gives z·N>=P+1/2, which is at least
the bound in (6), because P<=d.

The parallel interface is also fully retained. Opposite root normals
are impossible. A common strict endpoint normal would put both proper
tip resultants on the same radial ray, contrary to the boundary-angle
separation; a common tangential root normal has nonzero origin torque.
Thus a surviving parallel interface has common normal N, and again
both centers satisfy (6).

Therefore, whenever neither root edge is free, both actual tip centers
obey
\[
                      z_i\cdot N\ge P+\frac Pd-\frac12.
\tag{7}
\]
No midpoint has been substituted for an actual contact mean.

## 2. Every free interface is excluded already at P>=4/5

Use precisely the common finite selections and complete free-interface
cover in Sections 4--5 of END_TRIANGLE_HIGH_FACE_EXCLUSION.md.
Two physically radial tips are excluded independently of P. The
unique-tip/singleton and two-unique/shared cases are removed by the
compatible fixed-tip and two-tip-block selections, with all means
retained. There are exactly two remaining physical-mask charts.

If the free tip is radial and the other tip unique, a singleton other
root interface is already excluded by the full radial free-interface
theorem. For its shared-side alternative, that theorem gives
\[
 Q=(d j-f/2,d f+j/2),\qquad f,j>0,\quad f^2+j^2=1,
 \qquad P=Q_x,
\]
and the unique far circle corner of the other tip is
\[
                         Z=(P+1,d f-j/2-1).
\tag{8}
\]
If P>=4/5, then f<1/3. Indeed f>=1/3 would give
\[
 P\le\frac{61}{60}\frac{17}{18}-\frac16
       =\frac{857}{1080}<\frac45,
\]
using j<=sqrt(8)/3<17/18. Hence j>sqrt(8)/3>14/15 and
\[
 d f-j/2-1<\frac{61}{180}-\frac7{15}-1=-\frac{203}{180}.
\]
Equation (8) would then imply
\[
 |Z|^2>\frac{81}{25}+\left(\frac{203}{180}\right)^2
       =\frac{1105}{256}+\frac{20267}{103680},
\tag{9}
\]
contrary to containment.

If the free tip is unique and the other tip radial with a shared
mutual side, the complete remaining chart in that same source gives
\[
                   P\le\frac{\sqrt{113}}{16}<\frac34<\frac45.
\tag{10}
\]
This also contradicts the premise. Thus every free root interface is
excluded for P>=4/5. In particular, (7) applies throughout the entire
domain of both (2) and (3).

## 3. From center projection to the actual circle-resultant direction

Every contained center has norm less than 91/60. Moreover each physical
circle corner, and therefore each nonzero nonnegative weighted circle
resultant of one boundary square, differs from its center direction by
less than pi/12. The full all-mask proof is
FOUR_BOUNDARY_PATH_ENDPOINT_SEPARATION.md, Section 1; its local bound
does not require a four-body path.

When P>=4/5, (7) gives
\[
 z_i\cdot N\ge\frac45+\frac{48}{61}-\frac12
                =\frac{663}{610}.
\]
Consequently
\[
 \frac{z_i\cdot N}{|z_i|}>
       \frac{3978}{5551}>\frac1{\sqrt2},
 \qquad 2\cdot3978^2-5551^2=835367>0.
\tag{11}
\]
The center direction is thus less than pi/4 from N, and the actual
tip-resultant direction is less than pi/3 from N. Each tip satisfies
F_i·N>|F_i|/2. Summing the two genuine resultants and using the
triangle inequality proves (2).

If P>=29/30, the stronger instance of (7) is
\[
 z_i\cdot N\ge\frac{29}{30}+\frac{58}{61}-\frac12
                  =\frac{1297}{915}.
\]
It follows that
\[
 \frac{z_i\cdot N}{|z_i|}>\frac{5188}{5551}>\frac{14}{15},
             \qquad15\cdot5188-14\cdot5551=106>0.
\tag{12}
\]
Finally
\[
 \cos\left(\arccos\frac45-\frac\pi{12}\right)
      =\frac{7\sqrt6+\sqrt2}{20}<\frac{14}{15}.
\tag{13}
\]
For example, sqrt(6)<49/20 and sqrt(2)<10/7 reduce the last
comparison to 2601/2800<14/15. Thus adding the actual less-than-pi/12
corner deviation still leaves each tip resultant within arccos(4/5)
of N. Summing as before proves (3).

All projection and direction estimates use the original containing-circle
origin. Every physical mask, positive total load, possible zero corner
weight and actual shared-side mean remains. No new normal selection,
completion motion, sampled angle or numerical certificate is used.
