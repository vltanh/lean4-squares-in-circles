# A shared boundary page also excludes the free central S/S diamond contact

Date: October 26, 2026.

**Status: complete hand candidate, pending fresh independent review.**
This complements the shared leaf-page theorem. It excludes the whole
S/S hub-tip feature in which HC and CK are genuinely shared and HK
is free. All actual shared means are retained, and no physical mask
or owner at B is assumed.

## 1. Exact original scope

Retain the original edges
\[
          HK,\ HB,\ HC,\ KB,\ KC,\ HL_H,\ BL_B
\]
with distinct genuine S leaves at H,B, positive circle loads at K,C,
true pair degrees H4,K3,B3,C2 and all three arbitrary completion
units. Use
\[
 79/40\le R\le\sqrt{1105}/16,\qquad
 d=\sqrt{R^2-\tfrac14}-1,\qquad
 \delta=\max(d-1,0)<1/60.
 \tag{1}
\]

**Theorem 1.1.** If the physical HC and CK intersections have positive
length, the actual HK contact cannot be a free singleton.

The proof uses the complete H4 and B3 equations where stated. It
uses no shortened equation at K or C; only their physical boundary
contact and genuine containing-circle corners are needed.

## 2. The exact L and its missing quadrant

The shared HC and CK sides make H,C,K frames parallel. If their
side normals at C were opposite, H,K could not touch. If they were
equal, the two same-column unit neighbors could meet only along
a full shared side. Thus free HK forces the two side normals
at C to be perpendicular.

Rotate and reflect so C-to-H is -E_1 and C-to-K is E_2. The
same complete shared-slider calculation as in
SS_HUB_TIP_TWO_SHARED_TIP_PORTS_FREE_CENTRAL_EXCLUSION.md,
Section 4, gives
\[
 \begin{aligned}
 H&=[h-1,h]\times[t-1,t],\\
 C&=[h,h+1]\times[t-1,t],\\
 K&=[h,h+1]\times[t,t+1].
 \end{aligned}
 \tag{2}
\]
Indeed a nonzero overlap in both slider directions would overlap
H,K interiors; one nonzero slider would give their shared side.
A vertex/vertex HK contact fixes both sliders. Its actual strict
H-to-K normal has two strictly positive coordinates.

The degree-free missing-quadrant lemma in that source, Lemma 2.1,
applies to B, which physically touches H and K and is disjoint
from all three units in (2). It gives
\[
                    \max_B x=h,\qquad \min_B y=t,
       \qquad B\subseteq\{x\le h,\ y\ge t\}.
 \tag{3}
\]
All corner, side-interior and vertex-owner alternatives are included
in that lemma.

If B is axis-parallel, (3) already makes it the exact missing fourth
unit, so all four outer intersections HB,BK,KC,CH are shared.
The reviewed whole shared-perimeter exclusion applies directly.
It remains to exclude every tilted B frame.

## 3. The two actual boundary units put the shared line through O

The actual S-root inward segments put both H and B through
D_delta on d>=1. The strict d<1 part of this whole original layout
was already excluded by the distinct-root common-boundary-neighbor
theorem, so retain d>=1.

By (2)--(3), H lies below y=t and B above it. Hence
\[
                         |t|\le\delta.
 \tag{4}
\]
H also contains a point of D_delta and has maximum horizontal
coordinate h, so h>=-delta.

Consequently h>-1/2 and |t|<1/2. The unique farthest corners of
the two actual axis-parallel units C and K are respectively
\[
                        z_C=(h+1,t-1),\qquad
                        z_K=(h+1,t+1).
\]
Their genuine positive circle loads require both to have norm R.
Subtracting these two squared equalities gives 4t=0. Thus
\[
 \begin{gathered}
 t=0,\quad
 H=[h-1,h]\times[-1,0],\quad
 C=[h,h+1]\times[-1,0],\quad
 K=[h,h+1]\times[0,1],\\
                R^2=(h+1)^2+1,\qquad
                  4/5<h<1.
 \end{gathered}
 \tag{5}
\]
For the lower h bound, d>=1 gives R^2>=17/4, so
h+1>=sqrt(13)/2>9/5. For the upper bound,
R^2<=1105/256<5 gives h+1<2. These signs are uniform at d=1.

This is a physical circle-mask conclusion from the obtained coordinates.
No weighted resultant or C/K force equation has been replaced.

## 4. Both actual tilted-B contacts have fixed owner axes

A tilted unit with maximum x=h and minimum y=0 has one lowest
vertex and one rightmost vertex. The lowest vertex lies strictly
between h-1 and h on H's top side; the rightmost vertex has
height strictly between zero and one on K's left side.

For example, the two complete tilted frame types relative to
P=(h,0), with c>=s>0,c^2+s^2=1, are
\[
 \begin{array}{c|cccc}
 {\rm I}&(-s,0)&(-c-s,s)&(0,c)&(-c,c+s)\\
 {\rm II}&(-c,0)&(-c-s,c)&(0,s)&(-s,c+s).
 \end{array}
 \tag{6}
\]
The lowest/rightmost positions in either row prove both strict
side-interior statements. Thus the actual HB contact is a singleton
owned by H with H-to-B normal E_2, and the actual BK contact is a
singleton owned by K with B-to-K normal E_1. This is forced by
the physical supports, without a new normal choice.

The true B3 force equation gives
\[
             \lambda_B e_B-\mu E_2+\nu E_1=0,
                     \qquad \lambda_B,\mu,\nu>0.
\]
Hence
\[
                           (e_B)_x<0,\qquad (e_B)_y>0.
 \tag{7}
\]

## 5. The actual H4 leaf must use its lower-left corner

The H-owned HB side meets the near-origin genuine root B, and
K is a physical common boundary neighbor. The reviewed arbitrary-
degree owner-direction theorem applies at H and gives
\[
                               (e_H)_y<0.
 \tag{8}
\]
Therefore H's real leaf is at its lower-left or lower-right corner,
or is aligned downward with its complete actual side mean.

The lower-right corner has squared norm h^2+1>41/25>(61/60)^2,
so it cannot be the actual radial leaf support at radius d.
An aligned downward leaf would have d=1 and zero horizontal force.
But the real H-to-C force is E_1, the real free H-to-K force
has positive horizontal component, and the actual H-to-B force
is E_2. The horizontal component of the complete H4 sum would
then be strictly positive. Thus the aligned case is impossible,
including every possible leaf side mean.

Only the lower-left leaf remains:
\[
                         d^2=1+(1-h)^2.
 \tag{9}
\]
Since h<1, this also gives d>1. Combining (9) with (5) and
R^2=(d+1)^2+1/4 yields
\[
                         4h=2d+\frac54,\qquad
                         h=\frac d2+\frac5{16}.
\]
Consequently the entire retained tilted-B feature has
\[
                      \frac{13}{16}<h<\frac{197}{240},
               \qquad 1-h>\frac{43}{240}.
 \tag{10}
\]

## 6. Type I: all genuine B leaf features are impossible

Use the first row of (6). The actual B leaf has negative horizontal
and positive vertical direction by (7).

If the leaf is tilted relative to B's own axes, its real radial
application is a B vertex. The lowest vertex has y=0 and the
rightmost vertex has x=h>0, so neither can be that point.
The remaining two vertices are
\[
                   V_{\rm left}=(h-c-s,s),\qquad
                   V_{\rm top}=(h-c,c+s).
\]

For the left vertex, c+s<3/2 and h>4/5 give
0<c+s-h<7/10. Also s^2<=1/2. Therefore
\[
                    |V_{\rm left}|^2<49/100+1/2
                         =99/100<1<d^2.
 \tag{11}
\]
For the top vertex, subtract (9):
\[
 |V_{\rm top}|^2-d^2
         =2cs-s^2+2h(1-c)>0.
 \tag{12}
\]
Thus neither remaining vertex has the actual leaf radius.

If the B leaf is aligned with one of its side axes, (7) allows
only the northwest axis u=(-c,s). Its real support is
\[
                         h_B(u)=1+c(s-h)<1<d,
 \tag{13}
\]
because s<=1/sqrt2<4/5<h. This excludes the entire actual
aligned side, including endpoint means. Type I is exhausted.

## 7. Type II tilted leaf: its actual moment forces incompatible radii

Now use the second row of (6). The lowest vertex has y=0, the
rightmost has x=h>0, and the top vertex has x=h-s>0 because
h>4/5>s. Thus a leaf tilted relative to B must use the left vertex
\[
                        V=(h-c-s,c).
 \tag{14}
\]
The two actual singleton applications are
\[
                   Q_{HB}=(h-c,0),\qquad
                   Q_{BK}=(h,s).
\]
The true B3 force equation and (14) give
\[
                      \frac{\nu}{\mu}=\frac{c+s-h}{c}.
\]
The unchanged origin moment equation is
\[
                         \mu(c-h)=\nu s.
\]
In particular c>h>4/5, so c>s. Combining these equations yields
\[
                 (c-s)(c+s-h)=cs,\qquad
                   h=c-\frac{s^2}{c-s}.
 \tag{15}
\]

Put tau=s/c in (0,1). If tau>=1/3, then
tau^2/(1-tau)>=1/6 and c<=3/sqrt(10). Since h>0,
\[
 h=c\left(1-\frac{\tau^2}{1-\tau}\right)
       \le\frac56\frac3{\sqrt{10}}
       =\frac{\sqrt{10}}4<\frac45,
\]
contradicting (5). Thus the actual positive B3 stress requires
\[
                              s/c<1/3.
 \tag{16}
\]

But the two genuine leaf radii (9), (14) would have squared
difference
\[
 \begin{aligned}
 |V|^2-d^2
    &=2cs-s^2-2h(c+s-1)\\
    &>2cs(1-h)-s^2\\
    &>\frac{43}{120}cs-s^2
      =cs\left(\frac{43}{120}-\frac{s}{c}\right)
      >\frac{cs}{40}>0.
 \end{aligned}
 \tag{17}
\]
The first strict estimate uses c+s>1 and
c+s-1=2cs/(c+s+1)<cs. The second uses (10), and the final
reserve is 43/120-1/3=1/40. Equation (17) contradicts
the actual norm |V|=d. Every tilted-leaf Type II frame is excluded.

## 8. Type II aligned leaf: the entire real side mean also fails

The only aligned B leaf direction compatible with (7) is the
northwest axis u=(-s,c). Its real support and the actual leaf
point d u give the necessary identity
\[
                        \delta=d-1=s(c-h)>0.
 \tag{18}
\]
No transverse coordinate or mean on that side is fixed.

The same two actual singleton applications and the true B3
equation now give
\[
                   \frac{\nu}{\mu}=\frac{s}{c},
             \qquad \mu(c-h)=\nu s.
\]
Therefore
\[
                        c-h=\frac{s^2}{c},
                   \qquad \delta=\frac{s^3}{c}.
 \tag{19}
\]
Since c<=1 and delta<1/60, s^3<1/60. The strict comparison
(13/50)^3>1/60 gives s<13/50, and consequently c>24/25.
Now (19) implies
\[
 h=c-\frac{s^2}{c}
   >\frac{24}{25}
           -\frac{(13/50)^2}{24/25}
    =\frac{427}{480}
    >\frac{197}{240}.
 \tag{20}
\]
This contradicts (10), with final reserve 11/160.

The side-support identity (18) and the true moment were necessary
for every actual mean on that side, including its two endpoint
positions. Thus no aligned-leaf exception remains. Together with
Sections 6--7 this exhausts every tilted physical B frame.

## 9. Exact full-feature join

B must be axis-parallel. Equation (3), with t=0, then fixes
\[
                           B=[h-1,h]\times[0,1].
\]
Thus all four original outer contacts HB,BK,KC,CH are positive-length
shared sides. Their positive aggregate means remain the original ones.

The reviewed
SS_HUB_TIP_DIAMOND_SHARED_PERIMETER_EXCLUSION.md excludes this
whole feature with the original H4,K3,B3,C2 equations and the
existing common matched-junction selection. This proves Theorem 1.1.

Combined with the companion shared-tip-page theorem, the exact
consequence is:

**Whenever central HK is free, neither original page tip B nor C
can have both of its perimeter contacts genuinely shared.**

This is a whole feature reduction under the original gate. It does
not equate singleton owners with shared sides or close the remaining
central free family.

## 10. Exact sources and verification boundary

| Source | SHA256 | Exact use |
| --- | --- | --- |
| SS_HUB_TIP_TWO_SHARED_TIP_PORTS_FREE_CENTRAL_EXCLUSION.md | ecf6da01608b625eb3b357613856cb7df035930a8dba618663aca302922aa1f6 | Degree-free missing-quadrant lemma and complete two-shared/free-diagonal physical chart |
| S_LEAF_ROOT_NEAR_ORIGIN_TRIANGLE_OWNER_DIRECTION.md | e612ed13cd2c8621c014b14e898709cf4d4b2305ade9a2b818b9d14be1f066e5 | Actual H4 owner-direction consequence at HB |
| SS_HUB_TIP_DIAMOND_SHARED_PERIMETER_EXCLUSION.md | d7e7cafe4b9dd636bbbef1e0857e3dda1605404a382c27623ca26d3f707dc4b2 | Whole resulting four-shared original feature |
| RADIAL_BRIDGE_AND_LEAF_REDUCTION.md | faf453b3c519b10590cf9d6f6dbf9282233bd2ff04c90aa0cd8cd89e060bc676 | All actual S-leaf supports, aligned means and inward segments |
| DISTINCT_LEAF_ROOTS_LOW_RADIUS_JOINT_REDUCTION.md | c6a32136525f819e05a69ed9fe2ce6144a02b1b7f42a3115c1dde29cf0b4ddfd | Entire original d<1 hub-tip exit |
| PHYSICAL_BODY_GRAPH_UNCROSSING.md | bc98e6b6df24b88a05c1a50c1968f2f20d9a3c49cf3c6f067d1e6123aeb580fe | Actual strict free normal and shared/singleton distinction |

Original accepted files are compared with head
26d9e3042b733ff0796876a4607a7d834f4b630a. The new companion
source is pinned exactly and is a required review dependency.
The owner-direction and shared-perimeter sources have their
separate fresh full reviews.

The argument makes no new normal selection, does not use a C2
equation at K, and does not delete HC or HK from the H4 equation.
All original circle atoms, physical squares, actual positive forces,
means and radius endpoints remain until a named complete exit.
No new graph ID, gate tick, computation certificate, pose grid,
ledger edit, Lean build, CI workflow or remote mutation is introduced.
