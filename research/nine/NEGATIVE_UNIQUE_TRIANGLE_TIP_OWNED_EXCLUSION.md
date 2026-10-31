# A negative unique endpoint of a physical triangle cannot own its hub contact

**Status: complete whole-owner hand implication; root and separate
independent full hand audits passed.** Work throughout
\[
 R_0=\frac{79}{40}\le R\le\frac{\sqrt{1105}}{16},
 \qquad \sigma=\frac1{\sqrt2}.
\tag{1}
\]
Let H,A,K be three actual interior-disjoint contained unit squares,
with all three physical pair contacts. A and K touch the containing
circle. A has one physical circle corner z and exact positive degree
two, with positive edges HA and AK. Its actual circle weight is
positive. H and K may have arbitrary other positive forces, and
every other physical packing square remains present. Assume
\[
                              c_H\cdot z<0.
\tag{2}
\]

**Theorem.** The actual HA normal cannot be a side axis of A.
This includes a genuine shared HA interval with every original
application mean and both of its endpoints. The theorem imposes
no degree or force equation at H or K, and includes both physical
circle masks and every individual zero corner weight at K.

## 1. The entire side-owner and proper-concurrence domain

The complete geometric theorem
NEGATIVE_UNIQUE_NEIGHBOR_INNER_CONTACT.md puts the whole H/A
intersection on A's two inner faces. Rotate or reflect A's frame,
without translating the containing-circle origin, so the owned
HA face is the inner horizontal side. Write
\[
 \begin{split}
 z&=(a,b),\qquad a,b>\frac35,\qquad a^2+b^2=R^2,\\
 A&=[a-1,a]\times[b-1,b],\\
 n_{HA}&=e_y,\qquad P=(a-1,b-1).
 \end{split}
\tag{3}
\]
No ordering of a and b is assumed.

Let m be the actual A-to-K unit normal. The actual physical triangle
H,A,K and UNIT_TRIANGLE_SIDE_NORMAL_OBSTRUCTION.md give
m_y<=0, because the outward A-to-H normal is -e_y.
The true A force equation is
\[
                         k(a,b)=\mu e_y-\gamma m,
             \qquad k,\mu,\gamma>0.
\tag{4}
\]
Its first component forces m_x<0. Thus the two A pair normals
are nonparallel. The full nonparallel proper-concurrence lemma
in TRIANGLE_TWO_BRIDGES_CHAIN_EXCLUSION.md, Lemma 2.1, applies.
Since A has a unique circle corner, its concurrence lies in A
and is a strictly positive multiple of z. Write it as
\[
                                q=\kappa z,\qquad \kappa>0.
\tag{5}
\]
Its HA normal line is vertical. Consequently the actual HA
application, including an original shared-side mean, is exactly
\[
                         Q=(\kappa a,b-1).
\tag{6}
\]
In particular q belongs to A and Q belongs to H.

The circumradius of the actual H is sigma. From (2),(6),
\[
                    \kappa a^2+b^2-b=Q\cdot z<\sigma R.
\tag{7}
\]
This is the only use of the H center in the scalar step below.
No contact point has been reset to a corner or a midpoint.

## 2. A uniform bound on the actual transverse concurrence coordinate

We claim
\[
                              0<\beta:=\kappa b<\frac23.
\tag{8}
\]
If beta>=2/3, multiply (7) by b and use a^2=R^2-b^2.
It would imply
\[
       f(R,b):=2R^2-5b^2+3b^3-3\sigma Rb<0.
\tag{9}
\]
We prove the opposite sign on the complete parameter domain.

Here 0<b<=R<21/10. Along comparison in R from R_0 to the actual
R, with b held fixed, sigma<5/7 gives
\[
             f_R=4R-3\sigma b
                    >\frac{79}{10}-\frac92=\frac{17}{5}>0.
\tag{10}
\]
This comparison is polynomial and needs no intermediate circle
radicand. The exact endpoint comparisons
\[
          2R_0^2>\frac{39}{5},
                  \qquad \sigma R_0<\frac75
\]
give
\[
        f(R,b)>
          \frac15\bigl(15b^3-25b^2-21b+39\bigr)>0.
\tag{11}
\]
For the last strict sign put x=b-3/2. The single polynomial identity
and completed square are
\[
 \begin{split}
 15b^3-25b^2-21b+39
    &=(15b+20)x^2+\frac{21}{4}x+\frac{15}{8}\\
    &\ge20x^2+\frac{21}{4}x+\frac{15}{8}\\
    &=20\left(x+\frac{21}{160}\right)^2
                         +\frac{1959}{1280}>0.
 \end{split}
\tag{12}
\]
This contradicts (9) and proves (8), without a subdivision or an
assumption on which coordinate of z is larger.

Since q belongs to A, beta>=b-1, so
\[
                             b<\frac53.
\tag{13}
\]
The radius window gives R^2>34/9. Therefore
a^2=R^2-b^2>1. Also b>3/5 and
1105/256-9/25<4 give a^2<4. We have proved
\[
                              1<a<2.
\tag{14}
\]
All inequalities remain strict when an original side mean is an
endpoint.

## 3. The whole horizontal AK alternative is circle-clear

First suppose m_y=0. Then m=-e_x, and the actual AK normal line
is horizontal through q. Its application is
\[
                         T=(a-1,\beta).
\tag{15}
\]
The whole K lies in x<=a-1 and has T on that right supporting
line. Put X=a-1 and Y=beta. Equations (8),(14) give
\[
                              0<X<1,\qquad 0<Y<\frac23.
\tag{16}
\]

Here is the complete orientation-uniform corner bound at this
actual support point:
\[
          \max_{v\text{ a corner of }K}|v|^2
             \le\max\{X^2,(X-1)^2\}+(Y+1)^2.
\tag{17}
\]
If the right support is a side, K is aligned in this frame.
Its x interval is [X-1,X], and its vertical interval has length
one and contains Y, so (17) is immediate, for every actual mean.

Otherwise T is K's rightmost vertex. Its inward orthonormal axes,
including their aligned limits, have the form
\[
                 (-c,s),\quad(-s,-c),
                 \qquad c,s\ge0,\quad c^2+s^2=1.
\]
Each adjacent corner has squared norm at most X^2+(Y+1)^2.
For the opposite corner, its added scalar product is controlled by
\[
                 -X(c+s)+Y(s-c)\le Y-X.
\]
If Y>=X this follows from
(Y-X)s-(X+Y)c<=Y-X. If Y<X, write the same expression as
(Y-X)(c+s)-2Yc and use c+s>=1. Its squared norm is therefore
at most (X-1)^2+(Y+1)^2. The original corner also satisfies (17).
This proves the bound for every support feature and frame.

Equations (16)--(17) now give
\[
                  \max_{v\text{ a corner of }K}|v|^2
                       <1+\left(\frac53\right)^2
                        =\frac{34}{9}<R^2.
\tag{18}
\]
Thus the actual K is strictly circle-clear, contrary to its
physical circle contact. This excludes the entire m_y=0
alternative, including shared AK means.

## 4. The entire strict downward AK alternative violates contact radius

Suppose instead m_y<0. Write
\[
                              m=(-r,-t),\qquad r,t>0.
\]
Its strict vertex cone at A puts the actual AK application exactly
at P from (3). Write the untouched HA parameter as
\[
                            Q=P+s e_x,\qquad 0\le s\le1.
\]
The origin torque equation at A, or its torque about P combined
with (4), gives exactly
\[
                              k(b-a)=\mu s\ge0.
\tag{19}
\]
Thus b>=a. The weak inequality deliberately retains s=0 and the
coincident radial-D limit; no mean endpoint is discarded.

Since a^2+b^2=R^2, b>=a and b<5/3, the monotonicity of
sqrt(R^2-b^2)+b on b>=R/sqrt(2) gives
\[
                  a+b>
                     \sqrt{R^2-\frac{25}{9}}+\frac53.
\tag{20}
\]
For R^2>34/9,
\[
 \sqrt{R^2-1}>\frac53,\qquad
 \sqrt{R^2-\frac{25}{9}}>1.
\]
Consequently
\[
 \sqrt{R^2-1}-\sqrt{R^2-\frac{25}{9}}
    =\frac{16/9}
      {\sqrt{R^2-1}+\sqrt{R^2-\frac{25}{9}}}
       <\frac23.
\]
Equation (20) proves
\[
                              a+b>1+\sqrt{R^2-1}.
\tag{21}
\]

Both A and K are actual circle-touching units and P is their
common point. The universal contact-radius theorem in
C7_PINNED_VERTEX_CONTACT_TYPES.md, Section 3, has the
radius-independent scope
\[
                              |P|\ge\sqrt{R^2-1}-1.
\tag{22}
\]
Its elementary proof uses only the two tangent sectors at their
actual common point and a circle corner; no C7 or high-radius
premise is used for (22). Here
\[
                      |P|^2=R^2+2-2(a+b).
\]
Squaring (22), whose right side is positive, instead requires
a+b<=1+sqrt(R^2-1), contradicting (21). This also excludes the
coincident endpoint retained in (19).

## 5. Complete owner cover and exact attachment scope

The signs m_x<0 and m_y<=0 were forced in Section 1 from the
complete physical triangle and the true A equation. Sections 3
and 4 exhaust both possibilities for m_y. The actual normal may
be owned by A, by K, or be free; all are included in that support
cover. The HA contact may be singleton or shared, and every
original mean has survived (6),(15),(19).

In the diamond-hub attachment, the negative endpoint A has exact
degree two, the true H has degree five and K has degree three.
All three actual edges HA,AK,HK exist and K touches the circle.
The theorem therefore excludes the entire A-owned HA domain,
including every genuinely shared HA interval, for all four
remaining physical K/A/B masks. The actual K/B forces and the
intact H/X/Y petal are untouched.

This leaves the H-owned singleton HA domain and any still
unexcluded free domain. In particular this theorem does not
alone close the whole diamond response or its completion problem.
It applies only when the physical HK contact is present; a
four-cycle with an absent HK chord does not inherit that premise.
No new normal choice, change of packing, numerical angle premise,
Lean compilation or CI is used.

