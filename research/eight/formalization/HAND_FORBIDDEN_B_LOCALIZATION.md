# Residual forbidden-B owners: whole-domain hand localization

**Status: proved on paper, conditional on the existing candidate frame, tangent cuts, zero owners and S <= 3/200.** No quarter-owner or mixed-owner table is a premise. This note prepares the complete quarter-owner closure in `HAND_QUARTER_OWNER_CLOSURE.md`; it does not close the earlier mismatch gates.

All axis indices below are zero based. The cyclic roles are H,G,A,B,T,D,E. Put

\[
 c=\cos t,\quad s=\sin t,\quad
 W=(1+c+|s|)/2,\quad L=447/800,\quad U=283/200,\quad V=29/25.
\]

The candidate chart gives c >= 3/4, |s| <= 7/10, and c^2+s^2=1. In particular c <= 1. The original containment/cone bounds are

\[
 (a_i+1/2)^2+(b_i+1/2)^2\le q\le Q_0=9789/2500,
 \qquad L\le a_i\le U,\quad 0\le b_i\le9/10.
\]

For G and T we additionally have 7/12 <= a_i <= 349/250. For H, b_H >= a_H/2. These are consequences of the previously proved canonical/tangent bounds, not new contact equalities.

For each aligned edge i let e_i=|d_i|; their sum is S. An actual feasible aligned owner gives its nominal projection >= 1-(3/2)e_i. A feasible G owner gives its exact nominal projection >= W. Each feasible E owner gives its nominal projection >= W-2S. Every estimate concerns the original feasible axis, including ties.

## 1. Two coordinate consequences

First a_H <= V. Otherwise the H cone and circle would give

\[
 q\ge (29/25+1/2)^2+(29/50+1/2)^2
   =Q_0+4/625>Q_0.
\]

Suppose an original forbidden B-to-T axis, index 0 or 1, is feasible. Adding the A zero-edge and B inequalities gives

\[
 b_A+a_T\ge2-\tfrac32(e_A+e_B).
\]

Consequently

\[
 b_A\ge2-\tfrac32\tfrac3{200}-\tfrac{349}{250}
     =1163/2000>29/50.
\]

The same circle comparison gives a_A <= V. Thus a_H,a_A <= V and b_A >= 29/50 throughout the forbidden-B branch. This uses actual containment, not assumed circle contact.

## 2. Negative sine is greater than -3/8, before any mixed-owner choice

Suppose s=-r with r >= 3/8. The four original E projections are

\[
\begin{aligned}
 E_0&=ca_H-rb_H-b_E,\\
 E_1&=a_H-ra_E-cb_E,\\
 E_2&=ca_E-rb_E-b_H,\\
 E_3&=a_E-ra_H-cb_H.
\end{aligned}
\]

Using nonnegative b_E, the H cone, a_H <= V, and the common primary bounds gives respectively

\[
 E_0\le V(c-r/2),\quad E_1\le V-Lr,\quad
 E_2\le Uc-L/2,\quad E_3\le U-Lr-(L/2)c.
\]

For the first bound c-r/2 >= 1/4, so multiplying a_H <= V is legitimate. On c in [3/4,1] and r in [3/8,1], subtracting these four upper bounds from W yields at least

\[
 49/200,\qquad717/6400,\qquad83/1600,\qquad213/3200,
\]

respectively. These are four substitutions in affine functions on a rectangle: the coefficient of c is negative in the first and third expressions, positive in the second and fourth; the coefficient of r is positive in all four. All exceed 2S <= 3/100. Hence no E axis could be feasible, a contradiction.

Therefore s > -3/8. For a nonpositive sine write r=-s. Then

\[
 0\le r\le3/8,\qquad9/10\le c\le1,\qquad
 1-c=\frac{r^2}{1+c}\le\frac47r^2\le\frac3{14}r.
\tag{1}
\]

Here c^2=1-r^2 >= 55/64 > 81/100, and 1+c >= 7/4. The proof covers the closed larger domain in (1).

## 3. Residual G axes force positive sine below 1/10

Assume the forbidden B axis and one of G axes 0 or 1 are feasible, and s >= 0. The H nominal projection is b_H+b_G.

For G axis 0, add H to

\[
 G_0=ca_A-sb_A-b_G\ge W.
\]

Using a_A <= V, b_A >= 29/50, b_H <= 9/10 and c <= 1 gives

\[
 -3/50+(27/25)s\le\tfrac32e_H\le9/400,
\]

hence s <= 11/144 < 1/10.

For G axis 1, add c times H to

\[
 G_1=a_A-sa_G-cb_G\ge W.
\]

Since a_G >= 7/12, this gives

\[
 -33/50+(3/5)c+(13/12)s\le\tfrac32c e_H\le9/400.
\]

The unit-circle identity and c >= 3/4 imply 1-c <= (4/7)s^2. Since s <= 7/10, the left side is at least

\[
 -3/50+(13/12-6/25)s=-3/50+(253/300)s.
\]

Thus s <= 99/1012 < 1/10. In either residual G case, a nonnegative sine therefore satisfies

\[
 0\le s\le1/10,\qquad99/100\le c\le1.
\tag{2}
\]

The latter cosine bound follows from c^2 >= 99/100 > (99/100)^2. Equations (1) and (2) are forced geometric domains, not a numerical subdivision of the original interval.

## 4. All target-secondary and source-primary E owners fail in this branch

Assume a forbidden B axis, G axis 0 or 1, and E axis 2 or 3. A three-edge sum cancels both transverse coordinates of G and H. Each aligned H coefficient and E coefficient used below lies in [0,1], so the complete loss is at most (7/2)S <= 21/400.

### G0 and E2

Adding H+G0+E2 gives demand D=1+2W and force

\[
 F=c(a_A+a_E)+s(b_E-b_A).
\]

Since a_A+a_E <= V+U=103/40 and |b_E-b_A| <= 9/10,

\[
 D-F\ge2-(63/40)c+|s|/10\ge17/40.
\]

### G0 and E3

Adding c H+c G0+E3 gives D=c+(1+c)W and

\[
 F=c^2a_A-cs b_A+a_E+s a_H.
\]

For s >= 0, (2) applies. Dropping the nonpositive term -cs b_A and using a_A,a_H <= V and a_E <= U gives F <= 103/40+29/250. Meanwhile D >= 99/100+(199/100)^2/2=59401/20000. Therefore D-F >= 5581/20000 > 13/100.

For s=-r <= 0, use (1):

\[
 F\le103/40+(9/10-L)r,
 \qquad D\ge541/200+(19/20)r.
\]

It follows that D-F >= 13/100+(19/20-9/10+L)r >= 13/100.

### G1 and E2

Adding c H+G1+c E2 gives D=c+(1+c)W and

\[
 F=a_A-sa_G+c^2a_E+cs b_E.
\]

For s >= 0, drop -sa_G and use (2). Then F <= 103/40+9/100, whereas D >= 59401/20000. The gap is at least 6101/20000 > 13/100.

For s=-r <=0, use a_G <= 349/250 and b_E >=0. With c^2=1-r^2 left unevaluated, the gap is at least

\[
 -33/50+2c-(183/200)c^2+
       r\bigl((1+c)/2-349/250\bigr).
\]

The quadratic 2c-(183/200)c^2 is increasing on [9/10,1], because its derivative is at least 17/100 >0. Using c >=9/10 and r <=3/8 gives

\[
 D-F\ge7977/20000-(223/500)(3/8)=579/2500>13/100.
\]

### G1 and E3

Adding c H+G1+E3 gives D=c+2W and

\[
 F=a_A+a_E+s(a_H-a_G).
\]

For s >= 0, use (2), a_G >=7/12 and a_H <=V. Thus

\[
 D-F\ge1+2(99/100)-103/40+
      (1-V+7/12)s\ge81/200>13/100.
\]

For s=-r <=0, use (1), a_G <=349/250 and a_H >=L:

\[
 D-F\ge1+2(9/10)-103/40+
       (1-349/250+L)r\ge9/40>13/100.
\]

All four cases therefore have a common gap at least 13/100. The available error is only 21/400, leaving the strictly positive reserve

\[
 13/100-21/400=31/400.
\]

Consequently, whenever B is forbidden and G is one of its two residual axes, every actually feasible E axis belongs to {0,1}. No E axis was selected in advance; any forbidden feasible E axis can be inserted in the displayed chain. Owner ties are retained.

## Scope and provenance

The bounds used here are the actual nominal inequalities and cones in `Candidate/Nominal.lean` and the hand derivations in `OWNER_GEOMETRY.md`. Section 2 restates the earlier all-axis negative-tilt argument so its hypotheses are explicit. Sections 3 and 4 are new whole-domain consequences. The proof uses neither generated row identities nor numerical interval coverage. Exploratory optimization was used to locate promising chains; none of its output is a theorem premise. No Lean source was written, compiled or executed.
