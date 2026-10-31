# A long triangle arm leaves no room for two direct-leaf roots

Date: October 26, 2026.
**Status: accepted complete theorem after full-source independent review in REVIEW_LONG_ARM_TWO_DIRECT_ROOTS_ROOTED_BLOCKS_2026_10_26.md.** No ledger or original gate is changed here.

## 1. A force-free three-center cap

**Lemma.** Three interior-disjoint unit squares cannot have all their
centers in

    |c| < 29/40,          c_x < -11/40.                    (1)

Indeed two of the three center ordinates have the same weak sign.
Their horizontal coordinates belong to (-29/40,-11/40), so the
absolute horizontal difference is less than18/40. Their ordinates
have the same weak sign and absolute value less than29/40, so their
vertical difference is less than29/40. Thus their squared distance
is less than

    (18/40)^2+(29/40)^2 = 1165/1600 < 1.                  (2)

Distinct interior-disjoint unit squares have center distance at least
one, because their open incircles of radius1/2 are disjoint. This
contradicts (2). No orientation, force, contact-owner or circle-load
premise is used in the lemma.

## 2. Complete original triangle attachment

Work with the same nine physical squares and compatible selected
certificate in 79/40<=R<=sqrt(1105)/16, at the common canonical pose
and minimum-support scope of the accepted forest reductions.

The entire positive component is the triangle A--B--C--A, a genuine
length-three pendant path A--U--V--L, and one genuine direct leaf at
each of B and C. This is the whole eight-body path distribution
(3,1,1), with its one arbitrary completion square retained.

**Theorem.** This entire attachment is impossible. It includes every
original circle load at A, both S/D types for the direct leaves,
every original mean, slider, normal and physical circle mask.

Use the complete actual-arm theorem
ROOTED_TRIANGLE_LENGTH_THREE_ARM_GEOMETRY.md. All discarded leaf,
width and critical-radius alternatives have their original full
exclusions there. In the remaining domain put

    d=sqrt(R^2-1/4)-1,       epsilon=d-1,
    0<epsilon<1/60.

After a common rotation the unchanged genuine terminal L points east,
both original intermediates are side transmitters, and

    A subset {x<=epsilon-1},
    U=[epsilon-1,epsilon] times [a,a+1],      a<=0<=a+1.   (3)

In particular U contains zero and

    |c_U|<=sqrt(2)/2<29/40,
    (c_U)_x=epsilon-1/2<-29/60<-11/40.                   (4)

Only the true physical geometry in (3) is used below. No circle force
at A is declared zero, and no concurrence direction at A is used.

Each of B,C is the actual root of its own genuine direct S/D leaf.
The radial leaf theorem makes each meet D_epsilon: a D root contains
zero, while an S root contains the inward unit segment from d*e,
including epsilon*e. Their center bounds are therefore

    |c_B|,|c_C| <= epsilon+sqrt(2)/2
                < 1/60+17/24 = 29/40.                   (5)

Both are actual physical neighbors of A. Choose any actual point
P in the A--B contact. By (3), P_x<=epsilon-1. Every point of a unit
square lies within its circumradius sqrt(2)/2 of its center, so

    (c_B)_x <= P_x+sqrt(2)/2
             <= epsilon-1+sqrt(2)/2
              < 1/60-1+17/24 = -11/40.                  (6)

The identical argument at the unchanged A--C contact gives (6) for C.
This works for a vertex, an entire shared side, and every actual
application mean; it uses no replacement contact point in an equation.

The three distinct original bodies U,B,C now meet all hypotheses of
the force-free cap lemma. Equations (4)--(6) contradict (2), excluding
the full attachment. The remaining ninth square was never removed.

## 3. Exact scope

The proof retains the potentially positive circle load of the far
triangle root A. It does not apply a direct-leaf formula at A or an
end-triangle degree-two-tip equation at either of its attached neighbors.
The only leaf-root formulas are used at the actual direct-leaf roots B,C.

This source closes the whole distribution (3,1,1). A single additional
direct-leaf root, distribution (3,1), does not supply the third central
body needed by the cap lemma and remains outside this argument.

No numerical sample, coefficient packet, Lean compilation or CI is used.
The exact center-distance reserve is 1-1165/1600=87/320>0.
