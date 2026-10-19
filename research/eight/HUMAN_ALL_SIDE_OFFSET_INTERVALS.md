# Uniform central-side offset intervals for all eight population profiles

## Theorem (all square orientations)

Consider an eight-unit-square packing in a disk D_R centered at zero,
in the established exact search interval

    sqrt(2)+1/2 < R <= sqrt(9789)/50.

The strict left inequality is the unconditional pen-and-paper bound
of HUMAN_ANALYTIC_LOWER_BOUND.md. The right inequality is the
rational eight-square construction.

Let C be its unique origin-containing square. Choose one
signed unit side normal n of C, put t=n dot p_C and
h_plus=1/2+t, h_minus=1/2-t. Thus |t|<1/2.
Let N_plus,N_minus be the number of *distinct complete exterior
squares* beyond the corresponding central-owned support lines,
respectively. These are whole-square memberships, not center signs.

Then the exact cardinality-to-location implications are:

    N_plus >=1  => t< 83/200,
    N_plus >=2  => t< 5/24,
    N_plus  =3  => t< -5/24,                           (1)

and, by reflection,

    N_minus>=1  => t> -83/200,
    N_minus>=2  => t> -5/24,
    N_minus =3  => t> 5/24.                            (2)

Every side population is <=3, and populations (3,2),
(2,3),(3,3) are excluded by the previous exact cap theorems.

Consequently each one-axis opposite-side count profile,
written with N_plus>=N_minus after optional reflection,
forces the central-center projection t into the **open interval**

| N_plus+N_minus | Strict necessary interval for t |
| --- | --- |
| 0+0 | (-1/2, 1/2) |
| 1+0 | (-1/2, 83/200) |
| 2+0 | (-1/2, 5/24) |
| 3+0 | (-1/2, -5/24) |
| 1+1 | (-83/200, 83/200) |
| 2+1 | (-83/200, 5/24) |
| 3+1 | (-83/200, -5/24) |
| 2+2 | (-5/24, 5/24) |

Apply the same table independently to the perpendicular
central side coordinate. This is an exhaustive **necessary
continuous-domain pruning** for all eight opposite-side
profiles, with no selected contact or stress graph.

## 1. One-square cap cutoff without any frame assumptions

**Lemma.** If one unit square S of arbitrary orientation is
contained in D_R and in {x:n dot x>=h}, h>=0, then

    R^2 >= (h+1)^2+1/4.                               (3)

**Proof.** Let p be the center of S and (e,f) its own
orthonormal frame. The support half-width on n is
h_S(n)=(|n dot e|+|n dot f|)/2>=1/2.
Whole-square cap membership implies

    n dot p>=h+h_S(n)>=h+1/2.

Thus r=|p|>=h+1/2. The exact largest squared vertex
norm of a unit square is

    r^2+1/2+|p dot e|+|p dot f|
       >=r^2+r+1/2
       >=(h+1/2)^2+(h+1/2)+1/2
       =(h+1)^2+1/4.

Every vertex lies in D_R, proving (3). QED.

If h>=183/200, (3) gives

    R^2 >= (383/200)^2+1/4
        =156689/40000
        =9789/2500+13/8000
        >9789/2500,

a contradiction. Therefore any central side serving
at least one exterior whole square satisfies

    h<183/200,       t=h-1/2<83/200.             (4)

The same restriction applies to any noncentral outward cap line.

## 2. Extend the two-square cap inequality to EVERY positive side offset in n=8

HUMAN_EXTENDED_TWO_SQUARE_CAP.md proves the **sharp**
arbitrary-frame two-square cap inequality

    R^2 >=(1+h)^2+1                               (5)

whenever 2/5<=h<=1, for two interior-disjoint
complete unit squares beyond {n dot x>=h}.

For 0<=h<2/5, the same inequality holds
throughout our eight-square *radius range*,
for an even simpler reason. The analytic
n=8 lower bound gives

    R^2 >(sqrt(2)+1/2)^2
        =9/4+sqrt(2)
        >13/4
        >74/25=(7/5)^2+1
        >(1+h)^2+1.                                (6)

Thus (5) holds for **all** 0<=h<=1 in
an eight-square packing in this search range.
This does not purport to extend the separate
sharp two-square packing theorem to smaller
disk radii; (6) uses the eight-square lower bound.

If N_plus>=2, take h=h_plus and use (5):

    (3/2+t)^2+1 <=R^2 <=9789/2500<2257/576
                =(41/24)^2+1.

The positive square roots therefore give

    3/2+t<41/24,      t<5/24.                    (7)

Reflect to obtain the second inequality in (2).
For opposite 2+2 the two bounds combine to
|t|<5/24, without splitting into cap offsets
above/below 2/5.

## 3. Three-square cap and the final intervals

HUMAN_THREE_SQUARE_CAP.md gives the
orientation-free sharp bound

    R^2 >=(1+h)^2+9/4,                              (8)

for 0<=h<=1/3. If a positive central side
serves three, its h must be less than 1/3:
otherwise the three squares belong to the
smaller cap at h=1/3, forcing
R^2>=145/36>4, impossible at the search ceiling.

At the true positive offset h the inequality
(8) applies. Since R^2<2257/576 and

    (1+7/24)^2+9/4
       =(31/24)^2+9/4=2257/576,

we obtain

    h<7/24,      t=h-1/2< -5/24.                 (9)

The reflected triple case gives the last
implication in (2).

Combine (4), (7), (9) with the a priori
-1/2<t<1/2, taking both plus and minus
sides when nonzero. Reading off the
resulting intersection produces exactly
the eight interval rows in the theorem.
This proves the table.

## 4. Scope and further pruning

The eight intervals replace imprecise
'near centered' language by **explicit
open rational intervals** for each one-axis
side-count profile. The strict 3+1 interval
is particularly useful:

    N_plus=3, N_minus=1
       => -83/200<t<-5/24.                       (10)

Thus its central-center coordinate cannot
approach either 0 or -1/2; it lies in a
narrow signed band.

The theorem also shows any side serving two
whole exterior squares has outward line
offset h<17/24, even if h<2/5. This is a
uniform local rule usable without checking
the two-cap theorem's original offset
condition separately.

The coordinate bounds alone do not eliminate
corner-only separators, classify all seven
square frames or force the sharp five-corner
chain. The unrestricted implication R8>=Rhat
is still unproved.
