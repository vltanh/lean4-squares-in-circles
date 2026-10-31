# Every original far-return side has force ratio greater than one fifth

Date: October 31, 2026 UTC.

**Status: complete continuous hand bound over the entire original far-return
side feature.** The original ratio satisfies q>1/5, simultaneously for every
physical endpoint mask and all original circle coefficients. Together with
the complete hand upper bounds, every one-unique alternative has
1/5<q<1/3, and the radial/radial alternative has 1/5<q<5/12.
These are necessary ranges; their remaining configurations are not declared
excluded by this source.

The argument is one comparison with the already proved physical cap. Its
polynomial identity and positivity proof are printed in full. The small
tables below are exact rational comparisons of explicit monomials, not
samples of the original packing domain or a generated exclusion cover.

## 1. Complete original entry and the existing physical cap

Retain the original D02.L135 unique-circle V, Type II D-owned roof-direction,
strict far-A-vertex return, with full stars A3,D3,V2,B2,C2,N2. Keep all nine
actual units, the unchanged circle and origin, every original positive force,
selected normal, application and full side mean, physical circle corner and
individual nonnegative circle coefficient. A,D are unloaded true3, V,B,C are
loaded true2 and N is the original unloaded side transmitter.

The full hand entry and complete comparison-interval proof are

* `TYPE_II_FAR_SIDE_LINEAR_CAP_AND_STRICT_C_TANGENT_MONOTONIC_REDUCTION_2026_10_29.md`,
  Sections 1--5;
* `TYPE_II_FAR_SIDE_UNIFORM_C_TANGENT_BOUND_AND_COMPLETE_RADIAL_C_AXIS_REDUCTION_2026_10_29.md`,
  Sections 1--2.

They give, on the entire original side domain,

    0<e<1/2, q>0,
    A=1+e, B=1-e, J=sqrt(1+e^2),
    M=sqrt(A^2+(1+q)^2),
    z=(A/B)*(1-J^3/M),
    z>W(e)=8/15+(67/105)*e-(2/15)*e^2.          (1)

In particular the last inequality is a physical roof/C-cap consequence
with the original full hub equations retained. It is not a lower bound
imposed on a freely chosen slope. Its source proves the whole comparison
interval and its strict concavity reserve; no generated radial-cover leaf
is needed. This theorem does not use the later high-degree C-tangent bound
in that source, only its complete stronger-cap proof in Sections 1--2.

All quantities in (1) have their original meanings. No physical endpoint
mask is selected to obtain them. Loaded N and callers with different full
hub equations require their own original entry and are not included here.

## 2. One polynomial comparison is sufficient

For fixed e in [0,1/2], the displayed function z(e,q) increases strictly
with q>=0, because

    partial z/partial q=(A/B)*J^3*(1+q)/M^3>0.    (2)

It therefore suffices to prove

    z(e,1/5)<W(e) for every 0<=e<=1/2.           (3)

These closed endpoints are scalar comparison values, not newly asserted
physical configurations. Write

    P(e)=49+94e+81e^2-14e^3=105*(A-B*W(e)).

Here A,B,J are positive and P>=49, since 81-14e>=74. Thus the two
sides of the radical comparison below are positive. At q=1/5,

    M^2=A^2+36/25.

Consequently (3) is exactly the positive comparison

    J^3/M>P/(105*A).

Positive squaring and multiplication by 25*(105*A*M)^2 reduce it to

    Q(e):=275625*A^2*(1+e^2)^3
             -(25*A^2+36)*P(e)^2>0.             (4)

For an explicit check of the expansion, the coefficients of P^2 from
degree zero to six are

    2401, 9212, 16774, 13856, 3929, -2268, 196,

and those of A^2*(1+e^2)^3 from degree zero to eight are

    1, 2, 4, 6, 6, 6, 4, 2, 1.

Multiplying the first list by 61+50e+25e^2 and subtracting from 275625
times the second gives the exact polynomial

    Q(e)=129164-130732e-441339e^2-260466e^3
            +301931e^4+1249248e^5+1105719e^6
            +598150e^7+270725e^8.                (5)

The following two continuous comparisons prove (4) on the entire closed
interval. They retain their joining point e=2/5.

## 3. The whole first interval has a decreasing positive polynomial

Differentiate (5):

    Q'(e)=-130732-882678e-781398e^2
             +1207724e^3+6246240e^4+6634314e^5
             +4187050e^6+2165800e^7.

For 0<=e<=2/5, the positive part after factoring e^2 is bounded by

    1207724e+6246240e^2+6634314e^3
        +4187050e^4+2165800e^5<2100000.          (6)

Each monomial increases on this interval. The following integer upper
bounds at its right endpoint verify (6) directly:

| Monomial at e=2/5 | Strict integer upper bound |
| --- | ---: |
| 1207724*(2/5) | 484000 |
| 6246240*(2/5)^2 | 1000000 |
| 6634314*(2/5)^3 | 425000 |
| 4187050*(2/5)^4 | 108000 |
| 2165800*(2/5)^5 | 23000 |
| Sum | 2040000 < 2100000 |

Therefore

    Q'(e)<=-130732+e*(1318602e-882678)<0,         (7)

since 1318602*(2/5)<882678. At e=0 its derivative is exactly
-130732, so the monotonicity includes that endpoint as well.

The value at the right endpoint is positive. For a direct integer check,
bound each displayed monomial from below:

    Q(2/5)
      >129164-52293-70615-16670
           +7729+12792+4529+980+177
       =15793>15000.                            (8)

All comparisons in (8) follow by multiplying by the positive denominator
5^8; they can also be checked individually from the displayed coefficients.
Equations (7)--(8) give Q(e)>15000 on [0,2/5].

## 4. One quadratic lower support covers the whole second interval

On [2/5,1/2], the derivatives are

    Q''(e)=-882678-1562796e+3623172e^2
              +24984960e^3+33171570e^4
              +25122300e^5+15160600e^6,

    Q'''(e)=-1562796+7246344e+74954880e^2
               +132686280e^3+125611500e^4
               +90963600e^5.

Already -1562796+7246344*(2/5)>0, and every further term of Q'''
is nonnegative. Thus Q'' is increasing on the whole second interval.
Its value at 2/5 has the following exact lower comparison:

    Q''(2/5)
      >-1508000+579000+1599000+849000+257000+62000
       =1838000>1800000.                        (9)

Here the first bound combines the two negative terms; the other five
are strict lower bounds for their respective positive monomials. Each
is a rational multiplication at 2/5, without a numerical estimate.

At the arithmetic endpoint 1/2, direct substitution in (5) and its
derivative gives exactly

    Q(1/2)=466461/256>1800,
    Q'(1/2)=2035209/32, 0<Q'(1/2)<64000.         (10)

The lower second-derivative bound (9), integrated twice, gives throughout
the closed interval

    Q(e)>=Q(1/2)+Q'(1/2)*(e-1/2)
                        +900000*(e-1/2)^2.

Equivalently, subtracting 900000*e^2 gives a convex function, whose
tangent at 1/2 is a global lower support on this interval. Completing
the square and using (10) therefore yields

    Q(e)>1800-64000^2/3600000
         =5960/9>0.                             (11)

Together with Section 3, this proves Q>0 on all of [0,1/2], including
both comparison endpoints and their internal join. It proves (3).

## 5. The original ratio and the complete mask consequences

Suppose an original far-return side had q<=1/5. By (2)--(3),

    z(e,q)<=z(e,1/5)<W(e),

contradicting its original physical cap (1). Thus the entire original
side feature satisfies

    q>1/5.                                      (12)

No equation at B,C or N beyond the complete original-domain entry was
added in this argument, and no individual circle coefficient was made
positive by assumption. In particular (12) holds simultaneously in the
three exhaustive physical masks of

`TYPE_II_FAR_RETURN_B_RADIAL_GAP_AND_COMPLETE_RADIAL_MASK_HAND_REDUCTION_2026_10_31.md`.

Combining with its complete hand upper bounds gives:

| Original physical mask | Necessary hand range |
| --- | --- |
| B unique, C radial | 1/5<q<1/3 and z<11/12 |
| B radial, C unique | 1/5<q<1/3 and z<11/12 |
| B radial, C radial | 1/5<q<5/12, with its exact original radial bridge relation |

The low-ratio portion has been excluded across all three masks at once.
The remaining endpoint, hub and completion obligations are retained;
this necessary bound does not close a whole original row or alter any
fine or coarse flag. The proof uses the displayed identities, ordinary
differentiation, exact integer inequalities and convexity. No external
mathematical script, generated parameter cover, Lean/Lake build or CI
is a premise or operation of this argument.
