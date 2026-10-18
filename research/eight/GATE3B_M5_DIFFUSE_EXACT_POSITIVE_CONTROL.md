# An exact M5-DIFFUSE packing above the sharp candidate

**2026-10-13. Constructive negative control for overstrong structural claims.** This is an exact rational full eight-square packing. It is **not** a counterexample to the proposed sharp squared radius q_*≈3.915535: it fits in q=397/100=3.97, strictly ABOVE the research ceiling Q=9789/2500. Its purpose is to show that M5-DIFFUSE is not geometrically empty near radius two and that seven rational depth-three owner graphs plus a positive Jensen defect are not by themselves a complete radius obstruction.

## Rational frames and centers

Let `B=414213562373/10^12` and let

```
t=(1/2000,3/2000,-3/2000,-1/2000,-1/8000).
z=(0,1/1000, (B+t0)/(1-B*t0),...,(B+t4)/(1-B*t4),
   (1-1/1000)/(1+1/1000)).
```

For each i use genuine unit-square orthonormal frame

```
e_i=((1-z_i²)/(1+z_i²), 2z_i/(1+z_i²)),
f_i=(-e_i.y,e_i.x).
```

Take centers `p_i=(5001/5000)(a_i,b_i)/10^6`, where the integer pairs are

```
i  (a_i,b_i)
0  (-55438,9590)
1  (-501244,1222533)
2  (-1056036,-926381)
3  (1057741,-925965)
4  (-1265031,278678)
5  (356,-1284918)
6  (1265145,280149)
7  (500754,1222818).
```

These were discovered using a numerical fixed-frame convex optimization, then rounded and outward-center dilated. **The finite-coordinate proof uses only exact fractions and no optimizer.**

## Complete exact checks

[verify_m5_diffuse_rational_positive.py](verify_m5_diffuse_rational_positive.py) checks:

* all eight orientations; exact closed 45-degree window counts `(5,5,4,4,5,5,4,4)`, hence genuine maximum-five M5;
* folded word **I**, `LHLHLHLL`, by strict exact rational order of folded angle tangents, with label order `(0,2,1,3,4,7,5,6)`;
* all 32 genuine vertices strictly within the squared-radius `397/100`, in fact a squared-radius reserve larger than `1/2000`;
* all 28 pairwise disjointness conditions using genuine canonical signed SAT axes, with strictly positive support gap larger than `1/10000`;
* all seven rational projected-center order graphs from [GATE3B_M5_DIFFUSE_SEVEN_RATIONAL_ORDERS.md](GATE3B_M5_DIFFUSE_SEVEN_RATIONAL_ORDERS.md), with longest directed path lengths `(2,0,2,2,1,2,0)`;
* a strict **Jensen defect J>1/120>3/1000**, so the packing is genuinely M5-DIFFUSE rather than a LOW/near-cut example.

For the final nontrivial strict bound, its true pair-width sum W is an exact rational number, and the verifier proves

```
W -(41+15*(14143/10000))/2 > 3/200.
```

Since `sqrt(2)<14143/10000`, this gives `E=W-(41+15sqrt(2))/2>3/200`.

In its M5-I folded chart the dominant cut is k=4. The exact rational half-tangent frames satisfy `|tan(theta_3-pi/4)|<1/100` and `|tan(theta_4-pi/4)|<1/100`; because `pi/4>3/4`, the sum of odd simplex weights obeys

```
Lambda_odd <=1-lambda_4<2/75.
```

With `c=(sqrt(2)-1)/2<1/4`, the Jensen defect satisfies

```
J=E-c*Lambda_odd>3/200-1/150=1/120>3/1000.
```

Thus every qualitative descriptor—M5, folded I, DIFFUSE, actual nonoverlap, whole-disk containment, and owner-graph path depth—is proved exactly, not inferred from numerical sampling.

## Correct implication for Gate 3B.2

M5-DIFFUSE cannot be excluded on **combinatorial and frame-dispersion grounds alone**. The example already passes all seven depth-three rational order tests and the strict Jensen-diffuse condition. Any proof using these tests must also exploit sufficiently sharp disk/whole-square geometry at the actual research ceiling. Since this example lies at q<397/100 but **not** below Q=9789/2500, it does not refute a radius-specific M5 exclusion.

M5-DIFFUSE, M5, and unrestricted R_8>=R_* remain OPEN. No Lean/CI or global sharpness claim is made.
