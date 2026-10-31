# Uniform near-diameter bound for an actual four-square axial contact chain

**Date:** October 30, 2026 UTC. **Status:** complete short elementary hand derivation, **NEW / not independently reviewed or adopted as a closure gate**. Applicable to the full physical configuration, independently of stresses, orientations, circle masks and the number of other squares. It is a quantitative refinement of the projected-width mechanism in [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md), Section 7. It does **not** prove the full n=9 bound or exclude every open coarse row.

## Statement

Let `S_0,S_1,S_2,S_3` be four **distinct actual unit squares** with pairwise disjoint open interiors, each contained in the same disk of radius `R`, where

```text
R^2 <= Q := 1105/256.
rho := sqrt(1041)/16 - 1/2.
Delta := 2*rho-3 = sqrt(1041)/8-4.
0 < Delta < 1/30.
```

Let `c_j` be their actual centers, `u_j,v_j` their original orthonormal side axes, and `d` one fixed **signed unit normal**. Assume all **three consecutive pairs** are in tight supported contact in this same direction:

```text
d · (c_(j+1)-c_j) = h_j(d)+h_(j+1)(d),
    j=0,1,2,
h_j(d) = (|d·u_j|+|d·v_j|)/2.
```

The equalities must be actual support equalities; different normal axes on different edges are NOT allowed. Define `x_j=d·c_j` and `m_j=2*h_j(d)=|d·u_j|+|d·v_j| >= 1`.

**Theorem.** All the following are necessary:

1. **Almost exactly four unit-spaced projected centers:** for `j=0,1,2,3`,
   ```text
   j-rho <= x_j <= j+rho-3,
   |x_j-(j-3/2)| <= Delta/2 < 1/60.
   ```
2. **Combined directional width excess budget:**
   ```text
   (m_0-1)/2+(m_1-1)+(m_2-1)+(m_3-1)/2
      <= Delta < 1/30.
   ```
   Consequently `m_1,m_2 < 31/30`, and `m_0,m_3 < 16/15`.
3. **Uniform near-alignment:** let `theta_j in [0,pi/4]` be the smaller angle from `d` to either *unoriented* square side axis. Then
   ```text
   theta_1,theta_2 < (1/2)*arcsin(61/900),
   theta_0,theta_3 < (1/2)*arcsin(31/225).
   ```
   These are approximately 1.94 degrees and 3.96 degrees, respectively; the **exact** arcsin bounds are the assertion.
4. **Antipodal endpoints with transverse control:** for `d_perp` perpendicular to `d`,
   ```text
   x_0 <= rho-3 < 0 < 3-rho <= x_3,
   |d_perp·c_0|^2, |d_perp·c_3|^2
      <= 3*Delta < 1/10 .
   ```
5. A chain of **five** actual squares with **four** such consecutive tight contacts in one direction is impossible at `R^2<=Q` (four projected gaps of at least one would exceed the diameter bound).

This theorem makes **no assertion** that the four centers' transverse coordinates all coincide or that a tilted square can be rotated into alignment. The two interior center transverse coordinates can be substantial; any further capacity argument must retain them.

## Complete hand proof

### Step 1: all center radii are at most rho

For one square with center `c` and orthonormal axes `u,v`, its four corners are `c+(epsilon*u+eta*v)/2`. Maximizing the squared corner norm over both signs gives exactly

```text
max_corner |p|^2
  = |c|^2+1/2+|c·u|+|c·v|
  >= |c|^2+|c|+1/2.
```

The last inequality is the usual `l1>=l2` inequality in the square's orthonormal frame. Disk containment implies `|c|^2+|c|+1/2<=Q`. Solving that increasing quadratic on nonnegative radii yields

```text
|c| <= (sqrt(4Q-1)-1)/2
     = sqrt(1041)/16-1/2 = rho.
```

The exact rational comparison for the width slack is

```text
Delta = sqrt(1041)/8-4 > 0, since 1041>32^2;
Delta < 1/30
  <=> sqrt(1041)<484/15
  <=> 225*1041 = 234225 < 234256 = 484^2.
```

Thus `2rho=3+Delta<3+1/30<4`.

### Step 2: three contacts nearly saturate the full disk diameter

For any unit square, the width in a unit direction is `m=|d·u|+|d·v|>=1`. Each of the three assumed tight support equalities therefore gives

```text
x_(j+1)-x_j = (m_j+m_(j+1))/2 >= 1.
```

Summing gives `x_3-x_0 >= 3`. Since all four centers lie in the disk of radius `rho`, `-rho<=x_j<=rho`. In particular `x_3-x_0<=2rho=3+Delta`.

For any `j`, summing the first `j` minimum gaps gives `x_j>=x_0+j>=-rho+j`. Summing the remaining `3-j` gaps backward from `x_3` gives `x_j<=x_3-(3-j)<=rho-3+j`. These are the first claimed bounds. Their interval has midpoint `j-3/2` and half-width `rho-3/2=Delta/2<1/60`.

### Step 3: every actual directional width is almost minimal

The exact telescoping identity, **before dropping any nonnegative term**, is

```text
x_3-x_0
   = m_0/2 + m_1 + m_2 + m_3/2
   = 3 + (m_0-1)/2+(m_1-1)+(m_2-1)+(m_3-1)/2.
```

As `x_3-x_0<=3+Delta`, the entire excess sum is at most `Delta`. Every summand is nonnegative, hence each interior `m_j-1<=Delta<1/30`, and each endpoint `m_j-1<=2Delta<1/15`. No positive force, torque, orientation identity or circle-corner choice was used.

For the smaller unoriented angle `theta_j in [0,pi/4]`, we have `m_j=cos(theta_j)+sin(theta_j)`, so `sin(2theta_j)=m_j^2-1`. The respective exact upper bounds are

```text
(31/30)^2-1 = 61/900,
(16/15)^2-1 = 31/225.
```

Since `2theta_j in [0,pi/2]`, sine is increasing there and gives the announced arcsin bounds.

### Step 4: endpoint transverse projections are small

The `j=0` and `j=3` projected-center intervals yield `x_0<=rho-3<0` and `x_3>=3-rho>0`. Thus `|x_0|,|x_3|>=3-rho`. Orthogonality and `|c_0|,|c_3|<=rho` give

```text
|d_perp·c_e|^2 <= rho^2-(3-rho)^2
                = 6rho-9 = 3Delta < 1/10,
    e=0,3.
```

For five squares with four tight same-normal links, the same minimum-width argument gives an endpoint projected gap at least `4`, contradicting `2rho<4`. QED.

## Stress/graph corollary, exact scope

If a positive-stress path has two **genuine unloaded true-positive-degree-two** internal squares and its endpoint squares are distinct, then their two nonzero forces cancel at each internal vertex. By the actual selected tight support equality and consistent path orientation (cf. [PLANAR_STRESS_CORE.md](PLANAR_STRESS_CORE.md), Section 7), all three signed path normals agree, so **this theorem applies**. Endpoint degrees and circle loads can be arbitrary. Retain both internal squares and all other physical units, any independent endpoint forces and all actual application means. Do not apply it to a loaded degree-two node or to a branch that has been made degree two by deleting another positive edge.

This gives a full-width, configuration-independent **diagnostic** for the long near-diameter channels occurring in various six- through nine-body graphs. It does not establish that any particular original graph/load parent contains such a path, or that the additional five physical squares are impossible. A separate current-source independent review and complete caller joins are required before original fine/coarse closures can change.

**Sharpness guard:** the theorem retains `R^2=Q` and permits a unit-spaced four-square projected row; it does not exclude the known record packing. No CI, Lean compilation, numerical pose search, new packing certificate or gate update accompanied this derivation.