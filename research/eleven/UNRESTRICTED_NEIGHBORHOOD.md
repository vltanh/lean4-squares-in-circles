# An explicit physical neighborhood with eleven independent orientations

This makes the unrestricted local theorem quantitative. The neighborhood
includes independent motions of all eleven square centers and angles;
physical separation may choose either owner at each parallel contact. No
prescribed owner halfspace or common orientation group is assumed for the
perturbed packing. The result still requires proximity to the exact candidate
family and does not provide global capture.

Normalize the containing circle to have center zero and rotate the packing
so square 0 has angle zero. Choose the continuous angle lifts near the
candidate reference angles `(0,...,0,alpha*,alpha*,beta*,beta*)`. Let h be the
actual horizontal coordinate of square 1, and use as reference the exact
contact configuration with that same h and squared radius qc. Require

```
H - 1/10000 <= h <= a + 1/10000.
```

The reference configuration is defined throughout this enlarged interval,
even outside the physically feasible slider range. All twenty-four selected
contact equalities remain exact there. Denote center deviations by `delta pi`,
angle deviations by `omega_i`, and squared-radius deviation by `rho=q-qc`.
Thus `delta p1.x=0` and `omega_0=0`. Define

```
N = max(all twenty-one remaining center-coordinate deviations in absolute
        value, all eleven |omega_i|, |rho|).
```

Angles are measured in radians.

**Theorem.** Every physical packing with `N<=1/10^7` satisfies `q>=qc`.
If `q=qc`, then N=0 and `H<=h<=a`; hence the packing is precisely the exact
slider family. Rigid motions, reflection and relabeling transport this
statement to the corresponding copies of the family.

## Exact constants

`check_unrestricted_neighborhood.py` replays the established angular stress
certificate and checks additional rational bounds. Uniformly throughout the
enlarged slider range:

* Every one of the twenty-four stress weights exceeds 1/100, and their total
  W is less than 20.
* Every selected reference disk vertex has norm less than 5/2. Every selected
  pair's reference center difference has norm less than 3.
* Every parallel selected pair has `|tau|<999/1000`, where tau is its signed
  tangential center difference. Thus each unused transverse axis has physical
  separation slack less than -1/1000.
* The fifteen alternate owner axes at the five oblique contacts have slack
  less than -1/100, as previously certified. Each oblique relative angle is
  between 1/100 and `pi/2-1/100`: this follows from its certified positive
  sine and cosine bounds and `sin(x)<=x` for x>=0.
* The grouped twenty-four by twenty-four Jacobian, expressed in ordinary
  group angles rather than half-angles, has inverse infinity norm less than
  40. This matrix is used only to estimate a perturbation, not to assume that
  the perturbed angles form groups.

For the last bound, the exact interval solver encloses each column of the
inverse transposed half-angle Jacobian. Its column sums are the inverse
Jacobian's row sums. Converting to ordinary angles multiplies its two angle
rows by `2/(1+t^2)<2`; all other rows are unchanged. Every division uses an
interval pivot excluding zero. The resulting maximum row sum is checked
strictly below the rational constant 40. The grouped matrix is independent
of h: the only selected edges involving square 1 have vertical reference
normals and no variable group-angle derivative.

## Quantitative physical owner persistence

For a perturbation of size N, the center difference of any selected pair
changes in norm by at most `2*sqrt(2)*N<3N`. A unit owner normal changes by at
most N, and the reference center difference has norm less than 3. Hence its
unsigned projected center difference changes by at most 6N.

The square-pair support width along either owner's axis is
`k(delta)=(1+|cos(delta)|+|sin(delta)|)/2`. This function is 1-Lipschitz, and the
relative angle changes by at most 2N. Thus every unsigned physical separator
slack changes by at most 8N. Since `8/10^7<1/1000`, all previously excluded
axes remain excluded. Every selected projection has reference value at least
one; its sign remains positive because `6/10^7<1`. Each oblique relative angle
stays in its smooth first-quadrant branch because `2/10^7<1/100`.

Consequently physical nonoverlap implies the following twenty-four
nonnegative actual slacks `f_i`: ten selected disk-corner slacks, five unique
oblique separator slacks, and nine maxima of the two parallel-edge owner
slacks. Both parallel owners and their ties are retained.

## A uniform second-order error of 10N squared

Let `D_i` be the physical directional expression from `LOCAL_OPTIMALITY.md`
evaluated at the actual deviation vector, without normalizing its length.
Then

```
|f_i-D_i| <= 10 N^2
```

for all twenty-four slacks. The reference values are zero, including for the
formal reference configurations just beyond slider endpoints. Here are
explicit bounds proving this estimate.

For a disk corner, its reference offset z has norm `1/sqrt(2)<1`. Rotation
satisfies
`|R_omega z-z-Jz*omega| <= |z|*omega^2/2 <= N^2/2` and
`|R_omega z-z|<=N`. Its full vertex displacement has norm at most
`sqrt(2)N+N<(5/2)N`. Expanding the squared norm, using the reference vertex
norm less than 5/2, bounds the error by
`(5/2)N^2+(25/4)N^2<10N^2`.

For an owner projection, the normal's rotation remainder contributes at
most `(3/2)N^2`. The product of normal change and center-difference change
contributes less than `3N^2`. The total projection error is less than
`(9/2)N^2`.

At an oblique contact the support's second derivative has absolute value at
most one; its relative-angle perturbation is at most 2N. Its Taylor error is
at most `2N^2`. At a parallel contact, expand cosine at zero and use
`||sin(x)|-|x||<=|sin(x)-x|<=x^2/2`; the support error is again at most
`2N^2`. The maximum of two real numbers is 1-Lipschitz in their maximum norm,
so taking the physical maximum of the two owner projections preserves this
same error bound. Combining projection and support errors gives less than
`(13/2)N^2<10N^2`.

## From angular flow to a numerical contradiction

Let E be the nine parallel edges and define

```
T = sum_{(i,j) in E} |omega_j-omega_i|.
```

The exact positive angular-flow margin from `LOCAL_OPTIMALITY.md` gives

```
sum_i w_i D_i <= rho - T/100.
```

The weighted Taylor error has absolute value below `10W N^2<200N^2`.
Assume `rho<=0`. Since all actual slacks are nonnegative,

```
0 <= sum_i w_i f_i <= rho - T/100 + 200N^2 <= 200N^2.
```

Therefore

```
T <= 20000N^2,
0 <= f_i <= 20000N^2,
|D_i| <= 20010N^2.
```

The second inequality uses each weight's strict lower bound 1/100.

Now replace the eleven independent angle deviations in each linear smooth
expression by the group representatives `0,omega_7,omega_9`. Every angle
changes by at most T, because the nine-edge graph has exactly the connected
components `{0,...,6}`, `{7,8}`, `{9,10}` and `omega_0=0`.

Let `L_i` be the resulting grouped linear expression, retaining the actual
center deviations and rho. For a disk constraint the sum of absolute angular
coefficients is at most five, since it is `-2 vertex dot J offset`. For an
oblique separator it is at most `|tau|+2|k'|<3+2=5`. For a parallel separator,
the smooth coefficients have total absolute value at most one, and its
nonsmooth penalty is at most `T/2`. Thus in every case

```
|L_i-D_i| <= 5T,
|L_i| <= 120010N^2.
```

Let z collect the twenty-one center deviations, the two group representative
angles and rho. These twenty-four expressions are exactly `J_angle z`.
The certified inverse norm gives

```
|z|_infinity <= 40*120010 N^2.
```

Every actual angle differs from its representative by at most T, while the
other coordinates already occur in z. Hence

```
N <= |z|_infinity + T <= 4820400 N^2.
```

If `0<N<=1/10^7`, division by N gives
`1<=4820400/10^7<1`, a contradiction. Thus N=0 whenever q<=qc. Physical
nonoverlap then forces `H<=h<=a` by the previously proved full-SAT slider
necessity. This proves the theorem, including complete equality at both
slider endpoints.

## Reproduction and scope

```
python research/eleven/check_unrestricted_neighborhood.py
```

The checker uses only exact standard-library rational arithmetic and replays
the earlier physical angular certificate. No finite difference, optimizer
output, floating feasibility tolerance or unproved second-order condition is
used. The explicit radius is conservative. A future global classification
may use this rectangle-shaped neighborhood as an exact retained terminal,
but must still prove capture into it or exclude every other class.
