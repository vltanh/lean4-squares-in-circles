# Root physical review: full-angle common-side row and oriented pair cap

4 November 2026. **Accepted as conditional physical inputs.** This review
adds no original-cell or mask closure. The same 231 original cells and 32
masks retain their existing identities. No Lean, Lake or CI was run.

The review covers the physical reductions, all signed owner cases, the
closed finite covers, the independent exact checkers, equality, and the
caller obligations below. It does not treat an optimizer result or a guard
fixture as a proof of a whole original domain.

## 1. Oriented endpoint cap

Write Q=1105/256, a=46, b=27/2, k=207/16 and K=211/4. For two retained
original squares M,B in the disk, put h=(alpha+|beta|)/2. When M has
canonical angle in [0,pi/4] and a genuine original-owned separator from
M to B has strictly negative vertical component, the proved inequality is

```
46(-x_M-h_M)+(27/2)(-x_B-h_B)
    +(1265/32) beta_M-(119/2)(1-alpha_M) <= 211/4.
```

It is strict below Q. There is no replacement frame, surrogate square, or
new cone comparison. The normalized extra toll is
55 beta/64 -119(1-alpha)/92.

I checked the support reduction in the two actual disk directions
`-a e-k n` and `-b e+k n`, together with the actual square separator. After
vertical reflection, M's angle is negative and the separator is (c,s)
with s>0. The main contribution is exactly

```
a(alpha+beta)+k[(c alpha-s beta)_+ +(c beta+s alpha)_+].
```

For a B-owned normal, the free B frame has the complete E/N/D candidate
list. The reason is concavity of the support sum on every projection-sign
interval; no interior minimum or signed owner is omitted. For an M-owned
normal, the two possible axes with strictly positive vertical component
are (beta,alpha) and (-alpha,beta), with contributions
`a(alpha+beta)+k` and `a(alpha+beta)`. At beta=0 a horizontal axis is not
an additional strictly upward separator; it is only a limiting face.

The tangent estimate for the disk support is
`H(c) <= H(0)+(k/2)c`, strict unless c=0, with
`H(0)=32Q=a+b+2k+K`. I checked the analytic small rectangle
`|c|<=1/4`, `0<=z<=1/20`, including the positive boundary estimate
37793/1150000 and the unique zero c=beta=0. The remaining three closed
B-owned rectangles and four M-owned cases cover the full half-angle
range, since `sqrt(2)-1<5/12`. Both halves of each subdivision are kept.

The fresh root run of the independent directed-integer checker verified
all **6,170 leaves**, maximum depth 20, with no frontier, using 64-bit
directed rational bounds. The least positive reserve is
2041502494679/72057594037927936. Thirteen analytic identities were checked.
The equality analysis forces both frames aligned; the reflected centers
are M=(-3/2,-1/16), B=(-1,15/16), with the vertical signs reversed in the
unreflected statement.

## 2. Full-angle four-original row

The row theorem retains the seven originals A,H,I,D,E,F,G. It requires
horizontal order of A,H,I,D, total vertical variation at most 13/100,
and the actual EF,FG links with their original center-cone comparisons.
It proves `R^2>=Q`; at Q all seven frames align and `x_D-x_A=3`.
The other two original squares remain available to the caller.

Opposite endpoint signs use the already accepted full-angle opposite-tilt
theorem. For equal endpoint signs, the accepted common-side theorem puts
E,F,G on the same vertical side of the row. The endpoint separator signs
are therefore the signs required by the oriented cap. Its horizontal
endpoint gaps are strictly below 1; the cap is not inferred from a
non-strict horizontal bound. After the stated reflections, the left toll
is the good toll and the right toll is

```
max(2 beta/23, (9 beta-41(1-alpha))/32).
```

Both right-cap formulas have their full-angle inherited proofs. Summing
the actual endpoint caps and actual short-row gaps yields
`span-h_A-h_D+T_good+T_bad<=2`, strictly below Q.

For each adjacent pair of the four originals, choose its actual
separating normal. With horizontal center difference d and vertical
difference v, its owner o gives

```
d >= (1+cos(delta)+|sin(delta)|)/(2 alpha_o)
          - |tan(theta_o)| |v|.
```

I checked that d>|v| excludes the backwards normal choices and that the
steep-axis case has the same stated lower bound. The four sign patterns
of the internal frames, eight owner patterns, and each distinct selected
owner give exactly 80 scalar domains. The scalar lower bound has slope
coefficient 131/1000, exceeding the variation budget 130/1000.

I checked the half-angle substitution and the positive denominator used
by the independent integer-polynomial checker. The good-endpoint
numerator is `-368+529z-1536z^2` over `736(1+z^2)`. The two bad-branch
formulas differ by `z(143-943z)/(368(1+z^2))`. The epsilon coefficients
minorize the absolute sine terms; the tau mixture minorizes the maximum
of the two bad branches. Multiplication by
`92000 product(1-z_i^4)` and the positive dyadic witness denominator
gives degree at most four in each variable, with selected-slope term
`-24104 z_k`. All these multipliers are strictly positive on [0,5/12]^4.

The fresh root replay verified **80 domains, 1,704 nodes, 892 leaves and
557,500 integer Bernstein coefficients**. There are 812 strictly positive
leaves and 80 nonnegative alignment leaves, with no frontier. Every
binary split retains the whole parent and both shared faces. The checker
independently constructs the target polynomial and coefficient transform;
the discovery polynomial generator is not imported by replay.

Summation now gives `span-h_A-h_D+T_good+T_bad >= 2+M/1000`, where M is
the maximum absolute selected-owner slope. Equality forces M=0. An
unselected interior frame between aligned neighbors contributes
`alpha+beta-1`, positive unless aligned. An unselected endpoint has
positive toll unless aligned; the good toll divided by beta is at least
1415/4416. Thus the equality claim includes unselected frames as well as
the selected owners. Equality in the cap and short-row steps then aligns
E,F,G and gives span 3.

## 3. Closed-Q exclusion for the unchanged 001/00 caller

The generic seven-square theorem permits equality. The fixed 001/00
caller also retains B,C, actual AB and BC, the original CD center cone,
and the strictly weak CD bit. At equality,

```
3 = x_D-x_A >= h_A+2h_B+h_C+g_C+g_D
               = 1+2h_B+h_C+g_C >= 3.
```

Here `h+1/(4h)-1=(2h-1)^2/(4h)`. Equality aligns B,C and forces
`x_D-x_C=1=h_C+h_D`, contradicting the strict weak CD bit. This last
step must be supplied whenever the full-angle guard is used as an
exclusion rather than as the generic lower-bound theorem.

The guard uses weak horizontal order. Equality of adjacent horizontal
coordinates cannot survive the height budget and original unit center
separation, so the physical theorem's strict pair-gap argument follows.
Its full closed complement contains three order failures and all eight
signed-height failures. These **11 closed domains** deliberately overlap
on boundary faces. No endpoint sign restriction is introduced.

## 4. Guarded oriented affine row

The pair cap can also be used without a small-variation hypothesis. For
an actual original pair M,B, require proved strict horizontal bounds
`-1<dx_lower<=dx_upper<1`, a proved sign delta of `y_B-y_M`, and a proved
main frame sign eta. Set sigma=eta*delta. Every actual separator has the
required vertical sign; a zero vertical center gap would contradict
unit center separation under the strict horizontal bound. Independent
horizontal and vertical reflection gives precisely

```
46 sigma x_M +(27/2) sigma x_B
 +(73/2) alpha_M +(529/32) |beta_M|
 -(27/4) alpha_B -(27/4) |beta_B| <= 449/4.
```

I checked this expansion and every reflection sign. The absolute-beta
coordinate is the genuine original |beta|. The necessary row remains
valid in an outer relaxation because the row is asserted only for
physical witnesses, even when the relaxation's auxiliary bounds are
weaker. No new variables or independent auxiliary endpoints are used.

The producer and independent converter have matching 54-variable
layouts. The independent `check` function reconstructs the whole ordered
list of applicable rows and guards from the supplied original state;
its fresh fixture replay passes 32 exact checks. A caller must replay the
ancestry of every bound used by these guards. A guard report alone never
proves those bounds or the original physical premises.

## Accepted use and limits

`PREMISE_BINDINGS.json` pins the reviewed sources, proof tables, fresh
replay reports, and inherited theorem dependencies. The exact cap source
and its independent row converter may now be used in original-cell
certificates, subject to the strict horizontal and sign guards above.
The full-angle row guard may be used only with the complete original
caller and certified order/height bounds. A parent split must still have
all siblings closed before the parent earns credit.

The accepted ledger remains **219/231 original current-mask cells and
8/32 whole masks**. These tools strengthen future certificates; this
packet itself closes zero original cells and zero masks.
