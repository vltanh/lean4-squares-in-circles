# Distinct shared-side triangle: complete strict-normal vertex-endpoint exclusion

November 1, 2026. Constructors: root, geometry and vector agents, with independently reconstructed force/torque reductions and scalar disk bounds. **Evidence: H pending a clean noncontributor review.** This manuscript closes the full Type III endpoint from [the exhaustive physical notch classification](DISTINCT_SHARED_SIDE_TRIANGLE_COMPLETE_NOTCH_CHART_AND_TORQUE_EXCLUSION_2026_11_01.md).

## 1. Original physical domain

Keep the same actual nine-square packing in one disk of center O and radius R and its unchanged selected physical force-and-torque certificate. The three core squares are entirely circle-unloaded, have exactly the positive internal triangle edges and one original positive outside exit each. Their actual outside neighbors may repeat; their frames, loads, degrees, other contacts and circle masks are unrestricted.

The actual Type III chart is

    A=[0,1]×[0,1],
    B=[1,2]×[S,S+1],
    C=P+[0,1]u+[0,1]v,
    u=(C_0,S), v=(-S,C_0), C_0²+S²=1, C_0,S>0,
    P=(1-C_0,1), Q=P+u=(1,1+S).

The letter C denotes the actual third square; C_0 denotes the scalar cosine throughout. AB has its original shared-side application `(1,mu)`, with `S≤mu≤1`. AC is the A-owned North contact at P. BC is the point-only contact at the B upper-left vertex and the C right vertex Q. Its selected original strict normal is retained, not replaced by the West normal of the neighboring Type I chart.

Normalize all six forces of this local system by the positive horizontal magnitude of BC. This changes no direction, application, positivity or equilibrium. The original internal oriented vectors are then

    A-to-B: (t,0),      t>0;
    A-to-C: (0,a),      a>0;
    B-to-C: (-1,k),     k>0.

Strict support of Q at both original vertices means

    D_0 := C_0-kS >0,
    E_0 := S+kC_0 >0.

The full outside vectors are exactly

    A: (-t,-a),
    B: (t+1,-k),
    C: (-1,a+k).

**Theorem.** This entire original endpoint chart forces `R>25/12`, and hence is impossible when `R²≤1105/256`. Every original AB mean, strict BC normal, C outside support alternative and possible original outside side mean is included.

## 2. Full A and B torque and the complete C support split

The strictly signed outside vectors force A's original exit application to `(0,0)` and B's to `(2,S)`. Their full torques are

    t mu = a(1-C_0),
    k-1 = t(mu-S) >=0.

Thus k≥1. Together with `C_0>kS`, this implies `C_0>S`, so the actual orientation angle lies strictly between 0 and pi/4.

At C the outside vector F=(-1,a+k) has own components

    F dot u = aS-D_0,
    F dot v = aC_0+E_0 >0.

Its original internal BC force, applied at Q=P+u, is `(1,-k)`; its moment about P is `-E_0`. The AC application P contributes zero. These are the complete original internal moments.

If `F dot u>0`, the original outside application is P+u+v. Its full torque equation becomes

    a(C_0-S)+D_0=0,

which is impossible since both terms are positive.

If `F dot u<0`, the original outside application is P+v. The full torque is

    -aS+D_0-E_0=0.

But `D_0-E_0=C_0-S-k(S+C_0)≤-2S<0`, again impossible.

Consequently every surviving endpoint has `F dot u=0`. Its original outside normal is exactly v, and

    a=C_0/S-k >0,
    F=v/S.

Its unchanged original support application is `P+v+lambda u`, for some original mean `0≤lambda≤1`. The complete torque equation forces

    lambda = S E_0 = S²+kSC_0.

The strict BC support inequality `kS<C_0` implies `0<lambda<1`. The outside-side mean is not discarded: its exact value is derived from the unchanged full torque.

## 3. Three actual points of the same original disk

At any original contact q, a minimum-support point of the outside square in unit direction e has q+e in that same square. This follows component by component in its own side coordinates and includes all support means and endpoints. Apply it separately at the three unchanged outside exits.

### 3.1 A supplies a nearly vertical negative unit point

Let

    w_A=(-alpha,-beta),
    alpha=t/sqrt(t²+a²), beta=a/sqrt(t²+a²).

This is an actual point of A's outside neighbor. The full A torque and mu≥S give

    t/a=(1-C_0)/mu <= (1-C_0)/S.

Since C_0>S, the last quantity is less than `sqrt(2)-1<5/12`. Hence

    0<alpha<5/13<2/5,  beta>0,  alpha²+beta²=1.

### 3.2 B supplies a point strictly to the right of 27/10

From the full B torque and the retained upper mean bound mu≤1,

    k-1=t(mu-S) <= t(1-S) <t.

Thus k<t+1, so the horizontal component of B's original outside unit normal satisfies

    (t+1)/sqrt((t+1)²+k²) >1/sqrt(2)>7/10.

The actual point

    w_B=(2,S)+(t+1,-k)/sqrt((t+1)²+k²)

therefore has `w_B,x>27/10`. No prescribed value of its vertical coordinate is needed.

### 3.3 C supplies a point left of the vertical axis and above height three

The actual unit-step point at C is

    w_C=P+2v+lambda u,
    lambda=S²+kSC_0.

First derive the uniform strict scalar bound k<3/2. Using a=C_0/S-k and mu≥S,

    t <= a(1-C_0)/S
      = (C_0-kS)/(1+C_0)
      < C_0/(1+C_0) <1/2.

Together with k<1+t this proves k<3/2.

The horizontal coordinate is

    w_C,x = 1-C_0³-2S+kSC_0².

For 0≤x≤1, `(1-x)^(3/2)≥1-(3/2)x` (for example its derivative is increasing, or square both nonnegative sides when the right side is nonnegative). Substituting x=S² gives `1-C_0³≤(3/2)S²`. Consequently

    w_C,x < (3/2)S²-2S+(3/2)S(1-S²)
          = -(S/2)(3S²-3S+1) <0.

The last quadratic is `3(S-1/2)²+1/4`, strictly positive.

The vertical coordinate satisfies

    w_C,y = 1+2C_0+S³+kS²C_0
           >=1+C_0(2+S²)+S³.

We have `0<S<1/sqrt(2)<3/4`. Both `C_0(2+S²)` and `2-S³` are positive, and their squared difference is

    C_0²(2+S²)²-(2-S³)²
       = S³(4-3S-2S³)>0.

For the final sign, `3S+2S³<9/4+27/32=99/32<4`. Therefore `C_0(2+S²)>2-S³` and

    w_C,y>3.

We have proved that this actual disk point is of the form `w_C=(-g,d)` with g>0 and d>3.

## 4. Exact midpoint obstruction, with a rational positive margin

We prove the following slightly weaker closed-domain lemma, sufficient for the three actual points above.

> If a disk contains `w_A=(-alpha,-beta)` with `0≤alpha≤2/5`, `beta≥0`, `alpha²+beta²=1`; a point w_B with `w_B,x≥27/10`; and `w_C=(-g,d)` with g≥0,d≥3, then its radius satisfies R>25/12.

Put L=27/10 and

    m=(w_A+w_C)/2, v=(w_C-w_A)/2,
    D=L-m_x=L+(alpha+g)/2 >= L.

Suppose R≤25/12. The B point gives `O_x≥L-R`, hence `O_x-m_x≥D-R>0`. The two other points and the exact parallelogram identity give

    R² ≥ |O-m|²+|v|² ≥ (D-R)²+|v|²,
    D²+|v|² <= 2DR <= (25/6)D.

But direct expansion yields

    F := 4[D²+|v|²-(25/6)D]
       = -371/25+(37/15)(alpha+g)+alpha²+2g²
         +2 beta d+d².

Since d≥3 and `beta≥beta²=1-alpha²`,

    F >=4/25+(37/15)alpha-5alpha²+(37/15)g+2g²
      =4/25+alpha(37/15-5alpha)+(37/15)g+2g²
      >=4/25>0.

Here `alpha≤2/5` gives `37/15-5alpha≥7/15>0`. This contradicts the preceding necessary inequality and proves the lemma.

## 5. Complete endpoint conclusion and family join

The actual points from Section 3 satisfy all the closed-domain hypotheses of Section 4. Thus the entire strict-normal Type III endpoint forces R>25/12. Since

    (25/12)²-1105/256=55/2304>0,

it is excluded throughout the closed research radius. No limiting argument, approximate force deletion or artificially positive angle separation is used.

Combined with the [complete notch classification and radius-free Type II torque exclusion](DISTINCT_SHARED_SIDE_TRIANGLE_COMPLETE_NOTCH_CHART_AND_TORQUE_EXCLUSION_2026_11_01.md) and the [Type I strict-side-owner disk theorem](STRICT_SIDE_OWNER_SHARED_SIDE_NOTCH_EXCLUSION_2026_11_01.md), this proves that **no distinct-contact direct unloaded triangle can have any positive-length internal shared-side contact**. All three original physical internal pair contacts in a surviving triangle must therefore be singletons.

This is a whole geometric feature exclusion. It does not itself exclude all-singleton distinct triangles or automatically close any original nine-square coarse/fine parent. All remaining physical squares and the global common-selected-certificate obligations are retained.
