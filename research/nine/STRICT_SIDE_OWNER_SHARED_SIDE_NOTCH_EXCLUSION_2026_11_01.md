# Exact disk obstruction for the distinct shared-side notch with a side-interior return

November 1, 2026. Constructor: `vector_analytic`. Complete hand proof at the explicit chart scope below; independent review requested. This is one distinct-contact physical feature, not an automatic original-parent closure.

## 1. Original physical chart and complete scope

Retain the same actual packing, containing disk with center O and radius R, all nine squares, and one unchanged original force-and-torque certificate. Let three entirely circle-unloaded squares have exactly the three internal positive triangle edges and one original positive outside edge at each. The actual outside terminals may coincide and have arbitrary frames, loads, degrees and additional contacts.

Suppose that, after one rigid motion and relabeling, the actual core squares are

    A = [0,1] × [0,1],
    B = [1,2] × [s,s+1],
    C = P + [0,1]u + [0,1]v,
    u=(c,d), v=(−d,c), c²+d²=1, c,d>0,
    P=(1−c,1), Q=P+u=(1,1+d),
    d < s < 1.

Thus AB has the actual positive-length shared segment `{1}×[s,1]`; AC is C's bottom vertex P on the relative interior of A's top side; BC is C's right vertex Q on the relative interior of B's left side. The original shared-side AB application is `(1,mu)`, with its entire unchanged range `s≤mu≤1`.

Write t,a,b>0 for the original AB, AC and BC magnitudes. Their physically fixed outward normals are, respectively, A-to-B east, A-to-C north, and B-to-C west. The three full outside vectors are consequently

    A: (−t,−a),   B: (t+b,0),   C: (−b,a).

**Theorem.** Every such complete physical chart forces

    R > 25/12,
    R² > 625/144 > 1105/256,
    625/144 − 1105/256 = 55/2304.

The proof does not use a small-force approximation, delete any positive edge, reselect any support normal or mean, or impose any equation on an outside terminal. The endpoint `s=d`, where Q is also a B vertex and its original strict normal can be free, is a separate feature and is not silently included in this fixed-side-normal theorem.

## 2. Three-point disk lemma

Suppose the same disk contains points

    w_A=(−alpha,−beta),   w_B=(3,eta),   w_C=(−gamma,delta),

where eta is arbitrary and

    0≤alpha≤beta,  alpha²+beta²=1,
    gamma≥−1,  delta≥0,  gamma+delta≥3.

Then `R>25/12`.

**Proof.** Set

    m=(w_A+w_C)/2,  v=(w_C−w_A)/2,
    D=3−m_x=3+(alpha+gamma)/2≥5/2.

If `R≤25/12`, the point w_B implies `O_x≥3−R`, so

    O_x−m_x≥D−R>0.

The exact parallelogram identity for w_A,w_C, both in the disk, gives

    R² ≥ |O−m|²+|v|² ≥ (D−R)²+|v|².

Thus `D²+|v|²≤2DR≤(25/6)D`. We show the reverse inequality with a strictly positive rational margin. Direct expansion and `alpha²+beta²=1` give

    F := 4[D²+|v|²−(25/6)D]
       = −13+(11/3)(alpha+gamma)+alpha²+2gamma²
         +2 beta delta+delta².

Since `alpha≤1/sqrt(2)<11/15` and `beta≥beta²=1−alpha²`,

    K := alpha²+(11/3)alpha+6beta−4
       ≥ 2+alpha(11/3−5alpha) ≥ 2.

If `gamma≤3`, then `delta≥3−gamma≥0`. The displayed F is increasing in nonnegative delta, and therefore

    F ≥ 3gamma²−(7/3+2beta)gamma+K.

For gamma≤0 this is at least 2. For `0≤gamma≤3`, use beta≤1 to obtain

    F ≥ 3gamma²−(13/3)gamma+2
      = 3(gamma−13/18)²+47/108 > 0.

If gamma≥3, instead discard the nonnegative delta terms and the nonnegative alpha terms from the original formula:

    F ≥ −13+(11/3)gamma+2gamma² ≥16>0.

In every case F is strictly positive, contradicting the required inequality. This proves the lemma, including all displayed closed boundaries. QED.

## 3. Full original A torque gives the first actual disk point

Both components of A's original outside vector `(−t,−a)` are strictly negative, so its original outside application is forced to the actual A corner `(0,0)`. Torque about that corner, including both internal original forces, is

    −t mu + a(1−c) = 0.

Because `mu≥s>d`,

    t/a = (1−c)/mu < (1−c)/d = d/(1+c) <1.

Consequently its unit outside normal is `(-alpha,-beta)` with

    alpha=t/sqrt(t²+a²),  beta=a/sqrt(t²+a²),
    0<alpha<beta,  alpha²+beta²=1.

At any original square-square contact with unit normal e from the core to its outside neighbor and original application q, the same outside square contains q+e. In its own coordinates, adding the components of e moves inward from its minimizing support face by at most one. This includes all outside support vertices, side means and endpoints.

Here q=(0,0), so the actual outside square supplies `w_A=(-alpha,-beta)`.

At B its full outside force is `(t+b,0)`. Its unchanged original application has first coordinate 2, regardless of its tangential mean. The same unit-step fact supplies an actual disk point `w_B=(3,eta)`, with no imposed value of eta.

## 4. Every full C torque alternative gives the third scalar region

The full original outside vector at C is `E=(-b,a)`. Its v component is `bd+ac>0`. Its u component is `ad-bc`, whose three signs exhaust all actual support features of this exit. The original internal AC application is P and the original BC application is Q=P+u. Torque about P therefore gives

    −bd + det(q_C−P,E)=0.

No application on an outside support side is replaced by a convenient endpoint.

### 4.1 Negative u component: original exit at P+v

If `ad-bc<0`, its unchanged C application is `q_C=P+v`. The torque equation is

    b(c−d)=ad.

Thus c>d and the outside unit normal is

    e_C=(-d,c−d)/sqrt(d²+(c−d)²).

The actual point `w_C=P+v+e_C` has first coordinate at most one and positive second coordinate. Moreover

    w_C,y−w_C,x
       = 2c+d + c/sqrt(d²+(c−d)²) ≥ 3.

Indeed `d²+(c−d)²≤c²` when d≤c. Also `2c+d≥2`: writing `z=d/c∈[0,1]`, its squared comparison reduces to

    (2+z)²−4(1+z²)=z(4−3z)≥0.

### 4.2 Positive u component: original exit at P+u+v

If `ad-bc>0`, the original application is `q_C=P+u+v`. Full torque yields

    a(c−d)+bc=0.

Thus d>c and the unit exit normal is

    e_C=(-(d−c),c)/sqrt((d−c)²+c²).

Again `w_C=q_C+e_C` has first coordinate at most one and positive second coordinate. The symmetric version of the preceding elementary inequalities gives

    w_C,y−w_C,x
       = 2d+c + d/sqrt((d−c)²+c²) ≥3.

### 4.3 Zero u component: retain the full original exit mean

If `ad-bc=0`, the outside unit normal is exactly v. Its original maximum-support application is

    q_C=P+v+tau u,   0≤tau≤1.

This tau is the original mean, not a newly chosen one. The complete C torque equation forces `tau=d²`. Therefore the actual outside point is

    w_C=P+2v+d²u.

Its first coordinate is at most one and its second coordinate is positive. Writing `h=c+d∈[1,sqrt(2)]`, we obtain

    w_C,y−w_C,x = c³+d³+2(c+d)
                = h(7−h²)/2
                = 3+(h−1)(2−h)(h+3)/2 ≥3.

All three C cases therefore place the unchanged actual outside point in precisely the region of the disk lemma: on writing `w_C=(-gamma,delta)`, one has `gamma≥−1`, `delta≥0`, `gamma+delta≥3`.

## 5. Conclusion and original-feature boundary

The three actual outside points satisfy every hypothesis of Section 2. Hence `R>25/12` and this entire side-interior-return chart is excluded at the closed research radius `R²≤1105/256`.

The result includes all original AB means, all three C outside support alternatives, the complete C outside-side mean interval before it is forced by torque, arbitrary outside frames, and repeated actual terminal identities. All other squares, contacts and load masks remain unchanged.

For a complete shared-side-feature theorem, an exhaustive physical notch classification must separately treat the return at the B vertex, with its strict free normal, and the B-vertex/C-side-interior contact type. This source proves the displayed strict-side-owner chart only. It does not alter any original coarse or fine flag by itself.
