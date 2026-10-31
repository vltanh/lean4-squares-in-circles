# A shared radial root cannot have the far return in the parallel-tip chart

Date: October 27, 2026.  
Author: rooted_final_review.

**Status: complete local analytic theorem, frozen for full independent review.** The proof uses the complete four-force equation at H, its unchanged right-side mean and one actual physical boundary unit K. It excludes an arbitrary contained unit at the far H corner. It requires no circle contact, mask, force equation or return contact at that unit, and no force-degree premise at K. The original shared-HB/parallel-B chart must be supplied separately before an original-feature conclusion is adopted.

## 1. Exact local physical and force statement

Let

```
0<delta<1/60, d=1+delta, T=2*sqrt(delta),
X=1-delta, G=1-T,
R^2=(d+1)^2+1/4.
```

Keep the actual origin-centered disk of radius R. The actual contained unit H is

```
H=[delta-1,delta] x [-T,G].
```

Its radial leaf application is the actual lower-left vertex

```
L=(-X,-T), |L|=d.
```

Let c,s be positive with `c^2+s^2=1`. The second actual contained unit K, with physical boundary contact, has the full position

```
0<c<T,
Q=(delta,G+c),
m=(-c,s), t=(-s,-c),
K=Q+[0,1]m+[0,1]t.
```

Its actual lowest vertex is

```
W=Q+t=(delta-s,G).
```

The actual right-side force mean at H is

```
P=(delta,-a), 0<a<=T-c.
```

This is the whole stated mean interval; in particular `a=T-c` is included. It is not replaced by a lower H vertex. Retain the complete actual four forces at H:

| Force | Actual application | Actual outward direction or positive multiple |
| --- | --- | --- |
| Genuine radial leaf | L | L, with positive coefficient lambda |
| Right-side neighbor | P | E1, with positive magnitude mu |
| K | W | E2, with positive magnitude tau |
| Far return unit C | F=(-X,G) | r=(-u,v), with positive magnitude omega |

Here `u,v>0` and `u^2+v^2=1`. Writing the leaf coefficient on the unnormalized vector L is harmless: its original unit-direction magnitude is `lambda*d>0`. All other displayed directions are unit vectors. Both the full vector force equation and the full moment equation about H hold for these same data.

C is any actual contained unit square whose inward support for r contains F. Equivalently its actual incoming common normal at F is r, with F minimizing `Z.r` over C. Both physical interiors remain disjoint from H. C may touch further units and may have any physical circle mask or force degree; none is assumed here. K's degree and individual boundary coefficients are also arbitrary.

**Theorem 1.1.** This entire local physical/force configuration is impossible.

The applications P and W and all four actual positive coefficients remain fixed. The theorem does not discard an H force or replace H4 by an isolated three-force law. No C2 or K2 equation is used.

## 2. Whole parameter bounds and the actual K circle corner

The exact radial identity is

```
X^2+T^2=(1-delta)^2+4*delta=d^2.
```

The whole parameter domain gives

```
T^2<1/15, T<4/15,
X>59/60, 11/15<G<1,
G-delta>43/60,
0<c<T<4/15, s>c, 0<s<1,
0<G+c<1.
```

The comparison `T<4/15` follows from `1/15<16/225`, with reserve `1/225`. Also `2*c^2<2/15<1`, so s>c. All denominators used later are strictly positive on this full domain.

The four actual K vertices are Q, W, J=Q+m and

```
Z=Q+m+t=(delta-c-s,G+s).
```

Z is its unique largest-norm vertex. This is established from the full physical square, without selecting a positive circle atom. Direct expansion gives

```
|Z|^2-|W|^2=1-2*delta*c+2*c*s+2*G*s>0,

|Z|^2-|J|^2=1-2*delta*s-2*c*(G+c)
             >1-1/30-8/15=13/30>0,

|Z|^2-|Q|^2=2-2*delta*(c+s)+2*(G+c)*(s-c)>0.
```

For the last line, `c+s<2` and `delta<1/60` make its first two terms greater than `29/15>0`; its last term is positive. In the first line the only negative term has magnitude less than `2/225<1`. These strict comparisons cover the entire c interval.

Squared norm is convex on the actual unit square. Containment together with physical boundary contact therefore gives the exact original circle equality

```
R^2=|Z|^2.                                             (1)
```

No K force law, mask assumption or side-force mean was used in this identification.

## 3. An actual inward support segment

For any unit square C, any unit direction r, and any actual point F in its minimum-r support, the actual point `F+r` belongs to C.

To see this for a vertex support, choose the two actual inward unit axes e,f of C at F. The components of r on these axes are nonnegative and at most one. Thus `F+r` is in the actual square `F+[0,1]e+[0,1]f`. At a side support, r is its inward unit side normal; the whole supporting side translates by r to the opposite side. This includes every point of that actual support, including both endpoints and every shared mean. These alternatives cover the full support, including a zero axis coefficient.

Apply this fact to the actual far support r at F. Since C is contained,

```
|F+r|^2<=R^2.                                         (2)
```

The statement uses no owner selection at HC. In particular a free singleton normal and an actual C-owned side normal satisfy the same fact. No condition on CK is necessary.

Since `|F|^2=X^2+G^2=d^2+1-2*T`, equations (2) and the specified R give

```
X*u+G*v<=d-3/8+T<109/120.                              (3)
```

The final bound is the exact whole-domain comparison

```
61/60-3/8+4/15=109/120.
```

## 4. The complete far-normal angle bound

Equation (3) forces

```
u<1/3, v>14/15.                                       (4)
```

Indeed, the function

```
f(z)=X*z+G*sqrt(1-z^2)
```

is continuous and concave on `[1/3,1]`; on its open interior its second derivative is `-G/(1-z^2)^(3/2)<0`. Its minimum on that whole closed interval is at an endpoint. The two endpoint values satisfy

```
f(1)=X>59/60>109/120,

f(1/3)=X/3+G*sqrt(8/9)
       >59/180+(11/15)*(14/15)
       =911/900>109/120.
```

The radical bound has squared reserve `8/9-(14/15)^2=4/225`. The two displayed endpoint gaps are `3/40` and `187/1800`. Thus no u in the entire interval `[1/3,1]` is possible. Since v is positive, `v=sqrt(1-u^2)>sqrt(8/9)>14/15`. No angle is sampled or assigned a subinterval pose.

## 5. The unchanged H4 gives the opposite angle bound

The full actual H force equation is

```
lambda*(-X,-T)+mu*E1+tau*E2+omega*(-u,v)=0.
```

Its two components give

```
mu=lambda*X+omega*u,
tau=lambda*T-omega*v>0.                                (5)
```

Take the moment of all four actual forces about F. The application differences are

```
L-F=(0,-1), P-F=(1,-a-G), W-F=(1-s,0).
```

The unchanged moment equation is therefore

```
-lambda*X+mu*(a+G)+tau*(1-s)=0.
```

Substituting (5), putting `e=1-s`, and using `G=1-T` gives the exact identity

```
omega*((a+G)*u-e*v)=lambda*D_H,
D_H=X*(T-a)-T*e.                                      (6)
```

The multiplier comparison below needs its actual sign. It is strictly positive throughout the whole mean interval. Since `T-a>=c` and

```
e=c^2/(1+s)<c^2,
```

one has

```
D_H>=X*c-T*e
    >c*(X-T*c)
    >c*(X-T^2)
    >11*c/12>0.                                       (7)
```

Here `X-T^2>59/60-1/15=11/12`; no sign of an unproved force denominator is assumed. Thus `(a+G)*u-e*v>0` in (6). Equation (5) gives `omega/lambda<T/v`, and multiplication by this positive quantity in (6) is safe. Consequently

```
D_H<(T/v)*((a+G)*u-e*v),
X*(T-a)<T*(a+G)*u/v.
```

Every division is by a strictly positive quantity. The actual closed bound `a<=T-c` gives `a+G<=1-c`, so

```
u/v>X*(T-a)/(T*(a+G))
    >=X*c/(T*(1-c))
    >59*c/16.                                         (8)
```

Combining (8) with the whole-angle bound (4) yields

```
u>413*c/120.                                          (9)
```

The side mean a and all four positive magnitudes have remained actual and unchanged. In particular (7)--(9) retain the endpoint `a=T-c`; strictness is supplied by the positive central force tau and the uniform parameter bounds.

## 6. The actual K radius forces the incompatible displacement bound

Use the algebraic comparison point

```
Z_* = F+E2=(-X,G+1).
```

No square is moved to this point. The actual K corner Z of Section 2 gives, by direct expansion and `c^2+s^2=1`,

```
(R^2-|Z_*|^2)/2
  =c*(s-delta)-c^2/2-(G-delta)*(1-s)
  <X*c<c.                                            (10)
```

All strict signs follow from the established full domain: `c>0`, `G-delta>0`, `0<s<1`, and `0<X<1`. In particular `s-delta<X=1-delta`; no assertion that the left side is positive is needed to obtain (10).

The actual point `F+r` from Section 3 has the exact comparison

```
(|F+r|^2-|Z_*|^2)/2=X*u-G*(1-v).
```

Containment (2) and (10) therefore imply

```
X*u-G*(1-v)<c.                                       (11)
```

The same complete angle bound (4), with `u^2+v^2=1`, gives

```
X*u-G*(1-v)
 =u*(X-G*u/(1+v))
 >u*(X-1/3)
 >13*u/20.
```

The denominators are positive and `0<G<1`; hence this inequality remains strict over the whole angle interval. Equations (11) and (9) now give simultaneously

```
u<20*c/13,
u>413*c/120.
```

These are incompatible because c>0 and

```
413/120-20/13=2969/1560>0.
```

This proves Theorem 1.1.

## 7. Original transfer boundary and broad scope

In the intended original shared-HB/parallel-B chart, H is the genuine lower-leaf root, K is the original loaded degree-three unit, P is the unchanged actual shared-HB mean, and Q is the actual BK application. The whole actual B side interval gives `a+Q_y<=1`; the real central contact gives `Q_y=G+c`, so precisely `a<=T-c`. The genuine H vertex leaf supplies `T^2=4*delta` and L. The real H4 supplies (5) and its unchanged moment. These are the exact hypotheses that a complete original chart must establish before applying the local theorem.

No equality `a=T` is made. No actual shared mean is moved. The theorem does not require the B3 mean ratio, any C2 equation, a C circle corner, a physical C mask, a CK contact, a CK owner or a K2 law. It also does not require any further square to be removed. A local contradiction with H and K and an arbitrary contained far-return unit remains a contradiction in the original nine-unit packing.

This source does not prove the complete original shared-HB/parallel-B chart and does not exclude the complementary top HC direction. Those are separate original inputs and features. It is a complete local theorem on the explicitly stated whole chart, not a claim that a missing earlier original manuscript has been recovered.

The only direct original foundation is the full physical force and moment convention in `PHYSICAL_CONTACT_STRESS.md`, exact SHA256

```
d3a8d06a7ea8446585f765086f175ad3e165095a885b9c20631cbc55fcf14fc5.
```

That complete original source is present in `current_pr11/research/nine` and was read. The geometric support-segment fact, actual K corner identification, complete scalar interval and every new force and moment comparison are reproduced above. No newer missing source is a logical prerequisite.

## 8. Exact validation and adoption boundary

The accompanying exact sparse-polynomial and Fraction reconstruction expands the three full K vertex differences, the radial and support identities, both actual H4 components, the complete moment elimination and the two radius comparisons. It also checks every displayed fixed rational reserve and all positive-denominator arithmetic. Such identity checks supplement the whole-domain proof; they are not a geometric exclusion certificate or a sampled search.

The entire source requires a separate full independent mathematical/domain review before adoption. Its original caller must likewise supply the exact actual chart, both genuine-root and shared-mean endpoint covers, and the complementary HC direction union. No whole graph label or coarse original parent is marked here.

No frozen earlier source, original ledger, remote branch, Lean file or CI workflow is changed by this manuscript. The proof introduces zero computational exclusion packets.
