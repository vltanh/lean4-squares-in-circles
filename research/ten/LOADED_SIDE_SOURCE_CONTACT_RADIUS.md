# A loaded two-side source cannot apply a force inside the unit disk at large radius

**Status:** complete hand argument; root and independent full mathematical
reviews passed. The strengthened range `22/5<=q<=9/2` is proved and
independently reviewed in Section 3 of
[LOADED_OUTER_CORNER_CLEARANCE.md](LOADED_OUTER_CORNER_CLEARANCE.md).

Use an entirely loaded seven-ring with `223/50<=q=R^2<=9/2`. Let a
unique-circle body have the two-inner-side row U1. Then both of its
actual contact application points have norm strictly greater than one.

Consequently, in the selected certificate of
[LOADED_OUTER_VV_NORMAL_EXCLUSION.md](LOADED_OUTER_VV_NORMAL_EXCLUSION.md),
a U4/U5 body whose extra corner B has squared norm at least `83/50` has
its opposite V contact with a unique-circle mixed inner-side body U6 or
U7. The source alternative U1 in that note is excluded here.

## 1. A one-sided square bound without a slope restriction

Let `P=(a,-b)` with a,b>=0. Every unit square supported in `x<=a` and
containing P has each vertex z bounded by

```text
|z|^2<=max(a^2,(a-1)^2)+(b+1)^2.                     (1)
```

For side-interior support the square is parallel to the coordinate axes,
and (1) is immediate. For vertex support its incident unit edges are
`(-c,s),(-s,-c)`, with c,s>=0 and c^2+s^2=1, or their vertical reflection.
Each incident edge has scalar product with P at most b, giving the
first candidate `a^2+(b+1)^2`.

For the diagonal, the larger of the two reflection expressions is
`-a(c+s)+b|c-s|`. This is at most b-a. If b>=a, its two possible linear
expressions have one coefficient b-a and the other -(a+b), so the bound
follows from c,s<=1. If a>=b, use
`a(c+s)-b|c-s|>=(a-b)(c+s)>=a-b`.
The diagonal squared norm is consequently at most
`(a-1)^2+(b+1)^2`. This proves (1) for every support point, without an
assumption b<=a.

## 2. Source coordinates and a supposed small application point

Write the source as

```text
C=[U-1,U] x [-V,1-V],       U,V>7/8,
U^2+V^2=q,
P=(eta*U,1-V),       Q=(U-1,-eta*V),       0<eta<=1.   (2)
```

The coordinate and concurrence facts are the reviewed double-side
restriction. Both neighbors are loaded. Suppose, for a contradiction,
that `|P|<=1`, and put p=eta*U and b=eta*V. Then

```text
p^2+(V-1)^2<=1,
p<=1,
b<=V/U,
b^2<=V^3(2-V)/U^2.                                  (3)
```

If V>=3/2, the one-sided neighbor bound across the top support gives

```text
q<=(p+1)^2+(V-1)^2<=2+2p<=4,
```

contradicting q>=223/50>4. Hence V<3/2. This gives U>1, so the left
neighbor at Q satisfies (1) with a=U-1>0. Its squared vertex norms are
bounded by

```text
M=max((U-1)^2,(U-2)^2)+(b+1)^2.                       (4)
```

We show M<q using four elementary intervals covering 7/8<V<3/2.
In the first three, U>3/2 and the maximum in (4) equals (U-1)^2.
Always

```text
q-(U-1)^2=2U-1+V^2.                                 (5)
```

## 3. Four rational bounds make the other neighbor circle-clear

If `7/8<V<=1`, then U>9/5 and b<5/9<3/5. Therefore

```text
q-(U-1)^2>13/5+49/64>64/25>(b+1)^2.
```

If `1<=V<=5/4`, then
`U^2>=223/50-25/16=1159/400>(17/10)^2`.
Thus U>17/10 and b<25/34<3/4. Hence

```text
q-(U-1)^2>17/5>49/16>(b+1)^2.
```

If `5/4<=V<=7/5`, then U^2>=5/2>(79/50)^2. Thus
U>79/50 and b<70/79<9/10. Consequently

```text
q-(U-1)^2>79/25-1+25/16=1489/400
                          >361/100>(b+1)^2.
```

Finally suppose `7/5<=V<3/2`. Then
`U^2>221/100>(37/25)^2`, so U>37/25. It follows that

```text
max((U-1)^2,(U-2)^2)<(U-1)^2+1/25.                   (6)
```

The function `V^3(2-V)` increases up to V=3/2, with value 27/16 there.
Equation (3) and `sqrt(3)<7/4` therefore give

```text
b<75sqrt(3)/148<525/592<9/10.
```

Using (5)--(6),

```text
q-(U-1)^2-1/25>74/25-1+49/25-1/25
                         =97/25>361/100>(b+1)^2.
```

Thus M<q in every case. The left neighbor has every vertex strictly
inside the circle, contrary to its positive load. This excludes |P|<=1.
Reflection interchanging U,V and the two supports excludes |Q|<=1 as
well, proving the theorem.

## 4. Consequence at a large outer-edge corner

For an outer body with `|B|^2>=83/50`, the previously proved box gives
H>X>9/10 and `|A|<1`. Moreover

```text
q=|B|^2+2H+1>83/50+9/5+1=223/50.
```

The selected normal theorem makes its neighbor at A a unique-circle
inner-side body U1,U6 or U7. If it were U1, A would be one of that body's
actual force application points, contradicting the result just proved.
Therefore it is U6 or U7.

This identifies the next body in the ring; it does not exclude that mixed
neighbor or prove that the three-inner-square completion is impossible.
