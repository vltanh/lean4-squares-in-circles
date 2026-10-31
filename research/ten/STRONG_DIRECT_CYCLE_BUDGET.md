# Eight more cycle signatures excluded by the stronger direct-contact angle

**Status:** hand proof; root and independent full mathematical reviews
passed on 2026-10-29, including all exact angle comparisons and an
independent reconstruction of the eight fixed manifest entries. The
279-case manifest is unchanged.

Use the selected physical certificate of a hypothetical strictly
subcritical ten-square packing, and a whole mixed simple-cycle component.
The [radial-order theorem](RADIAL_ORDER_CYCLE_BUDGET.md) makes its
contracted loaded cycle follow the actual circular order of loaded
centers. Its successive angular gaps therefore sum to `2pi`, and each
gap is at least its endpoints' minor angle.

Let

```text
delta_*=2 atan(1/(sqrt(14)-1)),
a_D=(2sqrt(3-sqrt(2))-1)/(1+sqrt(2)),
a_T=(sqrt(2)-1)/3.
```

The [loaded-pair theorem](LOADED_PAIR_ANGLE_BOUND.md) gives a direct
loaded-loaded gap at least delta_*. The
[transmission cap theorem](TRANSMISSION_CAP_ANGLE_BOUND.md) gives

```text
S gap > pi/2,
D gap >= pi-2atan(a_D),
SS gap >= pi-2atan(a_T) > 9pi/10.                     (1)
```

All comparisons below are exact. Approximate angles are not premises.

## 1. Useful exact comparisons

First,

```text
delta_*>2pi/9.                                       (2)
```

Indeed its cosine is `(7-sqrt(14))/(8-sqrt(14))`, and this is less than
`49/64`: after cross multiplication the comparison is `56<15sqrt(14)`,
whose squared check is `3136<3150`. Put `A=acos(49/64)`. Then
`pi/6<A<pi/3`, and

```text
2cos(3A)+1=8(49/64)^3-6(49/64)+1=-111/32768<0.
```

Since `pi/2<3A<pi`, this gives `3A>2pi/3`, hence
`delta_*>A>2pi/9`.

We also have the rational tangent bounds

```text
a_D<17/27<7/11<2/3,
a_T<29/210.                                          (3)
```

For the first, squaring the positive sides of
`54sqrt(3-sqrt(2))<44+17sqrt(2)` reduces it to
`3117<2206sqrt(2)`, with squared difference

```text
2*2206^2-3117^2=17183>0.
```

For the second use `sqrt(2)<99/70`, since `99^2-2*70^2=1`.

A convenient additional consequence is

```text
D gap > 5pi/8.                                       (4)
```

To see this, `tan(3pi/16)>2/3`. By the half-angle identity this is
equivalent to `cos(3pi/8)<5/13`. The latter follows from

```text
cos(3pi/8)=sqrt(2-sqrt(2))/2,
sqrt(2)>238/169,
2*169^2-238^2=478>0.
```

Equations (1) and (3) now give (4).

## 2. Four loads, one D path, one SS path, and two direct gaps

By (3),

```text
atan(a_D)+atan(a_T)
 <atan(17/27)+atan(29/210)
 =atan(4353/5177)<delta_* .                           (5)
```

The tangent addition has positive denominator, and both sides of the
last comparison lie in `(0,pi/2)`. To check it, use

```text
tan(delta_*)=(sqrt(14)-1)/(7-sqrt(14))>4353/5177.
```

This is equivalent to `4765sqrt(14)>17824`; its squared difference is

```text
14*4765^2-17824^2=178174>0.
```

Thus the four gaps sum to at least

```text
[pi-2atan(a_D)]+[pi-2atan(a_T)]+2delta_*>2pi,
```

contradicting their circular sum. This excludes both cyclic placements
of these four gap types.

## 3. Four loads, two D paths, one S path, and one direct gap

Put `v=atan(7/11)`. The elementary tangent identity is

```text
tan(2v-pi/4)=41/113<4/11.
```

Here `0<2v-pi/4<pi/4`. Also `sqrt(14)<15/4` gives

```text
tan(delta_*/2)=1/(sqrt(14)-1)>4/11.
```

The strict rational comparison above is `41*11=451<452=4*113`.
Therefore

```text
delta_*>4v-pi/2>4atan(a_D)-pi/2.                      (6)
```

Using (1), the four gaps sum to more than

```text
2[pi-2atan(a_D)]+pi/2+delta_*>2pi.
```

This excludes both cyclic placements of these four gap types.

## 4. Six loads with S and D, or with one SS

If the contracted cycle has one S gap, one D gap, and four direct gaps,
(1), (2), and (4) give total angle strictly greater than

```text
pi/2+5pi/8+4(2pi/9)=145pi/72>2pi.                    (7)
```

This excludes all three cyclic placements of the S and D gaps.

If instead it has one SS gap and five direct gaps, (1)--(2) give total
angle strictly greater than

```text
9pi/10+5(2pi/9)=181pi/90>2pi.                         (8)
```

This excludes its one cyclic word.

## 5. The eight fixed manifest entries

| Stable ID | Canonical word | Exclusion above |
|---|---|---|
| C20-M07-L04-B01-T02 | `LLLDLSS` | Section 2 |
| C20-M07-L04-B02-T02 | `LLDLLSS` | Section 2 |
| C20-M07-L04-B03-T04 | `LLSLDLD` | Section 3 |
| C20-M07-L04-B03-T05 | `LLDLSLD` | Section 3 |
| C20-M08-L06-B01-T01 | `LLLLLLSS` | Section 4, (8) |
| C20-M08-L06-B02-T02 | `LLLLLSLD` | Section 4, (7) |
| C20-M08-L06-B03-T02 | `LLLLSLLD` | Section 4, (7) |
| C20-M08-L06-B04-T02 | `LLLSLLLD` | Section 4, (7) |

These exclusions use the angular bounds for every physical realization
of each listed word; they do not classify contact ownership or assume
that any nominal word has a geometric realization. The remaining C20
signatures and the unrestricted theorem are not closed by this batch.
