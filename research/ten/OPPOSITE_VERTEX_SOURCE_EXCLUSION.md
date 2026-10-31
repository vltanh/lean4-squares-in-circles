# Two paths from the circle-adjacent vertices force an equality boundary

**Status:** reviewed exact hand proof; root and independent full mathematical
reviews passed on 2026-10-31, including the complete closed-normal equality
boundary and its actual path widths.
This is a shared local restriction. In particular it excludes the entire
strict U-VV-O source row, without using any endpoint circle load or force
balance.

Let a unit square C have a unique vertex Z on the centered circle of
radius `R<=3/sqrt(2)`, with all of C in the disk. Choose its own axes so
that

```text
Z=(X,Y),       X,Y>1/2,       q=X^2+Y^2<=9/2,
C=[X-1,X] x [Y-1,Y],
J=(X-1,Y),     K=(X,Y-1).
```

Suppose that two transmission paths of widths `W_A,W_B>=1` leave C at
J and K, with outward unit normals

```text
n_A=(-p,s),       n_B=(r,-t),
p,s,r,t>=0,      p^2+s^2=r^2+t^2=1.
```

Each far endpoint is a unit square in the same disk and has inward
normal n_i at the far path contact `P_i+W_i n_i`. These are precisely
the normal-cone directions at the two vertices. Boundary side normals
are deliberately retained in this statement.

**Theorem.** Necessarily

```text
q=9/2,       X=Y=3/2,
n_A=(-1,0),  n_B=(0,-1),       W_A=W_B=1.             (1)
```

In particular, if either selected normal is strict in its vertex cone,
the configuration is impossible. This excludes U-VV-O in
[LSLSLSS_SUPPORT_NORMALIZATION.md](LSLSLSS_SUPPORT_NORMALIZATION.md)
and the same local form with any two S, D, or SS paths.

## 1. One circle-adjacent path forces a coordinate of at least 3/2

The unit-normal-step lemma puts `J+(W_A+1)n_A` in the endpoint square.
Convexity of the disk, using J in C and W_A>=1, therefore also puts
`J+2n_A` in the disk. Its squared-radius excess is

```text
|J+2n_A|^2-q
 =5-2X+4(1-X)p+4Ys
 =9-6X+4(X-1)(1-p)+4Ys.                              (2)
```

If X<=1, the first expression is positive. If `1<X<3/2`, the second
expression is positive. Thus X>=3/2. At X=3/2, that second expression
can be nonpositive only if `1-p=0` and s=0. Consequently

```text
X>=3/2,       and equality forces n_A=(-1,0).          (3)
```

Exchange the square axes and apply exactly the same argument at K:

```text
Y>=3/2,       and equality forces n_B=(0,-1).          (4)
```

The unit-normal-step fact used here holds at both vertex and side
supports; see
[SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md](SS_PATH_INCIDENT_SUPPORT_EXCLUSION.md).
No force ratio, endpoint loading, transmitter slide, or endpoint
orientation was used.

## 2. The radius bound determines the whole surviving boundary

Equations (3) and (4), together with `X^2+Y^2<=9/2`, force
`X=Y=3/2` and equality in both normal directions. In these coordinates
the actual endpoint normal-step point for the first path is

```text
J+(W_A+1)n_A=(-1/2-W_A,3/2).
```

Its membership in the radius-squared 9/2 disk implies
`(W_A+1/2)^2<=9/4`, so W_A<=1. Hence W_A=1. Exchanging the axes proves
W_B=1, establishing (1).

The conclusion (1) is only a necessary boundary form, not an assertion
that the two endpoint squares and all transmitters can be simultaneously
realized with an arbitrary remainder of a packing. The strict U-VV-O
row has s,r>0 and is therefore entirely excluded, including at the
maximum radius. No whole-cycle capacity claim follows from this note.
