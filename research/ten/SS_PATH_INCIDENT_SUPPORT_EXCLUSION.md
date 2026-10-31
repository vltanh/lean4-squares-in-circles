# A width-two path cannot use the incident vertex/side central form

**Status:** independently reviewed exact conditional hand proof (2026-10-29).
This is a local reduction for the remaining three-loaded six-cycles, not
a closure of either whole cycle signature.

Let a loaded degree-two body C have a unique circle vertex, and suppose
its two transmission paths terminate at unit squares A and B that touch.
The endpoint squares need only be contained in the radius-R disk; their
own circle loading is not used below. Work with `R<=3/sqrt(2)`.

Assume C has the incident strict-vertex/relative-side-interior normal form
derived in [SIDE_NORMAL_MIXED_FIVE_CYCLE.md](SIDE_NORMAL_MIXED_FIVE_CYCLE.md).
That local force and torque derivation is independent of the transmission
widths. Write

```text
Z=(X,Y),        X>0, Y>X,        |Z|=R,
C=Z+[-1,0]^2,
P=Z-(1,1),     Q=Z-(1-d,1),     0<d<1,
n=(-p,-q),     p>q>0,           p^2+q^2=1.
```

The path at P points along n and has width Wv; the path at Q points
vertically downward and has width Ws. Their far contacts are

```text
QA=Z-(1+Wv*p,1+Wv*q),
QB=Z-(1-d,1+Ws).
```

Each endpoint square is supported there by the corresponding inward
normal. Assume `Wv,Ws>=1` and at least one width equals two, meaning an
SS path under the reviewed transmission classification.

**Theorem.** This configuration is impossible.

## 1. Two width-independent identities

Put `rho=q/p`. The local force and torque equations on C give

```text
Y/X=(1-d*rho)/(1-d).                                  (1)
```

A square supported at QA with inward normal `(-p,-q)` can extend at most
q to its right. A square supported at QB with downward inward normal can
extend at most one to its left. These are the elementary support bounds
in [VERTEX_CONTACT_MIXED_FIVE_CYCLE.md](VERTEX_CONTACT_MIXED_FIVE_CYCLE.md).
Apply them at the actual A--B contact. Overlap of the horizontal
projections is necessary, and yields

```text
d<=1-Wv*p+q.                                         (2)
```

We will also use the unit-normal-step lemma: a unit square K supported
at Q with inward unit normal n contains Q+n. At a vertex, the components
of n along the two inward unit edges are nonnegative and at most one,
so Q+n lies in the square. At an edge, it is the point directly across
the square. Endpoint contacts are covered by these cases too.

## 2. Width two at the strict vertex

Suppose `Wv=2`. Since d>0, (2) gives `2p-q<1`. Squaring the positive
inequality `2p<1+q` gives

```text
(5q-3)(q+1)>0,
q>3/5.
```

Also `q<1/sqrt(2)` because p>q. On that interval,
`sqrt(1-q^2)+q` is strictly increasing, so

```text
p+q>7/5.
```

By the unit-normal-step lemma, A contains

```text
QA+n=Z-(1+3p,1+3q).
```

The squared distance of this point from Z is

```text
(1+3p)^2+(1+3q)^2=11+6(p+q)>97/5>18.
```

Both Z and this point would belong to the radius-R disk, whose diameter
has squared length `4R^2<=18`. This contradiction excludes `Wv=2`.

## 3. Width two at the side

Suppose `Ws=2`, and put `t=1-d`, so `0<t<1`. Equation (2) and Wv>=1
give `t>=Wv*p-q>=p-q`. Rewriting (1), and using `p>1/sqrt(2)>2/3`,
gives

```text
r:=Y/X
 =1+(p-q)(1-t)/(p*t)
 <=1+(1-t)/p
 <1+(3/2)(1-t)=:h=(5-3t)/2.                          (3)
```

The normal-step lemma says that B contains

```text
F=QB+(0,-1)=Z-(t,4).
```

Its squared-radius excess is

```text
|F|^2-R^2=t^2+16-2R*(t+4r)/sqrt(1+r^2).              (4)
```

For fixed t, the function `(t+4r)/sqrt(1+r^2)` increases for
`0<=r<=h`: its derivative has the sign of `4-tr`, which is positive
because `0<t<1` and `h<5/2`. Thus (3), `2R<=3sqrt(2)`, and (4) give

```text
|F|^2-R^2
 >=t^2+16-3sqrt(2)*(t+4h)/sqrt(1+h^2)>0.              (5)
```

Here is an explicit rational identity proving the last strict inequality.
Both sides to be compared are positive, so it is enough to square them.
Define

```text
P(t)=4[(t^2+16)^2(1+h^2)-18(t+4h)^2]
    =9t^6-30t^5+317t^4-960t^3+1432t^2-480t+224.
```

Direct expansion verifies

```text
15P(t)=3360(1-t)^6
       +12960t(1-t)^5
       +35880t^2(1-t)^4
       +66720t^3(1-t)^3
       +68835t^4(1-t)^2
       +35940t^5(1-t)
       +7680t^6.
```

Every term is nonnegative on `[0,1]`, and at least one is strictly
positive. Therefore P(t)>0 throughout that interval, proving (5).
The point F would be outside the containing disk, a contradiction.

## 4. Exact scope in the finite cycle ledger

The two unresolved three-loaded six-cycle words with a direct
loaded-loaded edge are

```text
C20-M06-L03-B01-T01: LLSLSS,
C20-M06-L03-B01-T02: LLDLSS.
```

They have transmission widths `(1,2)` and `(sqrt(2),2)` at their third
loaded body. The theorem excludes either orientation of the incident
strict-vertex/relative-side-interior central form in both signatures.

It does not transfer the five-cycle's earlier classification arguments
without checking their hypotheses at width two. Parallel directions,
coincident contacts, distinct vertex contacts, and a radial-side central
body still require their width-two arguments. Consequently neither stable
cycle ID is promoted to closed by this note alone.
