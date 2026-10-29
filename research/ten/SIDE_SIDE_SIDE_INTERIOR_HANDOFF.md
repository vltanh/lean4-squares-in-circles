# S-S side-interior endpoint: completed analytic lead, integration review pending

**Status:** saved handoff at the user's stop request (2026-10-29). The algebraic
route below received one independent helper check, but the integrated proof has
not received the root and second-reviewer audits required for ledger promotion.
**C15 remains OPEN.** No Lean verification is claimed.

The reviewed [vertex exclusion](SIDE_SIDE_VERTEX_EXCLUSION.md) forces relative
side support at A. Use the S-S normal form

```
R0=79/40<=R<=3/sqrt(2), p>q>0, p^2+q^2=1,
k=p-q, w=p+q, 0<d<1, d<=1-k,
Z=(X,Y), |Z|=R, Y/X=(1-d q/p)/(1-d),
Q_A=Z-(1+p,1+q), Q_B=Z-(1-d,2),
n=(-p,-q), t=(q,-p),
A=Q_A+[0,1]n+[-u,1-u]t, 0<u<1,
N=Q_A.n, T=Q_A.t.
```

The generic side-transmission proximity theorem gives `|Q_A|<R-1`, so
both vertices on the support side are circle-clear. The reviewed S-D normal
bound gives `0<N<27/40`; that argument only uses U-side data and `d<=1-k`.

Put `z=(1-d)/k`, so `1<=z<1/k`, and `D=sqrt(z^2+2qz+1)`. Then

```
N=1+w-R(z+q)/D, T=k-Rp/D.
```

Here `T<0`: equivalently `T=k(1-R/S_d)` with
`S_d=sqrt((1-d)^2+(1-d q/p)^2)<=sqrt(2)<R`.
Also `-T` decreases with z, and at z=1

```
-T <=(3/2)sqrt(1-q)-p+q
    <(1/2)sqrt(1-q)+q<1.
```

The last inequality follows from q<1/sqrt(2)<3/4. Thus the far vertex
`W=Q_A+n+(1-u)t` has

```
|W|^2<(67/40)^2+1=6089/1600<R0^2.
```

Only `F=Q_A+n-u t` can carry A's required positive circle load.

## Joint contact bound and convex reduction

Every B point has `x>=(Q_A)_x+d+p-1` and
`y<=(Q_A)_y+q-1`. At the actual A--B contact its t coordinate is therefore
at least `k+qd`, while A has t coordinate at most `1-u`. Hence

```
u<=U=1-k-qd=1-p+qkz.
```

Since T<0, replacing u by U increases `|F|^2`. Write

```
A0=2+w, B0=2p-q-1, b=qk,
A1=A0-pb=2+p+q^2w,
B1=A0 q+p B0=2+2q-q^2-p.
```

The upper squared-radius excess is

```
E(z)=A0^2+(B0-bz)^2-2R(A1 z+B1)/D.
```

Both A1 and B1 are positive, so E decreases with R; set R=R0.
For convexity put x=z+q and

```
C0=B1-A1 q=p(2p-q-1+q^2k),
f(z)=(A1 x+C0)/sqrt(x^2+p^2).
```

The sign of f'' is the sign of
`C0(2x^2-p^2)-3A1 p^2x`. We have `A1>5/2`, `p^2>1/2`,
and

```
C0-k=(1-p)[k(p+p^2-1)-p]<0.
```

If C0<0 the sign is negative immediately. Otherwise
`C0 x<=kx<=1+kq<3/2`, so the numerator is less than
`x(3-15/4)<0`. Thus f is strictly concave and
`E''=2b^2-2R0 f''>0`. It suffices to clear z=1 and z=1/k.

## Endpoint z=1/k

Set `a=R0/sqrt(2)-1`, so `39/100<a<1/2`. Direct expansion gives

```
E(1/k)=3-4a-4a sqrt(2-k^2)-2(1-a)k+(1-2a)k^2.
```

This is convex for `0<=k<=1`. At k=0 and k=1 it is respectively
`3-4a(1+sqrt(2))<0` and `2-8a<0`. Hence this endpoint is clear.

## Endpoint z=1

Let theta=atan(q/p), h=theta/2. At z=1,

```
N=1+cos(2h)+sin(2h)-R0 cos(pi/4-h)=J(h).
```

Strengthen the reviewed bound slightly. Since

```
w^2-2cos^2(pi/4-h)=q(2p-1)>=0,
```

we have `J''< -5/2`. The tangent quadratic at h=pi/12 yields

```
J(h)<=J(pi/12)+J'(pi/12)^2/5
     =92481/32000-513sqrt(3)/400
     <534993/800000<67/100,
```

using `sqrt(3)>433/250`.
The positive tangential extent is

```
g(theta)=U-T=R0 sin(pi/4-theta/2)+1-2p+q+qk,
g'(theta)=p+2q-2q^2+k^2-(R0/2)cos(pi/4-theta/2)>0.
```

For the last inequality, `sqrt(1-q^2)+2q-2q^2` is concave on
`[0,1/sqrt(2)]` and both endpoint values are at least 1. Consequently

```
g(theta)<R0 sin(pi/8)+1-1/sqrt(2)<21/20.
```

The final comparison is equivalent after squaring to
`9266<6561sqrt(2)`, verified by
`2*6561^2-9266^2=234686>0`. Thus

```
|F|^2_bound<(167/100)^2+(21/20)^2
           =38914/10000<R0^2,
R0^2-38914/10000=369/40000>0.
```

Convexity would therefore clear F throughout the physical parameter interval,
contradicting A's positive circle load and closing S-S when this argument has
passed the remaining independent reviews.

**Next action:** audit this integrated reduction, especially the transfer of
the generic side-transmission proximity and N bound, the joint contact bound,
the z parametrization, and convexity/endpoint calculations. Then consolidate
into a reviewed S-S exclusion manuscript and promote C15 only after both
independent reviews pass. No new numerical search is needed for this lead.
