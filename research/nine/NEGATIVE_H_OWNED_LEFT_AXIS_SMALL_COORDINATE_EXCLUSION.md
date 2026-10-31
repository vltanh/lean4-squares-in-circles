# Every left A-owned contact with small first corner coordinate has positive H pressure

**Status: complete continuous-domain hand proof; root and separate independent full saved-source, prerequisite, original-domain and exact-arithmetic audits passed.**

Work throughout 79/40≤R≤sqrt(1105)/16, with q=R² and q_0=6241/1600. Let A be a physically unique, positively circle-loaded square of true positive degree two, with actual neighbors H and K. Retain all physical squares, every individual circle weight, every positive force, the original shared application means and all other forces on H and K. Assume K physically touches the containing circle, c_H·z_A<0, and HA is an H-owned singleton.

**Theorem.** In the ordered negative-endpoint frame below, an actual A-owned left inner-side contact AK is impossible when a≤3/2. This includes a tilted K with a singleton contact and every genuinely shared contact. No equation at H or K, and no physical HK contact, is used.

## 1. A whole-orientation bound at a right supporting point

Let a unit square S have a right supporting point T=(x,beta), with 0<x<1 and beta>0. Every corner z of S satisfies

|z|²≤max(x²,(1−x)²)+(beta+1)². (1)

If T is a vertex, label its two inward unit edges as

(−c,s), (−s,−c), c,s≥0, c²+s²=1.

This includes the limiting axis directions. The two adjacent corners have squared norms

x²+beta²+1−2xc+2beta s≤x²+(beta+1)²,
x²+beta²+1−2xs−2beta c≤x²+(beta+1)².

The opposite corner has squared norm

x²+beta²+2−2x(c+s)+2beta(s−c)
≤(x−1)²+(beta+1)²,

because c+s≥1 and s−c≤1. The point T itself also obeys (1).

If T is in an aligned supporting side, retain its original position by writing

S=[x−1,x]×[beta−r,beta+1−r], 0≤r≤1.

Every corner satisfies |z_x|≤max(x,1−x) and |z_y|≤beta+1. This proves (1) for every original side mean, including both endpoints.

If S has a physical circle corner and q>max(x²,(1−x)²), then (1), with beta+1>0, gives

beta≥sqrt(q−max(x²,(1−x)²))−1. (2)

This is a physical containment statement; no load, concurrence, multiplier or equation on S was assumed.

## 2. Application to the complete original left-axis family

Section 1 of NEGATIVE_H_OWNED_ENDPOINT_RADIAL_MIDDLE_DOMAIN.md uses no radial-middle premise. Its actual negative-endpoint frame is

z_A=(a,b), a>b>3/5, a²+b²=q,
A=[a−1,a]×[b−1,b], P_A=(a−1,b−1),
q_A=kappa z_A, delta=1−kappa∈[0,1/a),
n=(u,v)=(1−delta a,1−delta b)/sqrt((1−delta a)²+(1−delta b)²),
0<u≤v.

Here n is the actual H-to-A normal, and every original H offset is retained:

H=P_A+[-1,0]n+[-1/2−eta,1/2−eta]Jn,
−1/2≤eta≤1/2. (3)

An actual A-owned left contact has its unchanged application at

T=(a−1,kappa b),

and K lies in x≤a−1. Since a≤3/2 and a≥R/sqrt2>139/100, set x=a−1∈(0,1/2] and beta=kappa b>0. Now max(x²,(1−x)²)=(2−a)² and q>(2−a)². Applying (2) to the physical K gives

Y=sqrt(q−(2−a)²), kappa b≥Y−1,
delta≤1−(Y−1)/b. (4)

No parallelism of K, no shared-side premise and no HK edge was used.

## 3. The full small-coordinate pressure estimate

We spell out the scalar comparison from NEGATIVE_H_OWNED_SHARED_LEFT_MIDDLE_SMALL_COORDINATE_EXCLUSION.md; its only middle-body input is (4).

Put

d=sqrt(q−1/4)−1, N=sqrt(q−9/4), t=3/2−a.

Over the entire original radius and coordinate domain,

91/100<d<61/60, 321/250<N≤23/16,
N≤b<a≤3/2, b>d, t≥0. (5)

For the derivative comparison at fixed q, use every a'∈[a,3/2]. Since a'>139/100,

d/da' sqrt(q−(2−a')²)
=(2−a')/sqrt(q−(2−a')²)<1/3.

The exact squared reserve q_0−10(61/100)²=1437/8000>0 proves this throughout the comparison interval. At a'=3/2, Y−1=d; hence

Y−1≥d−t/3.

Let U=1−d/b>0 and V=27/2−8b>0. From (4),

delta(9a−8b)
≤(U+t/(3b))(V−9t)
=UV+t[(9/2+9d)/b−35/3]−3t²/b
≤UV. (6)

The coefficient of t is strictly below −665/642 by (5). Also

UV<f(b):=(1−91/(100b))(27/2−8b)<1.

Indeed f'(b)=−8+2457/(200b²)<0 on b≥321/250, because

(321/250)²−2457/1600=113031/1000000>0,

and

f(321/250)=50303/53500<1.

Consequently

8/9<rho:=u/v≤1. (7)

For every original eta in (3), the actual H center satisfies

c_H·z_A
≥q−a−b−[(a−b)u+(a+b)v]/2
>q−a−b−(17a+b)/(2sqrt145). (8)

The subtracted expression has derivative with respect to rho of the sign

(a−b)−(a+b)rho<0,

so (7) proves the strict bound without changing eta or the original mean.

At fixed q, the last expression in (8) strictly decreases with a on the entire comparison interval [a,3/2]. Its derivative is less than −1/4, using a/b<6/5 and 12<sqrt145<17. Its minimum is thus at a=3/2, b=N. Since

sqrt145>301/25, with squared reserve 24/625,

the original pressure is strictly greater than

p(N)=N²−N+3/4−25(2N+51)/1204.

This polynomial increases on N≥321/250, and

p(321/250)=22233/9406250>0. (9)

This contradicts c_H·z_A<0. The proof includes delta=0, a=3/2, every original side mean, every H side offset and both radius endpoints.

## 4. Applications and retained obligations

The result excludes every small-coordinate A-owned left contact, including tilted singleton neighbors. It applies to both the actual H4/intact-petal ABC component and the actual H5/K3 diamond. No K force was removed or assigned a degree-two equation; the proof used only true A2 and physical circle containment of K. All physical masks, individual zero-weight endpoints, completion squares and other H/K forces remain.

The large-coordinate left-axis singleton family a>3/2 remains a separate obligation. A K-owned upper-left singleton is also not covered by this theorem. No normal, mean, force, square or original radius has been replaced, and no sampled pose, numerical angle cover, Lean compilation or CI is used.
