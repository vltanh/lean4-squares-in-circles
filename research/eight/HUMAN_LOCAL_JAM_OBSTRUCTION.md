# An exterior square can have three contacts and be locally immovable

This note records an exact obstruction to a proposed local step in the
unrestricted eight-square proof. It is a pen-and-paper construction. All the
coordinates and all the inequalities below are rational.

An exterior square can be strictly inside the containing circle, have exactly
three neighbours, and be locally immovable when those neighbours are fixed.
Moreover, the unique square containing the origin can have both of its centre
coordinates smaller than `1/4` in absolute value. Thus neither local
immovability nor force and moment balance alone reduces every circle-free
exterior square to an opposite-contact transmitter.

The construction is a four-square packing, not an eight-square packing or a
radius minimizer. In particular, it does not contradict a reduction using
simultaneous motions of several squares, global occupancy, or minimality of
the total number of actual contacts.

## 1. Exact construction

Put

\[
 a=\frac{800}{160001},\qquad
 b=\frac{159999}{160001},\qquad
 \eta=\frac1{200},\qquad
 n=(a,b),\qquad m=Jn=(-b,a).
\]

Then

\[
 a^2+b^2=1,\qquad 0<a<\frac1{200},\qquad
 \frac{999}{1000}<b<1.
\tag{1}
\]

Let the central and middle squares be

\[
 C=[-73/100,27/100]\times[-1/2,1/2],\qquad
 S=[27/100,127/100]\times[-1/2,1/2].
\tag{2}
\]

Their centres are respectively `(-23/100,0)` and `(77/100,0)`.
Write

\[
 z=(127/100,1/2),\qquad
 p_L=z+\frac n2+\left(\frac12-\eta\right)m.
\]

The upper square `L` has centre `p_L` and orthonormal side frame `(n,m)`.
The lower square `M` is its reflection in the horizontal axis.

The four vertices of `L` are

\[
 v=z-\eta m,\qquad u=z+(1-\eta)m,\qquad
 v+n,\qquad u+n.
\tag{3}
\]

In particular, `z` lies strictly inside the edge `[v,u]`.

## 2. Contacts and strict noncontacts

The squares `C` and `S` share the full vertical edge at `x=27/100`.
Because both coordinates of `n` are positive, `z` is the unique point of `S`
maximizing the scalar product with `n`. Equation (3) gives

\[
 \max_{x\in S}n\cdot x=n\cdot z
   =\min_{x\in L}n\cdot x.
\]

Thus `S` and `L` touch only at `z`, and their interiors are disjoint. The
reflected statement holds for `S` and `M`.

The least horizontal coordinate in `L` is

\[
 \frac{127}{100}-\frac{199}{200}b
 >\frac{127}{100}-\frac{199}{200}
 =\frac{11}{40}>\frac{27}{100}.
\tag{4}
\]

So `C` and `L` have a strict horizontal gap; the same is true of `C` and `M`.
The least vertical coordinate in `L` is

\[
 \frac12-\eta a>0.
\tag{5}
\]

Consequently `L` and `M` have a strict vertical gap. These facts check every
pair: the contact graph is the three-edge star with centre `S` and leaves
`C,L,M`.

The small displacement by `eta` along the edge in (3) matters. At the
`S,L` contact, their horizontal and vertical projection intervals overlap
strictly. Their projection intervals on `m` overlap strictly as well,
because `z` lies strictly inside the `m`-projection of both squares. Hence
the only active separating axis is `n`, owned by `L`. There is no alternative
horizontal or vertical separator at this contact. The corresponding unique
axis at the lower contact is `(a,-b)`.

## 3. Strict circle containment

All four squares lie strictly inside the circle of squared radius

\[
 \frac{39}{10}.
\tag{6}
\]

It suffices to check vertices. The potentially largest vertex of `L` is

\[
 v+n=\left(\frac{127}{100}+a+\eta b,
               \frac12+b-\eta a\right).
\]

Both coordinates are positive, and (1) gives

\[
 (v+n)_x<\frac{32}{25},\qquad (v+n)_y<\frac32,
\]

so

\[
 |v+n|^2<\left(\frac{32}{25}\right)^2+\frac94
 =\frac{9721}{2500}<\frac{39}{10}.
\tag{7}
\]

For completeness, the other three vertices have positive coordinates and
satisfy

\[
 v_x<\frac{51}{40},\quad v_y<\frac12;\qquad
 u_x<\frac{69}{250},\quad u_y<\frac{101}{200};\qquad
 (u+n)_x<\frac{57}{200},\quad (u+n)_y<\frac{301}{200}.
\]

Each of these bounds gives a squared norm smaller than `9721/2500`.
Reflection handles `M`. The largest squared norms among the vertices of
`C` and `S` are respectively

\[
 \left(\frac{73}{100}\right)^2+\frac14
   =\frac{7829}{10000},\qquad
 \left(\frac{127}{100}\right)^2+\frac14
   =\frac{18629}{10000}.
\]

Thus the circle inequalities impose no active constraint on `S`, or on any
of its neighbours, in this example.

## 4. Positive force and moment balance on the middle square

At the three contacts, use the outward normals of `S`

\[
 n_+=(a,b),\qquad n_-=(a,-b),\qquad n_C=(-1,0)
\]

with positive weights `1,1,2a`. Their weighted sum is zero. Put the central
force at `(27/100,0)`. The two remaining contact moments about the origin are

\[
 \left(\frac{127}{100},\frac12\right)\times(a,b)
 =\frac{127}{100}b-\frac a2,
\]

and its negative. The central moment is zero. Therefore both force and
moment balance hold on the circle-free square `S` with all three contact
weights positive.

This assertion concerns `S` alone; no equilibrium claim is made for the
other three squares.

## 5. Actual local immovability with the neighbours fixed

Fix `C,L,M`. Suppose a sequence of distinct feasible positions and
orientations of `S` converges to the position in (2). Write its centre
translation as `(t_x,t_y)` and its angle change as `theta`. Normalize by

\[
 \epsilon=(t_x^2+t_y^2+\theta^2)^{1/2}
\]

and pass to a subsequence for which

\[
 (t_x,t_y,\theta)/\epsilon\longrightarrow(v_x,v_y,\omega),
 \qquad v_x^2+v_y^2+\omega^2=1.
\tag{8}
\]

We derive incompatible necessary conditions.

At the `C,S` edge contact, the only separating axes that can remain feasible
near the given position are the horizontal axis of `C` and the nearly
horizontal axis of `S`. For the former, the separation gap is

\[
 t_x+\frac12-\frac12(\cos\theta+|\sin\theta|)
 =t_x-\frac12|\theta|+o(\epsilon).
\]

For the latter, with `e_theta=(cos theta,sin theta)`, it is

\[
 (t_x,t_y)\cdot e_\theta
 +\frac12\cos\theta-\frac12-\frac12|\sin\theta|
 =t_x-\frac12|\theta|+o(\epsilon).
\]

The other separating-axis choices have a strict negative gap at the
original position. Therefore either feasible branch implies

\[
 v_x\ge\frac12|\omega|.
\tag{9}
\]

At the upper contact the unique active axis is the fixed vector `n` from
section 2. Its support vertex on `S` remains the vertex corresponding to
`z`, whose velocity is

\[
 (v_x,v_y)+\omega J(1/2,1/2).
\]

The necessary nonpenetration inequality is consequently

\[
 a v_x+b v_y+\frac{b-a}{2}\omega\le0.
\tag{10}
\]

The lower contact gives

\[
 a v_x-b v_y-\frac{b-a}{2}\omega\le0.
\tag{11}
\]

Adding (10) and (11) gives `2a v_x<=0`. Since `a>0`, (9) now forces
`v_x=omega=0`; (10) and (11) then force `v_y=0`. This contradicts (8).
Therefore `S` is an isolated feasible position when `C,L,M` are held fixed.
The argument checks all separating-axis alternatives, so this is actual
local immovability, not merely rigidity within one arbitrarily selected
separator branch.

## 6. Implication for the unrestricted proof

The origin lies in the open interior of `C`, and the largest absolute
coordinate of its centre in its own side frame is

\[
 \frac{23}{100}<\frac14.
\]

Thus the following proposed implication is false:

> A circle-free exterior square with three contacts, even if locally
> immovable against its fixed neighbours, forces a central centre
> coordinate of absolute value at least `1/4`.

A useful global reduction must still account for the space occupied by
the three neighbours and for simultaneous motions. In particular, a
radius-dependent bound on the capacity of the opposite central cap could
still exclude this branch in an eight-square packing; the example does
not settle that occupancy question.
