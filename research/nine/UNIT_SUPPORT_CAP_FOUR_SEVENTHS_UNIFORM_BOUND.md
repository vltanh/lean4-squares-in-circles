# A unit beyond support one has transverse extent less than four sevenths

Date: October 28, 2026 UTC. Author: uniform_remaining continuation.

**Status: complete proposed force-free whole-domain hand theorem, submitted
for full root and separate independent review. No original family, feature,
or coarse gate is declared closed.**

This strengthens the whole-unit cap of
`UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md`, Section 1,
from `7/10` to `4/7`. The new proof is given in full and imports no
orientation enumeration, sampled configuration, coefficient table, or
stress equation. The earlier source and its callers remain unchanged.

## 1. Exact physical theorem

Put `Q=1105/256`. Let K be any actual closed unit square contained in
the unchanged disk `D_(sqrt(Q))`, with arbitrary orientation. Suppose

    K is contained in {x<=-1}.

Then every point of the entire closed unit satisfies

    -4/7 < y < 4/7.                                      (1)

More invariantly, if n,f are any orthonormal directions, `h>=1`, and

    n.z>=h for all z in K,

then

    |f.z|<4/7 for all z in K.                            (2)

All coordinates use the original circle origin. This is a force-free
geometric implication. K need not physically touch the circle, have a
positive force, have any stated degree, or be part of a specified graph.
It applies in particular to every actual completing unit. The support
may be a vertex, a whole side, or an unchanged original side mean.
Neither a support half-plane nor a containing rectangle replaces K.

## 2. The complete highest-corner chart

Choose a highest actual corner `Z=(x,y)` of K. Its two inward unit
side axes can be named so that

    u=(-c,-s), v=(s,-c),
    c,s>=0, c^2+s^2=1,
    K=Z+[0,1]u+[0,1]v.                                 (3)

The parallel-axis endpoints are included. If a whole horizontal side
is highest, choose either endpoint that realizes (3). Its highest
coordinate remains y.

The rightmost actual corner is `Z+v`, and the leftmost is `Z+u`.
Consequently

    x+s<=-1,
    c+s=width_x(K)<=sqrt(Q)-1<13/12.                   (4)

The width inequality is a consequence of the original whole-body
containment and `max_K x<=-1`: its leftmost x-coordinate is at least
`-sqrt(Q)`. The last strict comparison follows from

    (25/12)^2-Q=55/2304>0.

It follows that

    min(c,s)<1/10.                                     (5)

Indeed if both were at least `1/10`, the concave function
`t+sqrt(1-t^2)` on `[1/10,sqrt(99)/10]` would have minimum at an
endpoint, giving

    c+s >= (1+sqrt(99))/10 >13/12.

For the strict comparison use `sqrt(99)>59/6`, since
`99-(59/6)^2=83/36>0`. This contradicts (4).

The alternatives `s<1/10` and `c<1/10` cover every actual
orientation, including both parallel endpoints. No later case assumes
that a contact application is a vertex or a prescribed mean.

## 3. The entire s-small orientation interval

Assume `s<1/10` and suppose for contradiction `y>=4/7`.
The actual corner `Z+u` has

    (Z+u)_x <= -(1+s+c),
    (Z+u)_y = y-s >=4/7-s>0.

Since `c=sqrt(1-s^2)>=1-s^2`, its squared norm satisfies

    |Z+u|^2 >= (2+s-s^2)^2+(4/7-s)^2
             =4+16/49+s*(20/7-2s-2s^2+s^3).           (6)

For every `0<=s<1/10`, the final parenthesis is strictly positive;
for example it is greater than `20/7-1/5-1/50>0`.
Therefore (6) is at least `4+16/49`, including `s=0`. But

    4+16/49-Q=127/12544>0.

This contradicts the original circle containment. Hence `y<4/7`
throughout this entire closed-to-open orientation range.

## 4. The entire c-small orientation interval

Now assume `c<1/10`. Then `s>99/100`. From the actual highest
corner and `x<=-1-s<-199/100`, containment gives

    y<3/5.                                            (7)

In fact `|y|<3/5`, because

    (199/100)^2+(3/5)^2-Q=591/160000>0.

First suppose `c>=1/20`. The unit-circle identity in (3) gives
`s^2>99/100>(159/160)^2`, with exact second reserve `63/25600`.
Thus the actual corner `Z+u` satisfies

    (Z+u)_x <=-(1+s+c)<-327/160,
    (Z+u)_y =y-s<3/5-159/160=-63/160.

It follows that

    |Z+u|^2 > (327/160)^2+(63/160)^2
             =Q+199/12800,

another contradiction. Consequently this whole c-small orientation
case necessarily has

    0<=c<1/20.                                        (8)

It follows that `s^2>399/400`, and hence `s>399/400` as well.
The original highest corner therefore has

    x<=-1-s<-799/400.

If `y>=4/7`, that same actual corner would give

    |Z|^2 > (799/400)^2+(4/7)^2
            =Q+4/30625>Q.                            (9)

This excludes `y>=4/7` in the whole remaining interval (8),
including the aligned endpoint `c=0`.

Sections 3--4 prove `max_K y<4/7`. Reflect the entire actual square
in the x-axis; its containment and the hypothesis `x<=-1` are
preserved. The identical proof gives `min_K y>-4/7`, proving (1).
Apply an orthogonal change of coordinates, with x-axis `-n` and
y-axis f, to obtain the invariant statement (2). No translation
of the original circle origin is made.

## 5. Uniform southwest-support consequence and literal existing callers

Suppose an actual contained unit K has an original support

    M.z>=h_K>=1,
    M=(-s,-t), s,t>=0, s^2+t^2=1.

Use the orthonormal directions `e=(s,t)`, `f=(-t,s)`.
The theorem gives `e.z<=-1` and `|f.z|<4/7` on the entire actual
unit. Its original vertical coordinate is therefore

    z_y=t*(e.z)+s*(f.z)<4/7.                          (10)

If `s=0`, the stronger `z_y<=-1` proves (10) directly. For `s>0`,
the strict transverse inequality proves (10), including the horizontal
support endpoint `t=0` and every weak support endpoint `h_K=1`.

The shared-XH roof proof in
`UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md`
derives the genuine original whole-unit premise `h_C>1` at its
actual C, for every surviving original HC feature, from the entire
unloaded H3 equation and its original weak moment. Therefore its
Section 3 conclusion strengthens literally to

    max_C y<4/7.

Its XA-North case already gives `min_A y>=1-b>89/120`, so the
strict vertical gap there is now uniformly greater than

    89/120-4/7=143/840.

This keeps every actual C mask, every original shared mean, all
positive forces at the true A3 and H3, and the actual B2 equation.
The statement applies equally to the loaded-B ABC row and to the
unloaded-B AC row at their stated shared-root hypotheses; it assigns
no transmitter equation to the loaded B. It does not address the
remaining root positions or supply a whole-family contradiction.

The invariant cap (2) is available for any other literal caller after
that caller proves its actual whole-unit support premise. Zero load,
nearness of a point, or a supporting line without the correct
minimum-support orientation does not supply that premise.

## 6. Exact sources and bookkeeping limit

The geometric proof of Sections 1--4 is self-contained. The only
external input for the explicitly limited roof corollary is:

| Source | SHA256 | Exact scope used |
| --- | --- | --- |
| UNIT_SUPPORT_CAP_AND_SHARED_S_ROOT_ROOF_RETURN_SEPARATION.md | 2b90b565591b3c9bbc30c2c1af48cf117771b96bbc58ad81441f9e99497067d6 | Section 2's original shared-root chart, Section 3's actual full-star support `h_C>1`, and Section 4's actual North-XA height bound |

The earlier cap proof remains valid. No current or historical source
is silently replaced, no old review is treated as reviewing these new
bytes, and no downstream full-family re-audit is claimed.

The displayed rational reserves only check the written arithmetic.
The continuous geometric proof covers every orientation and every
stated support endpoint. There is no pose sampling, angle mesh,
coefficient sign table, new generic choice, altered force, replaced
mean, Lean compilation, CI, workflow, metadata change, or remote write.
This source earns zero additional original fine or coarse gate credit.
