# An occupied side pocket does not supply virtual contact-length edges

Date: October 30, 2026. Status: exact local obstruction; no original gate closes.

The proposed rerouting of a contact ring from `X-U-Y` to `X-E-Y`, where
E is the actual extra in the U pocket, cannot invoke the contact-center
bound `|c_X-c_E|<=sqrt(2)` automatically. The following four actual
unit squares give a counterexample below the target radius. This is
not a nine-square packing, a full positive-cycle certificate, or a
counterexample to the sharp nine-square conjecture.

Put

    a=11/20, b=9/20, h=2927/5880,
    P_X=(-a,h), P_Y=(b,h),
    u_X=(4/5,3/5), v_X=(-3/5,4/5),
    u_Y=(99/101,-20/101), v_Y=(20/101,99/101).

The vectors in each pair are orthonormal. Keep the actual squares

    U=[-a,b] x [0,1],
    X=P_X+[-1,0]u_X+[0,1]v_X,
    Y=P_Y+[0,1]u_Y+[0,1]v_Y,
    E=[-1/2,1/2] x [1,2].

Both applications belong to U, and the unchanged horizontal support
relations are `X subset {x<=-a}`, `Y subset {x>=b}`. Thus X-U-Y is
the actual width-one support chart with a strictly interior original
side mean `0<h<1`.

## Exact circle containment and all six nonoverlap comparisons

The unique farthest corners of X and Y are respectively

    z_X=P_X-u_X+v_X=(-39/20,h+1/5),
    z_Y=P_Y+u_Y+v_Y=(b+119/101,h+79/101).

Their squared norms agree, by the exact definition of h:

    q=|z_X|^2=|z_Y|^2=29660753/6914880,
    q-4=2001233/6914880>0,
    1105/256-q=746713/27659520>0.

To check that these are indeed the farthest actual corners, X's own
coordinate intervals are `[k-1,k]` and `[j,j+1]`, where
`k=-4a/5+3h/5<1/2` and `j=3a/5+4h/5>0`. Thus the farthest choices
are `k-1` and `j+1`, both uniquely. Both own coordinates of P_Y in
the Y frame are positive, so Y's unique farthest choices are its
two upper own coordinates. The squared farthest radii of U and E
are `521/400` and `17/4`; both are below q, with

    q-521/400=103270609/34574400>0,
    q-17/4=272513/6914880>0.

The pairs X/U and U/Y are separated by their original vertical support
lines. X/Y have a strict horizontal gap of one. X/E have the strict
horizontal gap `1/20`. U/E meet only along their horizontal support
line `y=1`. Finally use the actual Y side axis u_Y to separate E/Y:

    min_Y u_Y.p - max_E u_Y.p
      =(99b-20h-59/2)/101
      =14977/296940>0.

This proves all six physical interior-disjointness conditions without
sampling or any unproved placement convention.

## E really belongs to the unchanged upper pocket

Use the occupied crosscut `z_X-P_X-P_Y-z_Y`, whose middle segment lies
in U and whose other two segments lie in X and Y. Its three segments
are ordered by horizontal coordinate and form a simple graph from
the left circle corner to the right circle corner. Close it by the
upper containing-circle arc. Every E point is in the same disk.

The X strand has horizontal coordinate at most `-a<-1/2`, so it is
outside E's horizontal range. Above `-1/2<=x<=b`, the middle segment
has height h, strictly below E. In the remaining interval
`b<=x<=1/2`, the Y strand has height

    h+(79/119)(x-b)
      <=h+79/2380=53077/99960<1.

Thus every point of E is above the crosscut wherever the horizontal
ranges meet, and below the upper circle arc because E is contained
in the disk. The entire E is on the closed bounded side of the
specified upper loop. This is the actual upper channel pocket.

## The metric shortcut fails strictly

The actual centers are

    c_X=(-5/4,h+1/10), c_E=(0,3/2).

Their exact squared distance is

    |c_E-c_X|^2=3286621/1382976,
    |c_E-c_X|^2-2=520669/1382976>0.

Consequently an actual exterior extra cannot be substituted for the
transmitter in a contact-length center polygon merely because it
occupies that transmitter's pocket. A successful rerouting argument
must prove another enclosure and metric criterion from additional
original hypotheses. This source makes no claim about the other
cycle bodies or a common full force-and-torque certificate.

Every arithmetic statement above is a fixed rational identity or
inequality, checked directly. No numerical pose search, angle mesh,
new packing exclusion certificate, Lean compilation, CI execution,
remote publication or inventory mutation is used.
