# Every contact of two circle-touching units stays beyond a sharp inner radius

Date: October 27, 2026.

**Status: complete force-free hand lemma, awaiting independent and
root review.** All circle masks, zero circle weights, actual contact
owners and side endpoints are included.

Let S,T be actual unit squares with disjoint open interiors,
contained in the same disk D_R, where R>sqrt(2). Suppose both
physically touch its boundary. Then every actual point P in S∩T
satisfies

    |P| >= sqrt(R^2-1)-1.                               (1)

In particular, throughout the high-radius nine-square range
R>=sqrt(17)/2,

    |P| >4/5.                                          (2)

The threshold in (1) is sharp. No stress equation, positive pair
edge, selected normal or total circle weight is needed.

## 1. The complete contact-feature observation

Choose any genuine separating unit normal n at P, pointing from S
to T. Such a normal exists by convex separation, and its support
line passes through every common point. P lies on the boundary
of each unit: an open neighborhood of an interior point of one
would meet the other's open interior.

Suppose a vertex Z of one of these squares has |Z-P|>1.
Then the displacement Z-P makes an angle at most pi/4 with
that square's inward normal at the common support.

Here is the literal full feature cover. If P is a vertex, an
adjacent vertex is at distance1 and P itself is at distance0.
Thus Z must be the opposite vertex. Its displacement is the
sum of the two inward orthogonal unit side directions. Every
inward supporting normal at P belongs to their closed positive
quadrant, so the angle to that diagonal is at most pi/4.

If P is in the relative interior of a side, the two vertices of
that side are at distance at most1. The other two vertices lie
on the opposite side; their displacement has inward normal
coordinate1 and tangential coordinate in[-1,1]. Its angle to
the inward normal is therefore at most pi/4.

These two cases exhaust the boundary, retaining both side
endpoints. The argument concerns the actual P and every actual
supporting normal, not an adjusted mean or a preferred vertex.

Consequently, if Z_S and Z_T are actual circle vertices and both
are more than1 from P, their displacement vectors v_S,v_T satisfy

    v_S dot v_T <=0.                                    (3)

Indeed their inward supporting normals are -n and n, and the
two deviations from these opposite directions are at most pi/4.

## 2. A smaller radial contact would force the opposite dot sign

Put s=|P| and suppose contrary to (1) that

    s<sqrt(R^2-1)-1.

Then

    R^2>s^2+2s+2.                                      (4)

In particular R>s+1, because
s^2+2s+2>(s+1)^2. Thus every actual circle vertex Z of either
unit obeys

    |Z-P|>=R-s>1.

Section 1 applies to any choice of actual circle vertex in
each square. Their displacements have lengths at most sqrt(2),
by the unit-square diameter. If s=0, already R=|Z-P|<=sqrt(2)
is impossible. Otherwise

    2P dot v_i=R^2-s^2-|v_i|^2
                 >=R^2-s^2-2>2s
       (i=S,T).

It follows that

    cos(angle(P,v_i))
      =(P dot v_i)/(s|v_i|)
      >1/|v_i|>=1/sqrt(2).

Both displacement directions are therefore strictly within
pi/4 of the same direction P. Their mutual angle is strictly
less than pi/2, so v_S dot v_T>0. This contradicts (3) and
proves the closed bound (1).

For R>=sqrt(17)/2,

    sqrt(R^2-1)-1 >=sqrt(13)/2-1>4/5,

since 13>(18/5)^2, with exact squared reserve1/25.
Thus (2) is strict even at the critical radius.

## 3. Equality and exact physical scope

For any R>sqrt(2), set h=sqrt(R^2-1)-1. The two actual squares

    [-1,0] x [h,h+1],
    [0,1] x [h,h+1]

have disjoint open interiors, lie in D_R, and have actual outer
corners (±1,h+1) on its boundary. Their common lower endpoint
P=(0,h) realizes equality in (1). Hence the first inequality
cannot in general be strengthened to strict.

The theorem applies to every point of a genuine shared side,
so an actual convex combination of its endpoints is covered
directly. Physical radial masks keep both circle corners and
all individual weights, including zero endpoints; the proof
may choose either actual circle corner and uses no weight.
Additional contacts and forces at either unit are unrestricted.

No original proof gate is closed solely by this local lemma.
No selected normal is changed and no numerical, Lean or CI
premise is introduced.

