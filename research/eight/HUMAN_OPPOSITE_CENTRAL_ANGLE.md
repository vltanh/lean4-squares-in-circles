# Angular obstruction from two opposite sides of a central square

## Theorem (arbitrary square orientations)

Let C,A,B be three unit squares with pairwise disjoint open interiors,
all contained in a disk centered at zero with squared radius
q<=9789/2500. Suppose some unit vector n separates A from C
in the positive n direction and B from C in the negative n direction:

    n dot(p_A-p_C) >= h_A(n)+h_C(n),
    n dot(p_C-p_B) >= h_C(n)+h_B(n),                 (1)

where p_S denotes the square center and
h_S(n)=(|n dot e_S|+|n dot f_S|)/2 is the
centered square's support function in direction n.

Put W=|n dot e_C|+|n dot f_C|, so 1<=W<=sqrt(2).
Then the smaller angle delta between the **center rays**
of A and B satisfies the explicit sharp-domain estimate

    cos(delta) < 1-1250*(1+W)^2/5041.               (2)

In particular

    delta>pi/2-1/100.                                (3)

If n makes a 45-degree angle with both axes of C,
so W=sqrt(2), the stronger bound holds:

    delta>5*pi/8.                                     (4)

This result is geometric and does not assume a chosen
positive contact stress, pairwise orientation agreement,
or that A and B touch one another.

## 1. Separate the two neighbors through C

Adding (1) and using h_A(n),h_B(n)>=1/2 gives

    n dot(p_A-p_B)
       >= h_A(n)+2*h_C(n)+h_B(n)
       >=1+W.

Therefore their center distance satisfies

    |p_A-p_B| >= D:=1+W>=2.                         (5)

The exact farthest-vertex formula for any unit square
of center p and frame (e,f) gives

    |p|^2+|p dot e|+|p dot f|+1/2<=q.

The sum of the absolute projections is at least |p|.
Consequently r=|p| satisfies r^2+r+1/2<=q.
But at r=71/50,

    r^2+r+1/2 =9841/2500>9789/2500>=q,

so every center in the disk obeys

    |p|<M:=71/50.                                    (6)

Neither p_A nor p_B can be zero, because (5)
and (6) would then force the other center norm
to be at least two, impossible.

## 2. Convert center separation into an angle

Write r=|p_A| and s=|p_B|. The cosine law and
(5) give

    cos(delta) <= F(r,s):=(r^2+s^2-D^2)/(2*r*s).

For fixed s<=M the partial derivative is

    partial_r F=(r^2+D^2-s^2)/(2*r^2*s)>0,

since D>=2>M. By symmetry F is increasing
in both positive radii. Using (6) therefore yields

    cos(delta)< F(M,M)=1-D^2/(2*M^2)
           =1-1250*(1+W)^2/5041,

proving (2). With W>=1 this specializes to

    cos(delta)<1-5000/5041=41/5041.                  (7)

The sine inequality sin(x)>=x-x^3/6 at x=1/100,
together with direct rational comparison,
gives

    41/5041 <1/100-1/6000000
            <=sin(1/100)=cos(pi/2-1/100).

Cosine is strictly decreasing on [0,pi], so
(7) proves (3).

If W=sqrt(2), use sqrt(2)>7/5 in (2):

    cos(delta)<1-1250*(3+2*sqrt(2))/5041
              <1-1250*(3+14/5)/5041
              =-2209/5041<-2/5.

The exact half-angle identity gives
sin(pi/8)^2=(2-sqrt(2))/4<3/20<4/25,
so sin(pi/8)<2/5. Since
cos(5*pi/8)=-sin(pi/8)>-2/5, we obtain

    cos(delta)<cos(5*pi/8),

which proves (4) by strict monotonicity.
This completes the hand proof.

## Role in the eight-square project

The positive-stress equilibrium of a central square
which touches no containing-circle vertex has zero
resultant contact force. If that square has precisely
two nonzero forces carried by two separate opposing
contact normals, the two normals must be opposite;
the neighboring pair then satisfies the theorem's
separating-axis hypotheses (1).

This makes the angular cost of an exact central
two-contact transmission quantitative. It is
particularly large for diagonal central normals.
However the theorem does **not** establish that
every minimizer has such a transmitter or that
its two neighbors bound the remaining six squares
in the candidate's five-corner pattern. Higher
central stress degree and other actual contacts
remain possible. Thus no unrestricted equality
R8=Rhat is inferred.
