# n=9 TREE.03: three origin-vertex squares leave total capacity at most eight

**Status:** complete hand argument for the stated physical configuration; independent audit and Lean verification pending. This closes the entire TREE.03 completion case, not a small angle subcase. All additional squares may rotate independently and use oblique separating axes.

**Theorem.** Suppose pairwise interior-disjoint unit squares lie in the disk centered at 0 of squared radius q0=17/4. If three of the squares have 0 as a vertex, then there are at most **eight squares in total**.

The theorem assumes no stress, coordinate-separating frame, common orientation or exact contact pattern among the other squares. It therefore applies directly to the full TREE.03 family of TREE_RADIUS_QUANTIZATION.md.

## 1. Exact center and separation bounds

For a unit square with center c and orthonormal side vectors u,v, its largest corner squared norm is

    |c|^2 + 1/2 + |c.u| + |c.v| >= |c|^2 + 1/2 + |c|.

Since t^2+t+1/2 increases for t>=0 and equals 17/4 at t=3/2, every square center obeys |c|<=3/2. Distinct centers are at Euclidean distance >=1 because the open radius-1/2 inscribed disks are disjoint.

Let U be one of the three squares whose vertex is 0. In its own axes U=[0,1]^2, and its center has norm 1/sqrt(2). The tangent cone of U at 0 is its closed right-angle quadrant.

## 2. A vertex-origin quadrant excludes all other centers except its two outer endpoints

**Lemma 2.1.** If the center c=(x,y) of another square lies in U's closed quadrant x,y>=0, then c is exactly (3/2,0) or (0,3/2).

*Proof.* The inscribed open half-radius disk about c must avoid the interior of U. Therefore dist(c,[0,1]^2)>=1/2. Together with |c|<=3/2:

- If x,y<=1, the distance is zero.
- If x>1 and y<=1, the distance is x-1. Thus x>=3/2; the center-radius bound forces x=3/2,y=0. Exchange coordinates for the other one-sided case.
- If x,y>1, the squared distance is

      x^2+y^2+2-2(x+y) < 9/4+2-4 = 1/4,

  because x+y>2. This is impossible.

Boundary values x=1 or y=1 are included in the first two cases. QED.

In particular no other square center lies in the **open** quadrant of U. This uses only physical nonoverlap, not an axis-aligned separator between the squares.

## 3. Three vertex squares force every other center into an annulus and three short angular gaps

The three right-angle cone interiors at 0 are disjoint; otherwise the corresponding square interiors overlap near 0. Order the cones cyclically. The three intervening gaps have angular lengths g1,g2,g3>=0 with

    g1+g2+g3 = 2*pi-3*pi/2 = pi/2.

By Lemma 2.1, all additional center directions lie in these three **closed gaps**, endpoints included. A zero-length gap can contain at most one center, because its ray is a cone boundary and Lemma 2.1 permits only the radius-3/2 point on that ray. Gaps have disjoint endpoints except when their own two endpoints coincide; the original positive-width cones separate the different gaps.

**Lemma 3.1.** Every additional center c has |c|>=1/sqrt(2).

*Proof.* The three central centers have norm a=1/sqrt(2) and point along their cone bisectors. Successive bisector angle gaps are pi/2+gi<=pi. Hence every direction is within pi/2 of at least one central-center direction. Choose its center c_j, so c.c_j>=0. If |c|<a, then

    |c-c_j|^2 = |c|^2+a^2-2c.c_j < 2a^2 = 1,

contradicting the center-distance bound. The case c=0 is included by the same strict inequality. QED.

Thus the radius of every additional center belongs to the closed interval [1/sqrt(2),3/2].

## 4. Annular centers at angular distance at most thirty degrees are too close

**Lemma 4.1.** Two points with radii r,s in [1/sqrt(2),3/2] and minor angular separation theta<=pi/6 are at distance strictly less than one.

*Proof.* Their squared distance is r^2+s^2-2rs*cos(theta), at most r^2+s^2-sqrt(3)*rs. This expression is separately convex in r and s, so its maximum on the radius rectangle is attained at one of its four corners. The three distinct corner values are

    1-sqrt(3)/2,
    (9/2)*(1-sqrt(3)/2),
    (11-3*sqrt(6))/4.

All are strictly less than one. For the second inequality use sqrt(3)>14/9, following from 3>196/81. For the third use 3*sqrt(6)>7, following from 54>49. QED.

Consequently the directions of any two additional square centers are separated by **more than pi/6**, whenever they are compared within any one of the three gaps (each gap has length <=pi/2, so the consecutive gap angle is a minor angle).

## 5. The full completion capacity

Let m be the number of additional squares. Assign each additional center to its unique closed gap, and let k<=3 be the number of occupied gaps. If an occupied gap contains n_i centers in angle order, the distance between each consecutive pair of directions is greater than pi/6 by Lemma 4.1. Therefore

    g_i > (n_i-1)*pi/6       when n_i>=2,

and g_i>=0=(n_i-1)*pi/6 when n_i=1.

If m>=6, then m-k>=3, and some gap has at least two centers. Summing the preceding inequalities gives the strict contradiction

    pi/2 = sum g_i > (m-k)*pi/6 >= pi/2.

Hence m<=5. Including the three vertex-origin squares, the total is at most eight. This proves the theorem.

## 6. Exact gate impact

- [x] **TREE.03 CLOSED hand:** every physical nine-square completion of three unloaded origin-vertex bodies at R^2=17/4 is impossible, with arbitrary central cone gaps and arbitrary extra orientations.
- The argument also re-proves a capacity obstruction whenever such a three-square origin-vertex subconfiguration appears for any other reason; it does not require a positive-tree certificate.
- The earlier TREE.12 and TREE.04 completion gates remain closed. TREE.20, TREE.11 and TREE.02 remain open at this commit; the cyclic branch remains separate and open.
- No lower-radius window is needed for this capacity theorem itself. The tree-radius reduction leading to q0=17/4 still has its declared window dependency.

The general proof uses interval convexity, exact radicals and angular counting. Numerical sampling and an orientation grid are not premises. No Lean compilation, CI or independent full mathematical audit is claimed.