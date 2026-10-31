# Independent review of the radial C6 doubly shared return exclusion

Date: October 26, 2026.

**Result: PASS for the entire stated physical subfamily.** Reviewed
source: SIX_CYCLE_ONE_RADIAL_DOUBLE_SHARED_RETURN_EXCLUSION.md.
The two unique turns must be strictly greater than pi/2, and the
actual B--C transmitter must be genuinely shared at both endpoints.
The unrestricted radial parent and lower-turn unique features are
not inferred.

## 1. Physical frame, owner and moment checks

I checked the new source against the complete endpoint identities of
SIX_CYCLE_DOUBLE_SHARED_CHANNEL_EXCLUSION.md and the local genuine
share chart in SIX_CYCLE_SHARED_SUPPORT_FUNCTIONAL.md. The actual
double ownership makes both endpoint square frames parallel to the
side transmitter. The endpoint-center signs and positive channel
height give the physical corners (-a,b),(c,e), with all four own
coordinates strictly greater than 1/2 and a+c=3.

The two strict unique turns force their other applications to be the
opposite vertices (1-a,b-1),(c-1,e-1). Their S-incident interfaces
have no second genuine share. At a loaded vertex an axis normal
would either give such a genuine share or a forbidden singleton
vertex/vertex side-axis endpoint. Thus the two components of each
S-incident normal in its inward square frame are strictly positive,
as used in the estimate.

I independently reconstructed the sign a>b. For B, write
q=(-tau a,tau b), and its S-to-B normal as (-X,Y)/L, with
X=1-(1-tau)a and Y=1-(1-tau)b. Then

    det(q,(-X,Y)/L)=tau(b-a)/L.

The same oriented cycle moment on the rightward B--C channel is
det(q,(1,0))=-H<0. Hence a>b, and the reflected computation gives
c>e. This uses the unchanged positive proper concurrences of the
two unique bodies only. No assertion about the radial S concurrence
or its two weight values is needed.

The complete radial support theorem supplies the actual two distinct
inner ports of S, each with squared norm d^2+1/4. Their original
reserve-one equations are exactly P_B=Q_B-G_B and P_C=Q_C-G_C.
No transmitter slider or shared endpoint is replaced.

## 2. Concavity and exact arithmetic

From a>b and c>e, both a,c lie strictly between
R/sqrt(2) and 3-R/sqrt(2). The two endpoints of this interval lie
in (0,R) throughout the original radius window. The symmetric sum
sqrt(R^2-a^2)+sqrt(R^2-(3-a)^2) is concave there, so its minimum
over the closed interval is at either endpoint. This proves the
source's lower bound for b+e over the entire original interval.

I independently checked the fixed rational comparisons:

    (79/40)^2 - 2(139/100)^2 = 1457/40000,
    (79/40)^2 - (161/100)^2 - (8/7)^2
                                      = 4709/1960000,
    (121/60)^2 - 1041/256 = 31/57600,
    1773/700 - 151/60 = 17/1050.

All are strictly positive. Both individual heights b,e exceed 8/7,
and their sum exceeds 1773/700, which is strictly larger than
d+3/2. The use of concavity is legitimate at both angular/coordinate
endpoints; no sampling or extra radius subdivision enters.

## 3. Independent radial-port norm expansion

In B's inward orthonormal coordinates,
Q=(a-1,b-1), G=(g_x,g_y), with g_x,g_y>0 and |G|=1.
Since a>b>1,

    Q dot G > (b-1)(g_x+g_y) >= b-1.

I re-expanded the resulting norm:

    |Q-G|^2
      =R^2+3-2a-2b-2 Q dot G
      <R^2+5-2a-4b.

The reflected C formula has c,e in place of a,b. Both left
sides equal R^2-2d-1. Adding and using the unchanged actual
reserve identity a+c=3 gives b+e<d+3/2, contradicting the
strict concavity lower bound. All inequalities retain their strict
sign because g_x>0 and a>b.

## 4. Whole subfamily and retained limitations

The proof covers every original shared mean at the two B--C ends,
including both side endpoints whenever they are genuine means, and
all allowed values of both radial circle weights. It uses all three
real side transmitters only through their exact original ports;
their transverse positions and all three extras remain present.
It imports no upper bound of 135 degrees at the radial unit.

The right-turn radial endpoint has already been classified with
strict opposite-vertex B--C applications, so it cannot satisfy the
genuine double-share premise. The strict branch is excluded directly
by the new norm contradiction. The theorem does not assert that
every original one-radial C6 has both unique turns strict, nor does
it exclude one-owner or nonshared return channels by this argument.

This is a complete analytic physical-subfamily exclusion with no
finite sign packet, numerical pose premise, Lean compilation or CI.
