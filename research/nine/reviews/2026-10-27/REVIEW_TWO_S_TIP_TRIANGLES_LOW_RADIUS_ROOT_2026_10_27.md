# Root review: complete low and critical-radius S/S exclusion

Date: October 27, 2026.
Reviewer: root proof worker.
Source: TWO_S_TIP_TRIANGLES_LOW_RADIUS_EXCLUSION.md.

**Verdict: accepted for the entire original d<=1 S/S domain.**
The proof retains the possible H circle load until it proves physical
clearance, and includes the exact d=1 and all slider endpoints.
It leaves the separate d>1 family open.

The exact original graph has A,C true degree three with genuine
S leaves, B,D true loaded degree two, and H true degree four.
The source never invokes a two-force theorem at either decorated
root or at H. Both arbitrary completion squares remain.

The elementary radius comparisons in (1) are correct throughout
the declared window. In particular |d-1|<1/10 and r>11/20,
so the leaf-axis point (d-1,0) cannot belong to a physical
boundary square, even if that boundary corner has zero weight.

I checked the complete aligned S-star cover against the physical
unit-triangle owned-normal and opposite-vertex statements. An
owned vertical axis contradicts the original vertical balance.
One horizontal normal forces a same-sign west pair. Otherwise
the strict vertices have opposite vertical signs; the opposite
vertex pair and right-side pair are impossible, leaving exactly
the two left vertices. This uses only the local A equation and
physical contact of its two triangle neighbors, at arbitrary
degrees and loads on H.

For parallel west normals, every real mean height belongs to
[h-1,h] and their positive weighted mean is zero. At either
endpoint h=0 or h=1 both actual means must be zero. B would
contain the forbidden small leaf-axis point.

For the nonparallel pair I checked the exact torque cancellation:
vertical balance cancels the common x=d-1 term, leaving
mu_+ h s-mu_-(1-h)t=0 with all four factors mu_+,mu_-,s,t
strictly positive. Its sign is strictly negative at h=0 and
positive at h=1. Thus 0<h<1 in the complete local configuration,
with no normal selection and no changed shared-side mean.

Every genuine S root contains the inward radial unit segment.
For d<=1 it contains O. If its leaf direction is not an own
side axis, the full strict-vertex chart has both da,db strictly
between zero and one, so O is in its open interior. A distinct
closed S root containing O would then overlap it. For d<1,
the remaining aligned root also contains O openly because both
its radial interval and transverse slider are strict. This
gives the complete low-radius exclusion directly.

At d=1 both roots must therefore be aligned, and the endpoint
lemma makes O a relative side-interior point at each. Their
local open tangent half-planes must be opposite; any other
angle gives open overlap near O. Their two closed squares
therefore cover a full neighborhood of O. No third actual
unit can contain O, since its interior approaches O through
two-dimensional open sets.

The remaining critical-radius argument establishes exactly that
contradiction. In the parallel cover, the real B height has
absolute value at least r>1/2 and the other real height has
opposite sign. Their common unit-length interval bounds the
other absolute value by 1-r<r. In the nonparallel cover the
two vertex absolute heights sum to one, giving the same bound.
Thus the unchanged AH point has norm below r, proving H
physically circle-clear before its original circle force is
set to zero.

The two true H pair sums now are opposite. For either actual
triangle, all three full external origin moments vanish,
using the real private-branch torque sum at H and the genuine
leaf/circle systems at its other two bodies. The accepted
triangle external-ray theorem puts points of both opposite
closed rays in H. Convexity gives closed O containment,
including the case in which one ray is met only at O.
That contradicts the already proved neighborhood cover by A,C.

This is a complete strict-low and critical-radius core exclusion.
It does not use the false strict-positive-ray statement in a
zero-moment domain. No force is deleted, no endpoint is omitted,
and no higher-degree body is treated as a loaded tip. No numerical
pose, scalar certificate, Lean compilation, CI or full-parent
closure is claimed.

