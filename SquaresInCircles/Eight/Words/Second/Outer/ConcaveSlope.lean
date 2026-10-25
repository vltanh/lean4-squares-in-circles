module

public import Mathlib.Tactic
public import SquaresInCircles.Eight.Words.Second.Outer.MinimumCalculus

/-!
# Eight squares: endpoint minima from a concave first derivative

Reflection of the increasing-curvature endpoint lemma proves the dual
statement: a concave first derivative that is positive at the left
endpoint permits no value below both endpoint values.  The derivatives
of the reflected function are supplied explicitly.
-/

@[expose] public section
noncomputable section
open Set

namespace SquaresInCircles.Eight.SecondWord.MinimumCalculus

theorem endpoint_minimum_of_third_nonpos {f d dd ddd : ℝ→ℝ} {l u x : ℝ}
    (hx : x∈Icc l u)
    (hf : ∀ t∈Icc l u, HasDerivAt f (d t) t)
    (hd : ∀ t∈Icc l u, HasDerivAt d (dd t) t)
    (hdd : ∀ t∈Icc l u, HasDerivAt dd (ddd t) t)
    (hthird : ∀ t∈Icc l u, ddd t≤0)
    (hleft : 0<d l) : min (f l) (f u)≤f x := by
  have hdom (t : ℝ) (ht : t∈Icc (-u) (-l)) : -t∈Icc l u := by
    constructor <;> linarith [ht.1,ht.2]
  have hfr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => f (-s)) (-d (-t)) t := by
    have h : HasDerivAt (fun s => f (-s)) (d (-t)*(-1)) t :=
      (hf (-t) (hdom t ht)).comp t (hasDerivAt_neg t)
    convert h using 1
    ring
  have hdr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => -d (-s)) (dd (-t)) t := by
    have h : HasDerivAt (fun s => -d (-s)) (-(dd (-t)*(-1))) t :=
      ((hd (-t) (hdom t ht)).comp t (hasDerivAt_neg t)).neg
    convert h using 1
    ring
  have hddr (t : ℝ) (ht : t∈Icc (-u) (-l)) :
      HasDerivAt (fun s => dd (-s)) (-ddd (-t)) t := by
    have h : HasDerivAt (fun s => dd (-s)) (ddd (-t)*(-1)) t :=
      (hdd (-t) (hdom t ht)).comp t (hasDerivAt_neg t)
    convert h using 1
    ring
  have hh := endpoint_minimum (show -x∈Icc (-u) (-l) by
      constructor <;> linarith [hx.1,hx.2]) hfr hdr hddr
    (fun t ht => neg_nonneg.mpr (hthird (-t) (hdom t ht)))
    (show -d (-(-l))<0 by simpa only [neg_neg] using neg_neg_of_pos hleft)
  simpa only [neg_neg,min_comm] using hh

end SquaresInCircles.Eight.SecondWord.MinimumCalculus
