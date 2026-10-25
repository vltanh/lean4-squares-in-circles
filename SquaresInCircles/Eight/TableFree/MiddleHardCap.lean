module

public import SquaresInCircles.Eight.TableFree.HardSplitConstruction
public import SquaresInCircles.Eight.TableFree.MiddlePositiveContraction

/-!
# Positive hard-cap gain at every actual source radius

Uncompiled draft.  The transverse parameter may be as small as `2/5`.
No lower bound on the actual source squared radius is imposed.  On the
part of its cap above `1/2`, the cap decreases at rate strictly larger
than `21/20`.  The scalar reserve is an exact positive square identity.
This permits strict original-circle recovery after middle-frame moves.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.TableFree.MiddleHardCap
open HardSplitCap MiddlePositiveContraction

structure Feasible (q D : ℝ) : Prop where
  ceiling : q ≤ qCap
  transverse : 2/5 ≤ D
  corner : (D+1)^2+1/4 ≤ q

theorem primary_lower {D θ X Y : ℝ}
    (hD : 2/5 ≤ D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 0 ≤ Y)
    (hcontact : D ≤ (X-1)*Real.cos θ-Y*Real.sin θ) : D+1 ≤ X := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 < Real.cos θ := by linarith
  have hYs := mul_nonneg hY hs
  have hX : 0 ≤ X-1 := by
    by_contra! hn
    have hp := mul_neg_of_neg_of_pos hn hc0
    linarith
  have hp := mul_le_mul_of_nonneg_left (Real.cos_le_one θ) hX
  nlinarith

theorem feasible_of_contact {q D θ X Y : ℝ}
    (hq : q ≤ qCap) (hD : 2/5 ≤ D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 ≤ Y)
    (hcontact : D ≤ (X-1)*Real.cos θ-Y*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) : Feasible q D := by
  have hX := primary_lower hD hθ (by linarith) hcontact
  have hXs := pow_le_pow_left₀ (by linarith : 0 ≤ D+1) hX 2
  have hYs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) hY 2
  exact ⟨hq,hD,by nlinarith⟩

theorem radicand_lower {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    1/4 ≤ q-(contact D θ)^2 ∧
      1/4 ≤ q-(contact D θ)^2-(Real.sin θ)^2 := by
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc1 := Real.cos_le_one θ
  have hD : 0 < D := by linarith [h.transverse]
  have hp := mul_nonneg hD.le (sub_nonneg.mpr hc1)
  have hc2 := pow_le_pow_left₀ (by linarith : 0 ≤ Real.cos θ) hc1 2
  dsimp [contact]
  constructor <;> nlinarith [h.corner,Real.sin_sq_add_cos_sq θ]

theorem root_sq {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (root q D θ)^2=q-(contact D θ)^2 :=
  Real.sq_sqrt (by linarith [(radicand_lower h hθ).1])

theorem root_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < root q D θ :=
  Real.sqrt_pos.mpr (by linarith [(radicand_lower h hθ).1])

theorem contact_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < contact D θ := by
  dsimp [contact]
  linarith [h.transverse,(transport_trig_coarse hθ).1]

theorem drift_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < drift q D θ := by
  have hr := root_pos h hθ
  have hrs := root_sq h hθ
  have hs := (transport_trig_coarse hθ).2.1
  have hb := (radicand_lower h hθ).2
  dsimp [drift]
  nlinarith

theorem cornerX_pos {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : 0 < cornerX q D θ := by
  have hc : 0 < Real.cos θ := by linarith [(transport_trig_coarse hθ).1]
  have hs := (transport_trig_coarse hθ).2.1
  exact add_pos_of_pos_of_nonneg (mul_pos hc (contact_pos h hθ))
    (mul_nonneg hs (root_pos h hθ).le)

theorem root_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    HasDerivAt (root q D) (contact D θ*Real.sin θ/root q D θ) θ := by
  have hC := (Real.hasDerivAt_cos θ).const_add D
  have hr : q-(contact D θ)^2 ≠ 0 := by linarith [(radicand_lower h hθ).1]
  have hd := ((hC.pow 2).const_sub q).sqrt hr
  convert hd using 1
  · rfl
  · dsimp [contact,root]
    field_simp [(root_pos h hθ).ne']

theorem cap_deriv {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : HasDerivAt (cap q D) (first q D θ) θ := by
  have hC := (Real.hasDerivAt_cos θ).const_add D
  have hd := ((Real.hasDerivAt_cos θ).mul (root_deriv h hθ)).sub
    ((Real.hasDerivAt_sin θ).mul hC)
  convert hd using 1
  · rfl
  · dsimp [first,cornerX,drift,contact]
    field_simp [(root_pos h hθ).ne']
    ring

theorem first_neg {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) : first q D θ < 0 := by
  unfold first
  exact div_neg_of_neg_of_pos
    (mul_neg_of_neg_of_pos (neg_neg_of_pos (cornerX_pos h hθ)) (drift_pos h hθ))
    (root_pos h hθ)

theorem cap_strictAnti {q D : ℝ} (h : Feasible q D) :
    StrictAntiOn (cap q D) (Icc 0 (7/10 : ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc 0 (7/10 : ℝ))
  · exact fun θ hθ => (cap_deriv h hθ).continuousAt.continuousWithinAt
  · intro θ hθ
    rw [(cap_deriv h (interior_subset hθ)).deriv]
    exact first_neg h (interior_subset hθ)

theorem cap_majorizes {q D θ X Y : ℝ}
    (h : Feasible q D) (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 0 ≤ Y)
    (hcontact : D ≤ (X-1)*Real.cos θ-Y*Real.sin θ)
    (hcircle : X^2+Y^2 ≤ q) : Y ≤ cap q D θ := by
  let P := X*Real.cos θ-Y*Real.sin θ
  let R := X*Real.sin θ+Y*Real.cos θ
  have hX := primary_lower h.transverse hθ hY hcontact
  obtain ⟨hc,hs,hsc⟩ := transport_trig_coarse hθ
  have hc0 : 0 ≤ Real.cos θ := by linarith
  have hP : contact D θ ≤ P := by dsimp [P,contact]; nlinarith
  have hP2 := pow_le_pow_left₀ (contact_pos h hθ).le hP 2
  have hR0 : 0 ≤ R := add_nonneg
    (mul_nonneg (by linarith [h.transverse]) hs) (mul_nonneg hY hc0)
  have hrotation : P^2+R^2=X^2+Y^2 := by
    dsimp [P,R]
    calc
      _ = (X^2+Y^2)*((Real.sin θ)^2+(Real.cos θ)^2) := by ring
      _ = X^2+Y^2 := by rw [Real.sin_sq_add_cos_sq,mul_one]
  have hR : R ≤ root q D θ := by
    have hw := root_pos h hθ
    have hw2 := root_sq h hθ
    nlinarith
  have hback : Real.cos θ*R-Real.sin θ*P=Y := by
    dsimp [P,R]
    linear_combination Y*(Real.sin_sq_add_cos_sq θ)
  have hR' := mul_le_mul_of_nonneg_left hR hc0
  have hP' := mul_le_mul_of_nonneg_left hP hs
  dsimp [cap]
  linarith

/-- Exact rate numerator reserve.  The proof works on every positive
source circle and requires no lower circle bound or numerical mesh. -/
theorem rate_numerator {D Y c s : ℝ}
    (hD : 2/5 ≤ D) (hY : 1/2 ≤ Y)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hunit : s^2+c^2=1) :
    43/5000 ≤ (D+Y*s)*(Y+D*s)-c*(Y+D*s)/20-(21/20)*c^2*s := by
  let N := fun d y : ℝ => (d+y*s)*(y+d*s)-c*(y+d*s)/20-(21/20)*c^2*s
  have hcs : c*s ≤ 1 := by
    have hp := mul_le_mul_of_nonneg_right hc1 hs0
    nlinarith
  have hDY : 0 ≤ Y*(1+s^2)+(D+2/5)*s-c*s/20 := by
    have hys := mul_nonneg (show 0 ≤ Y by linarith) (sq_nonneg s)
    have hds := mul_nonneg (show 0 ≤ D+2/5 by linarith) hs0
    nlinarith
  have hYY : 0 ≤ (2/5)*(1+s^2)+(Y+1/2)*s-c/20 := by
    have hys := mul_nonneg (show 0 ≤ Y+1/2 by linarith) hs0
    nlinarith [sq_nonneg s]
  have hDprod := mul_nonneg (show 0 ≤ D-2/5 by linarith) hDY
  have hYprod := mul_nonneg (show 0 ≤ Y-1/2 by linarith) hYY
  have hdiffD : N D Y-N (2/5) Y=
      (D-2/5)*(Y*(1+s^2)+(D+2/5)*s-c*s/20) := by dsimp [N]; ring
  have hdiffY : N (2/5) Y-N (2/5) (1/2)=
      (Y-1/2)*((2/5)*(1+s^2)+(Y+1/2)*s-c/20) := by dsimp [N]; ring
  have hreserve : N (2/5) (1/2)=
      (s-2/5)^2*((21/20)*s+26/25)+s/250+43/5000+
        (1-c)*(1/40+s/50) := by
    dsimp [N]
    linear_combination -(21/20)*s*hunit
  have hp := mul_nonneg (sq_nonneg (s-2/5))
    (show 0 ≤ (21/20)*s+26/25 by linarith)
  have hq := mul_nonneg (show 0 ≤ 1-c by linarith)
    (show 0 ≤ 1/40+s/50 by linarith)
  change 43/5000 ≤ N D Y
  linarith

theorem first_lt_rate {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 ≤ cap q D θ) :
    first q D θ < -(21/20 : ℝ) := by
  let X := cornerX q D θ
  let Y := cap q D θ
  let w := root q D θ
  let c := Real.cos θ
  let s := Real.sin θ
  have hc0 : 0 < c := by dsimp [c]; linarith [(transport_trig_coarse hθ).1]
  have hs0 : 0 ≤ s := (transport_trig_coarse hθ).2.1
  have hw : 0 < w := root_pos h hθ
  have hunit : s^2+c^2=1 := Real.sin_sq_add_cos_sq θ
  have hcontact : (X-1)*c-Y*s=D := HardSplitCap.corner_contact q D θ
  have hback : Y*c+X*s=w := by
    dsimp [X,Y,w,c,s,cornerX,cap]
    linear_combination root q D θ*(Real.sin_sq_add_cos_sq θ)
  have hxc : X*c=D+c+Y*s := by nlinarith [hcontact]
  have hwc : w*c=Y+D*s+c*s := by
    linear_combination -c*hback+s*hcontact+Y*hunit
  have hwsc : (w-s)*c=Y+D*s := by nlinarith [hwc]
  have hN := rate_numerator h.transverse hY hc0.le (Real.cos_le_one θ)
    hs0 (Real.sin_le_one θ) hunit
  have hid : (X*(w-s)-(21/20)*w)*c^2=
      (D+Y*s)*(Y+D*s)-c*(Y+D*s)/20-(21/20)*c^2*s := by
    calc
      _ = (X*c)*((w-s)*c)-(21/20)*(w*c)*c := by ring
      _ = (D+c+Y*s)*(Y+D*s)-(21/20)*(Y+D*s+c*s)*c := by rw [hxc,hwsc,hwc]
      _ = _ := by ring
  have hpositive : 0 < X*(w-s)-(21/20)*w := by
    by_contra! hn
    have hp := mul_nonpos_of_nonpos_of_nonneg hn (sq_nonneg c)
    rw [hid] at hp
    linarith
  change -X*(w-s)/w < -(21/20 : ℝ)
  rw [div_lt_iff₀ hw]
  nlinarith

/-- Finite strict gain on the entire original feasible angle interval. -/
theorem cap_gain {q D r t : ℝ} (h : Feasible q D)
    (hr : r ∈ Icc 0 (7/10 : ℝ)) (ht : 0 ≤ t) (htr : t < r)
    (hfloor : 1/2 ≤ cap q D r) :
    cap q D r+(21/20)*(r-t) < cap q D t := by
  have hf : StrictAntiOn (fun x => cap q D x+(21/20)*x) (Icc 0 r) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 r)
    · intro x hx
      exact ((cap_deriv h ⟨hx.1,hx.2.trans hr.2⟩).fun_add
        ((hasDerivAt_id' x).const_mul (21/20))).continuousAt.continuousWithinAt
    · intro x hx
      have hxm := interior_subset hx
      have hxd : x ∈ Icc 0 (7/10 : ℝ) := ⟨hxm.1,hxm.2.trans hr.2⟩
      have hcap : 1/2 ≤ cap q D x := hfloor.trans
        ((cap_strictAnti h).antitoneOn hxd hr hxm.2)
      have hd := (cap_deriv h hxd).fun_add ((hasDerivAt_id' x).const_mul (21/20))
      rw [hd.deriv]
      linarith [first_lt_rate h hxd hcap]
  have hh := hf (show t ∈ Icc 0 r from ⟨ht,htr.le⟩) ⟨hr.1,le_rfl⟩ htr
  dsimp only at hh
  linarith

theorem corner_norm {q D θ : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) :
    (cornerX q D θ)^2+(cap q D θ)^2=q := by
  calc
    _ = ((Real.sin θ)^2+(Real.cos θ)^2)*
        ((contact D θ)^2+(root q D θ)^2) := by unfold cornerX cap; ring
    _ = q := by rw [Real.sin_sq_add_cos_sq,one_mul,root_sq h hθ]; ring

/-- A target transverse corner strictly below the same-radius cap gives
an explicit exact hard contact strictly inside that original circle. -/
theorem strict_contact_norm {q D θ Y : ℝ} (h : Feasible q D)
    (hθ : θ ∈ Icc 0 (7/10 : ℝ)) (hY : 1/2 ≤ Y) (hcap : Y < cap q D θ) :
    7/5 ≤ primaryCorner D Y θ ∧
      (primaryCorner D Y θ)^2+Y^2 < q ∧ Y < primaryCorner D Y θ := by
  have hc0 : 0 < Real.cos θ := by linarith [(transport_trig_coarse hθ).1]
  have hs0 := (transport_trig_coarse hθ).2.1
  have htarget := primaryCorner_contact (D := D) (Y := Y) hc0.ne'
  have hX := primary_lower h.transverse hθ (show 0 ≤ Y by linarith) htarget.ge
  have hsource := HardSplitCap.corner_contact q D θ
  have hcompare : primaryCorner D Y θ ≤ cornerX q D θ := by
    have hp := mul_nonneg hs0 (sub_nonneg.mpr hcap.le)
    apply (mul_le_mul_iff_right₀ hc0).mp
    nlinarith
  have hXsq := pow_le_pow_left₀ (show 0 ≤ primaryCorner D Y θ by linarith [h.transverse])
    hcompare 2
  have hYsq := pow_lt_pow_left₀ hcap (show 0 ≤ Y by linarith) (by decide : (2:ℕ)≠0)
  have hnorm : (primaryCorner D Y θ)^2+Y^2 < q := by linarith [corner_norm h hθ]
  have hprimary : 7/5 ≤ primaryCorner D Y θ := by linarith [h.transverse]
  have hsorted : Y < primaryCorner D Y θ := by
    by_contra! hn
    have hXs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 7/5) hprimary 2
    have hYs := pow_le_pow_left₀ (show 0 ≤ primaryCorner D Y θ by linarith) hn 2
    have hq := h.ceiling
    dsimp [qCap] at hq
    nlinarith
  exact ⟨hprimary,hnorm,hsorted⟩

end SquaresInCircles.Eight.TableFree.MiddleHardCap
