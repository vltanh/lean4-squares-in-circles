module

public import SquaresInCircles.Eight.Words.Second.Mixed.LPrimaryZero

/-!
# Eight squares: fixed references for the shared L primary zero-source curve

The references use exact harmonic coordinates and squared rational
radical cages. Whole-interval derivative signs, proved in the preceding
module, transfer these references to the complete curve.
-/

@[expose] public section
noncomputable section
open Set
namespace SquaresInCircles.Eight.SecondWord.LPrimaryZero
open CommonQuarter CorePairGeometry Arithmetic HeightLabel

lemma reference_trig :
    (98315693/100000000:ℝ)≤Real.sin (1387/1000) ∧
    Real.sin (1387/1000)≤98315697/100000000 ∧
    (9138163/50000000:ℝ)≤Real.cos (1387/1000) ∧
    Real.cos (1387/1000)≤4569082/25000000 := by
  have hs := HighOrderTaylor.S11_le_sin (x := (1387/1000:ℝ)) (by norm_num)
  have hsU := HighOrderTaylor.sin_le_S13 (x := (1387/1000:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (1387/1000:ℝ)) (by norm_num)
  have hcU := HighOrderTaylor.cos_le_C12 (x := (1387/1000:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.S13,HighOrderTaylor.C14,HighOrderTaylor.C12,
    sin9,sin7,cos10,cos8] at hs hsU hc hcU
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

lemma reference_coordinates :
    (16895719/10000000:ℝ)≤U (1387/1000) ∧ U (1387/1000)≤8447861/5000000 ∧
    (194741/200000:ℝ)≤w (1387/1000) ∧ w (1387/1000)≤2434263/2500000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [reference_trig.1,reference_trig.2.2.1],
    by linarith [reference_trig.2.1,reference_trig.2.2.2],
    by linarith [reference_trig.1,reference_trig.2.2.2],
    by linarith [reference_trig.2.1,reference_trig.2.2.1]⟩

lemma reference_height_value :
    -(467831/1000000:ℝ)<LHeight.eval (16895719/10000000) := by
  have hr := root_cage (u := (16895719/10000000:ℝ))
    (l := (515011357819/500000000000:ℝ))
    (r := (1030022715639/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma reference_height_slopes :
    (1027303/1000000:ℝ)<LHeight.d1 (16895719/10000000) ∧
    LHeight.d1 (8447861/5000000)<(205461/200000:ℝ) := by
  constructor
  · have hu : (16895719/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (16895719/10000000:ℝ))
      (l := (515011357819/500000000000:ℝ))
      (r := (1030022715639/1000000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    have hp := root_pos (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]
  · have hu : (8447861/5000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (8447861/5000000:ℝ))
      (l := (51501111177/50000000000:ℝ))
      (r := (206004444709/200000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    have hp := root_pos (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]

lemma reference_cost :
    (17999/20000:ℝ)<K (1387/1000) ∧ |KD (1387/1000)|<3/10000 := by
  have hφ : (1387/1000:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := reference_coordinates
  have hU : U (1387/1000)∈Icc (33/20) (383/200) :=
    ⟨by linarith [hu.1],by linarith [hu.2.1]⟩
  have hm := LHeightBounds.eval_monotone
    (show (16895719/10000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) hu.1
  have hdl := LHeightBounds.first_monotone_high
    (show (16895719/10000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hU hu.1
  have hdu := LHeightBounds.first_monotone_high hU
    (show (8447861/5000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hu.2.1
  have hd : (1027303/1000000:ℝ)≤LHeight.d1 (U (1387/1000)) ∧
      LHeight.d1 (U (1387/1000))≤205461/200000 :=
    ⟨reference_height_slopes.1.le.trans hdl,hdu.trans reference_height_slopes.2.le⟩
  have hl := mul_le_mul hd.1 hu.2.2.1 (by norm_num : (0:ℝ)≤194741/200000)
    (by linarith [hd.1] : 0≤LHeight.d1 (U (1387/1000)))
  have hh := mul_le_mul hd.2 hu.2.2.2
    (by linarith [hu.2.2.1] : 0≤w (1387/1000)) (by norm_num : (0:ℝ)≤205461/200000)
  constructor
  · dsimp [K,e]
    linarith [reference_height_value]
  · rw [abs_lt]
    dsimp [KD]
    constructor <;> norm_num at * <;> linarith

lemma middle_reference_coordinates :
    (8384279/5000000:ℝ)≤U (7/5) ∧ U (7/5)≤16768561/10000000 ∧
    (2456467/2500000:ℝ)≤w (7/5) ∧ w (7/5)≤9825871/10000000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [PrimaryZero.terminal_trig.1,PrimaryZero.terminal_trig.2.2.1],
    by linarith [PrimaryZero.terminal_trig.2.1,PrimaryZero.terminal_trig.2.2.2],
    by linarith [PrimaryZero.terminal_trig.1,PrimaryZero.terminal_trig.2.2.2],
    by linarith [PrimaryZero.terminal_trig.2.1,PrimaryZero.terminal_trig.2.2.1]⟩

lemma middle_reference_height :
    (7517/5000:ℝ)<LHeight.d2 (8384279/5000000) ∧
    LHeight.d1 (16768561/10000000)<(5029/5000:ℝ) := by
  constructor
  · have hu : (8384279/5000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (8384279/5000000:ℝ))
      (l := (525298635541/500000000000:ℝ))
      (r := (1050597271083/1000000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hp := root_pos (LHeightBounds.domain hu)
    have hh := LHeight.d2_mul (LHeightBounds.domain hu)
    have hl := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤525298635541/500000000000) hr.1.le 3
    have hu' := pow_le_pow_left₀ hp.le hr.2.le 3
    apply (mul_lt_mul_iff_left₀ (pow_pos hp 3)).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith
  · have hu : (16768561/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
    have hr := root_cage (u := (16768561/10000000:ℝ))
      (l := (1050596792253/1000000000000:ℝ))
      (r := (525298396127/500000000000:ℝ))
      (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
    have hp := root_pos (LHeightBounds.domain hu)
    have hh := LHeight.d1_mul (LHeightBounds.domain hu)
    apply (mul_lt_mul_iff_left₀ hp).mp
    rw [hh]
    norm_num [LHeight,Q0]
    nlinarith [hr.1,hr.2]

lemma middle_reference :
    (77/100:ℝ)<KDD (7/5) ∧ (11/1000:ℝ)<KD (7/5) := by
  have hφ : (7/5:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := middle_reference_coordinates
  have hdd := LHeightBounds.second_monotone
    (show (8384279/5000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) hu.1
  have hd := LHeightBounds.first_monotone_high
    (show U (7/5)∈Icc (33/20) (383/200) from ⟨by linarith [hu.1],by linarith [hu.2.1]⟩)
    (show (16768561/10000000:ℝ)∈Icc (33/20) (383/200) by norm_num) hu.2.1
  have hm : (1/2:ℝ)≤ m (7/5) ∧ m (7/5)≤6768561/10000000 := by
    dsimp [m,U,PrimaryZero.U] at hu ⊢
    constructor <;> linarith [hu.1,hu.2.1]
  have hdf : LHeight.d1 (U (7/5))≤(5029/5000:ℝ) := hd.trans middle_reference_height.2.le
  have hdf0 := LHeightBounds.first_lower (height_domain hφ)
  have hp := mul_le_mul hdf hm.2 (by linarith [hm.1] : 0≤ m (7/5)) (by norm_num : (0:ℝ)≤5029/5000)
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2456467/2500000) hu.2.2.1 2
  have hq := mul_le_mul (middle_reference_height.1.le.trans hdd) hs
    (by positivity : (0:ℝ)≤(2456467/2500000)^2)
    (by linarith [middle_reference_height.1] : 0≤LHeight.d2 (U (7/5)))
  have hprod := mul_le_mul hdf hu.2.2.2
    (by linarith [hu.2.2.1] : 0≤w (7/5)) (by norm_num : (0:ℝ)≤5029/5000)
  constructor
  · dsimp [KDD]
    norm_num at *
    linarith
  · dsimp [KD]
    norm_num at *
    linarith

lemma middle_terminal_coordinates :
    (15961679/10000000:ℝ)≤U (37/25) ∧ U (37/25)≤7980841/5000000 ∧
    w (37/25)≤1291919/1250000 := by
  dsimp [U,w,PrimaryZero.U,PrimaryZero.m,PrimaryZero.v]
  exact ⟨by linarith [middle_terminal_trig.1,middle_terminal_trig.2.2.1],
    by linarith [middle_terminal_trig.2.1,middle_terminal_trig.2.2.2],
    by linarith [middle_terminal_trig.2.1,middle_terminal_trig.2.2.1]⟩

lemma middle_terminal_height : LHeight.d1 (15961679/10000000)<(95891/100000:ℝ) := by
  have hu : (15961679/10000000:ℝ)∈LHeightBounds.heights := by norm_num [LHeightBounds.heights]
  have hr := root_cage (u := (15961679/10000000:ℝ))
    (l := (116955035591/100000000000:ℝ))
    (r := (1169550355911/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  have hp := root_pos (LHeightBounds.domain hu)
  have hh := LHeight.d1_mul (LHeightBounds.domain hu)
  apply (mul_lt_mul_iff_left₀ hp).mp
  rw [hh]
  norm_num [LHeight,Q0]
  nlinarith [hr.1,hr.2]

lemma middle_terminal_slope : (1/125:ℝ)<KD (37/25) := by
  have hφ : (37/25:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hu := middle_terminal_coordinates
  have hm := LHeightBounds.first_antitone_low
    (show (15961679/10000000:ℝ)∈Icc (171/125) (8/5) by norm_num)
    (show U (37/25)∈Icc (171/125) (8/5) from ⟨by linarith [hu.1],by linarith [hu.2.1]⟩) hu.1
  have hd := hm.trans middle_terminal_height.le
  have hp := mul_le_mul hd hu.2.2 (w_positive hφ).le (by norm_num : (0:ℝ)≤95891/100000)
  dsimp [KD]
  norm_num at hp
  linarith

lemma late_initial_height : (16167179/10000000:ℝ)≤U (73/50) := by
  have hs := HighOrderTaylor.S11_le_sin (x := (73/50:ℝ)) (by norm_num)
  have hc := HighOrderTaylor.C14_le_cos (x := (73/50:ℝ)) (by norm_num)
  norm_num [HighOrderTaylor.S11,HighOrderTaylor.C14,HighOrderTaylor.C12,sin9,sin7,cos10,cos8]
    at hs hc
  dsimp [U,PrimaryZero.U,PrimaryZero.m]
  linarith

lemma late_initial_value : -(67429/125000:ℝ)<LHeight.eval (16167179/10000000) := by
  have hr := root_cage (u := (16167179/10000000:ℝ))
    (l := (1140974685003/1000000000000:ℝ))
    (r := (285243671251/250000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma late_initial_cost : (9013/10000:ℝ)<K (73/50) := by
  have hφ : (73/50:ℝ)∈angles := ⟨by norm_num,by linarith [pi_hand_enclosure.1]⟩
  have hm := LHeightBounds.eval_monotone
    (show (16167179/10000000:ℝ)∈LHeightBounds.heights by norm_num [LHeightBounds.heights])
    (height_domain hφ) late_initial_height
  dsimp [K,e]
  linarith [late_initial_value]

lemma aligned_height_value : -(326887/500000:ℝ)<LHeight.eval (3/2) := by
  have hr := root_cage (u := (3/2:ℝ))
    (l := (161322658049/125000000000:ℝ))
    (r := (1290581264393/1000000000000:ℝ))
    (by norm_num) (by norm_num) (by norm_num [Q0]) (by norm_num [Q0])
  norm_num [LHeight,HeightLabel.eval,Q0]
  nlinarith [hr.2]

lemma aligned_cost : (4489/5000:ℝ)<K (Real.pi/2) := by
  norm_num [K,e,U,PrimaryZero.U,PrimaryZero.m]
  linarith [aligned_height_value,pi_hand_enclosure.1]

end SquaresInCircles.Eight.SecondWord.LPrimaryZero
