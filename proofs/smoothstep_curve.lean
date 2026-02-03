import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Topology.Order.DenselyOrdered

section GenericFramework

open ContDiff Topology
open MeasureTheory
open Filter

/-
## Generic Framework for Smoothstep Curves

The following definitions and lemmas establish the mathematical foundation for constructing
smoothstep curves from any C^∞ shape function H on [0,1] (or equivalently, from its derivative
G = H' which serves as a bump function in the implementation).
-/

lemma intervalIntegrable_on_unit_segment
  {f : ℝ → ℝ} {a b : ℝ} (hf : ContDiffOn ℝ ∞ f unitInterval)
  (ha : a ∈ unitInterval) (hb : b ∈ unitInterval) (hab : a ≤ b) :
  IntervalIntegrable f volume a b :=
  (hf.continuousOn.mono fun _ ht => ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩).intervalIntegrable_of_Icc hab

/-- A convenient `FTCFilter` instance for `𝓝[unitInterval]`. -/
private def ftcFilter_unitInterval {x : ℝ} (hx : x ∈ unitInterval) :
    intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) :=
  intervalIntegral.FTCFilter.nhdsIcc (h := ⟨hx⟩)

-- The standard primitive from 0: z ↦ ∫ t in (0)..z, f t.
noncomputable def primitiveFromZero (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ t in (0)..z, f t

-- Fundamental result: the primitive z ↦ ∫_{0..z} f is C^∞ on [0,1] if f is C^∞ on [0,1]
lemma primitive_is_C_inf_on_unitInterval
  (f : ℝ → ℝ) (hfinf : ContDiffOn ℝ ∞ f unitInterval) :
  ContDiffOn ℝ ∞ (primitiveFromZero f) unitInterval := by
  have h_deriv x (hx : x ∈ unitInterval) : HasDerivWithinAt (primitiveFromZero f) (f x) unitInterval x :=
    haveI := ftcFilter_unitInterval hx
    intervalIntegral.integral_hasDerivWithinAt_right
      (intervalIntegrable_on_unit_segment hfinf ⟨le_rfl, by norm_num⟩ hx hx.1)
      (hfinf.continuousOn.stronglyMeasurableAtFilter_nhdsWithin isClosed_Icc.measurableSet x)
      (hfinf.continuousOn.continuousWithinAt hx)
  exact (contDiffOn_infty_iff_derivWithin uniqueDiffOn_Icc_zero_one).mpr
    ⟨fun x hx => (h_deriv x hx).differentiableWithinAt,
     (contDiffOn_congr fun x hx => (h_deriv x hx).derivWithin (uniqueDiffOn_Icc_zero_one x hx)).mpr hfinf⟩

-- Helper: convert uIoc integral to intervalIntegral
lemma uIoc_to_intervalIntegral (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ unitInterval) :
  (∫ t in Set.uIoc 0 z, f t) = ∫ t in (0)..z, f t := by
  simpa [Set.uIoc, hz.1] using (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := 0) (b := z) hz.1).symm

def clampUnit (z : ℝ) : ℝ := min (max z 0) 1

lemma clampUnit_of_mem {z : ℝ} (hz : z ∈ unitInterval) : clampUnit z = z := by simp [clampUnit, hz.1, hz.2]

lemma clampUnit_of_nonpos {z : ℝ} (hz : z ≤ 0) : clampUnit z = 0 := by simp [clampUnit, hz]

/-
### Core Definitions
-/

namespace Smooth

-- Numerator of the normalized integral: ∫₀ᶻ H'(t) dt (where H' is the derivative of the shape function)
noncomputable def HInt (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

-- Denominator of the normalized integral: ∫₀¹ H'(t) dt (normalization constant)
noncomputable def HInt_denom (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

-- The shape function H(z) = HInt(clampUnit z) / HInt_denom
noncomputable def H (G : ℝ → ℝ) (z : ℝ) : ℝ := HInt G (clampUnit z) / HInt_denom G

lemma HInt_zero (G : ℝ → ℝ) : HInt G 0 = 0 := by simp [HInt]

lemma HInt_one (G : ℝ → ℝ) : HInt G 1 = HInt_denom G := by simp [HInt, HInt_denom]

lemma H_zero (G : ℝ → ℝ) : H G 0 = 0 := by simp [H, HInt_zero, clampUnit_of_nonpos le_rfl]

lemma H_one (G : ℝ → ℝ) (hden : HInt_denom G ≠ 0) : H G 1 = 1 := by
  simp [H, clampUnit_of_mem ⟨zero_le_one, le_rfl⟩, HInt_one, hden]

lemma HInt_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (HInt G) unitInterval :=
  (primitive_is_C_inf_on_unitInterval G hG).congr fun z hz => by
    simp only [HInt, primitiveFromZero, uIoc_to_intervalIntegral G hz]

lemma HInt_denom_pos
  {G : ℝ → ℝ} (hint : IntervalIntegrable G volume 0 1)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  0 < HInt_denom G := by
  rw [HInt_denom, uIoc_to_intervalIntegral G ⟨zero_le_one, le_rfl⟩]
  exact intervalIntegral.intervalIntegral_pos_of_pos_on hint hpos (by norm_num)

lemma HInt_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) :
  MonotoneOn (HInt G) unitInterval := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with rfl | hlt
  · exact le_rfl
  · have hint_xy := intervalIntegrable_on_unit_segment hG hx hy hxy
    have h0x := intervalIntegrable_on_unit_segment hG ⟨le_rfl, by norm_num⟩ hx hx.1
    have hpos_xy t (ht : t ∈ Set.Ioo x y) : 0 < G t :=
      hpos t ⟨hx.1.trans_lt ht.1, ht.2.trans_le hy.2⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals h0x hint_xy
    have hxInt : (∫ t in (0)..x, G t) = HInt G x := by simp [HInt, uIoc_to_intervalIntegral G hx]
    have hyInt : (∫ t in (0)..y, G t) = HInt G y := by simp [HInt, uIoc_to_intervalIntegral G hy]
    have hinc_pos := intervalIntegral.intervalIntegral_pos_of_pos_on hint_xy hpos_xy hlt
    linarith [hadd]

lemma H_eq_ratio_on_unit {G : ℝ → ℝ} {z : ℝ} (hz : z ∈ unitInterval) :
  H G z = HInt G z / HInt_denom G := by simp [H, clampUnit_of_mem hz]

lemma H_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < HInt_denom G) :
  MonotoneOn (H G) unitInterval := fun _ hx _ hy hxy => by
  simp only [H_eq_ratio_on_unit hx, H_eq_ratio_on_unit hy]
  exact div_le_div_of_nonneg_right (HInt_monotone_on_unit hG hpos hx hy hxy) hden.le

lemma H_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval) :
  ContDiffOn ℝ ∞ (H G) unitInterval :=
  (contDiffOn_congr fun _ hx => H_eq_ratio_on_unit hx).mpr ((HInt_contDiffOn hG).div_const _)

private lemma H_eq_ratio_eqOn (G : ℝ → ℝ) :
    Set.EqOn (H G) (fun z => HInt G z / HInt_denom G) unitInterval :=
  fun _ hz => H_eq_ratio_on_unit hz

lemma derivWithin_HInt_eq
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) :
    derivWithin (HInt G) unitInterval x = G x := by
  classical
  have hint := intervalIntegrable_on_unit_segment hG ⟨le_rfl, by norm_num⟩ hx hx.1
  have hcont : ContinuousWithinAt G unitInterval x := hG.continuousOn.continuousWithinAt hx
  have hmeas : StronglyMeasurableAtFilter G (𝓝[unitInterval] x) volume :=
    hG.continuousOn.stronglyMeasurableAtFilter_nhdsWithin isClosed_Icc.measurableSet x
  haveI : intervalIntegral.FTCFilter x (𝓝[unitInterval] x) (𝓝[unitInterval] x) :=
    ftcFilter_unitInterval hx
  have hEqOn : Set.EqOn (HInt G) (fun z => ∫ t in (0)..z, G t) unitInterval :=
    fun z hz => by simp [HInt, uIoc_to_intervalIntegral G hz]
  have hHas := intervalIntegral.integral_hasDerivWithinAt_right (a := 0) (b := x) (s := unitInterval) hint hmeas hcont
  rw [derivWithin_congr hEqOn (hEqOn hx)]
  exact hHas.derivWithin (uniqueDiffOn_Icc_zero_one x hx)

lemma iteratedDerivWithin_succ_HInt
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) (n : ℕ) :
    iteratedDerivWithin (n + 1) (HInt G) unitInterval x =
      iteratedDerivWithin n G unitInterval x := by
  simp only [iteratedDerivWithin_succ']
  exact iteratedDerivWithin_congr (fun z hz => derivWithin_HInt_eq hG hz) hx

lemma iteratedDerivWithin_succ_H
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) (n : ℕ) :
    iteratedDerivWithin (n + 1) (H G) unitInterval x =
      (1 / HInt_denom G) * iteratedDerivWithin n G unitInterval x := by
  set c := (1 / HInt_denom G)
  have hEq : Set.EqOn (H G) (fun z => c * HInt G z) unitInterval := fun z hz => by
    simp [H, clampUnit_of_mem hz, c, div_eq_mul_inv, mul_comm]
  have hcont : ContDiffWithinAt ℝ (↑(n + 1)) (HInt G) unitInterval x :=
    (HInt_contDiffOn hG).contDiffWithinAt hx |>.of_le (by exact_mod_cast le_top)
  calc iteratedDerivWithin (n + 1) (H G) unitInterval x
      = iteratedDerivWithin (n + 1) (fun z => c * HInt G z) unitInterval x :=
          iteratedDerivWithin_congr hEq hx
    _ = c * iteratedDerivWithin (n + 1) (HInt G) unitInterval x :=
          iteratedDerivWithin_const_mul hx uniqueDiffOn_Icc_zero_one c hcont
    _ = c * iteratedDerivWithin n G unitInterval x := by rw [iteratedDerivWithin_succ_HInt hG hx]

lemma H_deriv_vanishes_at_point_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    {x : ℝ} (hx : x ∈ unitInterval) (hG_x : G x = 0)
    (hG_deriv_x : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval x = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval x = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  simp only [iteratedDerivWithin_succ_H hG hx k]
  rcases k with _ | k <;> simp [hG_x, hG_deriv_x _ (Nat.succ_pos _)]

lemma H_deriv_vanishes_at_zero_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_zero : G 0 = 0)
    (hG_deriv_zero : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 0 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 0 = 0 :=
  H_deriv_vanishes_at_point_from_G hG ⟨le_rfl, by norm_num⟩ hG_zero hG_deriv_zero

lemma H_deriv_vanishes_at_one_from_G
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hG_one : G 1 = 0)
    (hG_deriv_one : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n G unitInterval 1 = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n (H G) unitInterval 1 = 0 :=
  H_deriv_vanishes_at_point_from_G hG ⟨zero_le_one, le_rfl⟩ hG_one hG_deriv_one

-- H maps to [0,1] on unitInterval
lemma H_mem_unitInterval
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < HInt_denom G)
  {z : ℝ} (hz : z ∈ unitInterval) :
  H G z ∈ unitInterval := by
  have hHmono := H_monotone_on_unit hG hpos hden
  constructor
  · simpa [H_zero G] using hHmono ⟨le_rfl, by norm_num⟩ hz hz.1
  · simpa [H_one G hden.ne'] using hHmono hz ⟨zero_le_one, le_rfl⟩ hz.2

-- The curvature function κ(s) = R₁ + (R₂ - R₁) H(s/L)
noncomputable def kappaOfShape (H : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  R₁ + (R₂ - R₁) * H (s / L)

noncomputable def kappa (G : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  kappaOfShape (H G) s R₁ R₂ L

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval :=
  ⟨div_nonneg hs.1 hL.le, by simpa [div_self hL.ne'] using div_le_div_of_nonneg_right hs.2 hL.le⟩

lemma kappaOfShape_contDiffOn
  {H : ℝ → ℝ} (hH : ContDiffOn ℝ ∞ H unitInterval)
  (R₁ R₂ L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := by
  have hcomp := hH.comp (contDiffOn_id.div_const L) fun s hs => div_mem_unitInterval_of_mem_Icc hL hs
  simpa [kappaOfShape] using contDiffOn_const.add (contDiffOn_const.mul hcomp)

lemma kappa_contDiffOn
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (R₁ R₂ L : ℝ) (hL : 0 < L) :
  ContDiffOn ℝ ∞ (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) :=
  kappaOfShape_contDiffOn (H_contDiffOn hG) R₁ R₂ L hL

lemma kappaOfShape_at_zero (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hH0 : H 0 = 0) :
    kappaOfShape H 0 R₁ R₂ L = R₁ := by simp [kappaOfShape, hH0]

lemma kappa_at_zero (G : ℝ → ℝ) (R₁ R₂ L : ℝ) :
    kappa G 0 R₁ R₂ L = R₁ := kappaOfShape_at_zero (H G) R₁ R₂ L (H_zero G)

lemma kappaOfShape_at_L (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hH1 : H 1 = 1) :
    kappaOfShape H L R₁ R₂ L = R₂ := by simp [kappaOfShape, div_self hL, hH1]

lemma kappa_at_L (G : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hden : HInt_denom G ≠ 0) :
    kappa G L R₁ R₂ L = R₂ := kappaOfShape_at_L (H G) R₁ R₂ L hL (H_one G hden)

-- Helper lemma for the common setup in monotonicity proofs
private lemma kappa_inequality_helper_of_shape
    {H : ℝ → ℝ} (hmono : MonotoneOn H unitInterval) (L : ℝ) (hL : 0 < L)
    (x y : ℝ) (hx : x ∈ Set.Icc 0 L) (hy : y ∈ Set.Icc 0 L) (hxy : x ≤ y) :
    H (x / L) ≤ H (y / L) :=
  hmono (div_mem_unitInterval_of_mem_Icc hL hx) (div_mem_unitInterval_of_mem_Icc hL hy)
    (div_le_div_of_nonneg_right hxy hL.le)

lemma kappaOfShape_monotone_on_Icc
    {H : ℝ → ℝ} (hHmono : MonotoneOn H unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := fun _ hx _ hy hxy =>
  add_le_add_right (mul_le_mul_of_nonneg_left
    (kappa_inequality_helper_of_shape hHmono L hL _ _ hx hy hxy) (sub_nonneg.mpr hmono)) R₁

lemma kappa_monotone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₁ ≤ R₂) :
    MonotoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) :=
  kappaOfShape_monotone_on_Icc (H_monotone_on_unit hG hpos hden) R₁ R₂ L hL hmono

lemma kappaOfShape_antitone_on_Icc
    {H : ℝ → ℝ} (hHmono : MonotoneOn H unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := fun _ hx _ hy hxy =>
  add_le_add_right (mul_le_mul_of_nonpos_left
    (kappa_inequality_helper_of_shape hHmono L hL _ _ hx hy hxy) (sub_nonpos.mpr hmono)) R₁

lemma kappa_antitone_on_Icc
    {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
    (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hden : 0 < HInt_denom G) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappa G s R₁ R₂ L) (Set.Icc 0 L) :=
  kappaOfShape_antitone_on_Icc (H_monotone_on_unit hG hpos hden) R₁ R₂ L hL hmono

section SmoothStepStructure

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

structure SmoothstepCurve where
  H : ℝ → ℝ
  κ : ℝ → ℝ → ℝ → ℝ → ℝ
  H_is_C_inf : ContDiffOn ℝ ∞ H unitInterval
  H_zero : H 0 = 0
  H_one : H 1 = 1
  H_mem_unitInterval :
    ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval
  κ_is_C_inf :
    ∀ R₁ R₂ L (_ : 0 < L),
      ContDiffOn ℝ ∞ (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  κ_at_zero : ∀ R₁ R₂ L, κ 0 R₁ R₂ L = R₁
  κ_at_L : ∀ R₁ R₂ L (_ : L ≠ 0), κ L R₁ R₂ L = R₂
  κ_formula :
    ∀ s R₁ R₂ L, κ s R₁ R₂ L = R₁ + (R₂ - R₁) * H (s / L)
  -- Monotonicity of the shape function on [0,1].
  H_monotone_on_unit : MonotoneOn H unitInterval
  -- κ is monotone when R₁ ≤ R₂ and antitone when R₂ ≤ R₁.
  κ_monotone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₁ ≤ R₂),
      MonotoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  κ_antitone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₂ ≤ R₁),
      AntitoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  -- Flatness at boundaries: all derivatives (n ≥ 1) of H vanish at 0 and 1
  H_deriv_vanishes_at_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 0 = 0
  H_deriv_vanishes_at_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 1 = 0

/-- Constructor that takes an abstract shape function satisfying the four core properties. -/
noncomputable def mkSmoothstepCurveFromShape (H : ℝ → ℝ)
  (hH_smooth : ContDiffOn ℝ ∞ H unitInterval)
  (hH_zero : H 0 = 0) (hH_one : H 1 = 1)
  (hH_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval)
  (hH_mono : MonotoneOn H unitInterval)
  (hH_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 0 = 0)
  (hH_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n H unitInterval 1 = 0) :
  SmoothstepCurve :=
  {
    H := H,
    κ := fun s R₁ R₂ L => kappaOfShape H s R₁ R₂ L,
    H_is_C_inf := hH_smooth,
    H_zero := hH_zero,
    H_one := hH_one,
    H_mem_unitInterval := hH_mem,
    κ_is_C_inf := fun R₁ R₂ L hL => kappaOfShape_contDiffOn hH_smooth R₁ R₂ L hL,
    κ_at_zero := fun R₁ R₂ L => kappaOfShape_at_zero H R₁ R₂ L hH_zero,
    κ_at_L := fun R₁ R₂ L hL => kappaOfShape_at_L H R₁ R₂ L hL hH_one,
    κ_formula := fun _ _ _ _ => rfl,
    H_monotone_on_unit := hH_mono,
    κ_monotone_on_Icc := fun R₁ R₂ L hL hmono => kappaOfShape_monotone_on_Icc hH_mono R₁ R₂ L hL hmono,
    κ_antitone_on_Icc := fun R₁ R₂ L hL hmono => kappaOfShape_antitone_on_Icc hH_mono R₁ R₂ L hL hmono,
    H_deriv_vanishes_at_zero := hH_deriv_zero,
    H_deriv_vanishes_at_one := hH_deriv_one
  }

/-- Constructor from bump function G. Derives H as the normalized primitive of G. -/
noncomputable def mkSmoothstepCurve (G : ℝ → ℝ) (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hG_zero : G 0 = 0) (hG_one : G 1 = 0)
  (hG_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n G unitInterval 0 = 0)
  (hG_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n G unitInterval 1 = 0) : SmoothstepCurve :=
  let hfi : IntervalIntegrable G volume 0 1 :=
    hG.continuousOn.intervalIntegrable_of_Icc (μ := volume) (a := 0) (b := 1) (by norm_num)
  let hden : 0 < HInt_denom G := HInt_denom_pos hfi hpos
  mkSmoothstepCurveFromShape (H G)
    (H_contDiffOn hG)
    (H_zero G)
    (H_one G hden.ne')
    (fun {z} hz => H_mem_unitInterval hG hpos hden hz)
    (H_monotone_on_unit hG hpos hden)
    (H_deriv_vanishes_at_zero_from_G hG hG_zero hG_deriv_zero)
    (H_deriv_vanishes_at_one_from_G hG hG_one hG_deriv_one)

-- Helper lemmas for expNegInvGlue compositions
-- These show that H has vanishing derivatives when G = expNegInvGlue ∘ denom,
-- without requiring denom itself to vanish.

lemma slope_zero_of_left_const {f : ℝ → ℝ} (hf : ∀ x ≤ 0, f x = f 0) :
    (fun x => slope f 0 x) =ᶠ[𝓝[Set.Iio (0 : ℝ)] 0] fun _ => 0 :=
  Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => by
    have hfx : f x = f 0 := hf x (le_of_lt hx)
    simp [slope, hfx]

lemma iteratedDerivWithin_zero_fun_all {s : Set ℝ} {n : ℕ} :
    ∀ x, iteratedDerivWithin n (fun _ => (0 : ℝ)) s x = 0 := by
  intro x
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [iteratedDerivWithin_succ]
    have : iteratedDerivWithin n (fun _ => (0 : ℝ)) s = 0 := funext ih
    rw [this]
    simp

lemma iteratedDeriv_expNegInvGlue_nonpos :
    ∀ (n : ℕ) {x : ℝ}, x ≤ 0 → iteratedDeriv n expNegInvGlue x = 0 := by
  intro n
  induction n with
  | zero => exact expNegInvGlue.zero_of_nonpos
  | succ n hn =>
    intro x hx
    simp only [iteratedDeriv_succ]
    rcases hx.lt_or_eq with hxlt | rfl
    · -- x < 0: deriv is 0 on open set where function is constant
      have heq : Set.EqOn (iteratedDeriv n expNegInvGlue) (fun _ => 0) (Set.Iio 0) :=
        fun _ hy => hn hy.le
      simpa using Set.EqOn.deriv heq isOpen_Iio hxlt
    · -- x = 0: use limit argument
      have hconst := slope_zero_of_left_const fun y hy => (hn hy).trans (hn le_rfl).symm
      have hDiff : HasDerivAt (iteratedDeriv n expNegInvGlue) (deriv (iteratedDeriv n expNegInvGlue) 0) 0 :=
        ((expNegInvGlue.contDiff.of_le (by exact_mod_cast le_top)).differentiable_iteratedDeriv' (m := n) 0).hasDerivAt
      have hNeBot : NeBot (𝓝[Set.Iio 0] (0 : ℝ)) :=
        mem_closure_iff_nhdsWithin_neBot.mp (by simp [closure_Iio])
      exact tendsto_nhds_unique
        (hDiff.tendsto_slope.mono_left (nhdsWithin_mono _ fun _ h => h.ne))
        (tendsto_const_nhds.congr' hconst.symm)

lemma iteratedDeriv_expNegInvGlue_zero (n : ℕ) :
    iteratedDeriv n expNegInvGlue 0 = 0 :=
  iteratedDeriv_expNegInvGlue_nonpos n le_rfl

lemma iteratedDeriv_comp_expNegInvGlue_at
    {denom : ℝ → ℝ} (hdenom : ContDiff ℝ ∞ denom)
    {a : ℝ} (ha : denom a = 0) :
    ∀ n : ℕ, iteratedDeriv n (fun t => expNegInvGlue (denom t)) a = 0 := by
  classical
  intro n
  have hsum := iteratedDeriv_comp_eq_sum_orderedFinpartition (n := (⊤ : ℕ∞)) (i := n)
    (hi := by exact_mod_cast le_top) (g := expNegInvGlue) (f := denom) (x := a)
    (hg := expNegInvGlue.contDiff.contDiffAt) (hf := hdenom.contDiffAt)
  simp only [ha, iteratedDeriv_expNegInvGlue_zero, zero_mul, Finset.sum_const_zero] at hsum
  exact hsum

lemma iteratedDerivWithin_expNegInvGlue_comp_of_mem
    {denom : ℝ → ℝ} (hdenom : ContDiff ℝ ∞ denom)
    {a : ℝ} (ha : denom a = 0) (ha_mem : a ∈ unitInterval) :
    ∀ n : ℕ, iteratedDerivWithin n (fun t => expNegInvGlue (denom t)) unitInterval a = 0 := fun n =>
  (iteratedDerivWithin_eq_iteratedDeriv
    (hs := uniqueDiffOn_Icc_zero_one) (hx := ha_mem)
    (h := ((expNegInvGlue.contDiff.comp hdenom).contDiffAt).of_le (by exact_mod_cast le_top))).trans
    (iteratedDeriv_comp_expNegInvGlue_at hdenom ha n)

lemma H_deriv_vanishes_at_endpoint_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  {a : ℝ} (ha_mem : a ∈ unitInterval) (ha_zero : denom a = 0) :
  ∀ n : ℕ, n ≥ 1 →
      iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval a = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiffOn ℝ ∞ G unitInterval := (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
  intro n hn
  by_cases hden : HInt_denom G = 0
  · have hH : ∀ x, H G x = 0 := fun x => by simp [H, hden]
    rw [iteratedDerivWithin_congr (fun x _ => hH x) ha_mem]
    exact iteratedDerivWithin_zero_fun_all _
  · exact H_deriv_vanishes_at_point_from_G hG ha_mem (by simp [G, ha_zero, expNegInvGlue.zero])
      (fun k _ => iteratedDerivWithin_expNegInvGlue_comp_of_mem hdenom_contDiff ha_zero ha_mem k) n hn

lemma H_deriv_vanishes_at_zero_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_zero : denom 0 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 0 = 0 :=
  H_deriv_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff ⟨le_rfl, by norm_num⟩ hdenom_zero

lemma H_deriv_vanishes_at_one_expNegInvGlue_comp
  {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_one : denom 1 = 0) :
  ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (H (fun t => expNegInvGlue (denom t))) unitInterval 1 = 0 :=
  H_deriv_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff ⟨zero_le_one, le_rfl⟩ hdenom_one

-- Helper to create smoothstep curve from any denominator function
noncomputable def mkSmoothstepCurveFromDenom (denom : ℝ → ℝ) (hdenom_contDiff : ContDiff ℝ ∞ denom)
  (hdenom_pos : ∀ x ∈ Set.Ioo 0 1, 0 < denom x) (hdenom_zero : denom 0 = 0) (hdenom_one : denom 1 = 0) : SmoothstepCurve :=
  mkSmoothstepCurve (fun t => expNegInvGlue (denom t))
    (expNegInvGlue.contDiff.comp hdenom_contDiff).contDiffOn
    (fun x hx => expNegInvGlue.pos_of_pos (hdenom_pos x hx))
    (by simp [hdenom_zero, expNegInvGlue.zero])
    (by simp [hdenom_one, expNegInvGlue.zero])
    (fun n _ => iteratedDerivWithin_expNegInvGlue_comp_of_mem hdenom_contDiff hdenom_zero ⟨le_rfl, by norm_num⟩ n)
    (fun n _ => iteratedDerivWithin_expNegInvGlue_comp_of_mem hdenom_contDiff hdenom_one ⟨zero_le_one, le_rfl⟩ n)

structure DenomParams where
  denom : ℝ → ℝ
  contDiff : ContDiff ℝ ∞ denom
  pos_on_Ioo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < denom x
  zero : denom 0 = 0
  one : denom 1 = 0

noncomputable def curveFrom (p : DenomParams) : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom p.denom p.contDiff p.pos_on_Ioo p.zero p.one

end SmoothStepStructure

end Smooth

end GenericFramework

/-
## Standard Smoothstep Curve

This section keeps the generic “parameterize by `G`” design but instantiates it
with the classical bump
```
G₁ z = expNegInvGlue (z * (1 - z)).
```
On the open interval `(0,1)` this coincides with `exp (-1 / (z (1 - z)))`, so it
is strictly positive there, integrates to a positive finite constant, and every
iterated derivative of `G₁` vanishes at `z = 0` and `z = 1`.  The exported shape
is still the normalized primitive `H G₁`, so downstream applications remain free
to swap in different bumps when tighter high-order derivative bounds are needed.
-/

section CanonicalSmoothstep

open scoped ContDiff Topology
open Smooth MeasureTheory

/-
### Canonical Smoothstep

Relies on `expNegInvGlue` to glue every derivative to zero at the endpoints.
-/

-- Canonical denominator z(1 - z) used in the base bump
def denomCanonical (z : ℝ) : ℝ := z * (1 - z)

lemma denomCanonical_contDiff : ContDiff ℝ ∞ denomCanonical :=
  contDiff_id.mul (contDiff_const.sub contDiff_id)

lemma denomCanonical_pos_on_Ioo (t : ℝ) (ht : t ∈ Set.Ioo 0 1) :
    0 < denomCanonical t := by
  rcases ht with ⟨ht0, ht1⟩
  exact mul_pos ht0 (sub_pos.mpr ht1)

-- Canonical denominator vanishes at both endpoints
lemma denomCanonical_fn_zero : denomCanonical 0 = 0 := by simp [denomCanonical]
lemma denomCanonical_fn_one : denomCanonical 1 = 0 := by simp [denomCanonical]

-- Resulting bump vanishes at both endpoints
lemma G₁_zero : (fun t => expNegInvGlue (denomCanonical t)) 0 = 0 := by
  simp [denomCanonical_fn_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

lemma G₁_one : (fun t => expNegInvGlue (denomCanonical t)) 1 = 0 := by
  simp [denomCanonical_fn_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

noncomputable def curveCanonical : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom denomCanonical denomCanonical_contDiff denomCanonical_pos_on_Ioo denomCanonical_fn_zero denomCanonical_fn_one

end CanonicalSmoothstep

/-
## Parametric Families of Denominators
-/

section ParametricDenominators

open scoped ContDiff Topology
open Smooth MeasureTheory

variable (a : ℝ)

/-
Here we simply rescale the denominator with a single coefficient `a` and pick
```
G₂ z = expNegInvGlue (az(1 - z)),
```
for some positive parameter `a`. Inside `(0,1)` this behaves like
`exp (-1 / (a z (1 - z)))`, while `expNegInvGlue` glues the bump (and every derivative)
to zero at the endpoints. Normalizing the primitive once again gives the shape `H G₂`,
so the public API is unchanged even though this particular bump can yield smaller
jerk/snap bounds in practice.
-/

def denomScaled (z : ℝ) : ℝ := a * z * (1 - z)

lemma denomScaled_contDiff : ContDiff ℝ ∞ (denomScaled a) :=
  (contDiff_const.mul contDiff_id).mul (contDiff_const.sub contDiff_id)

lemma denomScaled_pos_on_Ioo {x : ℝ} (hx : x ∈ Set.Ioo 0 1) (ha : 0 < a) :
    0 < denomScaled a x := by
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have : 0 < a * x * (1 - x) := by
    exact mul_pos (mul_pos ha hx_pos) h1x_pos
  simpa [denomScaled] using this

lemma denomScaled_zero : denomScaled a 0 = 0 := by
  simp [denomScaled]

lemma denomScaled_one : denomScaled a 1 = 0 := by
  simp [denomScaled]

noncomputable def curveScaled (ha : 0 < a) : SmoothstepCurve :=
  mkSmoothstepCurveFromDenom (denomScaled a) (denomScaled_contDiff a)
    (fun {x} hx => denomScaled_pos_on_Ioo (a := a) (x := x) hx ha) (denomScaled_zero a) (denomScaled_one a)

/-
Now we tweak it further by adding asymmetric powers of `p` and `q`
```
G(z) = expNegInvGlue (az^p(1 - z)^q)
```
-/

def denomPow (a : ℝ) (p q : ℕ) (z : ℝ) : ℝ :=
  a * z ^ p * (1 - z) ^ q

lemma denomPow_contDiff (a : ℝ) (p q : ℕ) : ContDiff ℝ ∞ (denomPow a p q) := by
  have hz_pow : ContDiff ℝ ∞ (fun z : ℝ => z ^ p) := by
    simpa using contDiff_id.pow p
  have h1_pow : ContDiff ℝ ∞ (fun z : ℝ => (1 - z) ^ q) := by
    simpa using (contDiff_const.sub contDiff_id).pow q
  have hconst : ContDiff ℝ ∞ (fun _ : ℝ => a) := contDiff_const
  have hprod := (hconst.mul hz_pow).mul h1_pow
  simpa [denomPow] using hprod

lemma denomPow_pos_on_Ioo {a : ℝ} {p q : ℕ} (ha : 0 < a) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPow a p q x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hx_pos : 0 < x := hx0
  have h1x_pos : 0 < 1 - x := sub_pos.mpr hx1
  have hz := pow_pos hx_pos p
  have h1z := pow_pos h1x_pos q
  exact mul_pos (mul_pos ha hz) h1z

lemma denomPow_zero {a : ℝ} {p q : ℕ} (hp : 0 < p) :
    denomPow a p q 0 = 0 := by
  cases p with
  | zero => cases hp
  | succ p' =>
      simp [denomPow]

lemma denomPow_one {a : ℝ} {p q : ℕ} (hq : 0 < q) :
    denomPow a p q 1 = 0 := by
  cases q with
  | zero => cases hq
  | succ q' =>
      simp [denomPow]

def denomPowParams {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) :
    DenomParams where
  denom := denomPow a p q
  contDiff := denomPow_contDiff a p q
  pos_on_Ioo := denomPow_pos_on_Ioo (a := a) (p := p) (q := q) ha
  zero := denomPow_zero (a := a) (p := p) (q := q) hp
  one := denomPow_one (a := a) (p := p) (q := q) hq

noncomputable def curvePow {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q) :
    SmoothstepCurve :=
  curveFrom (denomPowParams (a := a) (p := p) (q := q) ha hp hq)

-- Polynomial bump denominator with an affine skew term
def denomPoly (α β : ℝ) (z : ℝ) : ℝ :=
  (z * (1 - z)) * (α + β * z)

lemma denomPoly_contDiff (α β : ℝ) : ContDiff ℝ ∞ (denomPoly α β) := by
  have h1 : ContDiff ℝ ∞ (fun z : ℝ => z * (1 - z)) := by
    simpa [denomCanonical] using denomCanonical_contDiff
  have h2 : ContDiff ℝ ∞ (fun z : ℝ => α + β * z) :=
    (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hprod :
      ContDiff ℝ ∞ (fun z : ℝ => (z * (1 - z)) * (α + β * z)) :=
    h1.mul h2
  simpa [denomPoly] using hprod

lemma denomPoly_pos_on_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomPoly α β x := by
  intro x hx
  rcases hx with ⟨hx0, hx1⟩
  have hbase : 0 < x * (1 - x) := mul_pos hx0 (sub_pos.mpr hx1)
  have hβx : 0 ≤ β * x := mul_nonneg hβ hx0.le
  have hlin : 0 < α + β * x := by
    have hαle : α ≤ α + β * x := by
      have := add_le_add_left hβx α
      simpa using this
    exact lt_of_lt_of_le hα hαle
  have := mul_pos hbase hlin
  simpa [denomPoly] using this

lemma denomPoly_zero (α β : ℝ) : denomPoly α β 0 = 0 := by
  simp [denomPoly]

lemma denomPoly_one (α β : ℝ) : denomPoly α β 1 = 0 := by
  simp [denomPoly]

def denomPolyParams {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : DenomParams where
  denom := denomPoly α β
  contDiff := denomPoly_contDiff α β
  pos_on_Ioo := denomPoly_pos_on_Ioo hα hβ
  zero := denomPoly_zero α β
  one := denomPoly_one α β

noncomputable def curvePoly {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : SmoothstepCurve :=
  curveFrom (denomPolyParams (α := α) (β := β) hα hβ)

end ParametricDenominators

/-
## Reparametrization
-/

noncomputable
section Reparametrization

open scoped ContDiff
open Smooth

namespace Smooth

lemma iteratedDerivWithin_comp_vanish_of_flat
    {g φ : ℝ → ℝ} (hg : ContDiffOn ℝ ∞ g unitInterval)
    (hφ : ContDiffOn ℝ ∞ φ unitInterval)
    (hmap : Set.MapsTo φ unitInterval unitInterval)
    {a : ℝ} (ha : a ∈ unitInterval)
    (hflat : ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n φ unitInterval a = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDerivWithin n (fun z => g (φ z)) unitInterval a = 0 := by
  intro n hn
  classical
  have hginf : ContDiffWithinAt ℝ (n : ℕ∞) g unitInterval (φ a) :=
    (hg.contDiffWithinAt (hmap ha)).of_le (by exact_mod_cast le_top)
  have hφinf : ContDiffWithinAt ℝ (n : ℕ∞) φ unitInterval a :=
    (hφ.contDiffWithinAt ha).of_le (by exact_mod_cast le_top)
  have hsum := iteratedDerivWithin_comp_eq_sum_orderedFinpartition (i := n)
    (hg := hginf) (hf := hφinf) (ht := uniqueDiffOn_Icc_zero_one) (hs := uniqueDiffOn_Icc_zero_one)
    (hx := ha) (hst := hmap) (hi := le_rfl)
  have hparts (c : OrderedFinpartition n) :
      ∏ j : Fin c.length, iteratedDerivWithin (c.partSize j) φ unitInterval a = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ ⟨0, c.length_pos (Nat.succ_le_iff.mp hn)⟩)
      (hflat _ (Nat.succ_le_of_lt (c.partSize_pos _)))
  simp only [hparts, mul_zero, Finset.sum_const_zero] at hsum
  exact hsum

def reparam (base : SmoothstepCurve) (φ : ℝ → ℝ)
    (hφ_smooth : ContDiffOn ℝ ∞ φ unitInterval)
    (hφ_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → φ z ∈ unitInterval)
    (hφ_zero : φ 0 = 0) (hφ_one : φ 1 = 1)
    (hφ_mono : MonotoneOn φ unitInterval)
    (hφ_flat_zero : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n φ unitInterval 0 = 0)
    (hφ_flat_one : ∀ n : ℕ, 1 ≤ n → iteratedDerivWithin n φ unitInterval 1 = 0) :
    SmoothstepCurve :=
  mkSmoothstepCurveFromShape (fun z => base.H (φ z))
    (base.H_is_C_inf.comp hφ_smooth hφ_mem)
    (by simp [hφ_zero, base.H_zero])
    (by simp [hφ_one, base.H_one])
    (fun {z} hz => base.H_mem_unitInterval (hφ_mem hz))
    (fun _ hx _ hy hxy => base.H_monotone_on_unit (hφ_mem hx) (hφ_mem hy) (hφ_mono hx hy hxy))
    (iteratedDerivWithin_comp_vanish_of_flat base.H_is_C_inf hφ_smooth hφ_mem ⟨le_rfl, by norm_num⟩ hφ_flat_zero)
    (iteratedDerivWithin_comp_vanish_of_flat base.H_is_C_inf hφ_smooth hφ_mem ⟨zero_le_one, le_rfl⟩ hφ_flat_one)

end Smooth

end Reparametrization

/-
## Convex Combinations
-/

section ConvexCombination

open scoped ContDiff
open Smooth

namespace Smooth

def mixShape (w : ℝ) (H₁ H₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun z => w * H₁ z + (1 - w) * H₂ z

lemma mixShape_contDiff (w : ℝ)
    {H₁ H₂ : ℝ → ℝ} (hH₁ : ContDiffOn ℝ ∞ H₁ unitInterval)
    (hH₂ : ContDiffOn ℝ ∞ H₂ unitInterval) :
    ContDiffOn ℝ ∞ (mixShape w H₁ H₂) unitInterval :=
  (hH₁.const_smul w).add (hH₂.const_smul (1 - w))

lemma mixShape_mem_unitInterval {w : ℝ} (hw : w ∈ Set.Icc (0 : ℝ) 1)
    {H₁ H₂ : ℝ → ℝ}
    (hH₁ : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H₁ z ∈ unitInterval)
    (hH₂ : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H₂ z ∈ unitInterval)
    {z : ℝ} (hz : z ∈ unitInterval) :
    mixShape w H₁ H₂ z ∈ unitInterval := by
  obtain ⟨hw0, hw1⟩ := hw
  have h1w := sub_nonneg.mpr hw1
  obtain ⟨h1lo, h1hi⟩ := hH₁ hz
  obtain ⟨h2lo, h2hi⟩ := hH₂ hz
  constructor
  · exact add_nonneg (mul_nonneg hw0 h1lo) (mul_nonneg h1w h2lo)
  · calc mixShape w H₁ H₂ z ≤ w * 1 + (1 - w) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left h1hi hw0) (mul_le_mul_of_nonneg_left h2hi h1w)
    _ = 1 := by ring

lemma mixShape_monotone {w : ℝ} (hw : 0 ≤ w) (hw' : 0 ≤ 1 - w)
    {H₁ H₂ : ℝ → ℝ} (hH₁ : MonotoneOn H₁ unitInterval)
    (hH₂ : MonotoneOn H₂ unitInterval) :
    MonotoneOn (mixShape w H₁ H₂) unitInterval := fun _ hx _ hy hxy =>
  add_le_add (mul_le_mul_of_nonneg_left (hH₁ hx hy hxy) hw)
    (mul_le_mul_of_nonneg_left (hH₂ hx hy hxy) hw')

lemma iteratedDeriv_mixShape_zero
    {c₁ c₂ : SmoothstepCurve} {w : ℝ} {a : ℝ} (ha : a ∈ unitInterval) :
    ∀ n : ℕ, iteratedDerivWithin n
        (mixShape w c₁.H c₂.H) unitInterval a =
      w * iteratedDerivWithin n c₁.H unitInterval a +
        (1 - w) * iteratedDerivWithin n c₂.H unitInterval a := by
  intro n
  classical
  have hcont₁ : ContDiffWithinAt ℝ (n : ℕ∞) c₁.H unitInterval a :=
    (c₁.H_is_C_inf.contDiffWithinAt ha).of_le (by exact_mod_cast le_top)
  have hcont₂ : ContDiffWithinAt ℝ (n : ℕ∞) c₂.H unitInterval a :=
    (c₂.H_is_C_inf.contDiffWithinAt ha).of_le (by exact_mod_cast le_top)
  have hscale₁ := iteratedDerivWithin_const_mul ha uniqueDiffOn_Icc_zero_one w hcont₁
  have hscale₂ := iteratedDerivWithin_const_mul ha uniqueDiffOn_Icc_zero_one (1 - w) hcont₂
  have hadd := iteratedDerivWithin_fun_add (hx := ha) (h := uniqueDiffOn_Icc_zero_one)
    (hcont₁.const_smul w) (hcont₂.const_smul (1 - w))
  simpa [mixShape, hscale₁, hscale₂] using hadd

noncomputable def mixCurve (w : ℝ) (hw : w ∈ Set.Icc (0 : ℝ) 1)
    (c₁ c₂ : SmoothstepCurve) : SmoothstepCurve :=
  mkSmoothstepCurveFromShape (mixShape w c₁.H c₂.H)
    (mixShape_contDiff w c₁.H_is_C_inf c₂.H_is_C_inf)
    (by simp [mixShape, c₁.H_zero, c₂.H_zero])
    (by simp [mixShape, c₁.H_one, c₂.H_one])
    (fun {z} hz => mixShape_mem_unitInterval hw c₁.H_mem_unitInterval c₂.H_mem_unitInterval hz)
    (mixShape_monotone hw.1 (sub_nonneg.mpr hw.2) c₁.H_monotone_on_unit c₂.H_monotone_on_unit)
    (fun n hn => by simp [iteratedDeriv_mixShape_zero (c₁ := c₁) (c₂ := c₂) ⟨le_rfl, by norm_num⟩ n,
      c₁.H_deriv_vanishes_at_zero n hn, c₂.H_deriv_vanishes_at_zero n hn])
    (fun n hn => by simp [iteratedDeriv_mixShape_zero (c₁ := c₁) (c₂ := c₂) ⟨zero_le_one, le_rfl⟩ n,
      c₁.H_deriv_vanishes_at_one n hn, c₂.H_deriv_vanishes_at_one n hn])

end Smooth

end ConvexCombination
