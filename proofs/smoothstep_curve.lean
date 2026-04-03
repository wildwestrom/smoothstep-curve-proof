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

/-- The primitive `z ↦ ∫ t in (0)..z, f t` based at `0`. -/
noncomputable def primitiveFromZero (f : ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ t in (0)..z, f t

-- Helper: convert uIoc integral to intervalIntegral
lemma uIoc_to_intervalIntegral (f : ℝ → ℝ) {z : ℝ} (hz : z ∈ unitInterval) :
  (∫ t in Set.uIoc 0 z, f t) = ∫ t in (0)..z, f t := by
  simpa [Set.uIoc, hz.1] using (intervalIntegral.integral_of_le (μ := volume) (f := f) (a := 0) (b := z) hz.1).symm

-- Global smoothness of the primitive when f is globally C^∞
lemma primitive_is_C_inf_global
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (primitiveFromZero f) := by
  rw [contDiff_infty_iff_deriv]
  constructor
  · intro x
    exact (intervalIntegral.integral_hasDerivAt_right
      (hf.continuous.intervalIntegrable _ _)
      (hf.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hf.continuous.continuousAt).differentiableAt
  · have hderiv : deriv (primitiveFromZero f) = f := by
      ext x
      exact (intervalIntegral.integral_hasDerivAt_right
        (hf.continuous.intervalIntegrable _ _)
        (hf.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
        hf.continuous.continuousAt).deriv
    rw [hderiv]
    exact hf

/-
### Core Definitions
-/

namespace Smooth

/-- Numerator of the normalized primitive `∫₀ᶻ G(t) dt`. -/
noncomputable def HInt (G : ℝ → ℝ) (z : ℝ) : ℝ := ∫ t in Set.uIoc 0 z, G t

/-- Denominator `∫₀¹ G(t) dt` used to normalize `HInt`. -/
noncomputable def HInt_denom (G : ℝ → ℝ) : ℝ := ∫ t in Set.uIoc 0 1, G t

/-- The normalized shape function `H(z) = HInt G z / HInt_denom G`. -/
noncomputable def H (G : ℝ → ℝ) (z : ℝ) : ℝ := HInt G z / HInt_denom G

lemma HInt_zero (G : ℝ → ℝ) : HInt G 0 = 0 := by simp [HInt]

lemma HInt_one (G : ℝ → ℝ) : HInt G 1 = HInt_denom G := by simp [HInt, HInt_denom]

lemma H_zero (G : ℝ → ℝ) : H G 0 = 0 := by simp [H, HInt_zero]

lemma H_one (G : ℝ → ℝ) (hden : HInt_denom G ≠ 0) : H G 1 = 1 := by
  simp [H, HInt_one, hden]

-- Global smoothness of HInt when G is globally C^∞ and vanishes on (-∞, 0]
lemma HInt_contDiff
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish_left : ∀ x, x ≤ 0 → G x = 0) :
    ContDiff ℝ ∞ (HInt G) := by
  -- HInt is 0 on (-∞, 0], smooth on [0, 1], and constant on [1, ∞)
  -- We'll show this by showing it equals a globally smooth function
  have hprim := primitive_is_C_inf_global G hG
  -- On [0, ∞), HInt agrees with primitiveFromZero
  have heq_nonneg : ∀ z, 0 ≤ z → HInt G z = primitiveFromZero G z := fun z hz => by
    simp only [HInt, primitiveFromZero, Set.uIoc_of_le hz, intervalIntegral.integral_of_le hz]
  -- On (-∞, 0], both HInt and primitiveFromZero are 0
  have heq_neg : ∀ z, z ≤ 0 → HInt G z = primitiveFromZero G z := fun z hz => by
    simp only [HInt]
    rw [Set.uIoc_comm, Set.uIoc_of_le hz]
    have h1 : ∫ t in Set.Ioc z 0, G t = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish_left t (ht.2 : t ≤ 0)
    simp only [primitiveFromZero, intervalIntegral.integral_of_ge hz]
    have h2 : ∫ (t : ℝ) in Set.Ioc z 0, G t = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish_left t (ht.2 : t ≤ 0)
    simp [h1]
  have heq : HInt G = primitiveFromZero G := by
    ext z
    rcases le_or_gt z 0 with hz | hz
    · exact heq_neg z hz
    · exact heq_nonneg z hz.le
  rw [heq]
  exact hprim

-- Global smoothness of H when G is globally C^∞ and vanishes on (-∞, 0]
lemma H_contDiff
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish_left : ∀ x, x ≤ 0 → G x = 0) :
    ContDiff ℝ ∞ (H G) :=
  (HInt_contDiff hG hG_vanish_left).div_const _

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

lemma H_eq_ratio {G : ℝ → ℝ} (z : ℝ) :
  H G z = HInt G z / HInt_denom G := rfl

-- When G vanishes on (-∞, 0], HInt is zero for z ≤ 0
lemma HInt_eq_zero_of_nonpos
    {G : ℝ → ℝ} (hG_vanish : ∀ x, x ≤ 0 → G x = 0) {z : ℝ} (hz : z ≤ 0) :
    HInt G z = 0 := by
  simp only [HInt]
  rcases hz.lt_or_eq with hz' | rfl
  · -- z < 0: integral from 0 to z with G = 0 on Ioc z 0
    rw [Set.uIoc_comm, Set.uIoc_of_le hz'.le]
    refine MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => ?_
    exact hG_vanish t (ht.2 : t ≤ 0)
  · simp

-- When G vanishes on [1, ∞), HInt equals HInt_denom for z ≥ 1
lemma HInt_eq_denom_of_one_le
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, 1 ≤ x → G x = 0) {z : ℝ} (hz : 1 ≤ z) :
    HInt G z = HInt_denom G := by
  simp only [HInt, HInt_denom]
  have h01 : (0 : ℝ) ≤ 1 := zero_le_one
  have h0z : (0 : ℝ) ≤ z := zero_le_one.trans hz
  rw [Set.uIoc_of_le h01, Set.uIoc_of_le h0z]
  -- Use integral_add_adjacent_intervals with interval integrals
  have hint01 : IntervalIntegrable G volume 0 1 := hG.continuous.intervalIntegrable 0 1
  have hint1z : IntervalIntegrable G volume 1 z := hG.continuous.intervalIntegrable 1 z
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hint01 hint1z
  rw [intervalIntegral.integral_of_le h01, intervalIntegral.integral_of_le h0z,
      intervalIntegral.integral_of_le hz] at hsplit
  have hzero : ∫ (x : ℝ) in Set.Ioc 1 z, G x = 0 :=
    MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish t ht.1.le
  linarith [hsplit, hzero]

lemma H_eq_zero_of_nonpos
    {G : ℝ → ℝ} (hG_vanish : ∀ x, x ≤ 0 → G x = 0) {z : ℝ} (hz : z ≤ 0) :
    H G z = 0 := by
  simp [H, HInt_eq_zero_of_nonpos hG_vanish hz]

lemma H_eq_one_of_one_le
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, 1 ≤ x → G x = 0)
    (hden : HInt_denom G ≠ 0) {z : ℝ} (hz : 1 ≤ z) :
    H G z = 1 := by
  simp [H, HInt_eq_denom_of_one_le hG hG_vanish hz, hden]

lemma H_monotone_on_unit
  {G : ℝ → ℝ} (hG : ContDiffOn ℝ ∞ G unitInterval)
  (hpos : ∀ x ∈ Set.Ioo 0 1, 0 < G x) (hden : 0 < HInt_denom G) :
  MonotoneOn (H G) unitInterval := fun _ hx _ hy hxy => by
  simp only [H_eq_ratio]
  exact div_le_div_of_nonneg_right (HInt_monotone_on_unit hG hpos hx hy hxy) hden.le

-- Global derivative lemmas (avoiding iteratedDerivWithin)

lemma deriv_HInt_eq_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) :
    deriv (HInt G) x = G x := by
  have hHInt := HInt_contDiff hG hG_vanish
  have hderiv_prim : deriv (primitiveFromZero G) x = G x :=
    (intervalIntegral.integral_hasDerivAt_right
      (hG.continuous.intervalIntegrable _ _)
      (hG.continuous.stronglyMeasurableAtFilter volume (𝓝 x))
      hG.continuous.continuousAt).deriv
  have heq_nonneg : ∀ z, 0 ≤ z → HInt G z = primitiveFromZero G z := fun z hz => by
    simp only [HInt, primitiveFromZero, Set.uIoc_of_le hz, intervalIntegral.integral_of_le hz]
  have heq_neg : ∀ z, z ≤ 0 → HInt G z = primitiveFromZero G z := fun z hz => by
    simp only [HInt, primitiveFromZero]
    rw [Set.uIoc_comm, Set.uIoc_of_le hz, intervalIntegral.integral_of_ge hz]
    have : ∫ (t : ℝ) in Set.Ioc z 0, G t = 0 :=
      MeasureTheory.setIntegral_eq_zero_of_forall_eq_zero fun t ht => hG_vanish t (ht.2 : t ≤ 0)
    simp [this]
  have heq : HInt G = primitiveFromZero G := by
    ext z
    rcases le_or_gt z 0 with hz | hz
    · exact heq_neg z hz
    · exact heq_nonneg z hz.le
  rw [heq, hderiv_prim]

lemma iteratedDeriv_succ_HInt_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (HInt G) x = iteratedDeriv n G x := by
  have hderiv_eq : deriv (HInt G) = G := funext (deriv_HInt_eq_global hG hG_vanish)
  induction n generalizing x with
  | zero => simp [iteratedDeriv_one, hderiv_eq]
  | succ n ih =>
    rw [iteratedDeriv_succ']
    rw [hderiv_eq]

lemma iteratedDeriv_succ_H_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0) (x : ℝ) (n : ℕ) :
    iteratedDeriv (n + 1) (H G) x = (1 / HInt_denom G) * iteratedDeriv n G x := by
  set c := (1 / HInt_denom G)
  have hH_eq : H G = fun z => c * HInt G z := by
    ext z; simp [H, c, div_eq_mul_inv, mul_comm]
  have hHInt := HInt_contDiff hG hG_vanish
  induction n generalizing x with
  | zero =>
    rw [iteratedDeriv_one, hH_eq]
    simp [deriv_HInt_eq_global hG hG_vanish]
  | succ n ih =>
    have hG_diff : Differentiable ℝ (iteratedDeriv n G) :=
      ContDiff.differentiable_iteratedDeriv' n (contDiff_infty.mp hG (n + 1))
    calc iteratedDeriv (n + 1 + 1) (H G) x
        = deriv (iteratedDeriv (n + 1) (H G)) x := by rw [iteratedDeriv_succ]
      _ = deriv (fun y => c * iteratedDeriv n G y) x := by
          congr 1; ext y; rw [ih]
      _ = c * deriv (iteratedDeriv n G) x := deriv_const_mul c hG_diff.differentiableAt
      _ = c * iteratedDeriv (n + 1) G x := by rw [← iteratedDeriv_succ]

lemma H_deriv_vanishes_at_point_global
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hG_vanish : ∀ x, x ≤ 0 → G x = 0)
    {x : ℝ} (hG_x : G x = 0)
    (hG_deriv_x : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n G x = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDeriv n (H G) x = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  simp only [iteratedDeriv_succ_H_global hG hG_vanish]
  rcases k with _ | k <;> simp [hG_x, hG_deriv_x _ (Nat.succ_pos _)]

-- Unit interval derivative lemmas (legacy, for proofs that still need them)

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

/-- Curvature profile induced by a shape function over a transition of length `L`. -/
noncomputable def kappaOfShape (H : ℝ → ℝ) (s R₁ R₂ L : ℝ) : ℝ :=
  R₁ + (R₂ - R₁) * H (s / L)

lemma div_mem_unitInterval_of_mem_Icc {L : ℝ} (hL : 0 < L) {s : ℝ}
    (hs : s ∈ Set.Icc 0 L) : s / L ∈ unitInterval :=
  ⟨div_nonneg hs.1 hL.le, by simpa [div_self hL.ne'] using div_le_div_of_nonneg_right hs.2 hL.le⟩

lemma kappaOfShape_at_zero (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hH0 : H 0 = 0) :
    kappaOfShape H 0 R₁ R₂ L = R₁ := by simp [kappaOfShape, hH0]

lemma kappaOfShape_at_L (H : ℝ → ℝ) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (hH1 : H 1 = 1) :
    kappaOfShape H L R₁ R₂ L = R₂ := by simp [kappaOfShape, div_self hL, hH1]

lemma kappaOfShape_deriv_vanishes_at_zero
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n H 0 = 0)
    (R₁ R₂ L : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => kappaOfShape H s R₁ R₂ L) 0 = 0 := by
  rw [show (fun s => kappaOfShape H s R₁ R₂ L) =
      (fun s => R₁ + (R₂ - R₁) * H ((1 / L) * s)) by
        ext s
        simp [kappaOfShape, div_eq_mul_inv, mul_comm]]
  rw [iteratedDeriv_const_add (Nat.one_le_iff_ne_zero.mp hn).bot_lt]
  rw [iteratedDeriv_const_mul_field]
  have hHn : ContDiff ℝ n H := hH.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [iteratedDeriv_comp_const_mul hHn (1 / L)]
  simp [hflat n hn]

lemma kappaOfShape_deriv_vanishes_at_L
    {H : ℝ → ℝ} (hH : ContDiff ℝ ∞ H)
    (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n H 1 = 0)
    (R₁ R₂ L : ℝ) (hL : L ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => kappaOfShape H s R₁ R₂ L) L = 0 := by
  have hshift :
      iteratedDeriv n (fun t => kappaOfShape H (t + L) R₁ R₂ L) 0 =
        iteratedDeriv n (fun s => kappaOfShape H s R₁ R₂ L) L := by
    simpa using congrArg (fun g => g 0) (iteratedDeriv_comp_add_const n
      (fun s => kappaOfShape H s R₁ R₂ L) L)
  have harg : ∀ t : ℝ, (t + L) / L = (1 / L) * t + 1 := by
    intro t
    field_simp [hL]
  rw [← hshift]
  rw [show (fun t => kappaOfShape H (t + L) R₁ R₂ L) =
      (fun t => R₁ + (R₂ - R₁) * H ((1 / L) * t + 1)) by
        ext t
        simp [kappaOfShape, harg t]]
  rw [iteratedDeriv_const_add (Nat.one_le_iff_ne_zero.mp hn).bot_lt]
  rw [iteratedDeriv_const_mul_field]
  have hshifted : ContDiff ℝ n (fun z => H (z + 1)) :=
    (hH.comp (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have hshift_H : iteratedDeriv n (fun z => H (z + 1)) = fun t => iteratedDeriv n H (t + 1) := by
    simpa using iteratedDeriv_comp_add_const n H 1
  rw [show (fun t => H ((1 / L) * t + 1)) = (fun t => (fun z => H (z + 1)) ((1 / L) * t)) by
        ext t
        simp]
  rw [iteratedDeriv_comp_const_mul hshifted (1 / L)]
  rw [hshift_H]
  simp [hflat n hn]

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

lemma kappaOfShape_antitone_on_Icc
    {H : ℝ → ℝ} (hHmono : MonotoneOn H unitInterval)
    (R₁ R₂ L : ℝ) (hL : 0 < L) (hmono : R₂ ≤ R₁) :
    AntitoneOn (fun s => kappaOfShape H s R₁ R₂ L) (Set.Icc 0 L) := fun _ hx _ hy hxy =>
  add_le_add_right (mul_le_mul_of_nonpos_left
    (kappa_inequality_helper_of_shape hHmono L hL _ _ hx hy hxy) (sub_nonpos.mpr hmono)) R₁

section SmoothStepStructure

/-
### SmoothstepCurve Structure

This structure encapsulates a complete smoothstep curve with all its properties.
-/

/-- A globally smooth monotone shape together with its induced curvature profile. -/
structure SmoothstepCurve where
  /-- The shape function `H : ℝ → ℝ`. -/
  H : ℝ → ℝ
  /-- The induced curvature profile `κ(s, R₁, R₂, L) = R₁ + (R₂ - R₁) * H (s / L)`. -/
  κ : ℝ → ℝ → ℝ → ℝ → ℝ

  ----- Condition 1: Global Smoothness (H ∈ C^∞(ℝ)) -----
  H_is_C_inf : ContDiff ℝ ∞ H

  ----- Condition 2: Boundary values and extension -----
  H_zero : H 0 = 0
  H_one : H 1 = 1
  -- H is 0 for z ≤ 0
  H_eq_zero_of_nonpos : ∀ z, z ≤ 0 → H z = 0
  -- H is 1 for z ≥ 1
  H_eq_one_of_one_le : ∀ z, 1 ≤ z → H z = 1
  -- H maps [0,1] into [0,1] (consequence of monotonicity + boundary values)
  H_mem_unitInterval : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval

  ----- Curvature smoothness and boundary matching -----
  -- κ is globally C^∞
  κ_is_C_inf : ∀ R₁ R₂ L, ContDiff ℝ ∞ (fun s => κ s R₁ R₂ L)
  -- κ(0) = R₁: curvature matches start value at s = 0
  κ_at_zero : ∀ R₁ R₂ L, κ 0 R₁ R₂ L = R₁
  -- κ(L) = R₂: curvature matches end value at s = L
  κ_at_L : ∀ R₁ R₂ L (_ : L ≠ 0), κ L R₁ R₂ L = R₂
  -- The defining formula: κ(s) = R₁ + ΔR · H(s/L) where ΔR = R₂ - R₁
  κ_formula : ∀ s R₁ R₂ L, κ s R₁ R₂ L = R₁ + (R₂ - R₁) * H (s / L)

  ----- Condition 3: Monotonicity (H'(z) ≥ 0 for all z ∈ [0,1]) -----
  -- H is monotonically increasing on [0,1]
  H_monotone_on_unit : MonotoneOn H unitInterval
  -- κ increases when R₁ ≤ R₂ (curvature goes up)
  κ_monotone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₁ ≤ R₂),
      MonotoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)
  -- κ decreases when R₂ ≤ R₁ (curvature goes down)
  κ_antitone_on_Icc :
    ∀ R₁ R₂ L (_ : 0 < L) (_ : R₂ ≤ R₁),
      AntitoneOn (fun s => κ s R₁ R₂ L) (Set.Icc 0 L)

  ----- Condition 4: Flatness at endpoints (H^(n)(0) = H^(n)(1) = 0 for all n ≥ 1) -----
  -- All derivatives vanish at z = 0, ensuring G^∞ continuity at the start join
  H_deriv_vanishes_at_zero : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n H 0 = 0
  -- All derivatives vanish at z = 1, ensuring G^∞ continuity at the end join
  H_deriv_vanishes_at_one : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n H 1 = 0

/-- Constructor that takes an abstract shape function satisfying the four core properties. -/
noncomputable def mkSmoothstepCurveFromShape (H : ℝ → ℝ)
  (hH_smooth : ContDiff ℝ ∞ H)
  (hH_zero : H 0 = 0) (hH_one : H 1 = 1)
  (hH_eq_zero_of_nonpos : ∀ z, z ≤ 0 → H z = 0)
  (hH_eq_one_of_one_le : ∀ z, 1 ≤ z → H z = 1)
  (hH_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → H z ∈ unitInterval)
  (hH_mono : MonotoneOn H unitInterval)
  (hH_deriv_zero : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n H 0 = 0)
  (hH_deriv_one : ∀ n : ℕ, n ≥ 1 → iteratedDeriv n H 1 = 0) :
  SmoothstepCurve :=
  {
    H := H,
    κ := fun s R₁ R₂ L => kappaOfShape H s R₁ R₂ L,
    H_is_C_inf := hH_smooth,
    H_zero := hH_zero,
    H_one := hH_one,
    H_eq_zero_of_nonpos := hH_eq_zero_of_nonpos,
    H_eq_one_of_one_le := hH_eq_one_of_one_le,
    H_mem_unitInterval := hH_mem,
    κ_is_C_inf := fun R₁ R₂ L => by
      simp only [kappaOfShape]
      exact contDiff_const.add (contDiff_const.mul (hH_smooth.comp (contDiff_id.div_const L))),
    κ_at_zero := fun R₁ R₂ L => kappaOfShape_at_zero H R₁ R₂ L hH_zero,
    κ_at_L := fun R₁ R₂ L hL => kappaOfShape_at_L H R₁ R₂ L hL hH_one,
    κ_formula := fun _ _ _ _ => rfl,
    H_monotone_on_unit := hH_mono,
    κ_monotone_on_Icc := fun R₁ R₂ L hL hmono => kappaOfShape_monotone_on_Icc hH_mono R₁ R₂ L hL hmono,
    κ_antitone_on_Icc := fun R₁ R₂ L hL hmono => kappaOfShape_antitone_on_Icc hH_mono R₁ R₂ L hL hmono,
    H_deriv_vanishes_at_zero := hH_deriv_zero,
    H_deriv_vanishes_at_one := hH_deriv_one
  }

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

-- G = expNegInvGlue ∘ denom vanishes when denom ≤ 0
lemma expNegInvGlue_comp_vanish_of_nonpos
    {denom : ℝ → ℝ} (hdenom_nonpos : ∀ x, x ≤ 0 → denom x ≤ 0) :
    ∀ x, x ≤ 0 → expNegInvGlue (denom x) = 0 := fun x hx =>
  expNegInvGlue.zero_of_nonpos (hdenom_nonpos x hx)

lemma expNegInvGlue_comp_vanish_of_one_le
    {denom : ℝ → ℝ} (hdenom_nonpos : ∀ x, 1 ≤ x → denom x ≤ 0) :
    ∀ x, 1 ≤ x → expNegInvGlue (denom x) = 0 := fun x hx =>
  expNegInvGlue.zero_of_nonpos (hdenom_nonpos x hx)

-- Global derivative lemmas using iteratedDeriv instead of iteratedDerivWithin
lemma iteratedDeriv_H_vanishes_at_endpoint_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    {a : ℝ} (ha_zero : denom a = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (H (fun t => expNegInvGlue (denom t))) a = 0 := by
  let G := fun t => expNegInvGlue (denom t)
  have hG : ContDiff ℝ ∞ G := expNegInvGlue.contDiff.comp hdenom_contDiff
  have hG_vanish : ∀ x, x ≤ 0 → G x = 0 := expNegInvGlue_comp_vanish_of_nonpos hdenom_nonpos_left
  exact H_deriv_vanishes_at_point_global hG hG_vanish
    (by simp [G, ha_zero, expNegInvGlue.zero])
    (fun k _ => iteratedDeriv_comp_expNegInvGlue_at hdenom_contDiff ha_zero k)

lemma iteratedDeriv_H_vanishes_at_zero_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    (hdenom_zero : denom 0 = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (H (fun t => expNegInvGlue (denom t))) 0 = 0 :=
  iteratedDeriv_H_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hdenom_nonpos_left hdenom_zero

lemma iteratedDeriv_H_vanishes_at_one_expNegInvGlue_comp
    {denom : ℝ → ℝ} (hdenom_contDiff : ContDiff ℝ ∞ denom)
    (hdenom_nonpos_left : ∀ x, x ≤ 0 → denom x ≤ 0)
    (hdenom_one : denom 1 = 0) :
    ∀ n : ℕ, n ≥ 1 → iteratedDeriv n (H (fun t => expNegInvGlue (denom t))) 1 = 0 :=
  iteratedDeriv_H_vanishes_at_endpoint_expNegInvGlue_comp hdenom_contDiff hdenom_nonpos_left hdenom_one

/-- Parameters describing a denominator suitable for the `expNegInvGlue ∘ denom` construction. -/
structure DenomParams where
  /-- The denominator function used inside `expNegInvGlue`. -/
  denom : ℝ → ℝ
  contDiff : ContDiff ℝ ∞ denom
  pos_on_Ioo : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < denom x
  zero : denom 0 = 0
  one : denom 1 = 0
  nonpos_of_nonpos : ∀ x, x ≤ 0 → denom x ≤ 0
  nonpos_of_one_le : ∀ x, 1 ≤ x → denom x ≤ 0

/-- Build a `SmoothstepCurve` from denominator-side hypotheses. -/
noncomputable def curveFrom (p : DenomParams) : SmoothstepCurve :=
  let G := fun t => expNegInvGlue (p.denom t)
  let hG : ContDiff ℝ ∞ G := expNegInvGlue.contDiff.comp p.contDiff
  let hG_vanish_left : ∀ x, x ≤ 0 → G x = 0 := expNegInvGlue_comp_vanish_of_nonpos p.nonpos_of_nonpos
  let hG_vanish_right : ∀ x, 1 ≤ x → G x = 0 := expNegInvGlue_comp_vanish_of_one_le p.nonpos_of_one_le
  let hfi : IntervalIntegrable G volume 0 1 := hG.continuous.intervalIntegrable 0 1
  let hden : 0 < HInt_denom G := HInt_denom_pos hfi (fun x hx => expNegInvGlue.pos_of_pos (p.pos_on_Ioo x hx))
  mkSmoothstepCurveFromShape (H G)
    (H_contDiff hG hG_vanish_left)
    (H_zero G)
    (H_one G hden.ne')
    (fun _z hz => H_eq_zero_of_nonpos hG_vanish_left hz)
    (fun _z hz => H_eq_one_of_one_le hG hG_vanish_right hden.ne' hz)
    (fun {_z} hz => H_mem_unitInterval hG.contDiffOn (fun x hx => expNegInvGlue.pos_of_pos (p.pos_on_Ioo x hx)) hden hz)
    (H_monotone_on_unit hG.contDiffOn (fun x hx => expNegInvGlue.pos_of_pos (p.pos_on_Ioo x hx)) hden)
    (iteratedDeriv_H_vanishes_at_zero_expNegInvGlue_comp p.contDiff p.nonpos_of_nonpos p.zero)
    (iteratedDeriv_H_vanishes_at_one_expNegInvGlue_comp p.contDiff p.nonpos_of_nonpos p.one)

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

/-- The canonical denominator `z * (1 - z)`. -/
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

-- Canonical denominator is nonpositive outside (0,1)
lemma denomCanonical_nonpos_of_nonpos : ∀ x, x ≤ 0 → denomCanonical x ≤ 0 := fun x hx => by
  simp only [denomCanonical]
  exact mul_nonpos_of_nonpos_of_nonneg hx (by linarith : 0 ≤ 1 - x)

lemma denomCanonical_nonpos_of_one_le : ∀ x, 1 ≤ x → denomCanonical x ≤ 0 := fun x hx => by
  simp only [denomCanonical]
  exact mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x) (by linarith : 1 - x ≤ 0)

-- Resulting bump vanishes at both endpoints
lemma G₁_zero : (fun t => expNegInvGlue (denomCanonical t)) 0 = 0 := by
  simp [denomCanonical_fn_zero, expNegInvGlue.zero_of_nonpos (le_refl 0)]

lemma G₁_one : (fun t => expNegInvGlue (denomCanonical t)) 1 = 0 := by
  simp [denomCanonical_fn_one, expNegInvGlue.zero_of_nonpos (le_refl 0)]

/-- Denominator parameters for the canonical smoothstep family. -/
def denomCanonicalParams : Smooth.DenomParams where
  denom := denomCanonical
  contDiff := denomCanonical_contDiff
  pos_on_Ioo := denomCanonical_pos_on_Ioo
  zero := denomCanonical_fn_zero
  one := denomCanonical_fn_one
  nonpos_of_nonpos := denomCanonical_nonpos_of_nonpos
  nonpos_of_one_le := denomCanonical_nonpos_of_one_le

/-- The canonical smoothstep curve built from `denomCanonical`. -/
noncomputable def curveCanonical : SmoothstepCurve :=
  Smooth.curveFrom denomCanonicalParams

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

/-- A one-parameter scaling of the canonical denominator. -/
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

lemma denomScaled_nonpos_of_nonpos (ha : 0 < a) : ∀ x, x ≤ 0 → denomScaled a x ≤ 0 := fun x hx => by
  simp only [denomScaled]
  have h1 : a * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha.le hx
  exact mul_nonpos_of_nonpos_of_nonneg h1 (by linarith : 0 ≤ 1 - x)

lemma denomScaled_nonpos_of_one_le (ha : 0 < a) : ∀ x, 1 ≤ x → denomScaled a x ≤ 0 := fun x hx => by
  simp only [denomScaled]
  have h1 : 0 ≤ a * x := mul_nonneg ha.le (by linarith : 0 ≤ x)
  exact mul_nonpos_of_nonneg_of_nonpos h1 (by linarith : 1 - x ≤ 0)

/-- Denominator parameters for the scaled family. -/
def denomScaledParams (ha : 0 < a) : DenomParams where
  denom := denomScaled a
  contDiff := denomScaled_contDiff a
  pos_on_Ioo := fun {_} hx => denomScaled_pos_on_Ioo (a := a) hx ha
  zero := denomScaled_zero a
  one := denomScaled_one a
  nonpos_of_nonpos := denomScaled_nonpos_of_nonpos a ha
  nonpos_of_one_le := denomScaled_nonpos_of_one_le a ha

/-- The smoothstep curve induced by `denomScaled`. -/
noncomputable def curveScaled (ha : 0 < a) : SmoothstepCurve :=
  curveFrom (denomScaledParams a ha)

/-
Now we tweak it further by adding asymmetric powers of `p` and `q`
```
G(z) = expNegInvGlue (az^p(1 - z)^q)
```
-/

/-- A power-weighted denominator `a * z^p * (1 - z)^q`. -/
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

-- For nonpos_of_nonpos: z^p ≤ 0 when z ≤ 0 requires p odd
-- For nonpos_of_one_le: (1-z)^q ≤ 0 when z ≥ 1 requires q odd
lemma denomPow_nonpos_of_nonpos {a : ℝ} (ha : 0 < a) (p q : ℕ) (hp_odd : Odd p) :
    ∀ x, x ≤ 0 → denomPow a p q x ≤ 0 := by
  intro x hx
  simp only [denomPow]
  have hz_pow : x ^ p ≤ 0 := Odd.pow_nonpos hp_odd hx
  have h1z_pow : (0 : ℝ) < (1 - x) ^ q := pow_pos (by linarith : 0 < 1 - x) q
  have := mul_nonpos_of_nonneg_of_nonpos (mul_pos ha h1z_pow).le hz_pow
  linarith [this]

lemma denomPow_nonpos_of_one_le {a : ℝ} (ha : 0 < a) (p q : ℕ) (hq_odd : Odd q) :
    ∀ x, 1 ≤ x → denomPow a p q x ≤ 0 := by
  intro x hx
  simp only [denomPow]
  have hz_pow : (0 : ℝ) < x ^ p := pow_pos (by linarith : 0 < x) p
  have h1z_pow : (1 - x) ^ q ≤ 0 := Odd.pow_nonpos hq_odd (by linarith : 1 - x ≤ 0)
  have := mul_nonpos_of_nonneg_of_nonpos (mul_pos ha hz_pow).le h1z_pow
  linarith [this]

/-- Denominator parameters for the odd-power family. -/
def denomPowParams {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hp_odd : Odd p) (hq_odd : Odd q) :
    DenomParams where
  denom := denomPow a p q
  contDiff := denomPow_contDiff a p q
  pos_on_Ioo := denomPow_pos_on_Ioo (a := a) (p := p) (q := q) ha
  zero := denomPow_zero (a := a) (p := p) (q := q) hp
  one := denomPow_one (a := a) (p := p) (q := q) hq
  nonpos_of_nonpos := denomPow_nonpos_of_nonpos ha p q hp_odd
  nonpos_of_one_le := denomPow_nonpos_of_one_le ha p q hq_odd

/-- The smoothstep curve induced by `denomPow`. -/
noncomputable def curvePow {a : ℝ} {p q : ℕ} (ha : 0 < a) (hp : 0 < p) (hq : 0 < q)
    (hp_odd : Odd p) (hq_odd : Odd q) :
    SmoothstepCurve :=
  curveFrom (denomPowParams (a := a) (p := p) (q := q) ha hp hq hp_odd hq_odd)

/-
Polynomial bump denominator with an affine skew term
-/

/-- A cubic denominator with an affine skew factor. -/
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

-- For global smoothness, we need denomPoly nonpositive outside (0,1).
-- This requires β = 0 (otherwise for large negative z, the sign is wrong).
-- When β = 0: denomPoly α 0 z = α * z(1-z), same as denomScaled α.
lemma denomPoly_nonpos_of_nonpos {α : ℝ} (hα : 0 < α) :
    ∀ x, x ≤ 0 → denomPoly α 0 x ≤ 0 := by
  intro x hx
  simp only [denomPoly]
  have h1 : x * (1 - x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx (by linarith : 0 ≤ 1 - x)
  have h2 : 0 ≤ α + 0 * x := by simp [hα.le]
  exact mul_nonpos_of_nonpos_of_nonneg h1 h2

lemma denomPoly_nonpos_of_one_le {α : ℝ} (hα : 0 < α) :
    ∀ x, 1 ≤ x → denomPoly α 0 x ≤ 0 := by
  intro x hx
  simp only [denomPoly]
  have h1 : x * (1 - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ x) (by linarith : 1 - x ≤ 0)
  have h2 : 0 ≤ α + 0 * x := by simp [hα.le]
  exact mul_nonpos_of_nonpos_of_nonneg h1 h2

lemma denomPoly_pos_left_witness {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∃ x, x ≤ 0 ∧ 0 < denomPoly α β x := by
  refine ⟨-(α / β) - 1, ?_, ?_⟩
  · have : -(α / β) < 0 := by
      have hdiv : 0 < α / β := div_pos hα hβ
      linarith
    linarith
  · have hx : -(α / β) - 1 < 0 := by
      have : -(α / β) < 0 := by
        have hdiv : 0 < α / β := div_pos hα hβ
        linarith
      linarith
    have hbase : (-(α / β) - 1) * (1 - (-(α / β) - 1)) < 0 := by
      have h1 : 0 < 1 - (-(α / β) - 1) := by linarith
      exact mul_neg_of_neg_of_pos hx h1
    have hlin : α + β * (-(α / β) - 1) < 0 := by
      have hcalc : α + β * (-(α / β) - 1) = -β := by
        field_simp [hβ.ne']
        linarith
      rw [hcalc]
      linarith
    have : 0 < (-(α / β) - 1) * (1 - (-(α / β) - 1)) * (α + β * (-(α / β) - 1)) :=
      mul_pos_of_neg_of_neg hbase hlin
    simpa [denomPoly] using this

lemma denomPoly_pos_right_witness {α β : ℝ} (hα : 0 < α) (hβ : β < 0) :
    ∃ x, 1 ≤ x ∧ 0 < denomPoly α β x := by
  refine ⟨α / (-β) + 1, ?_, ?_⟩
  · have : 0 ≤ α / (-β) := div_nonneg hα.le (neg_nonneg.mpr hβ.le)
    linarith
  · have hx : 1 < α / (-β) + 1 := by
      have : 0 < α / (-β) := div_pos hα (neg_pos.mpr hβ)
      linarith
    have hbase : (α / (-β) + 1) * (1 - (α / (-β) + 1)) < 0 := by
      have hxpos : 0 < α / (-β) + 1 := by linarith
      have h1 : 1 - (α / (-β) + 1) < 0 := by linarith
      exact mul_neg_of_pos_of_neg hxpos h1
    have hlin : α + β * (α / (-β) + 1) < 0 := by
      have hdiv : α / (-β) = -(α / β) := by
        field_simp [hβ.ne']
      rw [hdiv]
      have hcancel : β * (α / β) = α := by
        field_simp [hβ.ne']
        rw [div_self (ne_of_lt hβ)]
      have hcalc : β * (-(α / β)) = -α := by
        nlinarith
      nlinarith [hcalc, hβ]
    have : 0 < (α / (-β) + 1) * (1 - (α / (-β) + 1)) * (α + β * (α / (-β) + 1)) :=
      mul_pos_of_neg_of_neg hbase hlin
    simpa [denomPoly] using this

lemma denomPoly_beta_eq_zero_of_global_nonpos {α β : ℝ} (hα : 0 < α)
    (hleft : ∀ x, x ≤ 0 → denomPoly α β x ≤ 0)
    (hright : ∀ x, 1 ≤ x → denomPoly α β x ≤ 0) :
    β = 0 := by
  by_contra hβ
  rcases lt_or_gt_of_ne hβ with hβ_neg | hβ_pos
  · rcases denomPoly_pos_right_witness hα hβ_neg with ⟨x, hx, hx_pos⟩
    exact (not_lt_of_ge (hright x hx)) hx_pos
  · rcases denomPoly_pos_left_witness hα hβ_pos with ⟨x, hx, hx_pos⟩
    exact (not_lt_of_ge (hleft x hx)) hx_pos

/-- Denominator parameters for the globally valid `β = 0` polynomial family. -/
def denomPolyParams {α : ℝ} (hα : 0 < α) : DenomParams where
  denom := denomPoly α 0
  contDiff := denomPoly_contDiff α 0
  pos_on_Ioo := denomPoly_pos_on_Ioo hα le_rfl
  zero := denomPoly_zero α 0
  one := denomPoly_one α 0
  nonpos_of_nonpos := denomPoly_nonpos_of_nonpos hα
  nonpos_of_one_le := denomPoly_nonpos_of_one_le hα

/-- The globally valid polynomial family, necessarily using `β = 0`. -/
noncomputable def curvePoly {α : ℝ} (hα : 0 < α) : SmoothstepCurve :=
  curveFrom (denomPolyParams (α := α) hα)

end ParametricDenominators

section AsymmetricDenominators

open scoped ContDiff Topology
open Smooth MeasureTheory

/-- A globally valid asymmetric denominator obtained by modulating `denomCanonical`
with the canonical shape function. -/
noncomputable def denomSkewed (α β : ℝ) (z : ℝ) : ℝ :=
  denomCanonical z * (α + β * curveCanonical.H z)

lemma denomSkewed_contDiff (α β : ℝ) : ContDiff ℝ ∞ (denomSkewed α β) := by
  refine denomCanonical_contDiff.mul ?_
  exact contDiff_const.add (contDiff_const.mul curveCanonical.H_is_C_inf)

lemma denomSkewed_pos_on_Ioo {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ ⦃x : ℝ⦄, x ∈ Set.Ioo (0 : ℝ) 1 → 0 < denomSkewed α β x := by
  intro x hx
  have hbase : 0 < denomCanonical x := denomCanonical_pos_on_Ioo x hx
  have hxH : curveCanonical.H x ∈ unitInterval := curveCanonical.H_mem_unitInterval ⟨hx.1.le, hx.2.le⟩
  have hβH : 0 ≤ β * curveCanonical.H x := mul_nonneg hβ hxH.1
  have hlin : 0 < α + β * curveCanonical.H x := by
    have hαle : α ≤ α + β * curveCanonical.H x := by
      have := add_le_add_left hβH α
      simpa using this
    exact lt_of_lt_of_le hα hαle
  exact mul_pos hbase hlin

lemma denomSkewed_zero (α β : ℝ) : denomSkewed α β 0 = 0 := by
  simp [denomSkewed, denomCanonical]

lemma denomSkewed_one (α β : ℝ) : denomSkewed α β 1 = 0 := by
  simp [denomSkewed, denomCanonical]

lemma denomSkewed_nonpos_of_nonpos {α β : ℝ} (hα : 0 < α) :
    ∀ x, x ≤ 0 → denomSkewed α β x ≤ 0 := by
  intro x hx
  rw [denomSkewed]
  have hbase : denomCanonical x ≤ 0 := denomCanonical_nonpos_of_nonpos x hx
  have hlin : 0 ≤ α + β * curveCanonical.H x := by
    rw [curveCanonical.H_eq_zero_of_nonpos x hx]
    simpa using hα.le
  exact mul_nonpos_of_nonpos_of_nonneg hbase hlin

lemma denomSkewed_nonpos_of_one_le {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) :
    ∀ x, 1 ≤ x → denomSkewed α β x ≤ 0 := by
  intro x hx
  rw [denomSkewed]
  have hbase : denomCanonical x ≤ 0 := denomCanonical_nonpos_of_one_le x hx
  have hlin : 0 ≤ α + β * curveCanonical.H x := by
    rw [curveCanonical.H_eq_one_of_one_le x hx]
    linarith
  exact mul_nonpos_of_nonpos_of_nonneg hbase hlin

/-- Denominator parameters for the asymmetric smoothstep family. -/
noncomputable def denomSkewedParams {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : DenomParams where
  denom := denomSkewed α β
  contDiff := denomSkewed_contDiff α β
  pos_on_Ioo := denomSkewed_pos_on_Ioo hα hβ
  zero := denomSkewed_zero α β
  one := denomSkewed_one α β
  nonpos_of_nonpos := denomSkewed_nonpos_of_nonpos hα
  nonpos_of_one_le := denomSkewed_nonpos_of_one_le hα hβ

/-- A globally smooth asymmetric family built from `denomSkewed`. -/
noncomputable def curveSkewed {α β : ℝ} (hα : 0 < α) (hβ : 0 ≤ β) : SmoothstepCurve :=
  curveFrom (denomSkewedParams (α := α) (β := β) hα hβ)

end AsymmetricDenominators

section ClosureProperties

open scoped ContDiff Topology
open Smooth

namespace Smooth

lemma SmoothstepCurve.kappa_deriv_vanishes_at_zero
    (sc : SmoothstepCurve) (R₁ R₂ L : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => sc.κ s R₁ R₂ L) 0 = 0 := by
  simpa [sc.κ_formula] using
    (kappaOfShape_deriv_vanishes_at_zero sc.H_is_C_inf sc.H_deriv_vanishes_at_zero R₁ R₂ L n hn)

lemma SmoothstepCurve.kappa_deriv_vanishes_at_L
    (sc : SmoothstepCurve) (R₁ R₂ L : ℝ) (hL : L ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (fun s => sc.κ s R₁ R₂ L) L = 0 := by
  simpa [sc.κ_formula] using
    (kappaOfShape_deriv_vanishes_at_L sc.H_is_C_inf sc.H_deriv_vanishes_at_one R₁ R₂ L hL n hn)

lemma SmoothstepCurve.kappa_eq_start_of_nonpos
    (sc : SmoothstepCurve) (R₁ R₂ L s : ℝ) (hL : 0 < L) (hs : s ≤ 0) :
    sc.κ s R₁ R₂ L = R₁ := by
  rw [sc.κ_formula]
  have hs_div : s / L ≤ 0 := div_nonpos_of_nonpos_of_nonneg hs hL.le
  simp [sc.H_eq_zero_of_nonpos _ hs_div]

lemma SmoothstepCurve.kappa_eq_end_of_ge_L
    (sc : SmoothstepCurve) (R₁ R₂ L s : ℝ) (hL : 0 < L) (hs : L ≤ s) :
    sc.κ s R₁ R₂ L = R₂ := by
  rw [sc.κ_formula]
  have hs_div : 1 ≤ s / L := by
    simpa [div_self hL.ne'] using div_le_div_of_nonneg_right hs hL.le
  simp [sc.H_eq_one_of_one_le _ hs_div]

lemma iteratedDeriv_comp_vanish_of_flat
    {g φ : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hφ : ContDiff ℝ ∞ φ)
    {a : ℝ} (hflat : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ a = 0) :
    ∀ n : ℕ, 1 ≤ n → iteratedDeriv n (fun z => g (φ z)) a = 0 := by
  intro n hn
  have hsum := iteratedDeriv_comp_eq_sum_orderedFinpartition (n := (⊤ : ℕ∞)) (i := n)
    (hi := by exact_mod_cast le_top) (g := g) (f := φ) (x := a)
    (hg := hg.contDiffAt) (hf := hφ.contDiffAt)
  have hparts :
      ∀ c : OrderedFinpartition n,
        ∏ j : Fin c.length, iteratedDeriv (c.partSize j) φ a = 0 := by
    intro c
    have hlen : 0 < c.length := c.length_pos (Nat.one_le_iff_ne_zero.mp hn).bot_lt
    have hprod :
        ((Finset.univ : Finset (Fin c.length)).prod fun j =>
            iteratedDeriv (c.partSize j) φ a : ℝ) = 0 := by
      refine Finset.prod_eq_zero
        (s := (Finset.univ : Finset (Fin c.length)))
        (f := fun j => iteratedDeriv (c.partSize j) φ a)
        (i := ⟨0, hlen⟩) ?_ ?_
      · simp
      · exact hflat _ (Nat.succ_le_of_lt (c.partSize_pos ⟨0, hlen⟩))
    simpa using hprod
  have hsum_zero :
      ∑ c : OrderedFinpartition n,
        iteratedDeriv c.length g (φ a) * ∏ j : Fin c.length, iteratedDeriv (c.partSize j) φ a = 0 := by
    refine Finset.sum_eq_zero ?_
    intro c _
    simp [hparts c]
  simpa using hsum.trans hsum_zero

/-- Convex combination of two shape functions. -/
def mixShape (t : ℝ) (H₁ H₂ : ℝ → ℝ) : ℝ → ℝ :=
  fun z => t * H₁ z + (1 - t) * H₂ z

lemma iteratedDeriv_mixShape
    {H₁ H₂ : ℝ → ℝ} (hH₁ : ContDiff ℝ ∞ H₁) (hH₂ : ContDiff ℝ ∞ H₂)
    (t x : ℝ) (n : ℕ) :
    iteratedDeriv n (mixShape t H₁ H₂) x =
      t * iteratedDeriv n H₁ x + (1 - t) * iteratedDeriv n H₂ x := by
  have h₁ : ContDiffAt ℝ n (fun z => t * H₁ z) x :=
    (contDiff_const.mul hH₁).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have h₂ : ContDiffAt ℝ n (fun z => (1 - t) * H₂ z) x :=
    (contDiff_const.mul hH₂).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [show mixShape t H₁ H₂ = (fun z => t * H₁ z) + (fun z => (1 - t) * H₂ z) by rfl]
  rw [iteratedDeriv_add h₁ h₂, iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]

/-- Reparametrize a smoothstep curve by a globally smooth map with the same flat endpoints. -/
noncomputable def reparam (base : SmoothstepCurve) (φ : ℝ → ℝ)
    (hφ_smooth : ContDiff ℝ ∞ φ)
    (hφ_zero_of_nonpos : ∀ z, z ≤ 0 → φ z = 0)
    (hφ_one_of_one_le : ∀ z, 1 ≤ z → φ z = 1)
    (hφ_mem : ∀ ⦃z : ℝ⦄, z ∈ unitInterval → φ z ∈ unitInterval)
    (hφ_mono : MonotoneOn φ unitInterval)
    (hφ_flat_zero : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ 0 = 0)
    (hφ_flat_one : ∀ n : ℕ, 1 ≤ n → iteratedDeriv n φ 1 = 0) :
    SmoothstepCurve :=
  mkSmoothstepCurveFromShape
    (fun z => base.H (φ z))
    (base.H_is_C_inf.comp hφ_smooth)
    (by simp [hφ_zero_of_nonpos 0 le_rfl, base.H_zero])
    (by simp [hφ_one_of_one_le 1 le_rfl, base.H_one])
    (fun z hz => by simpa [hφ_zero_of_nonpos z hz] using base.H_zero)
    (fun z hz => by simpa [hφ_one_of_one_le z hz] using base.H_one)
    (fun {_} hz => base.H_mem_unitInterval (hφ_mem hz))
    (fun _ hx _ hy hxy => base.H_monotone_on_unit (hφ_mem hx) (hφ_mem hy) (hφ_mono hx hy hxy))
    (fun n hn => by
      simpa using iteratedDeriv_comp_vanish_of_flat base.H_is_C_inf hφ_smooth hφ_flat_zero n hn)
    (fun n hn => by
      simpa using iteratedDeriv_comp_vanish_of_flat base.H_is_C_inf hφ_smooth hφ_flat_one n hn)

/-- Convexly mix two smoothstep curves. -/
noncomputable def mixCurve (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (c₁ c₂ : SmoothstepCurve) : SmoothstepCurve :=
  mkSmoothstepCurveFromShape
    (mixShape t c₁.H c₂.H)
    ((contDiff_const.mul c₁.H_is_C_inf).add (contDiff_const.mul c₂.H_is_C_inf))
    (by simp [mixShape, c₁.H_zero, c₂.H_zero])
    (by simp [mixShape, c₁.H_one, c₂.H_one, sub_eq_add_neg])
    (fun z hz => by simp [mixShape, c₁.H_eq_zero_of_nonpos z hz, c₂.H_eq_zero_of_nonpos z hz])
    (fun z hz => by simp [mixShape, c₁.H_eq_one_of_one_le z hz, c₂.H_eq_one_of_one_le z hz, sub_eq_add_neg])
    (fun {z} hz => by
      rcases c₁.H_mem_unitInterval hz with ⟨h₁lo, h₁hi⟩
      rcases c₂.H_mem_unitInterval hz with ⟨h₂lo, h₂hi⟩
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      constructor
      · exact add_nonneg (mul_nonneg ht0 h₁lo) (mul_nonneg ht1 h₂lo)
      · have hmix :
          t * c₁.H z + (1 - t) * c₂.H z ≤ t * (1 : ℝ) + (1 - t) * (1 : ℝ) := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left h₁hi ht0)
            (mul_le_mul_of_nonneg_left h₂hi ht1)
        simpa using hmix.trans_eq (by ring))
    (fun _ hx _ hy hxy => by
      have h₁ := c₁.H_monotone_on_unit hx hy hxy
      have h₂ := c₂.H_monotone_on_unit hx hy hxy
      have ht0 : 0 ≤ t := ht.1
      have ht1 : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
      exact add_le_add
        (mul_le_mul_of_nonneg_left h₁ ht0)
        (mul_le_mul_of_nonneg_left h₂ ht1))
    (fun n hn => by
      rw [iteratedDeriv_mixShape c₁.H_is_C_inf c₂.H_is_C_inf t 0 n]
      simp [c₁.H_deriv_vanishes_at_zero n hn, c₂.H_deriv_vanishes_at_zero n hn])
    (fun n hn => by
      rw [iteratedDeriv_mixShape c₁.H_is_C_inf c₂.H_is_C_inf t 1 n]
      simp [c₁.H_deriv_vanishes_at_one n hn, c₂.H_deriv_vanishes_at_one n hn])

/-- Concatenate two curvature transitions with a shared middle curvature `R₁`. -/
noncomputable def concat (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) : ℝ → ℝ :=
  fun s => sc₁.κ s R₀ R₁ L₁ + sc₂.κ (s - L₁) R₁ R₂ L₂ - R₁

lemma concat_contDiff (sc₁ sc₂ : SmoothstepCurve) (R₀ R₁ R₂ L₁ L₂ : ℝ) :
    ContDiff ℝ ∞ (concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂) := by
  unfold concat
  have hshift : ContDiff ℝ ∞ (fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) := by
    simpa [sub_eq_add_neg] using
      (sc₂.κ_is_C_inf R₁ R₂ L₂).comp (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => -L₁))
  have hsum :=
    (sc₁.κ_is_C_inf R₀ R₁ L₁).add hshift
  exact hsum.sub contDiff_const

lemma concat_eq_first_of_le_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ s : ℝ) (hL₂ : 0 < L₂) (hs : s ≤ L₁) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ s = sc₁.κ s R₀ R₁ L₁ := by
  unfold concat
  rw [sc₂.kappa_eq_start_of_nonpos R₁ R₂ L₂ (s - L₁) hL₂ (by linarith)]
  ring

lemma concat_eq_shifted_second_of_join_le (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ s : ℝ) (hL₁ : 0 < L₁) (hs : L₁ ≤ s) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ s = sc₂.κ (s - L₁) R₁ R₂ L₂ := by
  unfold concat
  rw [sc₁.kappa_eq_end_of_ge_L R₀ R₁ L₁ s hL₁ hs]
  ring

lemma concat_at_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) (hL₁ : L₁ ≠ 0) :
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ L₁ = R₁ := by
  calc
    concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ L₁
        = sc₁.κ L₁ R₀ R₁ L₁ + sc₂.κ 0 R₁ R₂ L₂ - R₁ := by
            simp [concat]
    _ = R₁ := by
      rw [sc₁.κ_at_L R₀ R₁ L₁ hL₁, sc₂.κ_at_zero R₁ R₂ L₂]
      ring

lemma concat_deriv_vanishes_at_join (sc₁ sc₂ : SmoothstepCurve)
    (R₀ R₁ R₂ L₁ L₂ : ℝ) (hL₁ : L₁ ≠ 0) (n : ℕ) (hn : 1 ≤ n) :
    iteratedDeriv n (concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂) L₁ = 0 := by
  have h₁ : ContDiffAt ℝ n (fun s => sc₁.κ s R₀ R₁ L₁) L₁ :=
    (sc₁.κ_is_C_inf R₀ R₁ L₁).contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞)))
  have h₂ : ContDiffAt ℝ n (fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) L₁ :=
    (by
      have hshift : ContDiff ℝ ∞ (fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) := by
        simpa [sub_eq_add_neg] using
          (sc₂.κ_is_C_inf R₁ R₂ L₂).comp (contDiff_id.add (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => -L₁))
      exact hshift.contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞))))
  have hsum : ContDiffAt ℝ n ((fun s => sc₁.κ s R₀ R₁ L₁) + fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) L₁ :=
    h₁.add h₂
  have hconst : ContDiffAt ℝ n (fun _ : ℝ => R₁) L₁ :=
    (contDiff_const : ContDiff ℝ ∞ fun _ : ℝ => R₁).contDiffAt.of_le
      (by exact_mod_cast le_top (a := (n : ℕ∞)))
  rw [show concat sc₁ sc₂ R₀ R₁ R₂ L₁ L₂ =
      ((fun s => sc₁.κ s R₀ R₁ L₁) + fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) - fun _ => R₁ by
        rfl]
  rw [iteratedDeriv_sub hsum hconst, iteratedDeriv_add h₁ h₂, iteratedDeriv_const,
    if_neg (Nat.one_le_iff_ne_zero.mp hn)]
  have hleft : iteratedDeriv n (fun s => sc₁.κ s R₀ R₁ L₁) L₁ = 0 :=
    sc₁.kappa_deriv_vanishes_at_L R₀ R₁ L₁ hL₁ n hn
  have hright_shift :
      iteratedDeriv n (fun s => sc₂.κ (s - L₁) R₁ R₂ L₂) L₁ =
        iteratedDeriv n (fun s => sc₂.κ s R₁ R₂ L₂) (L₁ - L₁) := by
    simpa using congrArg (fun f => f L₁) (iteratedDeriv_comp_sub_const n
      (fun s => sc₂.κ s R₁ R₂ L₂) L₁)
  rw [hleft, hright_shift, sub_self]
  simp [sc₂.kappa_deriv_vanishes_at_zero R₁ R₂ L₂ n hn]

end Smooth

end ClosureProperties
