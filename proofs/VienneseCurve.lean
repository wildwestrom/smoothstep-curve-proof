import proofs.smoothstep_curve

/-!
# Viennese Curve (Hasslinger-style)

Physics layer on top of `SmoothstepCurve` for real vehicles at aligning height `h`
above the rail. Following Hasslinger (WO 2004/009906), the physical curvature at
aligning height `h` satisfies the differential equation (eq. 1 in the patent):

  `κ_H(s) = (K_c / ψ_c) · ψ(s) − h · d²ψ/ds²`

In the normalized domain z = s/L (where L is the transition length), d²ψ/ds² becomes
(1/L²) · d²ψ/dz², giving:

  `κ_H(z) = (κ_ref / ψ_ref) · ψ(z) − (h / L²) · d²ψ/dz²`

where `ψ(z) = ψ_start + Δψ · H(z)`.
-/

open scoped ContDiff
open Smooth

section BridgeLemmas

/-! ### Bridge lemmas for iterated derivatives -/

lemma iteratedDeriv_iteratedDeriv {f : ℝ → ℝ} (m n : ℕ) :
    iteratedDeriv m (iteratedDeriv n f) = iteratedDeriv (m + n) f := by
  induction m generalizing n with
  | zero => simp [iteratedDeriv_zero]
  | succ m ih =>
    rw [iteratedDeriv_succ']
    have hderiv : deriv (iteratedDeriv n f) = iteratedDeriv (n + 1) f := by
      rw [← iteratedDeriv_succ]
    rw [hderiv, ih (n + 1)]
    congr 1; omega

lemma contDiff_iteratedDeriv_top {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [iteratedDeriv_iteratedDeriv m n]
  exact hf.differentiable_iteratedDeriv (m + n) (by exact_mod_cast ENat.coe_lt_top (m + n))

end BridgeLemmas

section VienneseCurveDefs

/-! ### Cant and physical curvature definitions -/

noncomputable def vienneseCant (sc : SmoothstepCurve) (psi_start psi_end : ℝ) : ℝ → ℝ :=
  fun z => psi_start + (psi_end - psi_start) * sc.H z

noncomputable def vienneseKappa (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ) : ℝ → ℝ :=
  fun z => (kappa_ref / psi_ref) * vienneseCant sc psi_start psi_end z
           - (h_align / L ^ 2) * iteratedDeriv 2 (vienneseCant sc psi_start psi_end) z

/-! ### Cant lemmas -/

lemma cant_contDiff (sc : SmoothstepCurve) (psi_start psi_end : ℝ) :
    ContDiff ℝ ∞ (vienneseCant sc psi_start psi_end) :=
  contDiff_const.add (contDiff_const.mul sc.H_is_C_inf)

lemma cant_at_zero (sc : SmoothstepCurve) (psi_start psi_end : ℝ) :
    vienneseCant sc psi_start psi_end 0 = psi_start := by
  simp [vienneseCant, sc.H_zero]

lemma cant_at_one (sc : SmoothstepCurve) (psi_start psi_end : ℝ) :
    vienneseCant sc psi_start psi_end 1 = psi_end := by
  unfold vienneseCant
  rw [sc.H_one]
  ring

lemma cant_deriv_vanishes (sc : SmoothstepCurve) (psi_start psi_end : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x = 0 ∨ x = 1) :
    iteratedDeriv n (vienneseCant sc psi_start psi_end) x = 0 := by
  have hn' : 0 < n := Nat.one_le_iff_ne_zero.mp hn |>.bot_lt
  show iteratedDeriv n (fun z => psi_start + (psi_end - psi_start) * sc.H z) x = 0
  rw [iteratedDeriv_const_add hn']
  rw [iteratedDeriv_const_mul_field]
  rcases hx with rfl | rfl
  · simp [sc.H_deriv_vanishes_at_zero n hn]
  · simp [sc.H_deriv_vanishes_at_one n hn]

/-! ### Physical curvature lemmas -/

lemma kappa_physical_contDiff (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ) :
    ContDiff ℝ ∞ (vienneseKappa sc h_align L kappa_ref psi_ref psi_start psi_end) := by
  apply ContDiff.sub
  · exact contDiff_const.mul (cant_contDiff sc psi_start psi_end)
  · exact contDiff_const.mul (contDiff_iteratedDeriv_top (cant_contDiff sc psi_start psi_end) 2)

lemma kappa_physical_deriv_vanishes (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x = 0 ∨ x = 1) :
    iteratedDeriv n (vienneseKappa sc h_align L kappa_ref psi_ref psi_start psi_end) x = 0 := by
  have hcant_cd := cant_contDiff sc psi_start psi_end
  have hcant2_cd := contDiff_iteratedDeriv_top hcant_cd 2
  have hterm1_cd : ContDiff ℝ ∞ (fun z => (kappa_ref / psi_ref) * vienneseCant sc psi_start psi_end z) :=
    contDiff_const.mul hcant_cd
  have hterm2_cd : ContDiff ℝ ∞ (fun z => (h_align / L ^ 2) * iteratedDeriv 2 (vienneseCant sc psi_start psi_end) z) :=
    contDiff_const.mul hcant2_cd
  rw [show vienneseKappa sc h_align L kappa_ref psi_ref psi_start psi_end =
    (fun z => (kappa_ref / psi_ref) * vienneseCant sc psi_start psi_end z) -
    (fun z => (h_align / L ^ 2) * iteratedDeriv 2 (vienneseCant sc psi_start psi_end) z) from rfl]
  rw [iteratedDeriv_sub
    (hterm1_cd.contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞))))
    (hterm2_cd.contDiffAt.of_le (by exact_mod_cast le_top (a := (n : ℕ∞))))]
  rw [iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_const_mul_field]
  have hcant_vanish := cant_deriv_vanishes sc psi_start psi_end n hn x hx
  have hcant2_vanish : iteratedDeriv n (iteratedDeriv 2 (vienneseCant sc psi_start psi_end)) x = 0 := by
    rw [iteratedDeriv_iteratedDeriv n 2]
    exact cant_deriv_vanishes sc psi_start psi_end (n + 2) (by omega) x hx
  simp [hcant_vanish, hcant2_vanish]

lemma kappa_at_zero (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ) :
    vienneseKappa sc h_align L kappa_ref psi_ref psi_start psi_end 0 =
    (kappa_ref / psi_ref) * psi_start := by
  simp only [vienneseKappa]
  rw [cant_at_zero]
  have : iteratedDeriv 2 (vienneseCant sc psi_start psi_end) 0 = 0 :=
    cant_deriv_vanishes sc psi_start psi_end 2 (by omega) 0 (Or.inl rfl)
  rw [this]
  ring

lemma kappa_at_one (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ) :
    vienneseKappa sc h_align L kappa_ref psi_ref psi_start psi_end 1 =
    (kappa_ref / psi_ref) * psi_end := by
  simp only [vienneseKappa]
  rw [cant_at_one]
  have : iteratedDeriv 2 (vienneseCant sc psi_start psi_end) 1 = 0 :=
    cant_deriv_vanishes sc psi_start psi_end 2 (by omega) 1 (Or.inr rfl)
  rw [this]
  ring

end VienneseCurveDefs

/-! ### VienneseCurve structure -/

structure VienneseCurve where
  sc : SmoothstepCurve
  h_align : ℝ
  L : ℝ
  kappa_ref : ℝ
  psi_ref : ℝ
  psi_start : ℝ
  psi_end : ℝ
  h_align_nonneg : 0 ≤ h_align
  L_pos : 0 < L
  psi_ref_ne_zero : psi_ref ≠ 0

namespace VienneseCurve

noncomputable def cant (vc : VienneseCurve) : ℝ → ℝ :=
  vienneseCant vc.sc vc.psi_start vc.psi_end

noncomputable def kappa (vc : VienneseCurve) : ℝ → ℝ :=
  vienneseKappa vc.sc vc.h_align vc.L vc.kappa_ref vc.psi_ref vc.psi_start vc.psi_end

end VienneseCurve

noncomputable def mkVienneseCurve
    (sc : SmoothstepCurve) (h_align L kappa_ref psi_ref psi_start psi_end : ℝ)
    (h_align_nonneg : 0 ≤ h_align) (L_pos : 0 < L) (psi_ref_ne_zero : psi_ref ≠ 0) :
    VienneseCurve where
  sc := sc
  h_align := h_align
  L := L
  kappa_ref := kappa_ref
  psi_ref := psi_ref
  psi_start := psi_start
  psi_end := psi_end
  h_align_nonneg := h_align_nonneg
  L_pos := L_pos
  psi_ref_ne_zero := psi_ref_ne_zero
