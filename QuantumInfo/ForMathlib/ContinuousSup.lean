/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Real.StarOrdered
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

variable {α β γ : Type*} {S : Set β} {f : γ → β → α}
variable [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
variable [TopologicalSpace γ]

namespace IsCompact
variable [TopologicalSpace β]

theorem sSup_image_eq_sSup_image_closure {f : β → α}
  (hS : IsCompact (closure S)) (hf : Continuous f) :
    sSup (f '' S) = sSup (f '' closure S) := by
  rcases S.eq_empty_or_nonempty with rfl | h; · simp
  refine csSup_eq_of_forall_le_of_forall_lt_exists_gt (by simpa) ?_ ?_
  · rintro a ⟨w, hw, rfl⟩
    exact le_csSup (hS.image hf).bddAbove (Set.mem_image_of_mem f <| subset_closure hw)
  · intro w hw
    simp only [Set.mem_image, exists_exists_and_eq_and]
    contrapose! hw
    have h_image_closure : f '' closure S ⊆ closure (f '' S) :=
      image_closure_subset_closure_image hf
    have h_closure_image : closure (f '' S) ⊆ Set.Iic w :=
      closure_minimal (Set.image_subset_iff.mpr hw) isClosed_Iic
    exact csSup_le ((h.mono subset_closure).image f) fun y hy ↦
      (h_image_closure.trans h_closure_image) hy

theorem sInf_image_eq_sInf_image_closure {f : β → α} (hS : IsCompact (closure S)) (hf : Continuous f) :
    sInf (f '' S) = sInf (f '' closure S) :=
  sSup_image_eq_sSup_image_closure (α := αᵒᵈ) hS hf

/-- A version of `IsCompact.continuous_sSup` with a slightly weaker hypothesis on the set `K`,
that its closure is compact (but the set itself need not be). -/
theorem closure_continuous_sSup (hS : IsCompact (closure S)) (hf : Continuous ↿f) :
    Continuous fun x ↦ sSup (f x '' S) := by
  simp_rw [fun x ↦ sSup_image_eq_sSup_image_closure hS (f := f x) (by fun_prop)]
  exact hS.continuous_sSup hf

/-- A version of `IsCompact.continuous_sInf` with a slightly weaker hypothesis on the set `K`,
that its closure is compact (but the set itself need not be). -/
theorem closure_continuous_sInf (hS : IsCompact (closure S)) (hf : Continuous ↿f) :
    Continuous fun x ↦ sInf (f x '' S) :=
  closure_continuous_sSup (α := αᵒᵈ) hS hf

theorem continuous_iSup (hS : IsCompact (closure S)) (hf : Continuous ↿f) :
    Continuous fun x ↦ ⨆ y : S, f x y := by
  simp_rw [iSup, ← Set.image_eq_range]
  exact hS.closure_continuous_sSup hf

theorem continuous_iInf (hS : IsCompact (closure S)) (hf : Continuous ↿f) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  continuous_iSup (α := αᵒᵈ) hS hf

end IsCompact

namespace Bornology.IsBounded
variable [PseudoMetricSpace β] [ProperSpace β]

/-- Similar to `IsCompact.continuous_sSup`, but taking a bounded set in the bornology instead
of a compact set. -/ --TODO: Can `ProperSpace` be relaxed to `CompleteSpace` here?
theorem continuous_sSup (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ sSup (f x '' S) :=
  hS.isCompact_closure.closure_continuous_sSup hf

/-- Similar to `IsCompact.continuous_sInf`, but taking a bounded set in the bornology instead
of a compact set. -/
theorem continuous_sInf (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ sInf (f x '' S) :=
  hS.isCompact_closure.closure_continuous_sInf hf

theorem continuous_iSup (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ ⨆ y : S, f x y := by
  simp_rw [iSup, ← Set.image_eq_range]
  exact hS.isCompact_closure.closure_continuous_sSup <| by fun_prop

theorem continuous_iInf (hS : Bornology.IsBounded S) (hf : Continuous ↿f) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  continuous_iSup (α := αᵒᵈ) hS hf

end Bornology.IsBounded

namespace LinearMap

/-- For bilinear maps in suitably well-behaved spaces with `IsModuleTopology`, taking the supremum in one
argument is still `Continuous`, by `Bornology.IsBounded.continuous_iSup`. -/
theorem continuous_iSup {E F 𝕜 : Type*}
  [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [IsModuleTopology 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [PseudoMetricSpace F] [ProperSpace F] [Module.Finite 𝕜 F] [IsModuleTopology 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  hS.continuous_iSup <| by fun_prop

/-- For bilinear maps in suitably well-behaved spaces with `IsModuleTopology`, taking the infimum in one
argument is still `Continuous`, by `Bornology.IsBounded.continuous_iInf`. -/
theorem continuous_iInf {E F 𝕜 : Type*}
  [CommRing 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E] [IsModuleTopology 𝕜 E]
  [AddCommGroup F] [Module 𝕜 F] [PseudoMetricSpace F] [ProperSpace F] [Module.Finite 𝕜 F] [IsModuleTopology 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  hS.continuous_iInf <| by fun_prop

/-- A specialization of `LinearMap.continuous_iSup` to finite dimensional spaces, in place
of requiring a (non-instance) `IsModuleTopology`. -/
theorem continuous_iSup' {E F 𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [PseudoMetricSpace F] [ProperSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [T2Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  let _ : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := E)
  let _ : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := F)
  f.continuous_iSup hS

/-- A specialization of `LinearMap.continuous_iInf` to finite dimensional spaces, in place
of requiring a (non-instance) `IsModuleTopology`. -/
theorem continuous_iInf' {E F 𝕜 : Type*}
  [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [FiniteDimensional 𝕜 E]
  [PseudoMetricSpace F] [ProperSpace F] [AddCommGroup F] [IsTopologicalAddGroup F] [T2Space F]
  [Module 𝕜 F] [ContinuousSMul 𝕜 F] [FiniteDimensional 𝕜 F]
  (f : E →ₗ[𝕜] F →ₗ[𝕜] 𝕜) {S : Set F} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  let _ : IsModuleTopology 𝕜 E := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := E)
  let _ : IsModuleTopology 𝕜 F := isModuleTopologyOfFiniteDimensional (𝕜 := 𝕜) (E := F)
  f.continuous_iInf hS

/-- Alias of `LinearMap.continuous_iSup' ` that takes `LinearMap.BilinForm`. -/
theorem BilinForm.continuous_iSup {𝕜 E : Type*}
  [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [ProperSpace E]
  (f : LinearMap.BilinForm 𝕜 E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  f.continuous_iSup' hS

/-- Alias of `LinearMap.continuous_iInf' ` that takes `LinearMap.BilinForm`. -/
theorem BilinForm.continuous_iInf {𝕜 E : Type*}
  [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [OrderTopology 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [ProperSpace E]
  (f : LinearMap.BilinForm 𝕜 E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  f.continuous_iInf' hS

end LinearMap

namespace ContinuousLinearMap

variable  {𝕜 𝕜₂ : Type*} {E F G : Type*} [NontriviallyNormedField 𝕜] [Semiring 𝕜₂] {σ₁₂ : 𝕜₂ →+* 𝕜}
 [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E]
 [AddCommMonoid F] [TopologicalSpace F] [Module 𝕜₂ F]
 [SeminormedAddCommGroup G] [NormedSpace 𝕜 G][ConditionallyCompleteLinearOrder G] [OrderTopology G]

/-- A specialization of `Bornology.IsBounded.continuous_iSup_bilinear` to `ContinuousLinearMap`. -/
theorem continuous_iSup
  (f : F →SL[σ₁₂] E →L[𝕜] G) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f x y :=
  hS.continuous_iSup <| by fun_prop

theorem continuous_iInf
  (f : F →SL[σ₁₂] E →L[𝕜] G) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f x y :=
  hS.continuous_iInf (α := G) <| by fun_prop

end ContinuousLinearMap

--This is the theorem we actually needed downstream...
theorem LinearMap.BilinForm.continuous_iSup_fst
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : LinearMap.BilinForm ℝ E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨆ y : S, f y x := by
  exact LinearMap.BilinForm.continuous_iSup f.flip hS
  --Old "direct" proof:
  -- -- Since $f$ is continuous, there exists $C > 0$ such that for all $y \in S$ and $x \in E$, $|f y x| \leq C \|y\| \|x\|$.
  -- obtain ⟨C, hC1, hC2⟩ : ∃ C > 0, ∀ y ∈ S, ∀ x : E, |f y x| ≤ C * ‖y‖ * ‖x‖ := by
  --   -- Since $f$ is continuous, there exists $C > 0$ such that for all $y, x \in E$, $|f y x| \leq C \|y\| \|x\|$ by the boundedness of continuous bilinear maps on finite-dimensional spaces.
  --   have h_cont : ∃ C > 0, ∀ y x : E, |f y x| ≤ C * ‖y‖ * ‖x‖ := by
  --     have h_bounded : Continuous (fun p : E × E => f p.1 p.2) := by
  --       have _ := isModuleTopologyOfFiniteDimensional (𝕜 := ℝ) (E := E)
  --       fun_prop
  --     obtain ⟨C, hC₀, hC⟩ : ∃ C > 0, ∀ y x : E, ‖y‖ ≤ 1 → ‖x‖ ≤ 1 → |f y x| ≤ C := by
  --       have h_compact : IsCompact {p : E × E | ‖p.1‖ ≤ 1 ∧ ‖p.2‖ ≤ 1} := by
  --         have h_closed_unit_ball : IsCompact {p : E | ‖p‖ ≤ 1} := by
  --           convert ProperSpace.isCompact_closedBall (0 : E) 1
  --           simp [Metric.closedBall, dist_eq_norm]
  --         exact h_closed_unit_ball.prod h_closed_unit_ball;
  --       obtain ⟨C, hC⟩ := h_compact.exists_bound_of_continuousOn h_bounded.continuousOn;
  --       exact ⟨C ⊔ 1, zero_lt_one.trans_le (le_max_right _ _), fun y x hy hx ↦ (hC (y, x) ⟨hy, hx⟩ ).trans (le_max_left _ _)⟩;
  --     refine ⟨C, hC₀, fun y x ↦ ?_⟩;
  --     rcases eq_or_ne y 0 with rfl | hy; · simp
  --     rcases eq_or_ne x 0 with rfl | hx; · simp
  --     have := hC (‖y‖⁻¹ • y) (‖x‖⁻¹ • x) (by simp [hy, norm_smul]) (by simp [hx, norm_smul])
  --     simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at this
  --     rw [abs_le] at this ⊢
  --     rw [← norm_ne_zero_iff] at hx hy
  --     have : 0 < ‖y‖ * ‖x‖ := by positivity
  --     have := inv_mul_cancel_left₀ hy ((f y) x)
  --     have := inv_mul_cancel_left₀ hx ((f y) x)
  --     have := mul_inv_cancel₀ hy
  --     constructor <;> nlinarith
  --   exact ⟨ h_cont.choose, h_cont.choose_spec.1, fun y hy x ↦ h_cont.choose_spec.2 y x ⟩;
  -- -- Since $S$ is bounded, there exists $M > 0$ such that for all $y \in S$, $\|y\| \leq M$.
  -- obtain ⟨M, hM1, hM2⟩ : ∃ M > 0, ∀ y ∈ S, ‖y‖ ≤ M :=
  --   hS.exists_pos_norm_le
  -- rw [Metric.continuous_iff]
  -- intro b ε hε
  -- refine ⟨ε / (C * M + 1), div_pos hε (by positivity), fun a ha ↦ ?_⟩
  -- -- Using the triangle inequality and the continuity of $f$, we get:
  -- have h_triangle (y) (hy : y ∈ S) : |f y a - f y b| ≤ C * M * ‖a - b‖ := by
  --   rw [← map_sub]
  --   apply (hC2 y hy ( a - b )).trans
  --   refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  --   exact mul_le_mul_of_nonneg_left (hM2 y hy) hC1.le
  -- rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩; · simp [*]
  -- simp [dist_eq_norm] at *
  -- -- Applying the triangle inequality to the suprema, we get:
  -- have h_sup_triangle : |(⨆ y : S, f y a) - (⨆ y : S, f y b)| ≤ C * M * ‖a - b‖ := by
  --   rw [abs_sub_le_iff]
  --   constructor
  --   · -- Applying the inequality $f y a \leq f y b + C * M * ‖a - b‖$ to each term in the supremum, we get:
  --     have h_le (y : S) : f y a ≤ f y b + C * M * ‖a - b‖ := by
  --       linarith [abs_le.mp (h_triangle y y.2)]
  --     rw [sub_le_iff_le_add, add_comm]
  --     convert ciSup_le fun y => le_trans ( h_le y ) _;
  --     · exact ⟨⟨ y, hy ⟩⟩
  --     · refine add_le_add ?_ le_rfl
  --       refine le_csSup ?_ (Set.mem_range_self _)
  --       exact ⟨C * M * ‖b‖, Set.forall_mem_range.2 fun y => le_of_abs_le ((hC2 _ y.2 _).trans (by gcongr; exact hM2 _ y.2))⟩;
  --   · rw [sub_le_iff_le_add']
  --     -- Applying the triangle inequality to each term in the supremum, we get:
  --     have h_sup_triangle (y) (hy : y ∈ S) : f y b ≤ f y a + C * M * ‖a - b‖ := by
  --       linarith [abs_le.mp (h_triangle y hy)]
  --     convert ciSup_le _
  --     · exact ⟨⟨y, hy⟩⟩
  --     · intro x
  --       refine (h_sup_triangle x x.2).trans (add_le_add_right ?_ _)
  --       exact le_ciSup (show BddAbove (Set.range fun y : S ↦ f y a) by
  --         refine ⟨C * M * ‖a‖, Set.forall_mem_range.2 fun y ↦ ?_⟩
  --         refine le_of_abs_le ((hC2 _ y.2 _).trans ?_)
  --         refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  --         exact mul_le_mul_of_nonneg_left (hM2 _ y.2) hC1.le
  --       ) x;
  -- apply h_sup_triangle.trans_lt
  -- rw [lt_div_iff₀ (by positivity)] at ha
  -- nlinarith [mul_pos hC1 hM1]

theorem LinearMap.BilinForm.continuous_iInf_fst
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  (f : LinearMap.BilinForm ℝ E) {S : Set E} (hS : Bornology.IsBounded S) :
    Continuous fun x ↦ ⨅ y : S, f y x :=
  LinearMap.BilinForm.continuous_iInf f.flip hS
