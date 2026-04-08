/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/- Postulate I
  There exist particular states ( called equilibrium states) of simple systems that,
  macroscopically, are characterized completely by the internal energy U, the volume V,
  and the mole numbers N_1, N_2 , ... , N_r, of the chemical components.
-/
@[expose] public section

variable (n : ℕ)
variable (hn : 3 ≤ n)

abbrev StateSpace := Fin n → ℝ

instance StateSpace.normedAddCommGroup (n : ℕ) : NormedAddCommGroup (StateSpace n) :=
  Pi.normedAddCommGroup

noncomputable instance StateSpace.normedSpace (n : ℕ) : NormedSpace ℝ (StateSpace n) :=
  Pi.normedSpace

abbrev StateSpace.U (s : StateSpace n) : ℝ :=
  s ⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩

abbrev StateSpace.V (s : StateSpace n) : ℝ :=
  s ⟨1, Nat.lt_of_lt_of_le (by decide) hn⟩

def basisVec {k : ℕ} (c : Fin k) : Fin k → ℝ :=
  fun c' => if c' = c then 1 else 0

abbrev WallType (k : ℕ) := Set (Fin k)

def exchangeSubspace {k} (c : ℕ) (walls : Fin c → Fin c → WallType k)
    : Submodule ℝ (Fin c → Fin k -> ℝ) :=
  Submodule.span ℝ { v | ∃ i j coord, coord ∈ (walls i j) ∧
      v = Pi.single i (basisVec coord) - Pi.single j (basisVec coord) }


@[simp] noncomputable def d {k : ℕ}
  (S : StateSpace k → ℝ)
  (x : StateSpace k)
  (c : Fin k) : ℝ :=
  (fderiv ℝ S x) (basisVec c)

noncomputable def invTemp (S : StateSpace n → ℝ) (x : StateSpace n) : ℝ :=
  d S x ⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩


/- Postulate II
  There exists a function ( called the entropy S) of the extensive parameters of any
  composite system, defined for all equilibrium states and having the following
  property: The values assumed by the extensive parameters in the absence of an
  internal constraint are those that maximize the entropy over the manifold of
  constrained equilibrium states.
-/

/- Postulate III
  The entropy of a composite system is additive over the
  constituent subsystems. The entropy is **continuous and differentiable** and is a
  monotonically increasing function of the energy.
-/
open ContDiff

structure ThermodynamicSystem where
  S : StateSpace n → ℝ
  smooth : ContDiff ℝ ∞ S
  monotonic : ∀ x : StateSpace n, d S x ⟨0, Nat.lt_of_lt_of_le (by decide) hn⟩ > 0

structure CompositeSystem (c : ℕ) where
  S_i : Fin c → StateSpace n → ℝ
  smooth : ∀ i, ContDiff ℝ ∞ (S_i i)
  walls : Fin c → Fin c → WallType n
  symm : walls i j = walls j i

noncomputable def CompositeSystem.S_total (sys : CompositeSystem n c) (z : Fin c → StateSpace n) : ℝ :=
  ∑ i, sys.S_i i (z i)

def isEquilibrium {n c : ℕ}
    (sys : CompositeSystem n c)
    (z : Fin c → StateSpace n) : Prop :=
  ∀ v ∈ exchangeSubspace c sys.walls,
    (fderiv ℝ (sys.S_total) z) v = 0

def allows_exchange (sys : CompositeSystem n c) (i j : Fin c) (coord : Fin n) : Prop :=
  coord ∈ sys.walls i j

lemma fderiv_apply_single
    (f : StateSpace n → ℝ)
    (z : StateSpace n)
    (coord : Fin n) :
    (fderiv ℝ f z) (basisVec coord) = d f z coord := rfl

theorem intensive_eq_at_equilibrium
    {n c : ℕ}
    (sys : CompositeSystem n c)
    (z : Fin c → StateSpace n)
    (heq : isEquilibrium sys z)
    (i j : Fin c) (coord : Fin n)
    (hwall : coord ∈ sys.walls i j) :
    d (sys.S_i i) (z i) coord = d (sys.S_i j) (z j) coord := by
  -- The key exchange vector
  let v : Fin c → StateSpace n :=
    Pi.single i (basisVec coord) - Pi.single j (basisVec coord)
  -- v is in the exchange subspace by construction
  have hv : v ∈ exchangeSubspace c sys.walls := by
    apply Submodule.subset_span
    exact ⟨i, j, coord, hwall, rfl⟩

  -- The equilibrium condition gives us fderiv S_total z v = 0
  have h0 := heq v hv

  -- Expand S_total: fderiv (∑ S_i) z v = ∑ fderiv (S_i) (z i) (v i)
  -- because z decomposes and S_total is a sum over independent components
  unfold CompositeSystem.S_total at h0

  -- have hd : HasFDerivAt (fun z => ∑ k, sys.S_i k (z k))
  --   (∑ k, (fderiv ℝ (sys.S_i k) (z k)).comp (ContinuousLinearMap.proj k)) z := by
  --   convert HasFDerivAt.
  --   refine HasFDerivAt.sum (fun k _ => ?_)
  --   rw [←Finset.sum_apply]
  --   convert HasFDerivAt.sum (fun k _ => ?_)

  --   case h =>
  --     exact ((sys.smooth k).differentiable le_top (z k)).hasFDerivAt.comp z (hasFDerivAt_apply k z)

  have hd : HasFDerivAt (fun z : Fin c → StateSpace n => ∑ k, sys.S_i k (z k))
    (∑ k, (fderiv ℝ (sys.S_i k) (z k)).comp (ContinuousLinearMap.proj k)) z := by
    have : (fun z : Fin c → StateSpace n => ∑ k, sys.S_i k (z k)) =
         (∑ k, fun z => sys.S_i k (z k)) := by
      ext; simp [Finset.sum_apply]
    rw [this]
    apply HasFDerivAt.sum
    intro k _
    exact (((sys.smooth k).differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
      (hasFDerivAt_apply k z)
  rw [hd.fderiv] at h0
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply] at h0

  simp only [Pi.sub_apply, Pi.single_apply, map_sub, Finset.sum_sub_distrib, v] at h0
  rw [Finset.sum_eq_single i, Finset.sum_eq_single j] at h0
  . simp only [↓reduceIte] at h0
    simp only [d]
    linarith
  . intro m _ hmj; simp only [hmj, ↓reduceIte, map_zero]
  . simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, IsEmpty.forall_iff]
  . intro m _ hmi; simp only [hmi, ↓reduceIte, map_zero]
  . simp only [Finset.mem_univ, not_true_eq_false, ↓reduceIte, IsEmpty.forall_iff]
