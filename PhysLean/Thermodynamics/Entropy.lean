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
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/- Postulate I
  There exist particular states ( called equilibrium states) of simple systems that,
  macroscopically, are characterized completely by the internal energy U, the volume V,
  and the mole numbers N_1, N_2 , ... , N_r, of the chemical components.
-/
@[expose] public section
variable {n : ℕ}

abbrev StateSpace (n : ℕ) := Fin n → ℝ
abbrev ThermoState := ℝ × ℝ × ℝ
/-- List of intensive characteristics of a system -/
abbrev ThermoState.U (s : ThermoState) : ℝ := s.1
abbrev ThermoState.V (s : ThermoState) : ℝ := s.2.1
abbrev ThermoState.N (s : ThermoState) : ℝ := s.2.2

def dU_dir : ThermoState := (1,0,0)

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
open ContDiff ThermoState
structure ThermodynamicSystem where
  S : ThermoState → ℝ
  smooth : ContDiff ℝ ∞ S
  monotonic : ∀ x : ThermoState, fderiv ℝ S x dU_dir > 0

namespace ThermodynamicSystem
variable (sys : ThermodynamicSystem)


-- noncomputable def dS (sys : ThermodynamicSystem) (state : ThermoState) := fderiv ℝ sys.S state

-- noncomputable def ddS (sys : ThermodynamicSystem) (state : ThermoState) :=
--   fderiv ℝ (dS sys state) state


structure ThermoGraph (n : ℕ) where
  systems       : Finset (ThermodynamicSystem)
  diathermal    : SimpleGraph (systems)  -- vertex type is the subtype
  movable       : SimpleGraph (systems)
  semipermeable : Fin n → SimpleGraph (systems)

def thermalComponent (g : ThermoGraph n ) (sys : g.systems) :
    SimpleGraph.ConnectedComponent g.diathermal :=
  g.diathermal.connectedComponentMk sys

def pressureComponent (g : ThermoGraph n) (sys : g.systems) :
    SimpleGraph.ConnectedComponent g.movable :=
  g.movable.connectedComponentMk sys

def ConstraintManifold
    (U_tot V_tot N_tot : ℝ) : Set (ThermoState × ThermoState) :=
  { p | p.1.U + p.2.U = U_tot
      ∧ p.1.V + p.2.V = V_tot
      ∧ p.1.N + p.2.N = N_tot
      -- Physical admissibility: extensive parameters are non-negative
      ∧ 0 ≤ p.1.U ∧ 0 ≤ p.2.U
      ∧ 0 ≤ p.1.V ∧ 0 ≤ p.2.V
      ∧ 0 ≤ p.1.N ∧ 0 ≤ p.2.N }

def totalEntropy
    (sys1 sys2 : ThermodynamicSystem)
    (p : ThermoState × ThermoState) : ℝ :=
  sys1.S p.1 + sys2.S p.2

lemma totalEntropy_eq (sys1 sys2 : ThermodynamicSystem) (p : ThermoState × ThermoState) :
  totalEntropy sys1 sys2 p = sys1.S p.1 + sys2.S p.2 := by rfl

def EntropyMaximized
    (sys1 sys2 : ThermodynamicSystem)
    (eq_state : ThermoState × ThermoState) : Prop :=
  -- The equilibrium state must be accessible (obeys all conservation laws)
  eq_state ∈ ConstraintManifold (eq_state.1.U + eq_state.2.U) (eq_state.1.V + eq_state.2.V)
    (eq_state.1.N + eq_state.2.N)
  ∧ fderiv ℝ (totalEntropy sys1 sys2) (eq_state.1, eq_state.2) = 0

-- prove additivity provides λS(a,b,c) = S(λa, λb, λc)

/- Postulate IV
  The entropy of any system vanishes in the state for which fderiv ℝ U State (S) = 0
-/

noncomputable def Temperature (sys : ThermodynamicSystem) (state : ThermoState) :=
    1 / (fderiv ℝ sys.S state (1,0,0))

noncomputable def TemperatureImpliesEntropy (sys : ThermodynamicSystem) (state : ThermoState) :=
  Temperature sys state = 0 → sys.S state = 0

theorem intensive_partials_eq
  (sys1 sys2 : ThermodynamicSystem)
  (eq_state : ThermoState × ThermoState)
  (h_eq : EntropyMaximized sys1 sys2 eq_state):
    fderiv ℝ sys1.S eq_state.1 = fderiv ℝ sys2.S eq_state.2 := by

  have hn : ∞ ≠ 0 := by simp only [ne_eq, WithTop.coe_eq_zero, ENat.top_ne_zero, not_false_eq_true]
  have d_s1 : Differentiable ℝ sys1.S := sys1.smooth.differentiable (hn)
  have d_s2 : Differentiable ℝ sys2.S := sys2.smooth.differentiable (hn)

  rw [EntropyMaximized] at h_eq
  obtain ⟨h_manifold, h_eq⟩ := h_eq
  rcases h_manifold with ⟨hU, hV, hN, rest⟩

  change fderiv ℝ (fun p => sys1.S p.1 + sys2.S p.2) (eq_state.1, eq_state.2) = 0 at h_eq

  rw [show (fun p : ThermoState × ThermoState => sys1.S p.1 + sys2.S p.2) =
    (fun p => (sys1.S ∘ Prod.fst) p + (sys2.S ∘ Prod.snd) p) from rfl] at h_eq

  simp only [fderiv_fun_add
      ((d_s1 eq_state.1).comp _ differentiableAt_fst)
      ((d_s2 eq_state.2).comp _ differentiableAt_snd),
    fderiv_comp _ (d_s1 eq_state.1) differentiableAt_fst,
    fderiv_comp _ (d_s2 eq_state.2) differentiableAt_snd,
    fderiv_fst, fderiv_snd] at h_eq

  have h1 : fderiv ℝ sys1.S eq_state.1 = 0 := ContinuousLinearMap.ext fun v => by
    have := congr_fun (congr_arg DFunLike.coe h_eq) (v, 0)
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at this; exact this

  have h2 : fderiv ℝ sys2.S eq_state.2 = 0 := ContinuousLinearMap.ext fun v => by
    have := congr_fun (congr_arg DFunLike.coe h_eq) (0, v)
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply] at this; exact this

  rw [h1, h2]


theorem equillibrium_temperature_eq
  (sys1 sys2 : ThermodynamicSystem)
  (eq_state : ThermoState × ThermoState)
  (h_eq : EntropyMaximized sys1 sys2 eq_state):
    Temperature sys1 eq_state.1 = Temperature sys2 eq_state.2 := by
    unfold Temperature
    congr 1
    have h : fderiv ℝ sys1.S eq_state.1 = fderiv ℝ sys2.S eq_state.2 :=
      intensive_partials_eq sys1 sys2 eq_state h_eq
    have h2 := congr_arg (· (((1,0,0)) : ThermoState)) h
    exact h2

lemma thermal_equilibrium_component
    (g : ThermoGraph n)
    (h_adj : ∀ s1 s2 : g.systems, g.diathermal.Adj s1 s2 →
        Temperature s1.val = Temperature s2.val)
    (sys1 sys2 : g.systems)
    (h_reach : g.diathermal.Reachable sys1 sys2) :
    Temperature sys1.val = Temperature sys2.val := by
    obtain ⟨w⟩ := h_reach
    induction w with
      | nil => rfl
      | cons h walk ih => exact (h_adj _ _ h).trans ih

end ThermodynamicSystem
