/-
  Thermodynamics/IdealGas.lean

  Monophase, one-component ideal gas as an instance of the abstract
  thermodynamic framework defined in `Thermodynamics/Core.lean`.

  We introduce:

  * `IdealGasExt`        : index type for extensive variables (V, N).
  * `IdealGasState`      : state space with (U, V, N) > 0.
  * `IdealGasParams`     : parameters (c, R, s₀, U₀, V₀, N₀) entering Callen's
                           fundamental equation (3.34).
  * `idealGasSystem p`   : core `ThermodynamicSystem IdealGasExt` with parameters `p`.
  * `idealGasEntropyRepresentation p` :
                           entropy representation S = S(U, V, N) in Callen's form.
  * `idealGasModel p`    : `ThermodynamicModel` bundling the core system and
                           its entropy representation.

  For now, some analytic properties (concavity, stability, etc.) are left as `sorry`.
-/

import PhysLean.Thermodynamics.Core
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace Thermodynamics

/-! ### 1. Index type for extensive variables of the ideal gas -/

/--
Index type for extensive variables of a monophase, one-component ideal gas.

We distinguish:

* `V` : volume
* `N` : particle number (for a single species)
-/
inductive IdealGasExt
| V -- volume
| N -- number of particles

deriving DecidableEq, Repr

open IdealGasExt

/-! ### 2. State space for the ideal gas -/

/--
State of a monophase, one-component ideal gas.

We work with macroscopic variables:

* `U` : internal energy
* `V` : volume
* `N` : particle number (for a single species)

and require them to be strictly positive.
-/
structure IdealGasState where
  (U V N : ℝ)
  (hU : 0 < U)
  (hV : 0 < V)
  (hN : 0 < N)

namespace IdealGasState

/-- A small convenience lemma: internal energy is positive. -/
lemma U_pos (x : IdealGasState) : 0 < x.U := x.hU

/-- Volume is positive. -/
lemma V_pos (x : IdealGasState) : 0 < x.V := x.hV

/-- Particle number is positive. -/
lemma N_pos (x : IdealGasState) : 0 < x.N := x.hN

end IdealGasState

/-! ### 3. Parameters for the ideal gas fundamental equation -/

/--
Parameters entering the simple ideal gas fundamental equation in Callen's form (3.34).

We consider
  S = N s₀ + N R ln [ (U/U₀)^c (V/V₀) (N/N₀)^{-(c+1)} ],
which we will rewrite using logarithm identities.
-/
structure IdealGasParams where
  c  : ℝ    -- heat-capacity-related constant (e.g. 3/2)
  R  : ℝ    -- gas constant (per mole)
  s0 : ℝ    -- reference molar entropy
  U0 : ℝ    -- reference energy
  V0 : ℝ    -- reference volume
  N0 : ℝ    -- reference mole number
  hU0 : 0 < U0
  hV0 : 0 < V0
  hN0 : 0 < N0

/-! ### 4. Core thermodynamic system: `idealGasSystem p` -/

/--
Core thermodynamic system for a monophase, one-component ideal gas,
parametrized by `p : IdealGasParams`.

We implement Callen's equation (3.34) in an algebraically convenient form:
  S(U,V,N) = N s₀
             + N R [ c (ln U − ln U₀)
                      + (ln V − ln V₀)
                      − (c + 1) (ln N − ln N₀) ].
-/
def idealGasSystem (p : IdealGasParams) : ThermodynamicSystem IdealGasExt :=
{ State := IdealGasState,
  U := fun x => x.U,
  S := fun x =>
    let N := x.N
    let logU := Real.log x.U - Real.log p.U0
    let logV := Real.log x.V - Real.log p.V0
    let logN := Real.log x.N - Real.log p.N0
    N * p.s0
      + N * p.R * (p.c * logU + logV - (p.c + 1) * logN),
  X := fun i x =>
    match i with
    | IdealGasExt.V => x.V
    | IdealGasExt.N => x.N }

/-! Some simp-lemmas for the core system. -/

namespace idealGasSystem

variable {p : IdealGasParams}

@[simp] lemma U_def (x : IdealGasState) :
    (idealGasSystem p).U x = x.U := rfl

@[simp] lemma X_V_def (x : IdealGasState) :
    (idealGasSystem p).X IdealGasExt.V x = x.V := rfl

@[simp] lemma X_N_def (x : IdealGasState) :
    (idealGasSystem p).X IdealGasExt.N x = x.N := rfl

end idealGasSystem

/-! ### 5. Entropy representation for the ideal gas -/

/--
Entropy representation for the ideal gas with parameters `p`.

We treat S as a function of the extensive coordinates
  (U, V, N) ∈ ℝ × (IdealGasExt → ℝ),
with
  S(U,V,N) = N s₀
             + N R [ c (ln U − ln U₀)
                      + (ln V − ln V₀)
                      − (c + 1) (ln N − ln N₀) ].

Analytic properties (concavity, stability, etc.) and some inequalities
are left as `sorry` for now; they can be filled in later.
-/
def idealGasEntropyRepresentation (p : IdealGasParams) :
    EntropyRepresentation IdealGasExt (idealGasSystem p) :=
{ coord := fun x =>
    -- map state x to (U, Xᵢ) = (U, V, N)
    ((idealGasSystem p).U x,
     fun i => (idealGasSystem p).X i x),
  coord_injective := by
    -- Two states with the same (U,V,N) should be equal.
    -- This requires unraveling IdealGasState equality; we leave it as a TODO.
    intro x y h
    -- `h` has type:
    --   ((idealGasSystem p).U x, (fun i => (idealGasSystem p).X i x))
    -- = ((idealGasSystem p).U y, (fun i => (idealGasSystem p).X i y))
    -- From this we can deduce x.U = y.U, x.V = y.V, x.N = y.N and then use
    -- structure extensionality. For now, we leave the detailed proof as `sorry`.
    sorry,
  S_of_ext := fun (ux : ExtSpace IdealGasExt) =>
    let U := ux.1
    let Xvals := ux.2
    let N := Xvals IdealGasExt.N
    let logU := Real.log U - Real.log p.U0
    let logV := Real.log (Xvals IdealGasExt.V) - Real.log p.V0
    let logN := Real.log N - Real.log p.N0
    N * p.s0
      + N * p.R * (p.c * logU + logV - (p.c + 1) * logN),
  S_agrees := by
    intro x
    -- By definition of `idealGasSystem` and `coord`, this is defeq:
    rfl,
  U_nonneg := by
    intro x
    -- From `x.hU : 0 < x.U` we can get `0 ≤ x.U`.
    exact le_of_lt x.hU,
  S_nonneg := by
    -- Non-negativity of S is not automatic from this expression; one can
    -- always shift `s0` to make S ≥ 0. For now we leave this as a TODO.
    intro x
    sorry,
  concave   := True,   -- TODO: prove using concavity of log and linearity
  extensive := True,   -- TODO: homogeneity of degree 1 in (U,V,N) in an appropriate sense
  mono_U    := True,   -- TODO: ∂S/∂U = N R c / U > 0 when c, R, U > 0
  stability := True }  -- TODO: stability conditions (e.g. positive heat capacity)

/-! ### 6. Thermodynamic model for the ideal gas -/

/--
Thermodynamic model for the ideal gas with parameters `p`:
core system + entropy representation, no energy representation yet.
-/
def idealGasModel (p : IdealGasParams) : ThermodynamicModel IdealGasExt :=
{ core := idealGasSystem p,
  entropyRep := some (idealGasEntropyRepresentation p),
  energyRep := none }

/--
Parameters for a monoatomic ideal gas: we fix `c = 3/2` but leave
`R, s₀, U₀, V₀, N₀` as arbitrary positive reference constants.
-/
def monoatomicIdealGasParams
    (R s0 U0 V0 N0 : ℝ)
    (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0) :
    IdealGasParams :=
{ c  := 3 / 2,
  R  := R,
  s0 := s0,
  U0 := U0,
  V0 := V0,
  N0 := N0,
  hU0 := hU0,
  hV0 := hV0,
  hN0 := hN0 }

/--
Monoatomic ideal gas model, parameterized by `R, s₀, U₀, V₀, N₀` and their
positivity conditions.

This keeps the reference scales symbolic, as in Callen, and only fixes
the heat-capacity constant `c = 3/2`.
-/
def monoatomicIdealGasModel
    (R s0 U0 V0 N0 : ℝ)
    (hU0 : 0 < U0) (hV0 : 0 < V0) (hN0 : 0 < N0) :
    ThermodynamicModel IdealGasExt :=
  idealGasModel
    (monoatomicIdealGasParams R s0 U0 V0 N0 hU0 hV0 hN0)

end Thermodynamics
