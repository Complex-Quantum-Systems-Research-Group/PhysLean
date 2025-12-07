/-
  TODO / Roadmap for Thermodynamics/Core.lean

  1. Smooth structure and derivatives
     - Decide how to represent differentiability on `State` (e.g. `State` as a normed space
       or manifold).
     - Introduce `fderiv` / partial derivatives for `U`, `S`, and each `X i`.
     - Replace the `Prop` placeholders in `FirstLawEnergy` and `FirstLawEntropy` with
       precise derivative equalities:
         * energyForm : dU = T dS + ∑ᵢ Yᵢ dXᵢ
         * entropyForm : dS = (1/T) dU - ∑ᵢ (Yᵢ/T) dXᵢ

  2. Properties of entropy (entropy representation)
     - Make `concave` a concrete statement (e.g. `StrictConcaveOn ℝ S_of_ext domain`).
     - Make `extensive` precise (homogeneity of degree 1 in all extensive variables).
     - Make `mono_U` explicit (e.g. ∂S/∂U > 0).
     - Make `stability` precise (e.g. positivity of heat capacity, concavity constraints).

  3. Properties of energy (energy representation)
     - Make `convex` a concrete statement (e.g. `ConvexOn` for `U_of_ext`).
     - Make `extensive` precise in this representation as well.
     - Make `mono_S` explicit (e.g. ∂U/∂S > 0).
     - Clarify and formalize stability conditions in the energy representation.

  4. Equivalence of representations
     - Prove conditions under which an `EntropyRepresentation` induces an
       `EnergyRepresentation` (Legendre transform) and vice versa.
     - Add helper lemmas to move between the two representations.

  5. Intensive variables
     - Define T and Yᵢ in each representation via derivatives:
         * entropy rep:  1/T = ∂S/∂U,  Yᵢ/T = -∂S/∂Xᵢ
         * energy rep:   T   = ∂U/∂S,  Yᵢ  = ∂U/∂Xᵢ
     - Connect these definitions to `FirstLawEnergy` and `FirstLawEntropy`.

  6. Global thermodynamic identities
     - Euler relation (e.g. U = TS + ∑ᵢ Yᵢ Xᵢ for extensive systems).
     - Gibbs–Duhem relation.
     - Provide abstract statements in terms of `ThermodynamicSystem` and representations.

  7. Constraints and equilibrium
     - Add lemmas about existence/uniqueness of maximizers in `equilibriumStates` given
       concavity/strict concavity.
     - Prove generic “equilibrium ⇔ equality of intensive variables” results for composites,
       abstracting the condition for thermal equilibrium, mechanical equilibrium, etc.

  8. Physical domain / admissible states
     - Optionally introduce a notion of "physical domain" in `ExtSpace ι` and relate it to
       `Material.Physical`.
     - Clarify how positivity of U, S, and other extensives is enforced (state space vs.
       representation domain).

  (Concrete models like the ideal gas, van der Waals gas, mixtures, etc., will live in
   separate files and instantiate these abstract notions.)
-/
/-
  Thermodynamics/Core.lean

  Core abstractions for a general thermodynamic formalization in Lean 4.

  This file defines:

  * `ThermodynamicSystem`:
      - basic macroscopic system with state space, U, S, and a family of
        other extensive variables Xᵢ indexed by `ι`.

  * Entropy and energy representations:
      - `ExtSpace`, `ExtSpaceEnergy`
      - `EntropyRepresentation` (S = S(U, Xᵢ))
      - `EnergyRepresentation`  (U = U(S, Xᵢ))

  * `ThermodynamicModel`:
      - a thermodynamic system together with optional entropy/energy
        representations.

  * Constraints, closure relations, materials:
      - `Constraint`, `ClosureRelation`, `Material`

  * Equilibrium as entropy maximization:
      - `equilibriumStates`

  * Composition of systems:
      - `ThermodynamicSystem.comp`

  * A skeleton for generalized intensives and the first law:
      - `Intensives`
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

namespace Thermodynamics

universe u v

/-! ## 1. Core thermodynamic system -/

/--
`ThermodynamicSystem ι` is the bare macroscopic object we work with.

* `State` : the set of (equilibrium) macroscopic states.
* `U`     : internal energy.
* `S`     : entropy.
* `X i`   : a family of other extensive variables indexed by `ι`
            (e.g. volume, particle numbers, magnetization, etc.).

We **always** have `U` and `S` in the structure, but for particular models
they can be trivial/unused (e.g. constant functions) if desired.
Non-negativity is *not* enforced here at the type level; instead it is
encoded as properties in the thermodynamic representations.
-/
structure ThermodynamicSystem (ι : Type u) where
  State : Type v
  U : State → ℝ
  S : State → ℝ
  X : ι → State → ℝ

namespace ThermodynamicSystem

variable {ι : Type u}

/--
Non-interacting composition of two systems with the same index set of
extensive variables.

* The state space is the Cartesian product `A.State × B.State`.
* Extensive quantities (U, S, Xᵢ) are **additive**.
-/
def comp (A B : ThermodynamicSystem ι) :
    ThermodynamicSystem ι :=
{ State := A.State × B.State
, U := fun x => A.U x.1 + B.U x.2
, S := fun x => A.S x.1 + B.S x.2
, X := fun i x => A.X i x.1 + B.X i x.2 }

end ThermodynamicSystem

/-! ## 2. Entropy and energy representations -/

/-- Extensive coordinate space for the entropy representation: (U, Xᵢ). -/
def ExtSpace (ι : Type u) := ℝ × (ι → ℝ)

/-- Extensive coordinate space for the energy representation: (S, Xᵢ). -/
def ExtSpaceEnergy (ι : Type u) := ℝ × (ι → ℝ)

/--
Entropy representation in the sense of Callen: `S = S(U, Xᵢ)`.

This structure ties the abstract entropy `P.S` of a system to a scalar
function on the extensive coordinate space `(U, Xᵢ)`, and packages
Callen-style axioms as propositional fields.

We *also* encode non-negativity of U and S as properties:

* `U_nonneg` : internal energy coordinate is ≥ 0 for all states.
* `S_nonneg` : entropy is ≥ 0 for all states.
-/
structure EntropyRepresentation (ι : Type u)
    (P : ThermodynamicSystem ι) where
  /-- Map each state to its extensive coordinates `(U, Xᵢ)`. -/
  coord : P.State → ExtSpace ι
  /-- Injectivity: states are uniquely determined (on the manifold of interest)
      by their extensive coordinates. -/
  coord_injective : Function.Injective coord
  /-- Entropy as a function of extensive coordinates. -/
  S_of_ext : ExtSpace ι → ℝ
  /-- Compatibility: the system's entropy agrees with `S_of_ext ∘ coord`. -/
  S_agrees : ∀ x, P.S x = S_of_ext (coord x)

  /-- Internal energy coordinate is non-negative on all states. -/
  U_nonneg : ∀ x, 0 ≤ (coord x).1
  /-- Entropy is non-negative on all states. -/
  S_nonneg : ∀ x, 0 ≤ S_of_ext (coord x)

  /- Callen-type axioms (to be instantiated precisely later): -/
  concave   : Prop   -- S is concave in (U, Xᵢ).
  extensive : Prop   -- S is homogeneous of degree 1 in extensives.
  mono_U    : Prop   -- ∂S/∂U > 0 (monotone in energy).
  stability : Prop   -- Thermodynamic stability (e.g. positivity of heat capacity).

/--
Energy representation: `U = U(S, Xᵢ)`.

This is dual to the entropy representation. We also encode non-negativity:

* `S_nonneg` : entropy coordinate is ≥ 0 for all states.
* `U_nonneg` : energy is ≥ 0 for all states.
-/
structure EnergyRepresentation (ι : Type u)
    (P : ThermodynamicSystem ι) where
  /-- Map each state to its extensive coordinates `(S, Xᵢ)`. -/
  coord : P.State → ExtSpaceEnergy ι
  /-- Injectivity in the energy representation coordinates. -/
  coord_injective : Function.Injective coord
  /-- Internal energy as a function of `(S, Xᵢ)`. -/
  U_of_ext : ExtSpaceEnergy ι → ℝ
  /-- Compatibility: the system's energy agrees with `U_of_ext ∘ coord`. -/
  U_agrees : ∀ x, P.U x = U_of_ext (coord x)

  /-- Entropy coordinate is non-negative on all states. -/
  S_nonneg : ∀ x, 0 ≤ (coord x).1
  /-- Internal energy is non-negative on all states. -/
  U_nonneg : ∀ x, 0 ≤ U_of_ext (coord x)

  /- Energy-representation analogues of Callen's axioms: -/
  convex    : Prop   -- U is convex in (S, Xᵢ).
  extensive : Prop   -- U is homogeneous of degree 1 in extensives.
  mono_S    : Prop   -- ∂U/∂S > 0.
  stability : Prop   -- Stability conditions.

/-! ## 2.1 Intensive variables and the first law -/

/--
Intensive variables and the first law in the **energy representation**.

Mathematically, for a system with fundamental equation
  U = U(S, Xᵢ),
the first law is the differential identity

  dU = T dS + ∑ᵢ Yᵢ dXᵢ.

Here we keep the differential statement as an abstract `Prop`; later we
can replace it with an explicit equality between Fréchet derivatives
once we equip `State` with a smooth structure.
-/
structure FirstLawEnergy (ι : Type u)
    (P : ThermodynamicSystem ι)
    (E : EnergyRepresentation ι P) where
  /-- Temperature as a function on the state space. -/
  T : P.State → ℝ
  /-- Generalized forces conjugate to the extensive variables `X i`. -/
  Y : ι → P.State → ℝ
  /-- Differential form of the first law in the energy representation.
      Intended meaning (schematic):

        dU = T dS + ∑ᵢ Yᵢ dXᵢ.

      This will eventually be expressed via derivatives (e.g. `fderiv`). -/
  energyForm : Prop

/--
Intensive variables and the first law in the **entropy representation**.

For a system with fundamental equation
  S = S(U, Xᵢ),
the first law can be written as

  dS = (1/T) dU - ∑ᵢ (Yᵢ / T) dXᵢ.

Again, the differential identity is kept as a `Prop` for now, to be
refined later using the appropriate calculus on the state space.
-/
structure FirstLawEntropy (ι : Type u)
    (P : ThermodynamicSystem ι)
    (Srepr : EntropyRepresentation ι P) where
  /-- Temperature as a function on the state space. -/
  T : P.State → ℝ
  /-- Generalized forces conjugate to the extensive variables `X i`. -/
  Y : ι → P.State → ℝ
  /-- Differential form of the first law in the entropy representation.
      Intended meaning (schematic):

        dS = (1/T) dU - ∑ᵢ (Yᵢ / T) dXᵢ. -/
  entropyForm : Prop

/--
Full thermodynamic model: a core thermodynamic system equipped with (optional)
entropy and/or energy representations.

In many cases we will start with just the entropy representation filled
and leave the energy representation as `none` until we prove equivalence.
-/
structure ThermodynamicModel (ι : Type u) where
  core : ThermodynamicSystem ι
  entropyRep : Option (EntropyRepresentation ι core) := none
  energyRep  : Option (EnergyRepresentation ι core) := none

/-! ## 3. Constraints, closure relations, and materials -/

/--
A macroscopic **constraint**: a non-empty subset of the state space of a
thermodynamic system, describing allowed states under given external conditions
(e.g. fixed total energy, fixed volume, fixed particle numbers, etc.).
-/
structure Constraint {ι : Type u} (P : ThermodynamicSystem ι) where
  carrier : Set P.State
  nonempty : carrier.Nonempty

/--
A **closure relation** on a thermodynamic system: a predicate representing some
equation of state or other algebraic/constitutive relation between
thermodynamic variables.

Examples:
* `p V = N k_B T` for an ideal gas.
* More complicated relations specific to a material.
-/
structure ClosureRelation {ι : Type u} (P : ThermodynamicSystem ι) where
  relation : P.State → Prop

/--
A **material**: a thermodynamic system plus

* `Physical` : a predicate describing which states are physically allowed.
* `closures` : a set of closure relations (equations of state, etc.).

In practice one often works on the subset of `State` where `Physical` holds
and all closure relations are satisfied.
-/
structure Material (ι : Type u) where
  core : ThermodynamicSystem ι
  Physical : core.State → Prop
  nonempty : ∃ x, Physical x
  closures : Set (ClosureRelation core)

/-! ## 4. Equilibrium as entropy maximization -/

/--
Equilibrium states for a given constraint `K` on a system `P`, defined
via the **Max Entropy Principle**:

`x` is an equilibrium state if
* it satisfies the constraint (`x ∈ K.carrier`) and
* its entropy is maximal among all constrained states:
    `∀ y ∈ K.carrier, S(y) ≤ S(x)`.
-/
def equilibriumStates {ι : Type u} (P : ThermodynamicSystem ι)
    (K : Constraint P) : Set P.State :=
  { x | x ∈ K.carrier ∧ ∀ y ∈ K.carrier, P.S y ≤ P.S x }

/-! ## 5. Generalized intensives and the first law (skeleton) -/

/--
Generalized intensive variables and the differential form of the first law.

This is currently a **skeletal** structure:

* `T` : temperature-like field.
* `Y i` : generalized forces conjugate to the extensive variables `X i`.
* `firstLawDifferential` : a placeholder for the differential identity
    (in the energy representation)
        dU = ∑ᵢ Yᵢ dXᵢ
  or, equivalently in the entropy representation,
        dS = (1/T) dU - ∑ᵢ (Yᵢ / T) dXᵢ

Later we can implement this in terms of Fréchet derivatives (`fderiv`) or
partial derivatives, once we decide on the smooth structure on `State`.
-/
structure Intensives (ι : Type u) (M : ThermodynamicModel ι) where
  T : M.core.State → ℝ
  Y : ι → M.core.State → ℝ
  firstLawDifferential : Prop

end Thermodynamics
