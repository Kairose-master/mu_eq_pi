/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.Linearization
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Flattening is projection onto the graph of the state transition

A nested computation reads a state, produces a new one, and then runs a second
stage. Before the two stages are joined, the second stage's input state is a
*free parameter*: the relevant index set is the **doubled configuration set**

  `DConf S X = (X × S) × S`,

carrying a value, an outer state slot, and an independent inner state slot.
Flattening is the act of *tying the inner slot to the outer computation*: the
inner slot is no longer free, it must equal `σ p`, where `σ : X × S → S` is the
state-transition function of the first stage.

Linearly, that is a projection. Writing

* `Sect σ : ℝ[X × S] →ₗ ℝ[(X × S) × S]` for the linearisation of `p ↦ (p, σ p)`,
* `Flat : ℝ[(X × S) × S] →ₗ ℝ[X × S]` for the linearisation of `Prod.fst`,

we prove `Flat ∘ Sect σ = id`, so `π_σ := Sect σ ∘ Flat` is idempotent, and on
basis vectors

  `π_σ (δ_{(p, s)}) = δ_{(p, σ p)}`,

i.e. `π_σ` is precisely **the projection of the doubled state space onto the
graph of `σ`**. Its range has dimension `|X| · |S|` inside an ambient space of
dimension `|X| · |S|²`, and its trace equals `|X| · |S|`.

## The tensor-product form

`ℝ[(X × S) × S] ≅ ℝ[X × S] ⊗ ℝ[S]`, and under that identification `Flat` is
`id ⊗ ε`, where `ε : ℝ[S] → ℝ` is the **augmentation** `δ_s ↦ 1`
(`MuEqPi.Flat_eq_aug`). This is the correct construction of the map informally
described as "project onto the second tensor factor": there is no such thing as
a projection `V ⊗ W → W` for general modules, and the map that *is* meant here
is the one obtained by applying the augmentation of the free module `ℝ[S]` to
one factor and then removing the resulting `ℝ` with the unitor.

## Main results

* `MuEqPi.Flat_comp_Sect` : `Flat ∘ Sect σ = id`.
* `MuEqPi.proj_isIdempotentElem` : `π_σ ∘ π_σ = π_σ`.
* `MuEqPi.proj_ne_id` : the projection is proper as soon as `S` is nontrivial.
* `MuEqPi.finrank_range_proj`, `MuEqPi.trace_proj` : `rank π_σ = tr π_σ = |X|·|S|`.
* `MuEqPi.Flat_eq_aug` : the tensor-product form of `Flat`.
-/

universe u

namespace MuEqPi

variable {S X : Type u}

/-- The **doubled configuration set** `(X × S) × S`: a configuration together
with a second, a priori unconstrained, state slot.

Note `DConf S X` is literally `Conf S (Conf S X)`, which is why the machinery of
`MuEqPi.Linearization` applies to it verbatim. -/
abbrev DConf (S X : Type u) : Type u := Conf S X × S

/-- The free real vector space on doubled configurations. -/
abbrev DConfSpace (S X : Type u) : Type u := DConf S X →₀ ℝ

/-- The graph embedding of a state-transition function `σ : X × S → S`. -/
def graph (σ : Conf S X → S) : Conf S X → DConf S X := fun p => (p, σ p)

/-- Forgetting the inner state slot. -/
def dropInner : DConf S X → Conf S X := Prod.fst

@[simp] theorem graph_apply (σ : Conf S X → S) (p : Conf S X) :
    graph σ p = (p, σ p) := rfl

@[simp] theorem dropInner_apply (q : DConf S X) : dropInner q = q.1 := rfl

/-- The graph is a section of the projection, at the level of index sets. -/
theorem dropInner_comp_graph (σ : Conf S X → S) :
    dropInner ∘ graph σ = (id : Conf S X → Conf S X) := rfl

/-- The set-theoretic image of `graph σ` — the graph of `σ` — indexes a basis of
the range of the linear projection built below. -/
theorem graph_injective (σ : Conf S X → S) : Function.Injective (graph σ) :=
  fun _ _ h => congrArg Prod.fst h

/-! ### The two linear maps -/

/-- `Flat`: linearisation of "forget the inner state slot". -/
noncomputable def Flat (S X : Type u) : DConfSpace S X →ₗ[ℝ] ConfSpace S X :=
  lin dropInner

/-- `Sect σ`: linearisation of the graph embedding of the transition function
`σ`. It writes the state that the computation actually produces into the
previously free inner slot. -/
noncomputable def Sect (σ : Conf S X → S) : ConfSpace S X →ₗ[ℝ] DConfSpace S X :=
  lin (graph σ)

@[simp] theorem Flat_single (q : DConf S X) (r : ℝ) :
    Flat S X (Finsupp.single q r) = Finsupp.single q.1 r := by
  simp [Flat]

@[simp] theorem Sect_single (σ : Conf S X → S) (p : Conf S X) (r : ℝ) :
    Sect σ (Finsupp.single p r) = Finsupp.single (p, σ p) r := by
  simp [Sect]

/-- **`Sect σ` is a section of `Flat`.** This is the linear shadow of the monad
law `μ ∘ Tη = id` (`MuEqPi.St.mu_map_eta`). -/
theorem Flat_comp_Sect (σ : Conf S X → S) :
    Flat S X ∘ₗ Sect σ = LinearMap.id := by
  rw [Flat, Sect, ← lin_comp, dropInner_comp_graph, lin_id]

theorem Sect_injective (σ : Conf S X → S) : Function.Injective (Sect σ) := by
  have h : Function.LeftInverse (Flat S X) (Sect σ) := fun v => by
    simpa using congrArg (fun L : ConfSpace S X →ₗ[ℝ] ConfSpace S X => L v)
      (Flat_comp_Sect σ)
  exact h.injective

/-! ### The projection -/

/-- **The flattening projection** `π_σ = Sect σ ∘ Flat` on the doubled
configuration space. -/
noncomputable def proj (σ : Conf S X → S) : DConfSpace S X →ₗ[ℝ] DConfSpace S X :=
  Sect σ ∘ₗ Flat S X

/-- The defining formula: `π_σ` overwrites the free inner state slot by the
value the transition function prescribes. -/
@[simp] theorem proj_single (σ : Conf S X → S) (q : DConf S X) (r : ℝ) :
    proj σ (Finsupp.single q r) = Finsupp.single (q.1, σ q.1) r := by
  simp [proj]

/-- **`π_σ` is idempotent.** -/
theorem proj_comp_proj (σ : Conf S X → S) :
    proj σ ∘ₗ proj σ = proj σ := by
  show (Sect σ ∘ₗ Flat S X) ∘ₗ (Sect σ ∘ₗ Flat S X) = Sect σ ∘ₗ Flat S X
  rw [LinearMap.comp_assoc, ← LinearMap.comp_assoc (Flat S X), Flat_comp_Sect,
    LinearMap.id_comp]

theorem proj_isIdempotentElem (σ : Conf S X → S) : IsIdempotentElem (proj σ) :=
  proj_comp_proj σ

/-- `π_σ` restricted to its range is the identity. -/
theorem proj_comp_Sect (σ : Conf S X → S) :
    proj σ ∘ₗ Sect σ = Sect σ := by
  show (Sect σ ∘ₗ Flat S X) ∘ₗ Sect σ = Sect σ
  rw [LinearMap.comp_assoc, Flat_comp_Sect, LinearMap.comp_id]

/-- The range of `π_σ` is the image of the graph embedding. -/
theorem range_proj (σ : Conf S X → S) :
    LinearMap.range (proj σ) = LinearMap.range (Sect σ) := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact ⟨Flat S X v, rfl⟩
  · rintro _ ⟨v, rfl⟩
    exact ⟨Sect σ v, congrArg (fun L : ConfSpace S X →ₗ[ℝ] DConfSpace S X => L v)
      (proj_comp_Sect σ)⟩

/-- **The projection is proper**: it is not the identity as soon as some inner
state slot disagrees with the value prescribed by `σ`. -/
theorem proj_ne_id_of_exists (σ : Conf S X → S) (h : ∃ q : DConf S X, σ q.1 ≠ q.2) :
    proj σ ≠ LinearMap.id := by
  obtain ⟨q, hq⟩ := h
  intro hproj
  have h1 : Finsupp.single (q.1, σ q.1) (1 : ℝ) = Finsupp.single q (1 : ℝ) := by
    simpa using congrArg (fun L : DConfSpace S X →ₗ[ℝ] DConfSpace S X =>
      L (Finsupp.single q (1 : ℝ))) hproj
  exact hq (congrArg Prod.snd (Finsupp.single_left_injective one_ne_zero h1))

/-- Whenever the state type has at least two elements, the flattening projection
is a proper projection: monadic flattening really does destroy information. -/
theorem proj_ne_id [Nontrivial S] [Nonempty X] (σ : Conf S X → S) :
    proj σ ≠ LinearMap.id := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨s⟩ : Nonempty S := inferInstance
  obtain ⟨s₂, hs₂⟩ := exists_ne (σ (x, s))
  exact proj_ne_id_of_exists σ ⟨((x, s), s₂), Ne.symm hs₂⟩

/-! ### Dimension count

Over a finite value type and a finite state type everything is
finite-dimensional and the projection can be measured. -/

section Finite

variable [Fintype X] [Fintype S]

@[simp] theorem finrank_confSpace :
    Module.finrank ℝ (ConfSpace S X) = Fintype.card X * Fintype.card S := by
  simp [ConfSpace, Module.finrank_finsupp_self]

@[simp] theorem finrank_dconfSpace :
    Module.finrank ℝ (DConfSpace S X) = Fintype.card X * Fintype.card S * Fintype.card S := by
  simp [DConfSpace, Module.finrank_finsupp_self, mul_assoc]

/-- The range of the flattening projection is linearly isomorphic to the space
of *flat* configurations. This is the linear form of "`T` is a retract of `T²`". -/
noncomputable def rangeProjEquiv (σ : Conf S X → S) :
    ConfSpace S X ≃ₗ[ℝ] LinearMap.range (proj σ) :=
  (LinearEquiv.ofInjective (Sect σ) (Sect_injective σ)).trans
    (LinearEquiv.ofEq _ _ (range_proj σ).symm)

/-- **Rank of the flattening projection.** -/
theorem finrank_range_proj (σ : Conf S X → S) :
    Module.finrank ℝ (LinearMap.range (proj σ)) = Fintype.card X * Fintype.card S := by
  rw [← (rangeProjEquiv σ).finrank_eq, finrank_confSpace]

/-- **Trace of the flattening projection.** For an idempotent operator the trace
counts the dimension of the range, so the trace of `π_σ` is the number of flat
configurations — independent of `σ`. -/
theorem trace_proj (σ : Conf S X → S) :
    LinearMap.trace ℝ (DConfSpace S X) (proj σ) =
      ((Fintype.card X * Fintype.card S : ℕ) : ℝ) := by
  -- Freeness of a subspace of a `Finsupp` is not found by instance search here
  -- (the `AddCommMonoid` diamond `Finsupp.instAddCommGroup` vs
  -- `Finsupp.instAddCommMonoid` blocks unification), so supply it by hand.
  haveI : Module.Free ℝ ↥(LinearMap.range (proj σ)) :=
    Module.Free.of_divisionRing ℝ ↥(LinearMap.range (proj σ))
  haveI : Module.Free ℝ ↥(LinearMap.ker (proj σ)) :=
    Module.Free.of_divisionRing ℝ ↥(LinearMap.ker (proj σ))
  rw [(LinearMap.IsIdempotentElem.isProj_range _ (proj_isIdempotentElem σ)).trace,
    finrank_range_proj]

/-- **The information destroyed by flattening**, measured in dimensions:
`|X| · |S| · (|S| - 1)`. -/
theorem finrank_ker_proj (σ : Conf S X → S) :
    Module.finrank ℝ (LinearMap.ker (proj σ)) =
      Fintype.card X * Fintype.card S * (Fintype.card S - 1) := by
  have h := LinearMap.finrank_range_add_finrank_ker (proj σ)
  rw [finrank_range_proj, finrank_dconfSpace] at h
  have key : Fintype.card X * Fintype.card S * (Fintype.card S - 1)
        + Fintype.card X * Fintype.card S
      = Fintype.card X * Fintype.card S * Fintype.card S := by
    cases hS : Fintype.card S with
    | zero => simp
    | succ k => simp only [Nat.add_sub_cancel]; ring
  omega

end Finite

/-! ### The tensor-product form: `Flat = id ⊗ ε`

The informal claim is that flattening is a map
`(ℝ^S ⊗ ℝ^S) ⊗ F(X) → ℝ^S ⊗ F(X)` obtained by "projecting onto the second
tensor factor". No such projection exists for general modules. What does exist,
because `ℝ[S]` is *free* on `S`, is the augmentation `ε : ℝ[S] → ℝ`; the map
actually meant is `id ⊗ ε` followed by the unitor `V ⊗ ℝ ≅ V`. The next results
make that precise and prove it agrees with `Flat`. -/

/-- The **augmentation** `ε : ℝ[S] → ℝ`, `δ_s ↦ 1`. It is the counit of the
canonical coalgebra structure on a free module, and it is the correct
replacement for the (nonexistent) projection of a tensor product onto a factor. -/
noncomputable def aug (S : Type u) : (S →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ => 1)

@[simp] theorem aug_single (s : S) (r : ℝ) : aug S (Finsupp.single s r) = r := by
  simp [aug]

/-- `ℝ[X × S] ⊗ ℝ[S] ≅ ℝ[(X × S) × S]`: the doubled configuration space really
is "the configuration space tensored with one more copy of the state space". -/
noncomputable def dconfTensorEquiv (S X : Type u) :
    TensorProduct ℝ (ConfSpace S X) (S →₀ ℝ) ≃ₗ[ℝ] DConfSpace S X :=
  finsuppTensorFinsupp' ℝ (Conf S X) S

/-- **`Flat` is `id ⊗ ε` up to the unitor.** -/
theorem Flat_eq_aug (S X : Type u) :
    Flat S X =
      (TensorProduct.rid ℝ (ConfSpace S X) ∘ₗ
        TensorProduct.map LinearMap.id (aug S)) ∘ₗ
          (dconfTensorEquiv S X).symm.toLinearMap := by
  apply Finsupp.lhom_ext
  rintro ⟨p, s⟩ r
  simp [dconfTensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul,
    Finsupp.smul_single]

/-- `Sect σ` in tensor form: it duplicates the configuration and writes `σ p`
into the new state coordinate. For the state-preserving transition
`σ = Prod.snd` this is exactly the comultiplication `δ_s ↦ δ_s ⊗ δ_s`, i.e. the
"copy the state" map of the informal account. -/
theorem Sect_tensor (σ : Conf S X → S) (p : Conf S X) (r : ℝ) :
    (dconfTensorEquiv S X).symm (Sect σ (Finsupp.single p r))
      = TensorProduct.tmul ℝ (Finsupp.single p 1) (Finsupp.single (σ p) r) := by
  simp [dconfTensorEquiv, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-! ### The state-preserving (reader) fragment

When the first stage does not modify the state, `σ = Prod.snd`, and the graph of
`σ` is the diagonal of `S × S`. The projection is then literally "collapse the
two state slots onto the diagonal" — the picture the informal account describes. -/

/-- For the state-preserving transition, `π` projects onto the diagonal. -/
@[simp] theorem proj_snd_single (x : X) (s₁ s₂ : S) (r : ℝ) :
    proj (Prod.snd : Conf S X → S) (Finsupp.single ((x, s₁), s₂) r)
      = Finsupp.single ((x, s₁), s₁) r := by
  simp

end MuEqPi
