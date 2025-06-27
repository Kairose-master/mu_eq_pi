/-
  F : (State monad on S)  ⇒  VecSpace
  ───────────────────────────────────
  • on objects :  ℝ^S ⊗ ℝ^X
  • on maps    :  id ⊗ Free.map(h)
  • split idempotent
        P  : (ℝ^S ⊗ ℝ^S) ⊗ ℝ^X → ℝ^S ⊗ ℝ^X      (drop first state)
        i  : ℝ^S ⊗ ℝ^X → (ℝ^S ⊗ ℝ^S) ⊗ ℝ^X      (duplicate state)
        e  = i ∘ P   with  e ∘ e = e
  Collapse theorem (Lean‑friendly flavour):
        e is idempotent   ∧   P ∘ i = id
-/
import Mathlib.Data.Finsupp
import Mathlib.LinearAlgebra.TensorProduct
import Jinu.StateMonad
import Jinu.VecSpace

open scoped TensorProduct
open TensorProduct

universe u v w

namespace Jinu

variable {S : Type u} {X Y Z : Type v}

/-! ### Free vector space ─ plain finsupp wrapper -/
def Free (α : Type v) : VSpace :=
{ carrier := α →₀ ℝ,
  _inst   := inferInstance }

/-! ### F on objects -/
def FObj : VSpace :=
{ carrier := (Free S).carrier ⊗[ℝ] (Free X).carrier,
  _inst   := inferInstance }

/-! ### F on morphisms -/
def FMap (h : X → Y) :
    (Free S).carrier ⊗[ℝ] (Free X).carrier →ₗ[ℝ]
    (Free S).carrier ⊗[ℝ] (Free Y).carrier :=
  TensorProduct.map LinearMap.id
    ((Finsupp.lmapDomain ℝ ℝ h).toLinearMap)

lemma FMap_id :
  FMap (S:=S) (X:=X) (Y:=X) (id) = LinearMap.id := by
  ext v; simp [FMap]

lemma FMap_comp (h₁ : X → Y) (h₂ : Y → Z) :
    FMap (S:=S) (X:=X) (Y:=Z) (h₂ ∘ h₁) =
      (FMap (S:=S) (X:=Y) (Y:=Z) h₂).comp
      (FMap (S:=S) (X:=X) (Y:=Y) h₁) := by
  ext v; simp [FMap, Function.comp]

/-! ## Split‑idempotent machinery P, i, e -/

/-- P : drop the *first* state basis element. -/
def stateDrop :
    ((Free S).carrier ⊗[ℝ] (Free S).carrier) ⊗[ℝ] (Free X).carrier
      →ₗ[ℝ] (Free S).carrier ⊗[ℝ] (Free X).carrier :=
by
  refine
    TensorProduct.lift
      { toLinearMap :=
          { toLinearMap := fun t ↦ by
              -- rearrange and apply second‑projection
              simpa using
                TensorProduct.map
                  (TensorProduct.snd ℝ (Free S).carrier (Free S).carrier)
                  LinearMap.id t,
            map_add'  := by intros; simp,
            map_smul' := by intros; simp },
        map_add'  := by intros; simp,
        map_smul' := by intros; simp }

/-- i : duplicate the state basis element (diagonal). -/
def stateDup :
    (Free S).carrier ⊗[ℝ] (Free X).carrier
      →ₗ[ℝ] ((Free S).carrier ⊗[ℝ] (Free S).carrier) ⊗[ℝ] (Free X).carrier :=
by
  -- e_s ⊗ δ_x ↦ (e_s ⊗ e_s) ⊗ δ_x
  refine
    TensorProduct.lift
      { toLinearMap :=
          { toLinearMap := fun t ↦ by
              -- pattern‑match on basis tensors
              rcases TensorProduct.exists_tmul (M:=ℝ) t with ⟨a, b, rfl⟩
              simpa using (TensorProduct.tmul ℝ _ _) },
        map_add'  := by intros; simp,
        map_smul' := by intros; simp }

/-- e := i ∘ P, the genuine idempotent. -/
def stateIdem :
    ((Free S).carrier ⊗[ℝ] (Free S).carrier) ⊗[ℝ] (Free X).carrier
      →ₗ[ℝ] ((Free S).carrier ⊗[ℝ] (Free S).carrier) ⊗[ℝ] (Free X).carrier :=
  stateDup.comp stateDrop

/-! ### Split identities -/
lemma stateDrop_stateDup : stateDrop (S:=S) (X:=X) ∘ₗ stateDup (S:=S) (X:=X) =
  LinearMap.id := by
  -- immediate on basis tensors
  ext t
  -- simplification relies on TensorProduct.map_tmul
  simp [stateDrop, stateDup, TensorProduct.map_tmul]

lemma stateIdem_idempotent :
    stateIdem (S:=S) (X:=X) ∘ₗ stateIdem (S:=S) (X:=X) =
      stateIdem (S:=S) (X:=X) := by
  -- e ∘ e = e  because  P ∘ i = id
  simpa [stateIdem, LinearMap.comp_assoc, stateDrop_stateDup]

/-! ##  “Collapse theorem” (Lean level)
      We merely restate that `stateIdem` is idempotent and
      `stateDrop ∘ stateDup = id`.
-/
theorem collapse_theorem :
    (stateDrop (S:=S) (X:=X) ∘ₗ stateDup (S:=S) (X:=X) =
        LinearMap.id) ∧
    (stateIdem (S:=S) (X:=X) ∘ₗ stateIdem (S:=S) (X:=X) =
        stateIdem (S:=S) (X:=X)) :=
  ⟨stateDrop_stateDup, stateIdem_idempotent⟩

end Jinu
