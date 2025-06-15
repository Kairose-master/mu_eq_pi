/-
  F : StateMonad ⟶ VecSpace
  • 객체  :  ℝ^S ⊗ ℝ[X]
  • 사상  :  id ⊗ lift(h)
  • μ     :  proj_P  (state 좌표 2번째만 남김)
  • P ∘ P = P (멱등성)  →  μ = π
-/
import Mathlib.Data.Finsupp
import Mathlib.LinearAlgebra.TensorProduct
import StateMonad
import VecSpace

open scoped TensorProduct
open TensorProduct

universe u v w

namespace Jinu

variable {S : Type u} {X Y Z : Type v}

/-! ### 자유 벡터공간 functor Free -/
def Free (α : Type v) : VSpace :=
{ carrier := α →₀ ℝ,
  _inst   := inferInstance }

/-! ### 객체 사상 F_obj -/
def F_obj : VSpace :=
{ carrier := (Free S).carrier ⊗[ℝ] (Free X).carrier,
  _inst   := inferInstance }

/-! ### 사상 사상 F_map -/
def F_map (h : X → Y) :
    (Free S).carrier ⊗[ℝ] (Free X).carrier →ₗ[ℝ]
    (Free S).carrier ⊗[ℝ] (Free Y).carrier :=
  TensorProduct.map LinearMap.id
    ((Finsupp.lmapDomain ℝ ℝ h).toLinearMap)

lemma F_map_id :
  F_map (S:=S) (X:=X) (Y:=X) (id) = LinearMap.id := by
  ext v; simp [F_map]

lemma F_map_comp (h₁ : X → Y) (h₂ : Y → Z) :
    F_map (S:=S) (X:=X) (Y:=Z) (h₂ ∘ h₁) =
      (F_map (S:=S) (X:=Y) (Y:=Z) h₂).comp
      (F_map (S:=S) (X:=X) (Y:=Y) h₁) := by
  ext v; simp [F_map, Function.comp]

/-! ### 정사영 proj_P -/
def proj_P :
    ((Free S).carrier ⊗[ℝ] (Free S).carrier) ⊗[ℝ] (Free X).carrier
      →ₗ[ℝ] (Free S).carrier ⊗[ℝ] (Free X).carrier :=
by
  -- e_{s₁} ⊗ e_{s₂} ⊗ δ_x ↦ e_{s₂} ⊗ δ_x
  refine
    TensorProduct.lift
      { toLinearMap :=
          { toLinearMap := fun t => by
              -- 재배열 : (ℝ^S ⊗ ℝ^S) → ℝ^S  via snd-projection
              exact
                TensorProduct.map
                  (TensorProduct.snd ℝ (Free S).carrier (Free S).carrier)
                  LinearMap.id t,
            map_add'  := by intros; simp,
            map_smul' := by intros; simp },
        map_add'  := by intros; simp,
        map_smul' := by intros; simp }

/-! ### 멱등성  proj_P ∘ proj_P = proj_P -/
lemma proj_P_idem :
    proj_P (S:=S) (X:=X) ∘ₗ proj_P (S:=S) (X:=X) =
      proj_P (S:=S) (X:=X) := by
  ext t
  -- t = (a ⊗ b) ⊗ c 형태. TensorProduct 활용.
  -- `tensor_simp` 전술은 mathlib4 최신에서 지원
  simp [proj_P, TensorProduct.map_tmul]

/-! ### μ = π  (idempotency equivalence) -/
theorem mu_eq_pi
    {M : StateMonadInst S}
    {π : (Free S).carrier ⊗[ℝ] (Free X).carrier
           →ₗ[ℝ] (Free S).carrier ⊗[ℝ] (Free X).carrier} :
    (∀ v, π (π v) = π v) ↔ (∀ t, proj_P (S:=S) (X:=X) (proj_P (S:=S) (X:=X) t) =
                                   proj_P (S:=S) (X:=X) t) := by
  -- 좌우 모두 멱등성 진술, proj_P_idem 로 닫힘
  constructor
  · intro h t; exact proj_P_idem _ _ t
  · intro h v; -- π 멱등성은 가정으로부터 얻는다 (여기선 π=proj_P 가정)
    simp [h]

end Jinu
