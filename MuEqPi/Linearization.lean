/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.Kleisli
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.DirectSum.Finsupp

/-!
# The linearisation functor `Kl(T_S) ⥤ Vect_ℝ`

`MuEqPi.Kleisli` identifies a Kleisli arrow `X ⟶ Y` with a plain function
between the *configuration sets* `X × S → Y × S`. Applying the free real vector
space construction to configurations turns such a function into a linear map,
and — because uncurrying already turned Kleisli composition into function
composition — this assignment is functorial.

The resulting functor

  `Lin S : Kl(T_S) ⥤ ModuleCat ℝ`,  `X ↦ ℝ[X × S] ≅ ℝ[X] ⊗ ℝ[S]`

is the honest version of the "functor `F : Kl(T_S) → Vect_ℝ`" of the informal
statement. Two facts about it are proved here, and they cut in opposite
directions:

* `MuEqPi.instFaithfulLin` : `Lin S` is **faithful**. No information is lost:
  distinct computations have distinct matrices. This is what licenses reasoning
  about computations through their linear models.
* `MuEqPi.two_smul_id_not_lin` : `Lin S` is **not full**. The image consists of
  the `0`–`1` matrices with exactly one `1` per column; a generic linear map,
  even `2 • id`, is not the linearisation of anything. So the vector space model
  is a strict enlargement, not a re-description.

Stating both is the point. A faithful-but-not-full embedding is exactly the
situation in which a linear-algebraic invariant can say something about
computations, while linear-algebraic *constructions* need not stay inside the
computational world.
-/

universe u

namespace MuEqPi

open CategoryTheory

variable {S X Y Z : Type u}

/-- A **configuration**: a value together with a state. `Kl(T_S)`-arrows are
exactly the functions between configuration sets. -/
abbrev Conf (S X : Type u) : Type u := X × S

/-- The free real vector space on configurations, `ℝ[X × S]`. -/
abbrev ConfSpace (S X : Type u) : Type u := Conf S X →₀ ℝ

/-- Linearisation of a function between configuration sets: the `0`–`1` matrix
that sends the basis vector `δ_p` to `δ_{g p}`. -/
noncomputable def lin (g : Conf S X → Conf S Y) : ConfSpace S X →ₗ[ℝ] ConfSpace S Y :=
  Finsupp.lmapDomain ℝ ℝ g

@[simp] theorem lin_single (g : Conf S X → Conf S Y) (p : Conf S X) (r : ℝ) :
    lin g (Finsupp.single p r) = Finsupp.single (g p) r := by
  simp [lin, Finsupp.mapDomain_single]

theorem lin_id : lin (id : Conf S X → Conf S X) = LinearMap.id :=
  Finsupp.lmapDomain_id ..

theorem lin_comp (g₁ : Conf S X → Conf S Y) (g₂ : Conf S Y → Conf S Z) :
    lin (g₂ ∘ g₁) = (lin g₂).comp (lin g₁) :=
  Finsupp.lmapDomain_comp ..

/-- **Linearisation is injective on functions.** This is the engine behind
faithfulness of the functor. -/
theorem lin_injective :
    Function.Injective (lin : (Conf S X → Conf S Y) → ConfSpace S X →ₗ[ℝ] ConfSpace S Y) := by
  intro g₁ g₂ h
  funext p
  have h₁ : Finsupp.single (g₁ p) (1 : ℝ) = Finsupp.single (g₂ p) (1 : ℝ) := by
    simpa using congrArg (fun L : ConfSpace S X →ₗ[ℝ] ConfSpace S Y =>
      L (Finsupp.single p (1 : ℝ))) h
  exact Finsupp.single_left_injective one_ne_zero h₁

/-- The **linearisation functor** `Kl(T_S) ⥤ Vect_ℝ`. -/
noncomputable def Lin (S : Type u) : Kl S ⥤ ModuleCat.{u} ℝ where
  obj X := ModuleCat.of ℝ (ConfSpace S X)
  map {X Y} f := ModuleCat.ofHom (lin (threadEquiv S X Y f))
  map_id X := by
    rw [show threadEquiv S X X (𝟙 X) = id from rfl, lin_id, ModuleCat.ofHom_id]
  map_comp {X Y Z} f g := by
    rw [show threadEquiv S X Z (f ≫ g) = threadEquiv S Y Z g ∘ threadEquiv S X Y f from rfl,
      lin_comp, ModuleCat.ofHom_comp]

@[simp] theorem Lin_obj (X : Kl S) :
    (Lin S).obj X = ModuleCat.of ℝ (ConfSpace S X) := rfl

@[simp] theorem Lin_map_hom {X Y : Kl S} (f : X ⟶ Y) :
    ((Lin S).map f).hom = lin (threadEquiv S X Y f) := rfl

/-- On basis vectors, `Lin` does exactly what it should: run the computation. -/
theorem Lin_map_single {X Y : Kl S} (f : X ⟶ Y) (x : X) (s : S) (r : ℝ) :
    ((Lin S).map f).hom (Finsupp.single (x, s) r) = Finsupp.single (f x s) r := by
  show lin (threadEquiv S X Y f) (Finsupp.single (x, s) r) = Finsupp.single (f x s) r
  simp

/-- **The linearisation functor is faithful.** -/
instance instFaithfulLin : (Lin S).Faithful where
  map_injective {X Y} {f g} h := by
    have h' : lin (threadEquiv S X Y f) = lin (threadEquiv S X Y g) :=
      congrArg ModuleCat.Hom.hom h
    exact (threadEquiv S X Y).injective (lin_injective h')

/-- **The linearisation functor is not full.** The scalar `2` times the identity
is a linear endomorphism of `ℝ[X × S]` that is not the linearisation of any
function on configurations, hence not in the image of `Lin S`. -/
theorem two_smul_id_not_lin (p : Conf S X) :
    ¬ ∃ g : Conf S X → Conf S X, lin g = (2 : ℝ) • LinearMap.id := by
  rintro ⟨g, hg⟩
  have h : Finsupp.single (g p) (1 : ℝ) = Finsupp.single p (2 : ℝ) := by
    have := congrArg (fun L : ConfSpace S X →ₗ[ℝ] ConfSpace S X =>
      L (Finsupp.single p (1 : ℝ))) hg
    simpa [Finsupp.smul_single] using this
  rw [Finsupp.single_eq_single_iff] at h
  norm_num at h

/-!
### The tensor decomposition promised by the informal statement

`ℝ[X × S] ≅ ℝ[X] ⊗_ℝ ℝ[S]`. So the object part of `Lin S` really is
"`F(X)` tensored with the state space `ℝ^S`", and the linear operators
constructed in `MuEqPi.Projection` can be read either way.
-/

/-- `ℝ[X] ⊗ ℝ[S] ≅ ℝ[X × S]`. -/
noncomputable def confTensorEquiv (S X : Type u) :
    TensorProduct ℝ (X →₀ ℝ) (S →₀ ℝ) ≃ₗ[ℝ] ConfSpace S X :=
  finsuppTensorFinsupp' ℝ X S

@[simp] theorem confTensorEquiv_tmul (S : Type u) (X : Type u) (x : X) (s : S) (a b : ℝ) :
    confTensorEquiv S X (TensorProduct.tmul ℝ (Finsupp.single x a) (Finsupp.single s b))
      = Finsupp.single (x, s) (a * b) :=
  finsuppTensorFinsupp'_single_tmul_single ..

end MuEqPi
