/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.StateMonad
import Mathlib.CategoryTheory.Category.KleisliCat
import Mathlib.CategoryTheory.Equivalence

/-!
# `Kl(T_S)` is isomorphic to the category of state-threading functions

The Kleisli category of the state monad has, as morphisms `X ⟶ Y`, the functions
`X → S → Y × S`. Uncurrying identifies these with plain functions `X × S → Y × S`,
and — this is the content — uncurrying turns *Kleisli composition into ordinary
composition of functions*.

That is the structural fact that makes a linear model possible at all. A Kleisli
arrow looks higher-order (`X → S → Y × S`), and higher-order data does not embed
in a finite-dimensional vector space. After uncurrying it is a function between
the *plain sets* `X × S` and `Y × S`, and functions between sets linearise: this
is the free-vector-space functor, used in `MuEqPi.Linearization`.

Concretely, `Kl(T_S)` is the co-Kleisli category of the comonad `- × S`.

## Main results

* `MuEqPi.ThreadCat` : the category of state-threading functions.
* `MuEqPi.uncur` : the identity-on-objects functor `Kl(T_S) ⥤ 𝒮_S`.
* `MuEqPi.instFullUncur`, `instFaithfulUncur`, `instEssSurjUncur` : it is full,
  faithful and (trivially) essentially surjective, hence an equivalence — in fact
  an isomorphism of categories.
* `MuEqPi.uncur_mu_map` : under this identification `μ` *is* composition.
-/

universe u

namespace MuEqPi

open CategoryTheory

variable {S X Y Z : Type u}

/-- The Kleisli category of the state monad `T_S`. -/
abbrev Kl (S : Type u) := KleisliCat (St S)

/-- The **state-threading category** `𝒮_S`: objects are types, and a morphism
`X ⟶ Y` is a plain function `X × S → Y × S`, composed as functions.

This is the co-Kleisli category of the product comonad `- × S`. -/
def ThreadCat (_S : Type u) := Type u

namespace ThreadCat

/-- Regard a type as an object of `𝒮_S`. -/
def mk (S : Type u) (X : Type u) : ThreadCat S := X

instance categoryStruct : CategoryStruct.{u} (ThreadCat S) where
  Hom X Y := X × S → Y × S
  id _ := _root_.id
  comp f g := g ∘ f

@[ext]
theorem hom_ext {X Y : ThreadCat S} {f g : X ⟶ Y} (h : ∀ p, f p = g p) : f = g :=
  funext h

instance category : Category.{u} (ThreadCat S) where
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_def (X : ThreadCat S) : 𝟙 X = _root_.id := rfl

@[simp] theorem comp_def {X Y Z : ThreadCat S} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = g ∘ f := rfl

end ThreadCat

/-- Uncurrying, as a bijection of hom-sets: a Kleisli arrow `X → S → Y × S` is
the same datum as a state-threading function `X × S → Y × S`. -/
@[simps]
def threadEquiv (S X Y : Type u) : (X → St S Y) ≃ (X × S → Y × S) where
  toFun f p := f p.1 p.2
  invFun g x s := g (x, s)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Uncurrying as an identity-on-objects functor `Kl(T_S) ⥤ 𝒮_S`. -/
def uncur (S : Type u) : Kl S ⥤ ThreadCat S where
  obj X := X
  map f := threadEquiv S _ _ f
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem uncur_obj (X : Kl S) : (uncur S).obj X = X := rfl

@[simp] theorem uncur_map {X Y : Kl S} (f : X ⟶ Y) (p : X × S) :
    (uncur S).map f p = f p.1 p.2 := rfl

instance instFaithfulUncur : (uncur S).Faithful where
  map_injective h := funext fun x => funext fun s => congrFun h (x, s)

instance instFullUncur : (uncur S).Full where
  map_surjective g := ⟨fun x s => g (x, s), rfl⟩

instance instEssSurjUncur : (uncur S).EssSurj where
  mem_essImage X := ⟨X, ⟨Iso.refl _⟩⟩

/-- **`Kl(T_S) ≃ 𝒮_S`.** The functor is bijective on objects and on hom-sets, so
this is in fact an isomorphism of categories, not merely an equivalence. -/
instance instIsEquivalenceUncur : (uncur S).IsEquivalence where

/-- The equivalence `Kl(T_S) ≌ 𝒮_S` packaged up. -/
noncomputable def threadEquivalence (S : Type u) : Kl S ≌ ThreadCat S :=
  (uncur S).asEquivalence

/-!
### `μ` is composition

`St.bind_eq_mu_map` says that Kleisli composition is `μ` applied to a functorial
image. The next lemma says that uncurrying sends that operation to plain
composition of functions. Together they justify the slogan that the state
monad's multiplication *is* the sequencing of two state-threading maps.
-/

/-- Under uncurrying, the action of `μ` is composition of functions. -/
theorem uncur_mu_map (f : X → St S Y) (k : Y → St S Z) :
    threadEquiv S X Z (fun x => St.mu (St.map k (f x)))
      = threadEquiv S Y Z k ∘ threadEquiv S X Y f := rfl

/-- The same statement phrased with `bind`. -/
theorem uncur_bind (f : X → St S Y) (k : Y → St S Z) :
    threadEquiv S X Z (fun x => St.bind (f x) k)
      = threadEquiv S Y Z k ∘ threadEquiv S X Y f := rfl

/-- Uncurrying sends the Kleisli identity `η` to the identity function. -/
theorem uncur_eta : threadEquiv S X X St.eta = _root_.id := rfl

end MuEqPi
