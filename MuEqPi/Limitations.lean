/-
Copyright (c) 2025 Jinu Jang. All rights reserved.
Released under the MIT license.
-/
import MuEqPi.Projection

/-!
# How much of this is really about the state monad, or about linear algebra?

The README lists limitations of the development. This file turns two of them
from claims into theorems, so that the boundary of the result is machine-checked
rather than asserted.

## 1. The split idempotent is not about the state monad

`St.collapse_idem` — that `Tη ∘ μ` is an idempotent on `T²` — reads like a fact
about the state monad. It is not. It is a restatement of the monad law
`μ ∘ Tη = id`, so it holds verbatim for *every* lawful monad
(`mcollapse_idem`), and `St.collapse` is literally an instance of the generic
construction (`St.collapse_eq_mcollapse`).

Nothing specific to `S → X × S` is used or needed.

## 2. The projection is not about linear algebra

`π_σ` is an idempotent linear operator, but it carries no information that is not
already present in an idempotent *function on a finite set*: it is exactly the
linearisation of `q ↦ (q.1, σ q.1)` (`proj_eq_lin_setIdem`), whose idempotence
holds by `rfl` (`setIdem_comp_setIdem`).

Consequently the matrix of `π_σ` is a `0`–`1` matrix with a single `1` in each
column, its spectrum is contained in `{0, 1}` for the trivial reason, and its
trace counts the fixed points of a set map (`fixedPoints_setIdem`) — which is
where `rank π_σ = |X| · |S|` really comes from. The vector space is bookkeeping.

This is the honest limit of the "geometric" reading. A monad whose linearisation
is *not* a `0`–`1` matrix — the distribution monad, whose Kleisli arrows become
stochastic matrices — is where a linear model would begin to carry content of its
own.
-/

universe u

namespace MuEqPi

/-! ### 1. Genericity: the split idempotent for an arbitrary lawful monad -/

section GenericMonad

variable {m : Type u → Type u} [Monad m] [LawfulMonad m] {A : Type u}

/-- `Tη ∘ μ` for an arbitrary monad, written with `Monad` operations. -/
def mcollapse (t : m (m A)) : m (m A) := pure <$> (t >>= id)

/-- The monad law `μ ∘ Tη = id`, for an arbitrary lawful monad. -/
theorem mjoin_map_pure (t : m A) : ((pure <$> t : m (m A)) >>= id) = t := by
  simp

/-- **The idempotence of `Tη ∘ μ` holds for every lawful monad.** So
`St.collapse_idem` says nothing about the state monad in particular. -/
theorem mcollapse_idem (t : m (m A)) : mcollapse (mcollapse t) = mcollapse t := by
  simp [mcollapse]

end GenericMonad

/-- The state monad's collapse operator is literally the generic one. -/
theorem St.collapse_eq_mcollapse {S X : Type u} :
    (St.collapse : St S (St S X) → St S (St S X)) = mcollapse :=
  rfl

/-! ### 2. Sharpness: the projection is a linearised set map -/

section SetLevel

variable {S X : Type u}

/-- The idempotent **function on a set** of which `π_σ` is the linear shadow:
overwrite the free inner state slot with the value the transition function
prescribes. -/
def setIdem (σ : Conf S X → S) : DConf S X → DConf S X := fun q => (q.1, σ q.1)

@[simp] theorem setIdem_apply (σ : Conf S X → S) (q : DConf S X) :
    setIdem σ q = (q.1, σ q.1) := rfl

/-- Its idempotence is definitional — no linear algebra is involved. -/
theorem setIdem_comp_setIdem (σ : Conf S X → S) :
    setIdem σ ∘ setIdem σ = setIdem σ := rfl

/-- **`π_σ` is exactly the linearisation of `setIdem σ`.** Hence `proj_comp_proj`
is the image under `lin` of `setIdem_comp_setIdem`, and the linear model adds no
information beyond the set-level one. -/
theorem proj_eq_lin_setIdem (σ : Conf S X → S) : proj σ = lin (setIdem σ) := by
  rw [proj, Sect, Flat, ← lin_comp]
  rfl

/-- The fixed points of `setIdem σ` are the graph of `σ`. Since the linearisation
of a set map has trace equal to the number of its fixed points, this — and not
any linear-algebraic phenomenon — is the source of `rank π_σ = tr π_σ = |X|·|S|`
(`finrank_range_proj`, `trace_proj`). -/
theorem fixedPoints_setIdem (σ : Conf S X → S) :
    {q : DConf S X | setIdem σ q = q} = Set.range (graph σ) := by
  ext q
  constructor
  · intro h
    exact ⟨q.1, h⟩
  · rintro ⟨p, rfl⟩
    rfl

/-- Restated: `π_σ` sends each basis vector to a basis vector, so its matrix is a
`0`–`1` matrix with exactly one `1` per column. -/
theorem proj_single_basis (σ : Conf S X → S) (q : DConf S X) :
    ∃ q' : DConf S X, proj σ (Finsupp.single q (1 : ℝ)) = Finsupp.single q' (1 : ℝ) :=
  ⟨setIdem σ q, by rw [proj_eq_lin_setIdem, lin_single]⟩

end SetLevel

end MuEqPi
