# Lean → Math Interpretation

This appendix explains the mathematical meaning behind each Lean definition in the three core files of the *`mu_eq_pi`* project.  The goal is to help readers who are comfortable with traditional category‑theoretic notation but may not read Lean fluently.

---

## 0. Notation at a Glance

| Symbol      | Meaning                                                           |
| ----------- | ----------------------------------------------------------------- |
| `ℝ`         | Base field (the real numbers)                                     |
| `X →₀ ℝ`    | Finitely‑supported functions `X → ℝ` (free ℝ‑vector space on `X`) |
| `⊗[ℝ]`      | Algebraic tensor product over ℝ                                   |
| `LinearMap` | Lean’s bundled linear map ‑ a morphism in **Vect**                |
| `∘ₗ`        | Composition of linear maps                                        |

---

## 1. `FlattenFunctor.lean`

### 1.1  Purpose

Constructs the functor

```
F : (State monad on S) ⇒ Vect_ℝ
```

that sends a set `X` to `ℝ^S ⊗ ℝ^X` and turns the monad multiplication into a split idempotent.

### 1.2  Main Definitions

| Lean name       | Math object                     | Informal meaning                             |
| --------------- | ------------------------------- | -------------------------------------------- |
| `Free`          | `X ↦ ℝ^X`                       | Free vector space functor                    |
| `FObj`          | `ℝ^S ⊗ ℝ^X`                     | Object part of `F`                           |
| `FMap h`        | `id ⊗ ℝ[h]`                     | Morphism part of `F` (linear lift of `h`)    |
| `stateDrop Pₛₓ` | `(ℝ^S ⊗ ℝ^S) ⊗ ℝ^X → ℝ^S ⊗ ℝ^X` | Throw away the *outer* state basis element   |
| `stateDup iₛₓ`  | `ℝ^S ⊗ ℝ^X → (ℝ^S ⊗ ℝ^S) ⊗ ℝ^X` | Duplicate the state basis along the diagonal |
| `stateIdem eₛₓ` | `i ∘ P`                         | Genuine idempotent with `e² = e`             |

> **Semantic picture**   `P` realises the monad multiplication `μ` by discarding the first state component; `i` is its section.  Hence `F(μₓ) = eₛₓ`.

### 1.3  Key Lemmas

- `` : `P ∘ i = id`  (retraction)
- `` : `e ∘ e = e`  (split idempotent)
- `` bundles the two equalities above.

These equalities are exactly what the PDF calls *Collapse Theorem*.

---

## 2. `StateMonad.lean`

### 2.1  Purpose

Defines a *record* `StateMonadInst S` that fixes a state‑set `S` and realises the usual state monad

```
T_S X = S → (X × S)
```

with `pure` and `bind` together with the three standard monad laws.

### 2.2  Highlights

| Lean name                              | Math meaning                                        |
| -------------------------------------- | --------------------------------------------------- |
| `pure`                                 | Unit η : `X → T_S X`                                |
| `bind`                                 | Kleisli extension (multiplication + functor action) |
| `bind_pure`, `pure_bind`, `bind_assoc` | Monad laws (`η` left/right unit + associativity)    |

The file is intentionally minimal: proofs are elementary pattern matches, mirroring the textbook construction.

---

## 3. `VSpace.lean`

A *light‑weight wrapper* around Lean’s `Module ℝ`.  It exists solely to provide a short name `VSpace` and the notation `⟦V⟧` for the underlying type.  No extra theory is introduced here; all linear‑algebra properties are inherited from `Mathlib`.

---

## 4. How the Pieces Fit Together

1. \*\*`StateMonadInst` \*\* supplies the monad `T_S` in **Set**.
2. \*\*`FObj/FMap` \*\* lift sets and functions to vector spaces via `ℝ^S ⊗ –`.
3. `` realises the semantic content of the monad multiplication `μ` under `F`.
4. `` splits that projection, yielding the idempotent `e`.
5. `` shows `P ∘ i = id` and `e² = e`, i.e. the image of `μ` is captured by a split idempotent in **Vect**.

---

## 5. Pending Work

- The Lean proof that *every* monad law transports correctly through `F` is still in progress.
- A short note on how this split‑idempotent picture generalises to arbitrary CCCs will be added in a later patch.

Questions or suggestions are always welcome!

