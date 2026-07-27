# Flattening the State Monad: a linear-algebraic model

A Lean 4 / mathlib formalisation of the sense in which the state monad's
multiplication `μ` is an **idempotent projection**.

Everything below is machine-checked. There are no `sorry`s and no custom axioms:
every theorem listed depends only on Lean's three standard axioms (`propext`,
`Classical.choice`, `Quot.sound`).

---

## The statement, precisely

Fix a state type `S`. The state monad is `T_S X = S → X × S`, with

```
η : X → T_S X                 η x = fun s => (x, s)
μ : T_S (T_S X) → T_S X       μ t = fun s => (t s).1 (t s).2
```

The slogan "monadic flattening is an idempotent projection" cannot be read
literally. `μ : T² ⇒ T` goes between two *different* functors, so `μ ∘ μ = μ`
does not typecheck. What is true is:

**1. `μ` is a split epimorphism.** The monad law `μ ∘ Tη = id` says `Tη` is a
section of `μ`. Hence

```
e := Tη ∘ μ : T² → T²
```

is an idempotent, `T` is the retract it splits off, and `e` is *proper* — it is
not the identity, so information really is destroyed
(`St.collapse_idem`, `St.collapse_ne_id`).

**2. Kleisli arrows are functions between plain sets.** Uncurrying gives an
isomorphism of categories

```
Kl(T_S)  ≅  𝒮_S ,   where 𝒮_S(X, Y) = (X × S → Y × S)
```

identity on objects, bijective on hom-sets, carrying Kleisli composition to
ordinary composition of functions (`uncur`, `instIsEquivalenceUncur`). `𝒮_S` is
the co-Kleisli category of the comonad `- × S`. This step is what makes a linear
model possible at all: a Kleisli arrow `X → S → Y × S` is higher-order and does
not embed in a vector space, but after uncurrying it is a function between the
sets `X × S` and `Y × S`, and functions between sets linearise.

**3. Linearisation is a faithful, non-full functor into `Vect_ℝ`.** Taking free
real vector spaces on configuration sets gives

```
Lin S : Kl(T_S) ⥤ ModuleCat ℝ ,   X ↦ ℝ[X × S] ≅ ℝ[X] ⊗ ℝ[S]
```

sending a computation to the 0–1 matrix `δ_p ↦ δ_{g p}`. It is **faithful**:
distinct computations have distinct matrices (`instFaithfulLin`). It is **not
full**: `2 • id` is linear but is not the linearisation of anything
(`two_smul_id_not_lin`). Both directions matter — faithfulness is what licenses
reasoning about computations through their matrices, and failure of fullness is
why the vector space model is a strict enlargement rather than a re-description.

**4. Flattening is projection onto a graph.** Before two stages are joined, the
second stage's input state is a free parameter, so the relevant index set is the
*doubled configuration set* `(X × S) × S`. A nested computation
`t : X ⟶ T_S T_S Y` determines

* a transition function `σ = outerNext t : X × S → S`, and
* a two-stage operator `expand t : (X × S) × S → Y × S`,

and — by definition, `threadEquiv_mu` —

```
μ ∘ t  =  expand t ∘ graph σ .
```

Flattening is *substitution of the transition function into the free inner
slot*. Linearising `graph σ` and `Prod.fst` gives

```
Sect σ : ℝ[X × S] → ℝ[(X × S) × S]        Flat : ℝ[(X × S) × S] → ℝ[X × S]
Flat ∘ Sect σ = id                         (Flat_comp_Sect)
π_σ := Sect σ ∘ Flat                       π_σ ∘ π_σ = π_σ   (proj_comp_proj)
π_σ (δ_{(p, s)}) = δ_{(p, σ p)}            (proj_single)
```

so `π_σ` is exactly **the projection of the doubled state space onto the graph
of the transition function**, and it is proper whenever `S` is nontrivial
(`proj_ne_id`).

**5. `μ = π`.** The two pictures fit into a commuting square (`mu_eq_pi`):

```
lin (expand t) ∘ π_σ  =  lin (μ ∘ t) ∘ Flat
```

— projecting onto the graph and then running is the same as flattening and then
running.

**6. The projection, measured.** For finite `X` and `S`
(`finrank_range_proj`, `trace_proj`, `finrank_ker_proj`):

```
dim ambient    = |X| · |S|²
rank π_σ       = |X| · |S|          (independent of σ)
tr  π_σ        = |X| · |S|
dim ker π_σ    = |X| · |S| · (|S| − 1)
```

The last line is the dimension count of what flattening destroys.

---

## The tensor form, and a correction

Under `ℝ[(X × S) × S] ≅ ℝ[X × S] ⊗ ℝ[S]` the operator `Flat` is
`id ⊗ ε` followed by the unitor, where `ε : ℝ[S] → ℝ` is the **augmentation**
`δ_s ↦ 1` (`Flat_eq_aug`).

This is worth spelling out because the natural-sounding description — "project
onto the second tensor factor" — does not name a real construction. There is no
map `V ⊗ W → W` for general modules. What exists here, and only because `ℝ[S]`
is *free* on `S`, is the augmentation; applying it to one factor and removing
the resulting `ℝ` with the unitor is the map actually meant. `Flat_eq_aug`
proves that this canonical description agrees with the basis description.

---

## File guide

| File | Contents |
|---|---|
| `MuEqPi/StateMonad.lean` | `T_S`, `η`, `μ`, `bind`; functor laws, naturality, the three monad laws; `Monad`/`LawfulMonad` instances; `μ` split epi; the idempotent `Tη ∘ μ` and its properness |
| `MuEqPi/Kleisli.lean` | the state-threading category `𝒮_S`; `uncur : Kl(T_S) ⥤ 𝒮_S` full, faithful, essentially surjective; `μ` as composition |
| `MuEqPi/Linearization.lean` | `lin`; the functor `Lin S : Kl(T_S) ⥤ ModuleCat ℝ`; faithfulness; failure of fullness; `ℝ[X × S] ≅ ℝ[X] ⊗ ℝ[S]` |
| `MuEqPi/Projection.lean` | `Flat`, `Sect σ`, `π_σ`; idempotence, properness, range, rank, trace, kernel dimension; the augmentation/tensor form |
| `MuEqPi/Collapse.lean` | `outerNext`, `expand`; `μ ∘ t = expand t ∘ graph σ`; the main square `mu_eq_pi`; a worked `S = Bool` example |
| `MuEqPi/Limitations.lean` | the boundary of the result, proved rather than asserted: the split idempotent holds for *every* lawful monad, and `π_σ` is a linearised set map |

---

## Building

```bash
lake exe cache get     # fetch prebuilt mathlib oleans
lake build
```

Pinned to `leanprover/lean4:v4.32.1` and mathlib `v4.32.1` (see `lean-toolchain`
and `lake-manifest.json`). There is no executable target; the library is the
artefact.

To re-audit the axiom footprint:

```lean
import MuEqPi
#print axioms MuEqPi.mu_eq_pi
```

---

## What is *not* claimed

Being explicit about the boundary is part of the point. The two sharpest
limitations are themselves theorems, in `MuEqPi/Limitations.lean`, so they can be
checked rather than taken on trust.

* **The split idempotent is not a fact about the state monad.** That `Tη ∘ μ` is
  idempotent is a restatement of the monad law `μ ∘ Tη = id`, so it holds for
  every lawful monad (`mcollapse_idem`), and `St.collapse` is literally an
  instance of the generic construction (`St.collapse_eq_mcollapse`). Nothing
  about `S → X × S` is used.

* **The projection is not a fact about linear algebra.** `π_σ` is exactly the
  linearisation of the idempotent *set map* `q ↦ (q.1, σ q.1)`
  (`proj_eq_lin_setIdem`), whose idempotence holds by `rfl`
  (`setIdem_comp_setIdem`). Its matrix is therefore a `0`–`1` matrix with one `1`
  per column (`proj_single_basis`), its spectrum lies in `{0, 1}` for the trivial
  reason, and `rank π_σ = tr π_σ = |X|·|S|` is a count of fixed points of a set
  map (`fixedPoints_setIdem`). The vector space is bookkeeping. A monad whose
  linearisation is *not* a `0`–`1` matrix — the distribution monad, whose Kleisli
  arrows become stochastic matrices — is where a linear model would start to
  carry content of its own.

* **`μ` itself is not idempotent.** It cannot be: its source and target are
  different types. Only the composite `Tη ∘ μ` is, and only on `T²`.
* **`T² X` is not linearised.** `T_S X` is a function space; `T_S (T_S X)`
  contains function-valued data and does not embed in a finite-dimensional
  vector space in any useful way. What is linearised are *hom-sets* — the
  configuration sets `X × S` and `(X × S) × S` — which are plain sets. Any claim
  to model `T²X` itself as a tensor product is where this subject goes wrong.
* **The projection depends on the computation.** `π_σ` is indexed by the
  transition function `σ`; there is no single canonical `π` doing the work of
  `μ` for all nested computations at once. Its *rank* and *trace*, however, are
  independent of `σ`.
* **`Lin` is not full**, so linear-algebraic constructions performed on the
  matrices need not correspond to computations.
* **No claim is made about language models, tensor "collapse", or any DSL.**
  Nothing of the sort is formalised here, and none of the theorems above bears
  on it.

---

## Errata relative to the earlier version of this repository

The previous `src/` tree did not compile, and several statements in it were not
merely unproved but false or ill-formed. Recording them is more useful than
quietly deleting them.

1. **`TensorProduct.snd` does not exist**, in mathlib or in mathematics: there is
   no natural linear map `V ⊗ W → W`. The old `proj_P` was built from it.
   Replaced by the augmentation construction (`aug`, `Flat_eq_aug`), which is
   canonical for free modules and provably agrees with the basis description.

2. **The old `mu_eq_pi` was vacuous.** It stated an `↔` whose right-hand side
   was an unconditional consequence of `proj_P_idem`, and whose forward
   direction discarded its hypothesis; it therefore said nothing about `π`.
   Replaced by the commuting square `mu_eq_pi`, which relates two independently
   defined operators.

3. **The old monad laws were stated about an arbitrary record**, `M :
   StateMonadInst S`, whose `pure` and `bind` fields were arbitrary functions
   with defaults. As stated, `bind_pure`/`pure_bind`/`bind_assoc` quantified over
   *all* such records and were false. Replaced by laws about the actual `η`, `μ`
   and `bind`, plus `Monad`/`LawfulMonad` instances tying them to Lean's
   hierarchy.

4. **`VSpace` was ill-typed**: `Module ℝ carrier` requires an `AddCommMonoid
   carrier` instance that the structure never supplied. Dropped in favour of
   mathlib's `ModuleCat ℝ`.

5. **`P ∘ P = P` for `P : (ℝ^S ⊗ ℝ^S) ⊗ F(X) → ℝ^S ⊗ F(X)` is not well-formed** —
   a map between different spaces cannot be idempotent. The corrected object is
   the endomorphism `π_σ` of `ℝ[X × S] ⊗ ℝ[S]`.

6. **The build was broken**: empty `lean-toolchain`, no library target in
   `lakefile.lean`, a `lake-manifest.json` pinning mathlib `master`, and a
   documented entry point `lake exe flatten_state_tensor` with no corresponding
   target. The project structure documented in the README (`Main.lean`,
   `Projection.lean`, `Collapse.lean`, `DSL.lean`) did not match the files that
   existed.

7. **Unsupported claims removed** — "formal integration with ETC and Kairosé
   DSL", "GPT tensor collapse", and "applying collapse projection to GPT/LLM
   token routing" were not formalised, and nothing here supports them.

---

## Citation

```bibtex
@misc{flatten-state-monad,
  author = {Jinu Jang},
  title  = {Flattening the State Monad: a linear-algebraic model},
  year   = {2025},
  note   = {Lean 4 formalisation, GitHub repository}
}
```

## License

MIT — see `license.md`.
