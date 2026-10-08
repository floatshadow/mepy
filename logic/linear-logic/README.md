# Linear Logic in Rocq: a tutorial

A literate Rocq development of **intuitionistic** and **classical linear
logic** and of a **linear type system** with the exponential `!`. Every
file is written to be read from top to bottom, with comments explaining
the ideas and custom notations that keep statements close to paper style.

## What is formalized

| | Intuitionistic (ILL) | Classical (CLL) |
|---|---|---|
| Formulas | `⊗ ⊸ 𝟙 & ⊤ ⊕ 𝟘 !`, `⊥` as a constant, `∼A := A ⊸ ⊥` | `⊗ ⅋ 𝟙 ⊥ & ⊤ ⊕ 𝟘 ! ?`, involutive `A^⊥`, `A ⊸ B := A^⊥ ⅋ B` |
| Sequents | `Γ ⊢ C`, one conclusion | `Γ ⊢ Δ`, two-sided |
| Rules | left and right rules, exchange, cut, `!` structural rules | left and right rules for every connective, including `!` and `?` (dereliction, weakening, contraction, promotion) |
| Semantics | intuitionistic phase spaces (stable closure operator) | classical phase spaces (pole, closure = `X^⊥⊥`) |
| Soundness | `Γ ⊢ A → Γ ⊨ A` | `Γ ⊢ Δ → Γ ⊨ Δ` |
| Completeness | `Γ ⊨ A → Γ ⊢cf A` | `Γ ⊨ Δ → Γ ⊢cf Δ` |
| Cut elimination | `Γ ⊢ A → Γ ⊢cf A` (Okada's semantic proof) | `Γ ⊢ Δ → Γ ⊢cf Δ` |
| Non-provability | counting model: no contraction, no weakening, no `∼∼A ⊢ A`, … | balance model ("the books must balance"), consistency |

The **comparison** chapter embeds ILL into CLL and proves that the
embedding is not conservative: `∼∼A ⊢ A` is unprovable in ILL, but its
translation is provable in CLL.

The **linear type system** is a linear λ-calculus with `⊗ ⊸ 𝟙 & ⊤ ⊕ 𝟘 !`,
in DILL style with an unrestricted and a linear context. It has a
call-by-value small-step semantics, and the file proves **progress,
preservation and type safety**. A **Curry–Howard** chapter translates every
typing derivation into an ILL proof. Through cut elimination and the
phase countermodels, this shows for example that no closed program has
type `A ⊸ A ⊗ A`.

## Reading order

1. `theories/Intuitionistic/Formula.v`: why linear logic, the connectives,
   and notations.
2. `theories/Intuitionistic/Sequent.v`: the ILL sequent calculus and
   worked examples.
3. `theories/Intuitionistic/Phase.v`: phase semantics, soundness, and
   countermodels.
4. `theories/Intuitionistic/CutElim.v`: the syntactic model, Okada's lemma,
   completeness, and cut elimination.
5. `theories/Classical/Formula.v`, `Sequent.v`, `Phase.v`, `CutElim.v`:
   the same four steps for CLL. Read them side by side with the ILL files.
6. `theories/Comparison.v`: ILL versus CLL.
7. `theories/Types/LinearTypes.v`: the linear λ-calculus and type safety.
8. `theories/Types/CurryHoward.v`: programs as ILL proofs.

## Main theorems

| File | Results |
|---|---|
| `Intuitionistic/Phase.v` | `soundness`; countermodels `no_contraction`, `no_weakening`, `no_free_lunch`, `with_is_not_tensor`, `no_promotion`, `consistency`, `no_duplicator`, `no_eraser`, `no_dne` |
| `Intuitionistic/CutElim.v` | `okada`, `completeness`, `cut_elimination`, `cut_admissible`, `provable_valid_cutfree` |
| `Classical/Sequent.v` | examples: `excluded_middle`, `dne`, De Morgan laws, `par_split` |
| `Classical/Phase.v` | `soundness`, `balance` (the books must balance), `no_contraction`, `no_weakening`, `no_duplicator`, `no_eraser`, `consistency` (`⊬ ·`), `bot_unprovable`, `zero_unprovable` |
| `Classical/CutElim.v` | `okada`, `completeness`, `cut_elimination`, `cut_admissible`, `provable_valid_cutfree` |
| `Comparison.v` | `ill_to_cll` (embedding), `classical_dne`, `not_conservative` |
| `Types/LinearTypes.v` | `subst_l_typed`, `subst_u_typed`, `progress`, `preservation`, `type_safety`; examples `swap_typed`, `dup_typed`, `no_copy`, `no_drop`, `swap_eval` |
| `Types/CurryHoward.v` | `curry_howard`, `closed_proof_cf`, `no_duplicating_program`, `no_erasing_program`, `no_zero_program`, `bang_duplicating_program` |

Every result is axiom-free: `Print Assumptions` reports *Closed under
the global context*.

## Design choices

- **Cut elimination is semantic** (Okada 1996/1999). Soundness of the
  calculus with cut, plus completeness of the cut-free calculus for one
  _syntactic_ phase model, gives cut elimination without the delicate
  termination argument (and the multicut for `!`) of Gentzen's
  syntactic proof.
- **One inductive, two calculi.** `Γ ⊢[c] A` takes a boolean `c` that
  permits the cut rule. `Γ ⊢ A` and `Γ ⊢cf A` are its two instances.
- **stdpp throughout**: `≡ₚ` and `solve_Permutation` for exchange,
  `propset` with `∈ ⊆ ∩ ∪` for phase semantics, the `Equiv`/`Proper`
  setoid idiom for monoids up to permutation, `!!` and `Forall3` in the
  type system.
- **No Autosubst.** The type system has two variable sorts (linear and
  unrestricted) in separate de Bruijn index spaces, and only ever
  substitutes closed values. A direct substitution function is simpler
  than a parallel-substitution framework, which would also need a
  resource-splitting typing of substitutions.
- Atoms are written `$0, $1, …` (`#0` clashes with stdpp's vector notation
  `[# …]`), and why-not is written `? A` with a space (`?A` is an evar).

## Building

```sh
make            # compile all theories
make html       # coqdoc HTML (comments rendered as prose) into ./html
make clean
```

To run a single tool by hand, use the same prefix, for example
`opam exec --switch=. -- rocq compile -Q theories LinearLogic theories/Comparison.v`.

## References

- J.-Y. Girard, *Linear logic*, TCS 50 (1987).
- M. Okada, *Phase semantic cut-elimination and normalization proofs of
  first- and higher-order linear logic*, TCS 227 (1999).
- A. S. Troelstra, *Lectures on Linear Logic*, CSLI (1992).
- A. Barber, *Dual Intuitionistic Linear Logic*, LFCS report (1996).
- H. Schellinx, *Some syntactical observations on linear logic*, JLC 1 (1991).
