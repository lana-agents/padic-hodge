# Blueprint: p-adic Hodge theory for [LocAn]

Status keys: **done** (proved, no `sorry`), **wip**, **planned**.

## 0. Survey of Mathlib v4.32.0 (commit 81a5d25)

Reused, not duplicated:

* `PadicAlgCl p` (= `AlgebraicClosure ℚ_[p]`, normed by the spectral norm) and
  `ℂ_[p] = PadicComplex p` (its completion; `PadicComplex.isAlgClosed`), in
  `Mathlib/NumberTheory/Padics/Complex.lean`. No Galois action on `ℂ_[p]` is defined there.
* `spectralNorm_eq_of_equiv` (`Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`):
  `K`-automorphisms are isometries for the spectral norm.
* `TopRep`, `continuousCohomology` (`Mathlib/RepresentationTheory/Homological/ContCohomology/`):
  continuous cohomology via homogeneous cochains; only `H⁰ ≅ invariants` (`zeroIso`) is
  computed; no description of `H¹` by crossed homomorphisms, no long exact sequence.
* `cyclotomicCharacter L p : (L ≃+* L) →* ℤ_[p]ˣ`
  (`Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean`).
* Krasner's lemma (`IsKrasner.of_complete`, `Mathlib/Analysis/Normed/Field/Krasner.lean`).
* `PreTilt`, Fontaine's `θ`, `BDeRhamPlus`, `BDeRham` (`Mathlib/RingTheory/Perfectoid/`);
  the file's TODO list says that the extension of `θ` to `B_dR⁺`, the DVR property and the
  principality of `ker θ` are not yet done.
* Witt vectors (`Mathlib/RingTheory/WittVector/`), isocrystals.

Not in Mathlib: the Galois action on `ℂ_[p]`, Ax–Sen–Tate, Tate twists of `ℂ_[p]`,
Tate's normalised traces, Hodge–Tate representations, finite flat group schemes,
p-divisible groups.

## PH0. Skeleton — done

Lake project `PadicHodge`, Mathlib only, `--wfail`, `mk_all` check (`.orchestra/validation.sh`).

## PH1. Tate's Galois cohomology of `ℂ_p` — wip (untwisted H⁰ done)

1. **done** `PadicHodge.galCp L : G_L →* (ℂ_[p] ≃+* ℂ_[p])`, `norm_galCp`, `continuous_galCp`
   (`Galois/Basic.lean`): extension by continuity of the isometric action on `ℚ̄_p`.
2. **done** Ax's lemma, `PadicHodge.ax` (`AxSenTate/AxLemma.lean`, `AxSenTate/Ax.lean`). For `L` an intermediate field of `ℚ̄_p/ℚ_p` and
   `α ∈ ℚ̄_p` with `‖σα − α‖ ≤ c` for all `σ ∈ G_L` there is `a ∈ L` with
   `‖α − a‖ ≤ p^{p/(p-1)²} c` ([BC, proof of Prop. 2.1.2] quoting [Ax, Prop. 1]).
   Proof (standard; written up here since [Ax] is not available locally): induction on
   `n = [L(α):L]`. Let `P` be the minimal polynomial, `d = p^{v_p(n)}` if `n` is not a power of
   `p` and `d = p^{k-1}` if `n = p^k`, and `Q = P^{(d)}/d!` (Hasse derivative, degree `n − d`,
   leading coefficient `binom(n,d)`, coefficients in `L`). By Taylor expansion `Q(α)` is the
   coefficient of `X^d` in `P(X + α) = ∏(X − (σ_iα − α))`, so `‖Q(α)‖ ≤ c^{n−d}`; hence some root
   `β` of `Q` has `‖α − β‖ ≤ c ‖binom(n,d)‖^{-1/(n−d)}`, and `β` has degree `< n` and satisfies
   the hypothesis with that constant. `‖binom(n,d)‖ = 1` in the first case (Lucas) and `= p^{-1}`
   in the second; the losses sum to at most `Σ_k 1/(p^{k−1}(p−1)) = p/(p−1)²`.
3. **done** Ax–Sen–Tate (`AxSenTate/Basic.lean`): `galCp_eq_self_iff_mem_closure`
   (`ℂ_[p]^{G_L} = closure L`, [BC, Prop. 2.1.2]); `galCp_eq_self_iff_mem` (`= L` for `L/ℚ_p`
   finite); `cpRep L` (`ℂ_[p]` as a `ContRepresentation ℚ_[p] G_L`); `H0CpIso`:
   `H⁰_cont(G_L, ℂ_[p]) ≅ L` via Mathlib's `continuousCohomology` (`zeroIso`).
4. **planned** Tate twists `ℂ_[p](j)` via `cyclotomicCharacter`; `ℂ_[p](j)^{G_K} = 0` (`j ≠ 0`),
   `H¹(G_K, ℂ_[p](j)) = 0` (`j ≠ 0`), `dim_K H¹(G_K, ℂ_[p]) = 1` ([BC, Thm. 2.2.7], proved in
   [BC, §14] by the Tate–Sen formalism: normalised traces on `K(μ_{p^∞})`, ramification of the
   cyclotomic tower, descent of cohomology from `G_K` to `Γ`). This is the bulk of PH1.

## PH2. Hodge–Tate representations — planned

`ℂ_K`-representations `W`, `W{q} = W(q)^{G_K}`, `ξ_W : ⊕ ℂ_K(−q) ⊗ W{q} → W` injective
(Serre–Tate, [BC, Lemma 2.3.1]; uses PH1.4 for `ℂ_K(r)^{G_K}`), `IsHodgeTate`, stability under
subobjects/quotients ([BC, Prop. 2.4.4]), duals and tensor products, unique splitting of
extensions with distinct weights ([BC, discussion after Thm. 2.2.7]).

## PH3. Finite flat group schemes, p-divisible groups, Tate's theorem — planned
