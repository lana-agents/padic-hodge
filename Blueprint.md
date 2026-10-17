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

## PH1. Tate's Galois cohomology of `ℂ_p` — wip (all of `H⁰` done; `H¹` open)

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
4. **done** `ℂ_[p](j)^{G_L} = 0` for `j ≠ 0`, `L/ℚ_p` finite ([BC, Thm. 2.2.7], first half).
   * `Cyclotomic/Norms.lean`: `‖ζ_{p^{m+1}} − 1‖^{φ(p^{m+1})} = p⁻¹`, value groups of finite
     extensions, `[ℚ_p(ζ_{p^{m+1}}) : ℚ_p] = φ(p^{m+1})` (`finrank_adjoin_primitiveRoot`).
   * `Cyclotomic/Tower.lean`, `Trace.lean`: one step `ℚ_p(ζ^p) ⊂ ℚ_p(ζ)` of the cyclotomic tower:
     representation `∑_{i<p} a_i ζ^i`, orthogonality of the `π`-adic expansion, the averaging
     operator `T = p⁻¹ ∑ δ^s` with `T(∑ a_i ζ^i) = a_0`, `‖T y‖ ‖π‖^{p−1} ≤ ‖y‖`, and
     `‖y‖ ‖ω−1‖ ‖π‖^{p−1} ≤ ‖δy − y‖` when `T y = 0`.
   * `Cyclotomic/Core.lean`: Tate generators `IsTateGen γ n`; composites of normalised traces;
     uniform estimates `‖A y‖ ≤ p‖y‖`, `‖y − A y‖ ≤ p⁴ ‖γ y − y‖` ([BC, §14.1] after Tate).
   * `Cyclotomic/Vanishing.lean`: `eq_zero_of_autCp_eq_smul` (no eigenvector with eigenvalue
     `λ ≠ 1`, `p⁴‖λ−1‖ < 1`, in the closure of `ℚ_p(μ_{p^∞})`).
   * `Cyclotomic/Character.lean`: `chi` (Mathlib `cyclotomicCharacter`), existence of `γ` with
     `χ(γ) = 1 + p^n u`, weak LTE, `χ(γ)^j ≠ 1`.
   * `TateSen/Invariants.lean`: over `ℚ_p` (`eq_zero_of_autCp_eq_chi_smul`) and for finite `L`
     by the norm trick over `G_{ℚ_p}/G_L` (`eq_zero_of_galCp_eq_chi_smul`).
   * `TateSen/Twist.lean`: `cpTwistRep L j` (`σ·c = χ(σ)^j σ(c)`),
     `cpTwistRep_invariants_eq_bot`, `H0CpTwistIso : H⁰_cont(G_L, ℂ_p(j)) ≅ 0`.
5. **wip** `H¹(G_K, ℂ_p(j)) = 0` (`j ≠ 0`), `dim_K H¹(G_K, ℂ_p) = 1` ([BC, Thm. 2.2.7], second
   half; [BC, §14]). Route: (i) `H¹(G_{K_∞}, ℂ_p) = 0` (almost étale, milestone PH1.AE below);
   (ii) inflation–restriction; (iii) `H¹(Γ, \hat K_∞(j))` via normalised traces.
   * **done** `Cohomology/ContH1.lean`: continuous `H¹` via crossed homomorphisms for a
     representation of a topological group on a topological module (`ContH1.cocycles`,
     `coboundaries`, `H1`), restriction, inflation from `G ⧸ S` with values in `M^S`, and the
     inflation–restriction exact sequence in degree one (`inf_injective`, `res_comp_inf`,
     `exists_inf_of_res_eq_zero`, the last assuming continuous orbit maps).
   * **done** (iii) for `K = ℚ_p`, `j ≠ 0`: `Galois/Continuity.lean` (orbit maps continuous),
     `Cyclotomic/Solve.lean` (`norm_le_of_twist`: `‖y‖ ≤ C‖λγy − y‖` uniformly on
     `ℚ_p(μ_{p^M})`; `exists_twist_eq`: `λγ − 1` surjective on the completion),
     `ContH1.mk_eq_zero_of_vanish` (finite-index averaging), `TateSen/H1Gamma*.lean`:
     `subsingleton_H1_quotient_twist : H¹(Γ, (ℂ_p(j))^H) = 0` for `j ≠ 0`
     (`Γ = G_{ℚ_p}/H`, `H = G_{ℚ_p(μ_{p^∞})}`).
   * **done** `j = 0`: `H¹(Γ, \hat F_∞) ≅ ℚ_p` (`TateSen/H1GammaZero.lean`:
     `H1QuotientZeroEquiv : ℚ_p ≃ₗ H¹(Γ, ℂ_p^H)`, `a ↦ a [log χ]`; `finrank_H1_quotient_zero`).
     Inputs: `Cyclotomic/Decomp.lean` (Tate's normalised trace `R_n` is independent of the level,
     `‖y‖ ≤ p^5 ‖(γ−1)y + R_n y‖`, `exists_decomp`: `c = (γ−1)m + r`, `r ∈ ℚ_p(μ_{p^n})`;
     `eq_zero_of_autCp_sub_eq`: `(γ−1)m ∈ ℚ_p(μ_{p^n})` forces `(γ−1)m = 0`), and
     `Cyclotomic/LogChi.lean` (`logChi σ = log χ(σ)^{p−1}`, a continuous homomorphism with
     `logChi γ ≠ 0`; the logarithm is `PadicLogVolume.padicLog` on Mathlib's completion
     `(Rat.padicValuation p).Completion ≅ ℚ_p`, transported along `Padic.withValRingEquiv`).
     Proof as in [BC, proof of Thm. 14.3.4] (`H¹(Γ, \hat K_∞) = H¹(Γ, K) ⊕ H¹(Γ, X)`), using
     that `Γ` is abelian: `(γ−1)F(g) = (g−1)F(γ)`.
   * **planned** general finite `K` via linear disjointness of `K_n` and `F_n` for large `n`.

### PH1.AE — almost étaleness of `K_∞ = K(μ_{p^∞})` (separate milestone, not started)

Statement ([BC, Thm. 13.1.2], Tate): for every finite `M / K_∞`, `Tr_{M/K_∞}(O_M) ⊇ m_{K_∞}`;
consequence ([BC, Lemma 14.1.3], axiom (TS1)) `H¹(G_{K_∞}, ℂ_p) = 0`.

* Tate's proof uses upper-numbering ramification groups, the Herbrand function, Hasse–Arf, the
  integral formula for the different ([BC, Lemma 13.1.8]) and Serre's geometric local class field
  theory ([BC, Lemma 13.1.6]); none of these is in Mathlib (only `ramificationGroup`, lower
  numbering). Estimate ≥ 20k lines; not recommended.
* **Planned route: Faltings' commutative-algebra proof** ([BC, Exercise 13.7.4], `d = 0`):
  inputs: Kähler differentials `Ω_{B/A}` of finite extensions of complete DVRs of mixed
  characteristic, `length_B Ω_{B/A} = length_B(B/𝔇_{B/A})` (Mathlib: `differentIdeal`, trace dual),
  the exact sequence `0 → B_{n+1} ⊗ Ω_{A_{n+1}/A_n} → Ω_{B_{n+1}/A_n} → Ω_{B_{n+1}/A_{n+1}} → 0`,
  elementary divisors over DVRs, the discriminant estimate `p^{δ_n−δ_{n+1}} B_{n+1} ⊆ B_n ⊗ A_{n+1}`,
  and the induction `δ_n − δ_{n+1} ≥ β_n − (d+1)(δ_n − δ_{n+1})` giving `δ_n → 0`; for the
  cyclotomic tower `Ω_{A_n/A_{n−1}} ≅ A_n/p` from `X^p − ζ_{p^{n−1}}`. Estimate **6–10k lines**.
* Plus descent of finite extensions `M / K_∞` to finite layers `L_n` with `M = L_n K_∞` and
  `L_m = L_n ⊗_{K_n} K_m` ([BC, Exercise 13.7.2]): about 1k lines; and the passage
  almost-étale ⇒ `H¹(G_{K_∞}, ℂ_p) = 0` (averaging over finite quotients, limits): 1–2k lines.

## PH2. Hodge–Tate representations — wip (core done)

* **done** `HodgeTate/SerreTate.lean`: abstract Serre–Tate lemma ([BC, Lemma 2.3.1], minimal
  relation argument) for a group acting semilinearly on a vector space over a field `B` with
  fixed field `K` and characters without nonzero eigenvectors in `B`:
  `linearIndependent_of_eigen`, `sum_finrank_le`, `exists_eigenbasis`,
  `sum_finrank_eq_of_eigenbasis`.
* **done** `HodgeTate/Basic.lean`: for `ρ : Representation ℚ_p G_L V` (`L/ℚ_p` finite, `V`
  finite-dimensional): `CpTensor ρ = ℂ_p ⊗ V` with `σ(c ⊗ v) = σ(c) ⊗ ρ(σ)v`;
  `DHT ρ q = {w | σ w = χ(σ)^{-q} w}` (`L`-subspace; `W[q]` of [BC, Rem. 2.3.2]);
  `sum_finrank_DHT_le`, `finite_support_DHT`, `htDim`, `IsHodgeTate`;
  `isHodgeTate_iff_exists_basis` (Hodge–Tate decomposition: `ℂ_p ⊗ V ≅ ⊕ ℂ_p(−q_i)`);
  `isHodgeTate_of_exact` (sub and quotient representations, [BC, Prop. 2.4.4]);
  `eq_zero_of_twist_equivariant` (`Hom_{G_L}(ℂ_p(a), ℂ_p(b)) = 0` for `a ≠ b`; this gives the
  *uniqueness* of splittings of extensions with distinct weights).
* **done** `htWeights` (multiset of Hodge–Tate weights, `count_htWeights`, `card_htWeights`).
* **done** `HodgeTate/Dual.lean`: `isHodgeTate_dual` (via `IsBaseChange.toDualBaseChange` and dual eigenbases).
* **done** `HodgeTate/Tensor.lean`: `isHodgeTate_tprod` (via `AlgebraTensorModule.distribBaseChange`).
* **planned** *existence* of splittings
  for distinct weights (needs `H¹(G_L, ℂ_p(j)) = 0`, PH1.5).

## PH3. Finite flat group schemes, p-divisible groups, Tate's theorem — wip (foundations)

* **done** `GroupScheme/FiniteFlat.lean`: `FFGroupScheme R` (finite free commutative and
  cocommutative Hopf algebras, [BC, Def. 7.1.6]), `order`, `points` with its commutative group
  structure (convolution; inverse via the antipode), homomorphisms and `Hom.mapPoints`,
  diagonalizable groups `diag M` (`order_diag`, `diagPointsEquiv : D(M)(S) ≃* Hom(M, S)`).
* **done** `GroupScheme/PDivisible.lean`: `PDivGroup R p` ([BC, Def. 7.2.1], kernel condition
  on points for all `R`-algebras, closed immersions), `TateModule`.
* **done** `GroupScheme/Mu.lean`: `muPDiv R p = μ_{p^∞}` of height `1`.
* **planned** Cartier duality (dual Hopf algebra of a finite free Hopf algebra), constant group
  schemes, connected–étale sequence over `O_K`, formal Lie groups, `T_p μ_{p^∞} = ℤ_p(1)`;
  Tate's Hodge–Tate decomposition of `T_p G ⊗ ℂ_p` and full faithfulness ([Tate] §4, Thm. 4;
  [Tate] not available locally, statements as quoted in [LocAn] and [BC]); these need PH1.5.
