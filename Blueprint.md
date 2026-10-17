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

## PH1. Tate's Galois cohomology of `ℂ_p` — done

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
5. **done** `H¹(G_K, ℂ_p(j)) = 0` (`j ≠ 0`), `dim_K H¹(G_K, ℂ_p) = 1` ([BC, Thm. 2.2.7], second
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
   * **done** general finite `K / ℚ_p` (`Γ_K = Gal(K_∞/K) = G_K/H_K`, `G_K` realised as
     `K.fixingSubgroup ⊆ Gal(ℚ̄_p/ℚ_p)`): `subsingleton_H1_quotient_twist_K`
     (`H¹(Γ_K, \hat K_∞(j)) = 0`, `j ≠ 0`, `TateSen/H1K.lean`) and
     `H1QuotientZeroEquivK : K ≃ₗ[ℚ_p] H¹(Γ_K, \hat K_∞)`, `s ↦ [s log χ]`
     (`TateSen/H1KZero.lean`). Instead of normalised traces for `K_∞` (which need Tate's
     ramification estimates, [BC, Lemma 14.1.4]) we use linear disjointness over `F_∞`
     (`TateSen/Coord.lean`): for a primitive element `α` of `K` of degree `d` over `F_∞`, with
     conjugates `β_k = τ_k α` (`τ_k ∈ Gal(ℚ̄_p/F_∞)`), every `z ∈ \hat K_∞` is
     `∑_{i<d} Y_i α^i`, `Y_i = ∑_k (V⁻¹)_{ik} τ_k z ∈ \hat F_∞` (`V` the Vandermonde matrix of the
     `β_k`), so twisted solving / decomposition / rigidity on `\hat K_∞` reduce coordinatewise to
     `\hat F_∞`; `γ ∈ G_K` with `χ(γ) = 1 + p^N u` from a pigeonhole argument
     (`exists_gamma_K`).
   * **done** (i)+(ii) `TateSen/TateH1.lean`: `res_HK_eq_zero` (restriction to `H_K` vanishes, by
     `exists_coboundary` of PH1.AE and `χ|_{H_K} = 1`), `inf_surjective`,
     **`subsingleton_H1_twist`** (`H¹_cont(G_K, ℂ_p(j)) = 0`, `j ≠ 0`) and
     **`H1ZeroEquiv : K ≃ₗ[ℚ_p] H¹_cont(G_K, ℂ_p)`**, `s ↦ [s log χ]` (`finrank_H1_zero`), i.e.
     `H¹(G_K, ℂ_p)` is free of rank one over `K` on `log χ`.

### PH1.AE — almost étaleness of `K_∞ = K(μ_{p^∞})` — done

Statement ([BC, Thm. 13.1.2], Tate): for every finite `M / K_∞`, `Tr_{M/K_∞}(O_M) ⊇ m_{K_∞}`;
consequence ([BC, Lemma 14.1.3], axiom (TS1)) `H¹(G_{K_∞}, ℂ_p) = 0`. Tate's own proof (upper
numbering, Herbrand, Serre's geometric class field theory) is avoided; we follow **Faltings'
commutative-algebra route** ([BC, Exercise 13.7.4], `d = 0`), but with explicit monogenic generators
in place of Kähler differentials (all rings of integers here are monogenic), everything inside
`ℚ̄_p` with norms (`v = -log_p ‖·‖`), traces via Mathlib's normalised trace
(`Algebra.normalizedTrace`, `Tr_{N/F} = [N:F] nt_F`):

* `AlmostEtale/Basic.lean`: `O_F`, polynomials over subrings, `S[z]`; `mp F z` has coefficients in
  `O_F` (roots are conjugates, spectral norm); division by `mp F z` in `O_F[X]`
  (`exists_eq_mp_mul`); `nt_nt` (transitivity), trace bound `‖Tr_{N/F} y‖ ≤ ‖y‖`.
* `Euler.lean` (Mathlib's `traceDual_powerBasis_eq`): `y g'(z) = ∑ Tr(y z^i) D_i`
  (`mul_derivative_eq_sum`), `Tr(z^j/g'(z)) = δ_{j,d-1}` (`trace_pow_div_derivative`): the trace
  dual of `O_F[z]` is `g'(z)^{-1} O_F[z]` ([BC, Ex. 13.7.4 (2)], the different of a monogenic order).
* `Mono.lean`: `O_L = ℤ_p[z]` for `L/ℚ_p` finite (`exists_monogenic`): uniformizer from the
  discrete value group, finite residue field (compactness of `O_L`), cyclic residue units,
  `Π₁ = ω^q − ω` a uniformizer after `ω ↦ ω + Π` (Taylor), successive approximation and
  closedness of `ℤ_p[z]` (image of the compact `ℤ_p^d`). (Serre, Local Fields III §6 Prop. 12 —
  not available locally; proof written out in the file.)
* `Step.lean`, **`faltings_step`** ([BC, Ex. 13.7.4 (4)–(6)]): for `F ⊆ F'`, `x ∈ O_F[z]`,
  `F'(x) = F'(z)`, and `‖G'(z)‖ ≤ ‖p‖ ‖g'(z)‖`: `‖f'(x)‖² ≤ ‖g'(z)‖² max(‖f'(x)‖, ‖p‖)`
  (`2(δ_n − δ_{n+1}) ≥ min(δ_n, 1)`). Kernel estimate: `G ∣ f ∘ h` gives `f'(x) h'(z) ∈ G'(z) O`;
  cokernel estimate: Euler gives `e = f'(x)/g'(z)`, `e z ∈ O_{F'}[x]`, and differentiating
  `q₁∘h − X q₂∘h` gives `e ∈ h'(z) O + g'(z) O`.
* `Cyclo.lean` ([BC, Ex. 13.7.4 (3)], `Ω_{A_n/A_{n−1}} ≅ A_n/p`): `O_{ℚ_p(ζ)} = O_{ℚ_p(ζ^p)}[ζ]`,
  minimal polynomial `X^p − ζ^p` (`mp_zeta`), and `cyc_transitivity` (`‖G'(z)‖ ≤ ‖p‖‖g'(z)‖`, via
  `Tr_{F(z)/F} = Tr_{F'/F} ∘ Tr_{F'(z)/F'}` and Euler for `ζ` and `z`).
* `Tower.lean`: `a_m = ‖g_m'(z_m)‖ → 1` (`tendsto_one_of_step`) along `L_{m+1} = L_m F_{m+1}`;
  **`exists_trace_large`**: `‖Tr_{L_m/F_m}(u)‖ ≥ ρ` for some `u ∈ O_{L_m}`, any `ρ < 1`, `m ≫ 0`.
* `TraceOne.lean` ([BC, Ex. 13.7.2], descent): the minimal polynomial of `θ` over `K_∞` lives over
  `N_m = K(μ_{p^{m+1}})` for `m ≫ 0`; **`exists_trace_one`**: `α ∈ N_m(θ)`, `‖α‖ ≤ 2`,
  `∑_σ σ(α) = 1`; `exists_extend`: the embeddings `σ` lift to `Gal(ℚ̄_p/K_∞)`.
* `H1.lean` ([BC, proof of Lemma 14.1.3] and the standard averaging argument): `exists_approx`
  (`B = ∑ σ(α) c(τ_σ)`, `‖c + dB‖ ≤ 2η`) and **`exists_coboundary`**:
  `H¹_cont(Gal(ℚ̄_p/K_∞), ℂ_p) = 0`.

## PH2. Hodge–Tate representations — done (as needed so far)

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
* **done** *existence* of splittings for distinct weights (`HodgeTate/Splitting.lean`):
  **`isHodgeTate_of_exact_of_disjoint`**: for `0 → V' → V → V'' → 0` exact, `ρ` continuous
  (`σ ↦ φ(ρ σ v)` continuous for the Krull topology), `V'`, `V''` Hodge–Tate and no weight of `V''`
  a weight of `V'`, `V` is Hodge–Tate. Key lemma `exists_DHT_lift` (`D_q(V) → D_q(V'')` onto for
  `q` not a weight of `V'`): the defect of a lift is a continuous cocycle in
  `ℂ_p ⊗ V' ≅ ⊕ ℂ_p(q − q_i)`, killed coordinatewise by Tate's `H¹(G_L, ℂ_p(j)) = 0`
  (`exists_twist_coboundary_GL`, transported along `L.fixingSubgroup ≅ G_L`,
  `continuous_fixingSubgroupEquiv`).

## PH3. Finite flat group schemes, p-divisible groups, Tate's theorem — wip (foundations)

* **done** `GroupScheme/FiniteFlat.lean`: `FFGroupScheme R` (finite free commutative and
  cocommutative Hopf algebras, [BC, Def. 7.1.6]), `order`, `points` with its commutative group
  structure (convolution; inverse via the antipode), homomorphisms and `Hom.mapPoints`,
  diagonalizable groups `diag M` (`order_diag`, `diagPointsEquiv : D(M)(S) ≃* Hom(M, S)`).
* **done** `GroupScheme/PDivisible.lean`: `PDivGroup R p` ([BC, Def. 7.2.1], kernel condition
  on points for all `R`-algebras, closed immersions), `TateModule`.
* **done** `GroupScheme/Mu.lean`: `muPDiv R p = μ_{p^∞}` of height `1`.
* **done** `GroupScheme/TateMu.lean`: `muPointsEquiv : μ_{p^v}(S) ≃* rootsOfUnity (p^v) S`,
  `tateMuEquiv : T_p μ_{p^∞}(S) ≃* RootSys p S` (compatible systems of `p`-power roots of unity).
* **done** `GroupScheme/TateMuZp.lean`: **`T_p μ_{p^∞} ≅ ℤ_p(1)`**: `tateMuZpEquiv :
  T_p μ_{p^∞}(ℚ̄_p) ≃* ℤ_p` (via a compatible system `ε` of primitive roots, `eps`) and
  `tateMuZpEquiv_gal`: `σ` acts by `χ(σ)`.
* **done** `GroupScheme/Constant.lean`: constant group schemes `M_R = Spec R^M` ([BC, Example
  7.1.7(1)]): the Hopf algebra `constHopf` on `M → R` (`Δ e_k = ∑_m e_m ⊗ e_{m⁻¹k}`, antipode
  `f ↦ f ∘ (·)⁻¹`), cocommutative; `FFGroupScheme.const`, `order_const = |M|`;
  `constPointsEquiv : M ≃* M_R(S)` for a domain `S`.
* **done** `GroupScheme/Cartier.lean`: **Cartier duality** ([BC, Exercise 12.5.3 (3), (4)]): for
  `A` finite free, commutative and cocommutative, `A^∨ = Cartier.Dual R A = WithConv (A →ₗ R)`
  (convolution product, unit `ε`) with comultiplication the transpose of `m` read through
  `ev2 : A^∨ ⊗ A^∨ ≅ (A ⊗ A)^∨` (`dualDistribEquiv`), counit `f ↦ f(1)`, antipode `f ↦ f ∘ S`:
  `instHopfAlgebra`, `instIsCocomm`, free and finite; `FFGroupScheme.dual`, `order_dual`. All
  axioms are checked after the injective evaluations `ev2`, `ev3` (on `A ⊗ A`, `A ⊗ (A ⊗ A)`).
* **done** `GroupScheme/CartierDouble.lean`: double duality `Cartier.evEquiv : A ≃ₐc[R] A^∨∨`
  ([BC, Ex. 12.5.3 (6)]), `FFGroupScheme.dualDualIso`.
* **done** `GroupScheme/CartierDiag.lean`: test case `D(M)^∨ ≅ M_R` (`dualDiagEquiv`,
  `FFGroupScheme.dualDiagIso : (const R M).A ≃ₐc[R] (diag R M).dual.A`; with double duality also
  `M_R^∨ ≅ D(M)`; [BC, Ex. 12.5.3 (1)] is `(ℤ/n)_R^∨ = μ_n`). Note: the dual of `D(M)` is the
  constant group on `M` itself (the earlier plan's "`M^∨_R`" was a typo).
  Caveat: Mathlib has a *different* global `Coalgebra` instance on `M → R` (the product coalgebra,
  `Pi.instCoalgebraStruct`); statements about `M_R` must be phrased via `(const R M).A`.
* **done** `HodgeTate/Character.lean`, `GroupScheme/TateMuHT.lean`: `ℚ_p(j) = charRep L j` is
  Hodge–Tate with `htWeights = {-j}`; `V_p μ_{p^∞} ≅ ℚ_p(1)` (`tateMu_charRep`), so
  `T_p μ_{p^∞} ⊗ ℂ_p ≅ ℂ_p(1)` (`isHodgeTate_tateMu`, `htWeights_tateMu = {-1}`): the first case of
  Tate's Hodge–Tate decomposition.
* **planned** Cartier pairing on points (`G^∨(S) = Hom(G_S, 𝔾_m)`), Cartier dual of a
  `p`-divisible group, connected–étale sequence over `O_K`, formal Lie groups;
  Tate's Hodge–Tate decomposition of `T_p G ⊗ ℂ_p` and full faithfulness ([Tate] §4, Thm. 4;
  [Tate] not available locally, statements as quoted in [LocAn] and [BC]); these need PH1.5.

## Hand-off (2026-10-17)

Next steps, in order:

1. **Cartier duality** (PH3): for a finite free commutative cocommutative Hopf algebra `A`, the
   dual `A^∨ = Hom_R(A, R)` is again one: algebra structure = convolution (Mathlib
   `WithConv`, `Coalgebra/Convolution.lean`), coalgebra structure = transpose of multiplication,
   which needs `(A ⊗ A)^∨ ≅ A^∨ ⊗ A^∨` for finite free `A` (`TensorProduct.dualDistribEquiv`).
   Points: `G^∨(S) = Hom_{S-gp}(G_S, 𝔾_m)`. Test case: `D(M)^∨ ≅ (M^∨)_R` against
   `GroupScheme/Constant.lean` (`constHopf`) and `FFGroupScheme.diag`. Estimate 1–2k lines.
2. **Connected–étale sequence** over a henselian local ring (`O_K`): idempotent decomposition of
   `A ⊗ k`, lifting idempotents; needs étale = separable residue algebra. Estimate 2–4k lines.
3. ~~PH1.AE~~ **done** (2026-10-17, `AlmostEtale/`, `TateSen/TateH1.lean`).
4. ~~Existence of splittings for distinct Hodge–Tate weights (PH2)~~ **done**
   (`HodgeTate/Splitting.lean`).
