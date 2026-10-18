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
* **done** `GroupScheme/PDivisibleHom.lean`: `G_v` killed by `p^v` (`pow_eq_one`); the quotient
  maps `quot v : G_{v+1} → G_v` with `i_v ∘ quot_v = [p]` (`incl_quot`; Yoneda: the universal point
  `id^p` comes from `G_v`, and an algebra map inducing group homomorphisms on all points is a
  bialgebra map, `homOfPoints`); Tate module points are `quot`-compatible systems
  (`TateModule.val_eq_quot`); morphisms `PDivGroup.Hom` (levelwise, compatible with `i_v`), `id`,
  `comp`, `quot_comm`, and the functor `Hom.mapTate : T_p G(S) →* T_p H(S)`.
* **done** `GroupScheme/BaseChange.lean`: base change `G_S = Spec(S ⊗_R A)` (Mathlib's Hopf
  structure on `S ⊗_R A`), `order_baseChange`, `baseChangePointsEquiv : G_S(T) ≃* G(T)` (natural),
  `PDivGroup.baseChange` (same height; kernel condition transported), `baseChangeTateEquiv :
  T_p(G_S)(T) ≃* T_p(G)(T)`, `Hom.baseChange` (compatible with `mapTate`).
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
* **done** `GroupScheme/ConstPDivMap.lean`, `ConstPDiv.lean`, `ConstPDivTate.lean`: functoriality
  `constMap h : M_R → M'_R` (closed immersion for injective `h`); points over any `S` via
  orthogonal idempotents (`ptVal_pow`, `pow_eq_one_iff`, `exists_mapPoints_eq_iff`); the constant
  `p`-divisible group `constPDiv R p = ℚ_p/ℤ_p` (height 1); `constTateEquiv : T_p(ℚ_p/ℤ_p)(S) ≃*
  ℤ_p` (domain `S`), general `PDivGroup.galTate`, trivial Galois action (`galTate_constPDiv`),
  `V_p = ℚ_p(0)` Hodge–Tate of weight `0`.
* **done** `GroupScheme/ConnectedIdempotent.lean`, `GroupScheme/Connected.lean`: connected
  component over a complete local ring `R` (deviation: complete instead of henselian, since
  idempotent lifting along finite algebras over henselian rings is not in Mathlib): point
  idempotent `e₀` of the counit (`exists_isPointIdempotent`, unique), `(1 - e₀)` is a Hopf ideal,
  `G⁰ = connectedComponent G` (finite free, local), closed immersion `connectedComponentHom`,
  `IsConnected` (local coordinate ring), `G⁰ = G` for connected `G`.
* **done** `GroupScheme/EtaleInvariants.lean`: `IsEtale`, `A^{et} = etaleInvariants` (subalgebra
  of `G⁰`-invariants, antipode-stable; `π = ε` on it; `= R` for connected `G`; `= A` and
  `|G⁰| = 1` for étale `G` and for constant groups), `comul_antipode`.
* **done** `GroupScheme/EtaleQuotient.lean` (`R` a complete local PID, e.g. `O_K`, `ℤ_p`; standard
  argument, written up here): `A^{et}` is finite free (torsion free over a PID) and a sub-Hopf
  algebra: `A^{et} = ker f`, `f = (id ⊗ π)Δ - (· ⊗ 1)`; `(id ⊗ f)(Δ a) = 0` by coassociativity,
  `(f ⊗ id)(Δ a) = 0` by cocommutativity, and an `x ∈ A ⊗ A` killed by both lies in
  `A^{et} ⊗ A^{et}` by flatness (`mem_range_map_of_lTensor_eq_zero_of_rTensor_eq_zero`);
  `comulEt` with `incl2_comulEt`, axioms checked after the injective `A^{et} ⊗ A^{et} → A ⊗ A`,
  `A^{et} ⊗ (A^{et} ⊗ A^{et}) → A ⊗ (A ⊗ A)`. `FFGroupScheme.etaleQuotient G = G^{et}`,
  `etaleQuotientHom : G → G^{et}` (injective on coordinate rings),
  `connectedComponentHom_etaleQuotientHom` (`G⁰ → G → G^{et}` trivial), `G → G^{et}` an
  isomorphism for étale `G`, `|G^{et}| = 1` for connected `G`.
* **done** `GroupScheme/EtaleQuotientEtale.lean` (standard arguments, written up here):
  `idemConn_mem_etaleInvariants` (`e₀ ∈ A^{et}`: an idempotent of `A ⊗ A⁰` killed by `id ⊗ ε`
  lies in `√(m_R (A ⊗ A⁰))`, hence vanishes); **kernel of `G → G^{et}` is `G⁰`**
  (`map_ker_counitEt`: `A · ker(ε|A^{et}) = (1 - e₀)`, `tensorQuotEquiv : A ⊗_{A^{et}}
  (A^{et}/ker ε) ≃ A⁰`); **`G` étale iff `G⁰` trivial** (`isEtale_iff`, `R` noetherian: formal
  unramifiedness by the lifting criterion and the group law, `h = f₁ f₂⁻¹` kills
  `ker ε = (ker ε)(1 - e₀)`; then Mathlib `Algebra.Etale.of_formallyUnramified_of_flat`);
  **`G^{et}` étale** (`isEtale_etaleQuotient`, its `e₀` is `e₀`, `idemConn_etaleQuotient`);
  `0 → G⁰(T) → G(T) → G^{et}(T)` exact for all `R`-algebras `T`
  (`mapPoints_etaleQuotientHom_eq_one_iff`, `mapPoints_connectedComponentHom_injective`).
* **done** `GroupScheme/EtaleQuotientFlat.lean`: **`A` faithfully flat over `A^{et}`**
  (`faithfullyFlat_etaleInvariants`), via `flat_of_formallyUnramified` (an `S`-module flat over
  `R` is flat over an unramified `R`-algebra `S`: the diagonal idempotent `δ ∈ S ⊗_R S` gives an
  `S`-linear section `m ↦ δ(1 ⊗ m)` of `S ⊗_R M → M`) and going up.
* **done** `GroupScheme/EtaleQuotientOrder.lean`: **`|G| = |G⁰| · |G^{et}|`** (`order_eq_mul`).
  Galois isomorphism `galoisEquiv : A ⊗_{A^{et}} A ≃ₐ[A] A ⊗_R A⁰`, `x ⊗ y ↦ (x ⊗ 1)(id ⊗ π)Δy`,
  inverse via `δ = i₁⁻¹ i₂`, which factors through `G⁰` since it dies in `G^{et}`; then
  `rankAtStalk_{A^{et}} A = |G⁰|` everywhere (base change + faithful flatness), `A^{et}` semilocal,
  so `A` is free of rank `|G⁰|` over `A^{et}` (Mathlib `nonempty_basis_of_flat_of_finrank_eq`,
  Stacks 02M9), and the tower law. (No base change to the fraction field needed.)
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
* **done** `GroupScheme/CartierPairing.lean` ([BC, Ex. 12.5.3 (5), (6)] over the base ring):
  `isGroupLikeElem_dual_iff` (`f ∈ A^∨` group-like iff `f` is an algebra map),
  `pointsEquivGroupLike : G(R) ≃* GroupLike(A^∨)`, `dualPointsEquivGroupLike :
  G^∨(R) ≃* GroupLike(A)` (characters of `G`), `cartierPairing : G(R) →* G^∨(R) →* R`.
* **done** `GroupScheme/CartierPairingBase.lean`: **Cartier pairing over an `R`-algebra `S`**
  `cartierPairingBase : G(S) →* G^∨(S) →* S`, `⟨φ, ψ⟩ = ∑ φ(e_i) ψ(e_i^*)` (`pairing_eq_sum`, any
  basis). Basis-free: `θ : A^∨ ⊗ S ≃ Hom_R(A, S)` (Mathlib `dualTensorHomEquiv`) is multiplicative
  for convolution (`theta_mul`), `⟨φ, ψ⟩ = (ψ ⊗ id)(θ⁻¹φ)`; multiplicativity in `ψ` from symmetry
  under double duality (`pairing_symm`); values in `μ_n` if `n` kills `G(S)`
  (`cartierPairingBase_pow_eq_one`); naturality `⟨f φ, ψ⟩_H = ⟨φ, ψ ∘ (f^*)^∨⟩_G`
  (`pairing_mapPoints`, `Cartier.transposeAlgHom`). [Stix, §11.2.2] for the levelwise use.
* **done** `GroupScheme/EtaleInvertible.lean`: **a finite flat group scheme over a noetherian
  ring killed by an invertible integer is étale** (`isEtale_of_univPt_pow_eq_one`); hence the
  layers of a `p`-divisible group over a noetherian ring with `p` invertible (e.g. `K`, `ℚ_p`)
  are étale (`PDivGroup.isEtale_of_isUnit`). Proof avoids Cartier's theorem: in the convolution
  ring `Hom(A, A/I²)` the projection is `1 + d` with `d² = 0`, so `1 = q^n = 1 + n d` gives
  `I = I²`, `I = (f)` idempotent, and the group law gives formal unramifiedness.
* **done** `GroupScheme/EtalePoints.lean`: `K`-algebra maps `K^X → K` are evaluations
  (`card_algHom_pi`); **`#G(K) = |G|` for `G` étale over a separably closed `K`**
  (`card_points_of_isEtale`, via Mathlib's `Algebra.FormallyEtale.equivPiOfIsSepClosed`);
  **`#G_v(ℚ̄_p) = p^{hv}`** for a `p`-divisible group over `ℚ_p` (`card_points_padicAlgCl`).
* **done** `GroupScheme/PDivisiblePoints.lean`: `G_{v+1}(S)[p] ≅ G_1(S)` (`card_ker_pow`),
  `ker(quot_v) = G_{v+1}(S)[p]`, and **`quot_v` surjective on points when `#G_w(S) = p^{hw}`**,
  in particular on `ℚ̄_p`-points for `G` over `ℚ_p` (`quot_surjective_padicAlgCl`).
* **done** `GroupScheme/TatePairing.lean` ([Stix, §11.2.2], [Hong, Prop. 3.4.6]): dual
  homomorphisms `Hom.dual` (transpose of a bialgebra map is a bialgebra map), naturality
  `pairing_dual`, `pairing_postComp`; `DualTate G S = lim_v G_v^∨(S)` along `i_v^∨` (the Tate
  module of the Cartier dual system); **`tatePairing : T_p G(S) →* DualTate G S →* RootSys p S`**
  (levelwise Cartier pairings, compatible by naturality and `i_v ∘ quot_v = [p]`); over `ℚ_p`:
  `tatePairingZp` with values in `ℤ_p`, biadditive, and **`⟨σx, σy⟩ = χ(σ)⟨x, y⟩`**
  (`tatePairingZp_gal`), i.e. values in `ℤ_p(1)`. Perfectness: `TatePerfect.lean` below.
* **done** `GroupScheme/CartierPerfect.lean` (standard arguments, written up here): the transpose
  `End_R(A) → End_R(A^∨)` is a monoid map for convolution (`Cartier.transposeHom`), hence
  **`[n]_{G^∨} = ([n]_G)^∨`** and `G^∨` is killed by `n` if `G` is (`dual_univPt_pow_eq_one`);
  **injectivity of `ψ ↦ ⟨·, ψ⟩`** over a field `S` with `#G(S) = |G|`
  (`pairing_injective_right`: the matrix `(φ(e_i))_{φ,i}` is square with independent rows by
  Dedekind); `#Hom(M, L) ≤ #M` (`card_monoidHom_le`); perfectness `G^∨(S) ≅ Hom(G(S), S)` and
  `G(S) ≅ Hom(G^∨(S), S)` when `#G(S) = #G^∨(S) = |G|` (`pairingHom_bijective`,
  `pairingHom'_bijective`); over `ℚ_p`: `G_v^∨` étale, `#G_v^∨(ℚ̄_p) = p^{hv}`, the level-`v`
  pairing over `ℚ̄_p` is perfect (`levelPairingHom_bijective`).
* **done** `GroupScheme/CartierDualPDiv.lean`: **the Cartier dual `p`-divisible group**
  `G^∨ = (G_v^∨, quot_v^∨)` over `ℚ_p` (`PDivGroup.dualPDiv`, same height):
  `quot_v^∨ ∘ i_v^∨ = [p]` (`dual_quot_incl`), `p^v G_{v+1}(S) = G_{v+1}(S)[p]` by counting
  (`pow_range_eq_ker_pow`), closed immersion (`quot_v^*` injective since the `ℚ̄_p`-points of an
  étale algebra separate elements, `eq_zero_of_forall_algHom`), kernel condition over `ℚ̄_p` via
  perfectness at levels `v`, `v+1` (`exists_dual_quot_eq_padicAlgCl`) and over any `ℚ_p`-algebra
  via the ideal `J = ([p^v]^*(b) - ε(b))` of `O(G_{v+1}^∨)`, `B/J` étale
  (`exists_dual_quot_eq`); **`T_p(G^∨) = DualTate G`** (`tateModule_dualPDiv`).
* **done** `GroupScheme/TateFree.lean`: iterated quotient maps `quotLE` (`Nat.leRecOn`),
  `ker(G_b → G_a) = G_b[p^{b-a}]` (`quotLE_eq_one_iff`); **`T_p G(S) → G_v(S)` surjective**
  (`TateModule.proj_surjective`, lifting along chosen sections); coordinates
  `phiLevel t v : (ℤ/p^v)^h → G_v(S)` injective (induction on `v`) and bijective by counting when
  the `(t_i)_1` are an `𝔽_p`-basis of `G_1(S)` (`exists_basis_level_one`); **`T_p G(ℚ̄_p) ≃*
  ℤ_p^h`** (`PDivGroup.tateEquivZp`).
* **done** `GroupScheme/TatePerfect.lean`: **perfectness on Tate modules** ([Stix, §11.2.2,
  Cor. 85], [Hong, Prop. 3.4.6]): for a `ℤ_p`-basis `(t_i)` of `T_p G(ℚ̄_p)`
  (`exists_tateBasis`), `y ↦ (⟨t_i, y⟩)_i`, `T_p(G^∨)(ℚ̄_p) → ℤ_p^h`, is bijective
  (`dualTateCoord_bijective`, `exists_perfect_tatePairing`; with `tatePairingZp_gal` this is
  `T_p(G^∨) ≅ Hom_{ℤ_p}(T_p G, ℤ_p(1))`).
* **done** `GroupScheme/EtaleUnramified.lean`: integral elements map into the unit ball
  (`norm_le_one_of_isIntegral`); **rigidity of unramified points**
  (`algHom_eq_of_norm_sub_lt_one`, via `Algebra.FormallyUnramified.iff_exists_tensorProduct`);
  `IsInertia`; inertia fixes the `ℚ̄_p`-points of finite étale group schemes over `ℤ_p`-like bases
  (`FFGroupScheme.inertia_comp_eq`); **inertia acts trivially on `T_p` of (the generic fibre of)
  a `p`-divisible group over `ℤ_p` with étale layers** (`galTate_baseChange_eq_of_isInertia`).
* **done** `GroupScheme/TateRep.lean`: `ℤ_p`-module structure on `T_p G(S)` (`instModuleZp`,
  `a · x = (x_v^{a mod p^v})_v`), Galois action `ℤ_p`-linear (`galLin`), `T_p G(ℚ̄_p) ≅ ℤ_p^h`
  linearly (`nonempty_tateLinearEquiv`, `finrank_tate`); **the representation
  `V_p G = ℚ_p ⊗ T_p G(ℚ̄_p)` of `G_L`** (`tateRep`, dimension `h`, `finrank_tateRep`);
  unramified for étale `G` over `ℤ_p` (`tateRep_baseChange_eq_one_of_isInertia`); Hodge–Tate of
  weight `0` if the image is finite (`isHodgeTate_tateRep_of_trivial_on`).
* **done** `GroupScheme/TateDual.lean`: **`T_p(G^∨)(ℚ̄_p) ≅ Hom_{ℤ_p}(T_p G(ℚ̄_p), ℤ_p)`**
  intrinsically: `tatePairingZp` is `ℤ_p`-bilinear, `tateDualHom` is bijective, and
  `tateDualHom (σ y) (σ x) = χ(σ) tateDualHom y x` ([Hong, Prop. 3.4.6], [Stix, Cor. 85]).
* **done** `HodgeTate/FiniteImage.lean`: **representations with finite image are Hodge–Tate with
  all weights `0`** (`isHodgeTate_of_trivial_on`; Galois descent: traces over lifts of the
  embeddings `M → ℚ̄_p`, Dedekind, Serre–Tate).
* **done** `Hilbert90/` (**Hilbert 90 for `\hat{ℚ_p^{ur}}`**, standard arguments, written up here;
  deviation from the fourth-session plan: instead of `ℚ_p^{ur}` itself we use the finite fields
  generated by the points of the layers, which are shown to be unramified directly):
  `Residue.lean`: `IsUnrStable M` (`M/ℚ_p` finite, Galois-stable, `|z| < 1 ⇒ |z| ≤ |p|` on `M`,
  and *rigid*: automorphisms trivial on the residue field fix `M`); `O_M` local
  (`instIsLocalRingOM`), `resAut σ` on `κ_M`, Dedekind over `κ_M` for the lifts `σ_e` of the
  embeddings `e : M → ℚ̄_p` (`linearIndependent_resAut`), **trace one** (`exists_trace_one`:
  `∑_e σ_e(b) = 1`, `b ∈ O_M`) and **additive Hilbert 90 mod `p`** (`exists_additive`:
  `Z = ∑_e c(σ_e) σ_e(b)`). `Linear.lean`: **`exists_GL_mod_p`** (Speiser descent over `κ_M`:
  the twisted traces span `κ_M^h` by Dedekind; lift an invariant basis). `Matrix.lean`: entrywise
  bounds (`InO`, `Bd`, `norm_det_sub_le`). `Main.lean`: **`exists_hilbert90`**: for
  `A : Gal(ℚ̄_p/ℚ_p) → GL_h(ℤ_p)` with `A ≡ 1 mod p^k` on `Gal(ℚ̄_p/M_k)` along a tower
  `M_1 ⊆ M_2 ⊆ ⋯` of `IsUnrStable` fields there is `X ∈ GL_h(ℂ_p)` with `A(σ) σ(X) = X`
  (`exists_good_zero`; `exists_good_succ`: `U(σ) = X⁻¹A(σ)σ(X) = 1 + p^{k+1}c(σ)`,
  `c(στ) = c(σ) + σc(τ) + p^{k+1}c(σ)σc(τ)`, `X' = X(1 + p^{k+1}Z)`; limit in `M_h(ℂ_p)`).
* **done** `HodgeTate/Trivialization.lean`: a representation with `R(σ) σ(X) = X` for some
  `X ∈ GL_h(ℂ_p)` (`R` the matrix of `ρ`) is Hodge–Tate with all weights `0`
  (`isHodgeTate_of_matrix`: the columns of `X` are independent invariants).
* **done** `GroupScheme/EtaleFrobenius.lean`: Frobenius on `A/p` is periodic for finite étale
  `A/ℤ_p` (`exists_frobenius_period`, `pA` radical by `isRadical_map_isMaximal`); the
  `ℤ_p`-algebra `D` generated by points of étale group schemes has `|D ∖ 0| ⊆ |p|^ℕ`
  (`norm_eq_pow_of_mem_adjoin`), so `ℚ_p(points)` is unramified (`unr_adjoin`).
* **done** `GroupScheme/EtaleHT.lean`: `coordField G k = ℚ_p(G_w(ℚ̄_p), w ≤ k)` is `IsUnrStable`
  (`isUnrStable_coordField`; rigidity from `algHom_eq_of_norm_sub_lt_one`), the matrix of `σ` on
  `T_p G` is `≡ 1 mod p^k` on `Gal(ℚ̄_p/coordField G k)` (`tateMatrix_fix`), and
  **`isHodgeTate_tateRep_of_etale`**: for `G` over `ℤ_p` with étale layers, `V_p G` is
  Hodge–Tate with all `h` weights `0`, over every finite `L/ℚ_p`.
* **done** `GroupScheme/TateDualRep.lean`: Hodge–Tate data are invariant under equivariant
  isomorphisms (`finrank_DHT_eq_of_equiv`, `isHodgeTate_iff_of_equiv`, `htWeights_eq_of_equiv`);
  **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)`** (`tateRepDualEquiv`, `tateRepDualEquiv_gal`, base change of
  `tateDualHom` via `IsBaseChange.toDualBaseChange`) ([Hong, Prop. 3.4.6], [Stix, Cor. 85]);
  `isHodgeTate_tateRep_dualPDiv`.
* **done** `GroupScheme/Faithful.lean`: for `R → Ω` injective, `Ω` separably closed, `p ≠ 0` in
  `Ω`: `#G_v(Ω) = p^{hv}` (`card_points_sepClosed`), `T_p G(Ω) ↠ G_v(Ω)`; finite étale algebras
  over `Ω` are separated by points (`eq_of_forall_algHom_eq`); **`Hom.ext_of_mapTate`** (a
  homomorphism `G → H` over `R` is determined by `T_p G(Ω) → T_p H(Ω)`) and
  **`Hom.ext_of_baseChange`** (faithfulness of the generic fibre functor: uniqueness part of
  [Hong, Thm. 3.5.4, proof], faithfulness part of [Hong, Prop. 2.1.14]).
* **planned** rest of the connected–étale sequence over `O_K`, formal Lie groups;
  Tate's Hodge–Tate decomposition of `T_p G ⊗ ℂ_p` and full faithfulness ([Tate] §4, Thm. 4;
  [Tate] not available locally, statements as quoted in [LocAn] and [BC]); see the hand-off.

## PH4. Formal groups and the logarithm — wip

* **done** `FormalGroup/Law.lean`: `FGL R d` ([Hong, Def. 2.2.3]; axioms (i)–(iii) as identities
  of `MvPowerSeries.subst`). `FormalGroup/Mult.lean`: `Ĝ_m` ([Hong, Ex. 2.2.4]).
* **done** `FormalGroup/OC.lean`: `O_{ℂ_p}` as a complete linearly topologised ring;
  `norm_eval₂_le`. `FormalGroup/Points.lean`: the commutative monoid `F(m_{ℂ_p})` (open
  polydisc, coefficients in a discrete `R` with `R → O_{ℂ_p}`), via `MvPowerSeries.eval₂_subst`.
* **done** `FormalGroup/Neg.lean`: `F(m_{ℂ_p})` is a group (`instAddCommGroupPt`): the inverse of
  `x` is the fixed point of `y ↦ y − Φ(x, y)`, a contraction of the polydisc of radius
  `max |x_j|` (Lipschitz estimates `norm_add_sub_add_le`, Banach `exists_fixed_of_contract`);
  `bnd_neg`, `rad`. (The formal inverse `ι(T)` of [Hong, Lemma 2.2.5 (3)] is not constructed.)
* **done** `FormalGroup/Log.lean`, `LogProps.lean`: [Hong, Lemma 3.3.2, 3.3.3, Def. 3.3.4,
  Prop. 3.3.6]: `log_F = lim (p^n x)/p^n`, additive (`logF_add`, `logHom`);
  `|log_F x − x| ≤ r²/|p|` on radius `r ≤ |p|`; **(2)** `logF_bijOn` for `r < |p|` (deviation:
  [Hong] says `ν ≥ λ ≥ 1`, i.e. `r ≤ |p|`, which fails for `p = 2`, `Ĝ_m`, `x = −2`);
  **(3)** `logF_eq_zero_iff`, `ker_logHom` (kernel = torsion); **(4)** `exists_logF_eq_pow_mul`.
* **done** `FormalGroup/Formal.lean`: `addPS`, `mulPS` (`[n]_F`, [Hong, Ex. 2.2.8]),
  `addPS_assoc/comm/zero`, `mulPS_add`, `subst_mulPS` (`[m]∘[n] = [mn]`).
* **done** `FormalGroup/Torsion.lean`: `ev_mulPS` (`[n]_F(x) = n·x`), no prime-to-`p` torsion,
  `torsionBy v = F(m)[p^v]`, `isOfFinAddOrder_iff`, `logF_eq_zero_iff_mem_torsionBy`.
* **done** `FormalGroup/GaloisAction.lean`: `GalFixed`, `galPt`, `ev_autCp`, `logF_galPt`.
* **done** `FormalGroup/Gm.lean`: `logF_surjective_of_divisible`; `Ĝ_m`: `n·x = (1+x)^n − 1`,
  `p`-divisible (`gm_exists_p_nsmul_eq`), `gm_logF_surjective`, `gm_logF_eq_zero_iff`
  ([Hong, Ex. 3.4.8]: `0 → μ_{p^∞} → 1 + m_{ℂ_p} → ℂ_p → 0`). `FormalGroup/GmLog.lean`:
  `log_{Ĝ_m}(x) = log(1 + x)` on `p ℤ_p` (`gm_logF_eq_logQp`, [Hong, Ex. 3.3.5]).
* **done** `FormalGroup/Invariants.lean`: `F(m_{ℂ_p})^{G_L} = F(m_L)` (`galPt_fixed_iff`, [Hong,
  Lemma 3.4.2]), `log_F` of fixed points in `L`; `⋂_n p^n F(p ℤ_p) = 0`
  (`eq_zero_of_forall_pow_nsmul_Qp`, [Hong, Lemma 3.4.3]; uniform version for any `L`).
* **done** `FormalGroup/TateModule.lean`: `T_p F = lim F(m)[p^v]` (`tate`), Galois-stable, terms
  in `ker log_F`; surjective onto `F(m)[p^v]` if `F(m)` is `p`-divisible
  (`exists_tate_of_divisible`); `T_p Ĝ_m` = compatible `p`-power roots of unity (`gm_tate_iff`).
* **done** `FormalGroup/Layers.lean`, `LayerPoints.lean` (start of [Hong, Prop. 2.2.10]):
  `mem_span_X` (`ker ε = I`), `layerIdeal` `J_v`, `J_{v+1} ⊆ J_v`, `Layer` `A_v`, `layerIncl`,
  `layerP`; `layerPt : F(m)[p^v] → Hom_R(A_v, O_{ℂ_p})`, injective, compatible with `layerIncl`
  and `layerP`, Galois-equivariant.
* **done** `FormalGroup/AdicEval.lean`: evaluation `f ↦ f(s)` of power series in an
  `𝔞`-adically complete algebra (`eval`, via `IsAdicComplete.liftAlgHom` and `truncTotal`),
  uniqueness of algebra maps out of `R[[X]]` into `𝔞`-separated algebras (`algHom_ext`; no
  continuity assumed: `f − trunc_n f ∈ (X)^n`, `mem_pow_span_X`); topologically nilpotent
  families (`TopNil`, `evalT`, `algHom_ext_topNil`); finite free algebras over `𝔪`-adically
  complete rings are `𝔪S`-adically complete (`isAdicComplete_of_free`).
* **done** `FormalGroup/AdicPoints.lean`: topologically nilpotent families in such algebras form
  a commutative monoid under `Φ` (`addE`, `addE_assoc/comm/zero`), algebra maps are
  homomorphisms (`addE_comp`), `[n]` (`mulE`, `mulE_addE`, `mulE_mulE`).
* **done** `FormalGroup/LayerFree.lean` ([Hong, Def. 2.2.9, Prop. 2.2.10, (2.1)]):
  `IsPDivisible F p h` (`A` free of rank `p^h` over itself via `[p]^*`; deviation: the rank is
  part of the datum instead of [Hong, Prop. 1.5.10]), freeness in towers (`FreeVia.comp`),
  `[p^v]^* = ([p]^*)^v`; **`A_v` is free of rank `p^{hv}`** (`layerBasis`, `finrank_layer`).
* **done** `FormalGroup/LayerHopf.lean` ([Hong, Prop. 2.2.10 (1)]): over a complete local `R`
  (`PDivFGL`): `t_j` topologically nilpotent in `A_v` (`tnf_t`; `A_v/𝔪A_v` artinian local),
  maps out of `A_v` determined on `t` (`algHom_ext_A`); comultiplication `t ↦ Φ(t⊗1, 1⊗t)`,
  counit, antipode `t ↦ [p^v − 1](t)` (deviation: no formal inverse needed), Hopf axioms,
  cocommutativity; `groupScheme v : FFGroupScheme R` of order `p^{hv}`.
* **done** `FormalGroup/LayerPDiv.lean` ([Hong, Prop. 2.2.10 (2)]): `incl` bialgebra maps,
  convolution powers `y^n = y ∘ [n]^*` (`pow_eq`), kernel condition (`range_eq`),
  `isConnected_groupScheme`; **`PDivFGL.pdivGroup : PDivGroup R p`**.
* **done** `FormalGroup/LayerSurj.lean`: `layerPt` surjective (`|φ(t_j)| < 1` from `tnf_t`;
  uniqueness via separatedness of `O_{ℂ_p}` for `(x_j)`, `isHausdorff_span`), `layerPtEquiv`.
* **done** `FormalGroup/LayerTate.lean`: `layerPt ∘ [n]^* = layerPt(n·)`, **`T_p F ≃ T_p
  F[p^∞](O_{ℂ_p})`** (`tateEquiv`, `R : Type`).
* **done** `FormalGroup/FormalInv.lean` ([Hong, Lemma 2.2.5 (3)]): `Φ(T,U) − T − U ∈ (T)(U)`
  (`Φ_sub_mem`, from the unit axioms via `MvPowerSeries.coeff_subst`), `(T)`-adic continuity of
  substitution, **`formalInv`** as the `(T)`-adic limit of `y_{k+1} = y_k − Φ(T, y_k)`
  (deviation from [Hong]'s degree-by-degree construction).
* **done** `FormalGroup/Lift.lean`: ring maps `A → K` (`K` algebraically closed) lift along a
  finite free endomorphism of `A` (`FreeVia.exists_lift`: going up + `IsAlgClosed.lift`).
* **done** `FormalGroup/Divisible.lean` ([Hong, Prop. 3.2.7], connected case): **`F(m_{ℂ_p})` is
  `p`-divisible** for `p`-divisible `F` (`PDivFGL.exists_p_nsmul_eq`), hence `log_F` is surjective
  (`PDivFGL.logF_surjective`, [Hong, Prop. 3.4.7] for `G = F[p^∞]`).
* **done** `FormalGroup/FGLHom.lean`: homomorphisms of formal group laws `FGL.Hom F F'`
  (`f(Φ(T,U)) = Φ'(f(T), f(U))`), their evaluation on topologically nilpotent families
  (`fE_addE`, `fE_mulE`, `fE_comp`), the bialgebra maps `A'_v → A_v`, `t' ↦ f(t)`
  (`layerHom`) and **the induced homomorphism `F[p^∞] → F'[p^∞]`** (`FGL.Hom.toPDiv`; the
  functor of [Hong, Thm. 2.2.16] on morphisms, formal → `p`-divisible direction).
* **done** `FormalGroup/FGLHomPoints.lean`: `FGL.Hom.ptHom : F(m_{ℂ_p}) →+ F'(m_{ℂ_p})`,
  Galois-equivariant (`ptMap_galPt`), preserving `p^v`-torsion; `layerMap_mk` (`g ↦ g(f)`),
  `layerPt_comp_layerMap` (`toPDiv` induces `ptHom` on `F(m)[p^∞] = F[p^∞](O_{ℂ_p})`).
* **done** `FormalGroup/LogNat.lean`: **naturality of the logarithm**
  `log_{F'}(f(x)) = df · log_F(x)` (`FGL.Hom.logF_ptMap`; the right square of
  [Hong, Prop. 3.4.9, proof]), via the local estimate `|D(y)| ≤ s²/|p|` (`norm_defect_le`).
* **done** `FormalGroup/GmHom.lean`: a formal homomorphism `u : F → Ĝ_m` gives
  `F[p^∞] → μ_{p^∞}` (`PDivFGL.toMuOfFGLHom`) and `T_p F[p^∞](S) → T_p μ_{p^∞}(S)`
  (`tateToMu`); the `u_{O_C}` of [Hong, Prop. 3.4.9], for `u` defined over `R`.
* **done** `FormalGroup/ExactSeq.lean` ([Hong, Prop. 3.4.7] for `G = F[p^∞]`):
  `phiPt v : G_v(O_{ℂ_p}) ↪ F(m_{ℂ_p})` (inverse of `layerPtEquiv`), compatible with
  `G_v ↪ G_{v+1}` (`phiPt_incl`); `exact_logHom`: `ker log_F = ⋃_v phiPt(G_v(O_{ℂ_p}))`
  (`= Φ_p(G)`), `log_F` surjective.
* **done** `FormalGroup/WeierstrassFree.lean`: for `A` complete local and `g ∈ A[[X]]` without
  constant term whose reduction has order `n`, `A[[X]]` is free of rank `n` over itself via
  `f ↦ f(g)`, basis `1, …, X^{n−1}` (`WeierstrassFree.freeVia_psi`; iterated Weierstrass division,
  Mathlib `PowerSeries.eq_mul_weierstrassDiv_add_weierstrassMod`, uniqueness from
  `IsWeierstrassDivision.eq_zero`).
* **done** `FormalGroup/GmHeight.lean` ([Hong, Ex. 2.2.4, Def. 2.2.9]): `[n]_{Ĝ_m} = (1+t)^n − 1`
  (`gm_mulPS`); over a complete local ring with `p ∈ 𝔪`, **`Ĝ_m` is `p`-divisible of height 1**
  (`gm_isPDivisible`, `gmPDiv`).
* **done** `FormalGroup/GmMu.lean`: **`Ĝ_m[p^∞] ≅ μ_{p^∞}`** as `p`-divisible groups
  (`GmMu.gmToMu`, `muToGm`, both composites the identity; `[k] ↦ (1+t)^k`, `t ↦ [1] − 1`),
  `T_p(Ĝ_m[p^∞]) ≅ T_p μ_{p^∞}` (`GmMu.tateEquiv`).
* **done** `FormalGroup/Filtration.lean`: the coefficient filtration `N_w = {f | coeff_m f ∈
  𝔪^{w−|m|}}` of `R[[T]]` (an ideal, `N_a N_b ⊆ N_{a+b}`, `⋂ N_w = 0` for separated `R`; no
  noetherianity of `R[[T]]` needed); linear parts of substitutions (`coeff_single_subst`);
  **[Hong, Lemma 2.2.14]** (`coeff_single_Φ`, `coeff_single_mulPS`, `mulPS_sub_mem`:
  `[n](T) ≡ nT` mod `(T)^2`); `J_v ⊆ (𝔪A + I)^{v+1}` if `p ∈ 𝔪` (`layerIdeal_le_pow`) and
  **`⋂_v J_v = 0`** (`eq_zero_of_mem_layerIdeal`).
* **done** `FormalGroup/LayerLimit.lean` (**[Hong, Lemma 2.2.15]**): `R[[T]] → lim_v A_v`
  surjective (`PDivFGL.exists_mk_eq`; coefficientwise limits, `N_w ⊆ J_v + 𝔪^k A` for `w ≫ k`).
  Hypothesis `p ∈ 𝔪_R` (residue characteristic `p`).
* **done** `FormalGroup/SerreTateHom.lean` (**[Hong, Thm. 2.2.16], full faithfulness**): a
  power series in `(T, U)` vanishing in all `A_v ⊗ A_v` is zero (`PDivFGL.eq_zero_of_evPair`,
  via `R[[T,U]] → A_v ⊗ A_v → R[[T,U]]/K_v`); **`FGL.Hom.pdivEquiv :
  Hom(F, F') ≃ Hom(F[p^∞], F'[p^∞])`** (`ofPDiv`, `toPDiv_injective`, `toPDiv_ofPDiv`), any
  dimensions `d, d'` (in particular `d = g` for Jacobians).
* **done** `FormalGroup/LayerLimitBase.lean`: for an `R`-algebra `S` complete for `𝔪_R S`
  (e.g. `O_{ℂ_p}` over `ℤ_p`, once its `p`-adic completeness is formalised): evaluation
  `evB v : S[[T]] → S ⊗_R A_v` (surjective, compatible with the closed immersions) and
  **`S[[T]] ≅ lim_v S ⊗_R A_v`** (`eq_zero_of_evB`, `exists_evB_eq`; [Hong, Lemma 2.2.15] for
  `F_S`, without proving that `F_S` is `p`-divisible over `S`); the two-variable injectivity
  over `S` (`eq_zero_of_evB2`); **compatible group-like families `b_v ∈ S ⊗ A_v` come from a
  power series `U ∈ S[[T]]` with `U(Φ(T, T')) = U(T) U(T')`** (`exists_groupLike`: the step
  `lim_v Hom(G_v ⊗ S, μ_{p^v}) → Hom(F_S, Ĝ_m)` of [Hong, Prop. 3.4.9, (3.7)]). Generic kernel
  lemma `MvPowerSeries.mem_sup_pow_of_comp_eq_mk`.
* **done** `FormalGroup/OCAdic.lean`: `x ∈ p^n O_{ℂ_p}` iff `|x| ≤ |p|^n`;
  **`O_{ℂ_p}` is `p`-adically complete** (`OC.isAdicComplete_span_p`), hence
  `𝔪_{ℤ_p}`-adically complete for any `ℤ_p`-algebra structure (`OC.isAdicComplete_padicInt`):
  `LayerLimitBase` applies to `S = O_{ℂ_p}`.
* **done** `FormalGroup/PointsOC.lean`: `OCd p` (`O_{ℂ_p}` with the discrete uniformity) as a
  coefficient ring for the points framework; `ev_map`, `ev_mul`; **`ev_add_of_groupLike`**: if
  `U ∈ O_{ℂ_p}[[T]]` satisfies `U(Φ(T,T')) = U(T)U(T')`, then `U(x +_F y) = U(x)U(y)` on
  `F(m_{ℂ_p})` (the homomorphism property of `α(·)(u)` in [Hong, Prop. 3.4.9]).
* **done** `GroupScheme/CartierChar.lean`: for `ψ ∈ G^∨(S)` the character
  `χ_ψ = ⟨u, ψ⟩ ∈ S ⊗_R A` (`u` the universal point over `S ⊗ A`): multiplicative in `ψ`,
  **group-like** (`charOf_comul`), evaluates to the Cartier pairing at points of `G(S)`
  (`productMap_charOf`), natural in `G` (`charOf_dual`) and in `S` (`charOf_postComp`).
* **done** `FormalGroup/Alpha.lean` (**[Hong, Prop. 3.4.9, construction of `α`]**), for a
  `p`-divisible formal group law over a complete local `R` with `p ∈ 𝔪_R` and
  `O_{ℂ_p}` complete for `𝔪_R O_{ℂ_p}` (instance `OCd.algebraOf`, low priority): for
  `y ∈ T_p(G^∨)(O_C) = DualTate` the power series `U_y = charSeries` (unique, `U_y(t) = χ_{y_v}`,
  group-like, `U_{yy'} = U_y U_{y'}`, `U_y(0) = 1`), **`α(x)(y) = U_y(x)`** (`alpha`),
  `alpha_add`, `alpha_mul`, values in `1 + m_{ℂ_p}` (`norm_alpha_sub_one_lt`), and the **left
  square**: for `p^v`-torsion `x`, `α(x)(y) = ⟨x_v, y_v⟩` (`alpha_torsion`; via
  `layerPt_evB`: evaluating `U(t)` at the layer point of `x` is `U(x)`).
* **done** `FormalGroup/MapFGL.lean`: base change `F.map h` of formal group laws.
* **done** `FormalGroup/AlphaLog.lean`: `u_y = U_y − 1 : F_{O_C} → Ĝ_m` is a formal homomorphism
  (`charHom`, (3.7)); **`dα(z)(y) = ∑_j ∂_jU_y(0) z_j`** (`dalpha`, additive in `y`); **right
  square** `log_{Ĝ_m}(α(x)(y) − 1) = dα(log_F x)(y)` (`logGm_alpha`, from `LogNat`).
* **done** `FormalGroup/AlphaGal.lean`: for `σ` fixing the coefficients `R → O_C` (hypothesis per
  `σ`, so `σ ∈ Gal(ℚ̄_p/K')` for `R = O_{K'}`), `σ` acts on `O_C` as an `R`-algebra map (`galS`)
  and on `T_p(G^∨)(O_C)` (`galDual`); `U_{σy} = σ(U_y)` (`charSeries_gal`, via `evB_map_gal` and
  the general `AdicEval.ringHom_ext`); **`α(σx)(σy) = σ(α(x)(y))`** (`alpha_gal`).
* **done** `GroupScheme/IntegralPoints.lean`: **`G(O_{ℂ_p}) ≃* G(ℂ_p)`** for finite flat `G` over
  `R → O_{ℂ_p}` (`pointsOCEquiv`; [Hong, Lemma 3.4.1] at finite level).
* **done** `GroupScheme/CartierPerfectOC.lean`: for `G` killed by `n ≠ 0`, `#G^∨(ℂ_p) = |G|`
  (`card_dual_points_Cp`) and **a point of `G(O_C)` pairing trivially with `G^∨(O_C)` is
  trivial** (`eq_one_of_pairing_OC`): injectivity of the left vertical map of [Hong,
  Prop. 3.4.9] at level `v`.
* **done** `FormalGroup/OCAdicPi.lean`: `O_{ℂ_p}` is `π`-adically complete for every
  `0 < |π| < 1` (`OC.isAdicComplete_span`, `OC.isAdicComplete_of_map_eq_span`): the completeness
  hypothesis of `Alpha.lean` for `R = O_{K'}` with `𝔪_{K'} O_C = (π)`.
* **done** `FormalGroup/Zp.lean`: `ZpD p` (`ℤ_p` with the discrete uniformity, `ℤ_p → O_{ℂ_p}`)
  discharges all hypotheses (`p ∈ 𝔪`, `𝔪 ↦ m_{ℂ_p}`, `O_{ℂ_p}` complete for `𝔪 O_{ℂ_p}`,
  `GalFixed`): `alphaZp` with `alphaZp_add`, `alphaZp_mul`, `alphaZp_gal`, `alphaZp_torsion`,
  `logGm_alphaZp` ([Hong, Prop. 3.4.9] over `K = ℚ_p`, connected `G`, except injectivity).

## Hand-off (2026-10-18, tenth session)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians
(dimension `d = g`).

Done this session (pushed with green validation): `33a51f4` (`CartierChar`, `Alpha`, `MapFGL`,
`AlphaLog`, `AlphaGal`: **`α` for connected `G = F[p^∞]`** — `T_p(G^∨)(O_C)` points give
group-like `χ_{y_v} ∈ O_C ⊗ A_v`, hence `U_y ∈ O_C[[T]]` with `U_y(Φ) = U_y U_y`,
`α(x)(y) = U_y(x)` bimultiplicative with values in `1 + m_C`, left square = Cartier pairing on
torsion, `u_y = U_y − 1 : F_{O_C} → Ĝ_m`, `dα`, right square via `LogNat`, Galois equivariance)
and the commit with `Zp` (all hypotheses discharged for `R = ℤ_p`) and this hand-off.

**[Hong, Prop. 3.5.1] (discriminant formula): proofs located.** Downloaded (not committed) to
`~/iut-scratch/lit/dl/padic-hodge/disc/` (text via `python3 -I`): [Tate] OCR scan — the
statement is **[Tate, §(2.2), Prop. 2, pp. 164–165]** (over complete noetherian local `R` with
residue char. `p`; *not* §2.3, which is duality, Prop. 3 = `n + n' = h`, p. 166); [Haines,
§2.3, Lemmas 2.3.1–2.3.3, pp. 5–7]; [Lipnowski, Appendix, Claims 2, 2', 2'', pp. 17–19] (B.
Conrad's proof of Tate's Lemma 1, which Tate only reduces to an unproved trace map);
[Stacks, Tags 0BWA, 0BWC, 0BWD, 0BWH, 0BVZ, 0BJF]. See `references/README.md`. Proof plan
(for `R = O_K` a complete DVR, everything free):
  (a) multiplicativity `disc H = (disc H')^{m''} (disc H'')^{m'}` for `0 → H' → H → H'' → 0`
      ([Tate, p. 164–165]; [Haines, Lemma 2.3.2] via `A' ⊗ A ≅ A ⊗_{A''} A` and the tensor /
      transitivity formulas [Haines, Lemma 2.3.1]); étale ⇒ `disc = 1` ([Stacks 0BJF]);
  (b) reduce to `v = 1` and connected `G` via `0 → G_1 → G_{v+1} → G_v → 0` and
      connected–étale;
  (c) `disc(A_1) = N(det J)` with `J = (∂[p]_i/∂T_j)`: [Lipnowski, Claim 2''] (full proof, pure
      linear algebra: `disc = N(τ)` if `Hom_A(R, A) ≅ R`, `Tr ↦ τ`) + [Lipnowski, Claim 2'] =
      Tate's Thm. A.3 in the appendix to Mazur–Roberts (**not available**; Stacks 0BWC/0BWH is
      the polynomial version). Alternative avoiding A.3: compute the trace form of
      `A_1 = R[[T]]/[p](T)` directly in the Weierstrass basis (`WeierstrassFree`) for `d = 1`;
  (d) `det J = p^d · unit` via invariant differentials ([Tate, p. 165]: `[p]^*ω_i = p ω_i`
      for a basis of translation-invariant differentials; needs partial derivatives of power
      series, cf. item 2(a) below).
  Not started (3.5.x waits for items 1–2 below).

Next steps, in order:

1. **Injectivity of `α` on `G(O_K)`** ([Hong, Prop. 3.4.9, proof]). Route (avoids the snake
   lemma): for `x ∈ ker α ∩ G(ℤ_p)` write `x = p x''` in `F(m_C)` (`Divisible.lean`); then
   `α(x'')` is `p`-torsion, so by **perfectness of the level-1 Cartier pairing over `O_C`**
   there is `t ∈ G[p](O_C)` with `α(t) = α(x'')` (`alpha_torsion`), `x' = x'' − t ∈ ker α`,
   `p x' = x`, and `σx' − x' ∈ ker α ∩ G[p] = 0`, so `x' ∈ G(ℤ_p)` (`Invariants.lean`, [Hong,
   Lemma 3.4.2]); hence `x` is infinitely `p`-divisible in `G(ℤ_p)`, `x = 0` ([Hong, Lemma
   3.4.3]). Done: (i) injectivity half of the perfectness of `G_v(O_C) × G_v^∨(O_C) → μ_{p^v}`
   (`eq_one_of_pairing_OC`; the surjectivity half is `pairingHom'_bijective` over `ℂ_p` with
   `card_points_sepClosed` for `#G_v(ℂ_p)`, transported by `pointsOCEquiv`). Missing: (ii) surjectivity of
   `DualTate → G_v^∨(O_C)` (lifting along `i_v^∨`; over `ℚ̄_p` this is
   `exists_dual_quot_eq_padicAlgCl`), (iii) `x ↦ α(x)` determines torsion: `α(t) = 1 ⇒ t = 0`.
2. **`d + d^∨ = h`** ([Hong, Thm. 2.2.19]) — sub-project, all in characteristic `p` (special
   fibre `B_v = A_v ⊗ k`): (a) partial derivatives on `MvPowerSeries` and the chain rule for
   `subst` (not in Mathlib); (b) **`[p]_F(T) ∈ (T_1^p, …, T_d^p)` over `k`** (invariant
   derivations `D_j f = ∂_{U_j} f(Φ(T, U))|_{U=0}` = invertible matrix times `∂/∂T`, and
   `D_j [p] = 0` since `d[p] = p = 0`; [Hong, Prop. 1.5.10, proof]); hence `ker φ_{G_1}` =
   `Spec k[T]/(T^p)` has order `p^d` ([Hong, Cor. 1.5.11, Cor. 2.2.18]); (c) Frobenius `φ` and
   Verschiebung `ψ = φ_{G^∨}^∨` of finite flat `k`-group schemes, `ψ ∘ φ = [p]`
   ([Hong, Prop. 1.5.8], proof via symmetric tensors, which [Hong] takes from Pink's notes, §14); (d) orders in exact
   sequences of finite `k`-group schemes, Cartier duality exchanges kernels and cokernels;
   (e) **for non-connected `G^∨`**: `d^∨` is the dimension of `(G^∨)°`, needing the
   connected–étale sequence and Serre–Tate *essential surjectivity* ([Hong, Thm. 2.2.16, second
   half], uses Prop. 2.2.13). Estimate: several sessions.
3. Tate's theorem [Hong, Thm. 3.4.10] / Cor. 3.4.11 for connected `G` over `ℤ_p`: `dα` is now
   defined (`dalpha`); needs injectivity (1), the `ℚ_p`-linear algebra of (3.9)–(3.11)
   (`tateDualHom`, `sum_finrank_DHT_le` exist), the identification of `DualTate (OC p)` of `G`
   over `ℤ_p` with `T_p(G^∨_{ℚ_p})(ℚ̄_p)` (`dualPDiv`, via `G_v^∨(O_C) = G_v^∨(ℚ̄_p)`), and (2).
4. Base `O_{K'}` (item 4 of the task): `Alpha.lean`, `AlphaLog.lean` are for a general complete
   local `R` with `p ∈ 𝔪_R`; `OCAdicPi` gives the completeness of `O_C` for `𝔪_{K'} O_C = (π)`,
   and `AlphaGal` needs only `σ` to fix `R` (so `σ ∈ Gal(ℚ̄_p/K')`). Missing: a concrete
   `O_{K'}` (Mathlib: integral closure of `ℤ_p` in a finite `K'/ℚ_p`, its local ring /
   adic completeness instances, `O_{K'} → O_C`, `𝔪_{K'} O_C = (π)`), and the Tate-module /
   Hodge–Tate wiring (`tateRep`, `dualPDiv`, `tatePairingZp`) over `K'` instead of `ℚ_p`
   (`GalFixed` quantifies over all of `Gal(ℚ̄_p/ℚ_p)`; `ev_autCp`, `galPt` work per `σ`).
5. Full faithfulness, existence half [Hong, Thm. 3.5.4] (Prop. 3.5.3, Lemma 3.5.2 with the
   discriminant formula above).

## Hand-off (2026-10-18, ninth session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`), for `p`-divisible groups of Jacobians,
so formal groups of **dimension `d = g`** (everything below is for arbitrary `d`, `d'`).

Done this session (all pushed with green validation, `origin/main`): `0e22c06`
(`Filtration`, `LayerLimit`, `SerreTateHom`: [Hong, Lemma 2.2.14, Lemma 2.2.15]
`R[[T]] ≅ lim_v A_v`, and **[Hong, Thm. 2.2.16] full faithfulness**
`FGL.Hom.pdivEquiv : Hom(F, F') ≃ Hom(F[p^∞], F'[p^∞])`, hypothesis `p ∈ 𝔪_R`; no
noetherianity of `R[[T]]` needed: the coefficient filtration `N_w` replaces the `(𝔪, T)`-adic
topology, so Mathlib's missing `IsNoetherianRing (MvPowerSeries (Fin n) R)` is not a blocker),
`202ad58` (`LayerLimitBase`: `S[[T]] ≅ lim_v S ⊗_R A_v` for `S` complete for `𝔪_R S`, and
compatible group-like families `b_v ∈ S ⊗ A_v` give `U ∈ S[[T]]` with
`U(Φ(T, T')) = U(T) U(T')`), `1837e2f` (`OCAdic`: `O_{ℂ_p}` is `p`-adically complete; hand-off) and the commit with
`PointsOC` (`U(x +_F y) = U(x)U(y)` for group-like `U ∈ O_{ℂ_p}[[T]]`).

**[Hong, Prop. 3.5.1] (discriminant formula `disc(A_v/O_K) = (p^{d v p^{hv}})`)**: no proof in
the local literature. [Hong] states it without proof (remark after Prop. 3.5.1: sketch via
`0 → G_1 → G_{v+1} → G_v → 0`); [Horawa] (`tate/horawa.txt`, Prop. 2.9.3) gives the same sketch
and says "This is hard so we omit the details"; [BC] (`bc.txt`) has no discriminant formula for
finite flat group schemes (its discriminants are those of field extensions, §13). [Tate] is not
available locally. A proof has to be found elsewhere (e.g. [Tate, §2.3, Prop. 2] or Faltings–
Chai / Messing) or reconstructed: `disc(A_1) = (p^{d p^h})` via `Ω_{A_1/O_K} ≅ A_1 ⊗ ω_{G_1}`,
`ω_{G_1} ≅ (O_K/p)^d` for `G_1 = F[p]` (the cotangent space of `A_1 = R[[T]]/[p](T)` is
`(T)/((T)^2 + [p](T)) ≅ (R/p)^d` by [Hong, Lemma 2.2.14] = `mulPS_sub_mem`), different = Fitting
ideal of `Ω`, discriminant = norm of different, and multiplicativity in towers.

Next steps, in order:

1. **`α` for connected `G = F[p^∞]`** ([Hong, Prop. 3.4.9]). Available: `exists_groupLike`
   (`S = O_{ℂ_p}`, needs an `Algebra ℤ_[p] (OC p)` instance compatible with the existing
   `[Algebra R (OC p)]` setups, and `OC.isAdicComplete_padicInt`). Remaining:
   (a) `T_p(G^∨)` points as group-likes: a point `y ∈ G_v^∨(S) = Hom_alg(A_v^∨, S)` is a group-like
   element of `S ⊗ A_v` (Cartier: `CartierPairingBase.hat`/`theta`, `CartierDouble`), compatible
   in `v` along `inclB`; over `ℚ̄_p` the values lie in `O_{ℚ̄_p} ⊆ O_{ℂ_p}` (integrality of finite
   `ℤ_p`-algebras). Note `dualPDiv` is only defined over `ℚ_p` (generic fibre); work with
   `(G_v)^∨` over `ℤ_p` levelwise.
   (b) evaluation of `U ∈ O_{ℂ_p}[[T]]` at `x ∈ F(m_{ℂ_p})`: **done** (`PointsOC.lean`, synonym
   `OCd p`; `ev_add_of_groupLike`). To combine with `exists_groupLike` take `S = OCd p` with
   `Algebra ℤ_[p] (OCd p)` and `OC.isAdicComplete_padicInt` (transported along the synonym).
   (c) `α(x)(u) = U_u(x)`, homomorphism in `x` (from `U(Φ) = U·U`) and in `u`, Galois-equivariant;
   left square of [Hong, Prop. 3.4.9] (on torsion: the Cartier pairing `tatePairing`); right square
   via `LogNat`-type argument for `log(U(x))` (`dα`).
   (d) injectivity of `α` on `G(O_K)` ([Hong, Lemma 3.4.2, 3.4.3], `Invariants.lean`).
2. **`d + d^∨ = h`** ([Hong, Thm. 2.2.19]): needs [Hong, Prop. 2.2.13] (structure of
   `lim(A_v ⊗ k)` via Frobenius kernels), Cor. 2.2.18 (`ker φ_G` has order `p^d`), Frobenius and
   Verschiebung of finite flat group schemes in characteristic `p` (Prop. 2.1.12) and their Cartier
   duality, and the dual `p`-divisible group over `R` (not only over `ℚ_p`). For `G = F[p^∞]`
   connected: `ker φ` on `A_1 ⊗ k = k[[T]]/[p](T)` is `k[T]/(T^p)`. A separate project; without
   it Tate's argument only gives `d + d^∨ ≤ h`.
3. Then Tate's theorem [Hong, Thm. 3.4.10] / Cor. 3.4.11 (`ℚ_p`-linearity of `dα` suffices for
   the dimension count over `K = ℚ_p`), Hodge–Tate [Hong, Thm. 3.4.12] via the existing
   `sum_finrank_DHT_le`, `isHodgeTate_of_exact_of_disjoint`; the connected–étale sequence for
   `G(O_{ℂ_p})` ([Hong, Prop. 3.2.5]) for non-connected `G` (connected part as `F[p^∞]` needs
   Serre–Tate *essential surjectivity*, [Hong, Thm. 2.2.16, second half], which again needs
   [Hong, Prop. 2.2.13]).
4. **Full faithfulness, existence half** [Hong, Thm. 3.5.4]: [Hong, Prop. 3.5.3] (scheme-theoretic
   closure of a Galois-stable summand), Lemma 3.5.2 (needs Cor. 3.4.11 and Prop. 3.5.1; see above).
5. Base `O_K` instead of `ℤ_p`: the Galois/Tate-module wiring (`tateRep`, `dualPDiv`,
   `tatePairingZp`) is over `ℚ_p`; [LocAn] needs finite `K'/ℚ_p`.

## Hand-off (2026-10-18, eighth session; superseded)

Scope reminder (`~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs only
Tate's Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`), whose proof in [Hong, Thm.
3.5.4] uses Tate's theorem [Hong, Thm. 3.4.10 / Cor. 3.4.11] (dimension of `G` from `T_p G`)
and the discriminant formula [Hong, Prop. 3.5.1] (stated in [Hong] without proof).

Done this session (all pushed with green validation, `origin/main`): `3630199`, `0ad70ec`
(`WeierstrassFree`, `GmHeight`: **`Ĝ_m` is `p`-divisible of height 1**; `GmMu`:
**`Ĝ_m[p^∞] ≅ μ_{p^∞}`**, `T_p` iso), `6e6c08b` (`GroupScheme/Faithful`: **`Hom.ext_of_mapTate`,
`Hom.ext_of_baseChange`** — faithfulness of `G ↦ T_p G(Ω)` and of the generic fibre functor,
i.e. the uniqueness half of [Hong, Thm. 3.5.4]), `6d9163d` (`ExactSeq`: [Hong, Prop. 3.4.7] for
`G = F[p^∞]`), `36398e4` (`FGLHom`: formal homomorphisms induce `F[p^∞] → F'[p^∞]`),
`387c52f` (`FGLHomPoints`: on points, Galois-equivariant, compatible with the layers),
`2d67761` (`LogNat`: **`log_{F'} ∘ f = df · log_F`**, the right square of [Hong, Prop. 3.4.9]),
and the commit with `GmHom` (`F → Ĝ_m` gives `F[p^∞] → μ_{p^∞}`) and this hand-off.

Next steps, in order (each a validated increment; split further if blocked):

1. **Serre–Tate for `G = F[p^∞]`** ([Hong, Prop. 2.2.13, Thm. 2.2.16]): `R[[T]] ≅ lim_v A_v`
   (injective since `J_v ⊆ (𝔪, T)^v`, from `[p](T) ∈ 𝔪T + (T)^2`, plus Krull; surjective needs
   `J_v` closed in `R[[T]]`). **Blocker**: Mathlib (81a5d25) has `IsNoetherianRing R⟦X⟧` but not
   for `MvPowerSeries (Fin d) R`; do `d = 1` first (via `FGL.fin1Equiv`), or prove closedness of
   `J_v` directly from the basis of `R[[T]]` over `[p^v]^*` (`freeVia_psiV`, coordinates are
   `(T)`-adically continuous). Then `Hom(F[p^∞], F'[p^∞]) = Hom(F, F')` (`FGL.Hom.toPDiv` is the
   map; inverse: a compatible family of Hopf maps gives a power series in the limit).
2. **`α` for connected `G = F[p^∞]`** ([Hong, Prop. 3.4.9]): needs formal homomorphisms
   `F_{O_C} → Ĝ_m` with coefficients in `O_{ℂ_p}`; the `Pt`/`ev` framework requires a *discrete*
   coefficient ring `R → O_{ℂ_p}`, so add a variant with bounded coefficients in `O_{ℂ_p}`
   (evaluation converges for `|x| < 1`). Then `T_p(G^∨) ≅ Hom(F_{O_C}, Ĝ_m)` (via 1. over `O_C`,
   (3.7)), `α(x)(u) = 1 + u(x)`, `dα` from `LogNat` (`logF_ptMap`), injectivity of `α` on
   `G(O_K)` ([Hong, Lemma 3.4.2, 3.4.3]: `Invariants.lean` has both).
3. **`d + d^∨ = h`** ([Hong, Thm. 2.2.19]) and the general (non-connected) `G` over `O_K`:
   connected–étale sequence for `G(O_C)` ([Hong, Prop. 3.2.5]); then Tate's theorem
   [Hong, Thm. 3.4.10] and the Hodge–Tate decomposition [Hong, Thm. 3.4.12] as in the
   sixth-session plan (`tateDualHom`, `sum_finrank_DHT_le`, `isHodgeTate_of_exact_of_disjoint`).
4. **Full faithfulness, existence half** [Hong, Thm. 3.5.4]: uniqueness is done
   (`Hom.ext_of_baseChange`). Existence: [Hong, Prop. 3.5.3] (closure of a Galois-stable direct
   summand of `T_p G`), [Hong, Lemma 3.5.2] (an iso on generic fibres is an iso; needs
   Cor. 3.4.11 and the discriminant formula Prop. 3.5.1, plan (a)–(d) of the fifth hand-off).

## Hand-off (2026-10-18, seventh session; superseded)

Done this session (all pushed with green validation): `abc5a8d` (`AdicEval`, `LayerFree`:
`A_v` free of rank `p^{hv}`), `1887dff` (`AdicPoints`, `LayerHopf`, `LayerPDiv`: Hopf algebras
`A_v` and the `p`-divisible group `F[p^∞]`), `31b5da2` (`LayerSurj`), `8b69b45` (`FormalInv`),
`0053520` (`LayerTate`), `fd662ee` (`isConnected_groupScheme`, this hand-off), and the commit
adding `Lift`, `Divisible` ([Hong, Prop. 3.2.7] for `F[p^∞]`, step 2 below). Step 1
of the sixth-session plan ([Hong, Prop. 2.2.10] (a)–(d)) is complete, with the deviations
recorded above (height part of the datum; antipode `[p^v − 1]`; Weierstrass preparation not
used, so no example of a `p`-divisible formal group law (e.g. `Ĝ_m` over `ℤ_p`, height 1) is
formalised yet). Steps 2–3 were not started.

Next steps, in order:

1. **`Ĝ_m` is `p`-divisible of height 1** over `ℤ_p` (needs: `ℤ_p[[t]]` free over itself via
   `t ↦ (1+t)^p − 1` with basis `1, …, t^{p−1}`; Mathlib has `PowerSeries` Weierstrass division,
   `Mathlib/RingTheory/PowerSeries/WeierstrassPreparation.lean`; iterate it and take
   `(t)`-adic limits as in `FormalInv.lean`); compare `PDivFGL.pdivGroup` with `μ_{p^∞}`.
2. **done** ([Hong, Prop. 3.2.7] for `G = F[p^∞]`, `Divisible.lean`). Remaining from it:
   `exists_tate_of_divisible` now gives `T_p F ↠ F(m)[p^v]`; the exact sequence
   `0 → T_p F → … ` of [Hong, Prop. 3.4.7] in the form `0 → G(O_C)[p^∞] → G(O_C) → t_G(C) → 0`
   for connected `G = F[p^∞]` (`ker_logHom`, `PDivFGL.logF_surjective`).
3. **Tate's theorem** ([Stix, Thm. 91], [Hong, Thm. 3.4.10]) and the **Hodge–Tate
   decomposition** ([Hong, Thm. 3.4.12]): unchanged from the sixth-session plan (formal group of
   `G°` = Serre–Tate [Hong, Prop. 2.2.13, Thm. 2.2.16]; `G(O_C)` and the connected–étale
   sequence [Hong, Prop. 3.2.5]; `d + d^∨ = h` [Hong, Thm. 2.2.19]; then `α`, `dα` of
   [Hong, Prop. 3.4.9] with `logF_galPt`, `tateDualHom`, `sum_finrank_DHT_le`,
   `isHodgeTate_of_exact_of_disjoint`). For connected `G = F[p^∞]` the identification
   `T_p G ≅ T_p F` is now available (`tateEquiv`).
4. **Full faithfulness** [Hong, Thm. 3.5.4]: plan (a)–(d) of the fifth hand-off.

## Hand-off (2026-10-18, sixth session; superseded)

Done this session (all pushed with green validation): the formal-group drafts were moved into
`PadicHodge/FormalGroup/` and finished (`2742552`), [Hong, Prop. 3.3.6 (1)–(4)] with inverses
(`762011a`), formal identities, torsion, Galois action, `Ĝ_m`, layers (`a04dcc8`), layer points
(`bd2d774`), `log_{Ĝ_m} = log` (`3089268`), Galois invariants and [Hong, Lemma 3.4.3]
(`9f3ed00`), Tate module `T_p F` (`a8786ca`). See PH4 above. Items 1–2 of the fifth-session
plan were only partly reached: step 1 (Prop. 3.3.6) is complete; step 2 (Prop. 2.2.10) has the
ideals, layers, transition maps and the torsion points but not yet finiteness nor the group
scheme structure; steps 3–4 were not started.

Next steps, in order:

1. **Finish [Hong, Prop. 2.2.10]** (connected `p`-divisible group `F[p^∞]` of a `p`-divisible
   formal group law; base `R` complete noetherian local, e.g. `ℤ_p`):
   (a) *finiteness*: assume `[p]_F^* : A → A` makes `A = R[[T]]` finite free of rank `p^h` over
   itself (definition of height `h`); show `A_v ≅ R ⊗_{A, [p^v]^*} A` (`J_v = [p^v]^*(I) A`,
   `mem_span_X`) is finite free of rank `p^{hv}` (`[p^{v}]^* = ([p]^*)^v` by `subst_mulPS`,
   freeness in towers);
   (b) *group structure*: topologise `A_v ⊗_R A_v` (finite free over `R`, `t_i` nilpotent mod
   `m_R` because `A_v/m_R A_v` is a finite local `k`-algebra) and define the comultiplication
   `t ↦ Φ(t ⊗ 1, 1 ⊗ t)` by `MvPowerSeries.eval₂`; counit `t ↦ 0`; antipode from the **formal
   inverse** `ι(T)` ([Hong, Lemma 2.2.5 (3)]: degree-by-degree, not yet done — only inverses of
   points exist); Hopf axioms from `addPS_assoc/comm/zero`; package as `FFGroupScheme`;
   (c) `PDivGroup` with `incl = layerIncl` (surjective, done) and the kernel condition on
   `S`-points: the convolution power `y^{p^v}` is `y ∘ [p^v]^*`;
   (d) `layerPt` surjective over `ℚ̄_p`/`O_{ℂ_p}` (points of a finite `R`-algebra are integral,
   so `|f(t_i)| ≤ 1`, and `t_i^N ∈ m_R A_v` gives `< 1`), identifying
   `F[p^v](ℚ̄_p) ≅ F(m)[p^v]` Galois-equivariantly, hence `T_p F[p^∞] ≅ lim F(m)[p^v]`.
2. **Tate's theorem** ([Stix, Thm. 91], [Hong, Prop. 3.4.7, 3.4.9, Thm. 3.4.10]): needs, beyond
   1., the formal group of `G°` for a `p`-divisible group `G` over `ℤ_p`/`O_K` ([Hong, Prop.
   2.2.13, Thm. 2.2.16], Serre–Tate), `G(O_{ℂ_p})` with `0 → G°(O_C) → G(O_C) → G^{et}(O_C) → 0`
   ([Hong, Prop. 3.2.5]), `d + d^∨ = h` ([Hong, Thm. 2.2.19]); then `α`, `dα` as in
   [Hong, Prop. 3.4.9] using `logF_galPt`, `gm_logF_surjective`/`gm_logF_eq_zero_iff` (bottom
   row), `tateDualHom`, and the dimension count via `sum_finrank_DHT_le`; the splitting step is
   `isHodgeTate_of_exact_of_disjoint`. For `p`-divisible formal groups over `ℤ_p` themselves,
   `F(m_{ℂ_p})` is `p`-divisible ([Hong, Prop. 3.2.7]; needs Weierstrass preparation /
   finiteness of `[p]`) and then `logF_surjective_of_divisible` gives Prop. 3.4.7 for `G°`.
3. **Full faithfulness** [Hong, Thm. 3.5.4]: unchanged plan (a)–(d) of the fifth hand-off.

## Hand-off (2026-10-17, fifth session; superseded)

Done this session (pushed `c278a2c`, validation green): items 1 and 2 of the fourth-session
list. **Hilbert 90 for `\hat{ℚ_p^{ur}}`** (`Hilbert90/`, `exists_hilbert90`) and **`V_p G`
Hodge–Tate with all weights `0` for `G` over `ℤ_p` with étale layers**
(`isHodgeTate_tateRep_of_etale`, over every finite `L/ℚ_p`); **`V_p(G^∨) ≅ V_p(G)^∨ ⊗ ℚ_p(1)`**
(`tateRepDualEquiv_gal`) and `isHodgeTate_tateRep_dualPDiv`. Deviation from the plan of
item 1: no `ℚ_p^{ur}`/Frobenius element is constructed; the fields generated by the points of
the layers are shown to be unramified (Frobenius periodicity mod `p`) and rigid, which is all
the descent needs. The base is `ℤ_p` (the only base for which `PDivGroup` points are wired to
Galois representations so far); `O_K` needs `K`-versions of `tateRep`/`IsInertia`.

**Unvalidated drafts** (not in the repository; copied to
`~/iut-scratch/padic-hodge-drafts/FormalGroup/`): `Law.lean` (`FGL R d`, [Hong, Def. 2.2.3]
with axioms (i)–(iii) via `MvPowerSeries.subst`; compiles), `OC.lean` (`O_{ℂ_p}` as complete
linearly topologised ring, `norm_eval₂_le`; compiles after the last fixes up to warnings),
`Points.lean` (commutative monoid `F(m_{ℂ_p})` via `MvPowerSeries.eval₂_subst`, coefficients in
a discrete ring `R` with `Algebra R O_{ℂ_p}`; last compile had only `pt_ext`-argument errors,
fixed but not re-checked), `Log.lean` (never compiled: `norm_add_sub_le`
`|Φ(x,y) − x − y| ≤ r²` via the mixed-monomial decomposition, [Hong, Lemma 3.3.2]
`bnd_p_nsmul`, `exists_bnd_pow`, the logarithm `logF` as `lim (p^n x)/p^n` and `logF_add`).
Next steps, in order:

1. **Formal groups and the logarithm**: finish the drafts above (re-check `Points.lean`; in
   `Log.lean` replace the `rw`-chains in `exists_bnd_pow` by explicit `calc`s, `ha1` by
   `fin_cases`), then [Hong, Prop. 3.3.6 (2)–(4)]: `log_F` is an isometry on
   `{|x| ≤ |p|^λ}`, `λ > 1/(p−1)` (needs the inverse of `[p]` on that disc or the formal
   logarithm power series), `ker log_F = F(m)_tors`, `F(m) ⊗ ℚ_p ≅ ℂ_p^d`; inverses of points
   ([Hong, Lemma 2.2.5 (3)]) are needed for the group structure (or work with the monoid and
   cancel via `log`).
2. **Connected `p`-divisible group of a `p`-divisible formal group law** ([Hong, Prop. 2.2.10]:
   `A_v = R[[T]]/[p^v](I)`, finite free when `[p]` is finite flat) as a `PDivGroup`, and the
   identification of its `ℚ̄_p`-points with `F(m)[p^v]` (torsion points of the open polydisc).
3. **Tate's theorem** [Stix, Thm. 91], [Hong, Prop. 3.4.9, Thm. 3.4.10]: the maps `α`, `dα`;
   needs `T_p(G^∨) ≅ Hom(F_{O_C}, Ĝ_m)` (formal homomorphisms from compatible group-like
   elements) and `d + d^∨ = h` ([Hong, Thm. 2.2.19], via Frobenius/Verschiebung in
   characteristic `p` — a separate project) — or, as a shortcut for the dimension count, use
   Serre–Tate: `dim D_0(V_p G) + dim D_{-1}(V_p G) ≤ h` (`sum_finrank_DHT_le`) together with
   the two injections `t_G(K) ↪ D(V_p G(-1))`, `t_{G^∨}(K) ↪ D(V_p G)` and `d + d^∨ = h`.
   The final splitting step is `isHodgeTate_of_exact_of_disjoint` (`HodgeTate/Splitting.lean`),
   the weights of `V_p(G^∨)` follow from `tateRepDualEquiv_gal`.
4. **Full faithfulness** [Hong, Thm. 3.5.4, Cor. 3.5.5]: Proposition 3.5.1 (the discriminant of
   `A_v / O_K` is generated by `p^{d v p^{h v}}`) is stated in [Hong] without proof (sketch via
   `0 → G_1 → G_{v+1} → G_v → 0`, multiplicativity of discriminants in towers, and
   `disc(A_1) = p^{d p^h}` from `ω_{G_1} ≅ (O_K/p)^d`); plan: (a) discriminant of a finite flat
   group scheme as the norm of the different, (b) the different of `A_v` from `Ω_{A_v/O_K}`
   and the cotangent space ([Hong, Lemma 3.5.2]), (c) [Hong, Prop. 3.5.3]
   (`G' ⊆ G_K`-closure argument comparing discriminants of the scheme-theoretic closure),
   (d) Theorem 3.5.4 by induction on `v` using (c). Not attempted this session.

## Hand-off (2026-10-17, fourth session; superseded)

Done this session (all pushed, validation green): items 1–3 of the third-session list completely
(`CartierPerfect.lean`, `CartierDualPDiv.lean`, `TateFree.lean`, `TatePerfect.lean`,
`TateDual.lean`), the
unramifiedness half of item 4 (`EtaleUnramified.lean`, `TateRep.lean`), the representation
`V_p G` (`TateRep.lean`), and the finite-image case of Hodge–Tate weight `0`
(`HodgeTate/FiniteImage.lean`). Next steps, in order:

1. **Hodge–Tate weight `0` for étale `G` over `ℤ_p` (then `O_K`)**: `V_p G` is unramified
   (`tateRep_baseChange_eq_one_of_isInertia`) but in general of infinite image, so
   `isHodgeTate_tateRep_of_trivial_on` does not apply. Needed: Hilbert 90 for
   `\hat{ℚ_p^{ur}}`, i.e. for `A ∈ GL_h(ℤ_p)` (Frobenius on `T_p`) a solution
   `X ∈ GL_h(O_{\hat{ℚ_p^{ur}}})` of `X = A φ(X)`. Plan: (a) `ℚ_p^{ur}` as the intermediate field
   generated by the roots of unity of order prime to `p`, Frobenius `φ` (`ζ ↦ ζ^p`), its fixed
   field `ℚ_p`, and its closure in `ℂ_p` = `ℂ_p^{I}` (Ax–Sen–Tate, `galCp_eq_self_iff_mem_closure`);
   (b) finite level: for `A` of finite order mod `p^k` the equation is solvable in a finite
   unramified `M / ℚ_p` by Galois descent for `O_M / p^k` (the trace/Dedekind argument of
   `FiniteImage.lean` works integrally since unramified traces are surjective and the
   discriminant is a unit); (c) lift solutions mod `p^k` to mod `p^{k+1}` (additive Hilbert 90 /
   normal basis for the residue extension) and pass to the limit in the complete
   `O_{\hat{ℚ_p^{ur}}}`; (d) then `(ℂ_p ⊗ V)^{G_{ℚ_p}}` contains the `h` columns of `X`, and
   `finrank_DHT_zero` follows as in `finrank_DHT_zero_of_trivial_on`.
2. **`V_p(G^∨) ≅ V_p(G)^*(1)` as representations**: the `ℤ_p`-level statement is done
   (`TateDual.lean`: `tateDualHom : T_p(G^∨) ≃ Hom_{ℤ_p}(T_p G, ℤ_p)` bijective, `ℤ_p`-bilinear,
   `tateDualHom_gal`). Remaining: base change to `ℚ_p` (`Hom_{ℤ_p}(T, ℤ_p) ⊗ ℚ_p ≅
   Hom_{ℚ_p}(T ⊗ ℚ_p, ℚ_p)` for `T` free of finite rank), the resulting `G_L`-equivariant
   isomorphism `tateRep (dualPDiv G) ≅ (tateRep G).dual ⊗ charRep 1`, and transport of
   `IsHodgeTate` along it (`isHodgeTate_of_exact` with an isomorphism), so that
   `isHodgeTate_dual`, `isHodgeTate_tprod`, `isHodgeTate_charRep` give HT of `V_p(G^∨)` from HT
   of `V_p G`.
3. **Formal Lie groups and the logarithm** ([Stix, §11.1, Example 81 (3), Lemma 82,
   Cor. 83–84, §11.3.1–11.3.2, Lemma 86, Cor. 87]; [Hong, §3.2: Def. 3.2.1, Prop. 3.2.3,
   Cor. 3.2.4, Prop. 3.2.5, Cor. 3.2.6, Prop. 3.2.7; §3.3: Def. 3.3.1, Lemmas 3.3.2–3.3.3,
   Def. 3.3.4, Prop. 3.3.6]). This needs the Serre–Tate equivalence between connected
   `p`-divisible groups over `O_K` and divisible formal group laws ([Hong, Thm. 2.2.16]; in
   particular `lim A_v° ≅ O_K[[t_1, …, t_d]]`), which is a separate project; a possible shortcut
   is to *define* the connected part through a formal group law `μ` with `G° = μ[p^∞]` and
   prove Tate's theorem for those, as [Hong] does after Thm. 2.2.16.
4. **Tate's theorem** [Stix, Thm. 91] / [Hong, Prop. 3.4.9, Thm. 3.4.10] (`G(O_K) ≅
   Hom_Γ(T_p G^∨, 1 + m_{ℂ_K})`, `t_G(K) ≅ Hom_Γ(T_p G^∨, ℂ_K)`; uses Tate's `H⁰`, `H¹` of
   `ℂ_p(j)`, `TateSen/TateH1.lean`), then the Hodge–Tate decomposition [Hong, Thm. 3.4.12],
   [Stix, Cor. 92] via `isHodgeTate_of_exact_of_disjoint` (`HodgeTate/Splitting.lean`).
5. **Full faithfulness** [Hong, Thm. 3.5.4, Cor. 3.5.5] needs the discriminant formula
   [Hong, Prop. 3.5.1] (`disc(A_v / O_K) = (p^{d v p^{hv}})`; only sketched in [Hong], via
   Haines' notes) and [Hong, Lemma 3.5.2, Prop. 3.5.3]; plan: compute the different of `A_v`
   from the cotangent space `ω_{G_v} ≅ (O_K/p^v)^d` and the Cartier-duality trace form.

## Hand-off (2026-10-17, third session; superseded)

Literature found (free, downloaded to `~/iut-scratch/lit/dl/padic-hodge/tate/`, not committed;
see `references/README.md`): [Stix] (Heidelberg course notes, §11: Tate's proof of the
Hodge–Tate decomposition after [Tate, §4] and Shatz) and [Hong] (Notes on p-adic Hodge theory,
Ch. II §3.4–3.5: Hodge–Tate decomposition and Tate's full faithfulness, Thm. 3.5.4). [Tate]
itself was not found freely.

Done this session (all in `GroupScheme/`): `|G| = |G⁰|·|G^{et}|` (`EtaleQuotientOrder.lean`);
Cartier pairing over `R`-algebras (`CartierPairingBase.lean`); quotient maps `G_{v+1} → G_v`,
morphisms of `p`-divisible groups, `T_p` functor (`PDivisibleHom.lean`); base change
(`BaseChange.lean`); dual homomorphisms and the Galois-equivariant Cartier pairing
`T_p G × lim G_v^∨ → ℤ_p(1)` (`TatePairing.lean`); finite flat group schemes killed by an
invertible integer are étale (`EtaleInvertible.lean`); `#G(K) = |G|` for étale `G` over a
separably closed field, `#G_v(ℚ̄_p) = p^{hv}` (`EtalePoints.lean`); `quot_v` surjective on
`ℚ̄_p`-points (`PDivisiblePoints.lean`). Next steps, in order:

1. **Perfectness of the Cartier pairing over `ℚ̄_p`** ([Stix, §11.2.2], [Hong, Prop. 3.4.6]).
   (a) Injectivity of `G^∨(K) → Hom(G(K), K^×)` for `G` étale over separably closed `K`: take
   the basis `b_x = e⁻¹(δ_x)` of `A` from `equivPiOfIsSepClosed`; `⟨φ_y, ψ⟩ = ψ(b_y^*)`
   (`pairing_eq_sum`), so `ψ` is determined. (b) `#Hom(M, K^×) ≤ #M` (Mathlib
   `linearIndependent_monoidHom`). (c) `G^∨` killed by `n` when `G` is: for a group-like
   `u ∈ S ⊗ A` (a character), `[n]^*(u) = u^n`; equivalently show `[n]_{G^∨} = ([n]_G)^∨`
   (transpose of `μ^{(n)} ∘ Δ^{(n)}`), then `EtaleInvertible` gives `G_v^∨` étale over `ℚ_p`,
   `#G_v^∨(ℚ̄_p) = p^{hv}` and the levelwise pairing is perfect by counting.
2. **Cartier dual `p`-divisible group.** Show `(G_v^∨, quot_v^∨)` is a `PDivGroup`: closed
   immersion = `quot_v^*` injective with torsion-free cokernel (over a PID `R`; over `ℚ_p`
   from surjectivity on `ℚ̄_p`-points + étaleness), kernel condition = exactness of
   `0 → G_1 → G_{v+1} → G_v → 0` (fppf; over a field: counting). Then
   `DualTate G ≅ T_p(G^∨)` and `T_p(G^∨) ≅ Hom(T_p G, ℤ_p(1))` from 1.
3. `T_p G(ℚ̄_p) ≅ ℤ_p^h`: surjectivity of `T_p G → G_v` from `quot_surjective_padicAlgCl`
   (sequential lifting; beware the dependent indices `G (v + n)`), and the structure of
   `G_v(ℚ̄_p)` (`#G_v[p^w] = p^{hw}`, hence `≅ (ℤ/p^v)^h`).
4. Étale `p`-divisible groups over `O_K`: Hodge–Tate weight `0` needs Hilbert 90 for
   `\hat{K^{ur}}` (`H¹(Gal(K^{ur}/K), GL_n(\hat{K^{ur}})) = 1`, successive approximation + Lang)
   and unramifiedness of `T_p` (points over `O_{\hat{K^{ur}}}` lift uniquely).
5. Formal Lie groups of connected `p`-divisible groups, the logarithm ([Stix, §11.3, Lemma 86,
   Cor. 87]; [Hong, §3.3]), Tate's Theorem 91 / [Hong, Thm. 3.4.10] (`G(O_K) ≅ Hom_Γ(T_p G^∨,
   1 + m_{ℂ_K})`, `t_G(K) ≅ Hom_Γ(T_p G^∨, ℂ_K)`), then the decomposition [Hong, Thm. 3.4.12]
   using `isHodgeTate_of_exact_of_disjoint` (`HodgeTate/Splitting.lean`) and Tate's `H¹`
   (`TateSen/TateH1.lean`); full faithfulness [Hong, Thm. 3.5.4] additionally needs the
   discriminant formula [Hong, Prop. 3.5.1] (proof only sketched there; Haines' notes §2.3).

## Hand-off (2026-10-17, second session; superseded)

Done this session: Cartier duality (dual Hopf algebra, double duality, `D(M)^∨ ≅ M_R`), the
connected component `G⁰` over a complete local ring and the `G⁰`-invariants `A^{et}`,
`ℚ_p(j)` and `V_p μ_{p^∞}` Hodge–Tate. Next steps, in order:

1. **Étale quotient** (`EtaleQuotient.lean`: `G^{et}` as an `FFGroupScheme` over a complete
   local PID, `G^{et}` étale, `ker(G → G^{et}) = G⁰`, `A` faithfully flat over `A^{et}` are
   done): remaining is `|G| = |G⁰| · |G^{et}|`. Plan: (i) Galois isomorphism
   `A ⊗_{A^{et}} A ≅ A ⊗_R A⁰`, `x ⊗ y ↦ (x ⊗ 1) coactConn y`, inverse `x ⊗ π y ↦ ∑ x S(y₁) ⊗ y₂`
   (well defined since `i₁⁻¹ i₂ ∈ G(A ⊗_{A^{et}} A)` is trivial on `A^{et}`, hence factors through
   `G⁰` by `mapPoints_etaleQuotientHom_eq_one_iff`); (ii) base change to `K = Frac R`:
   `A^{et}_K ≅ ∏ L_i` (Mathlib: étale over a field), `A_K = ∏ A_K e_i` with `A_K e_i` an
   `L_i`-space of dimension `r_i > 0` (faithful flatness), and (i) gives `r_i² = r_i |G⁰|`;
   hence `dim_K A_K = |G⁰| · dim_K A^{et}_K`. Henselian version
   needs idempotent lifting along finite algebras (Stacks 04GG), not in Mathlib.
2. **Cartier pairing over `S`** (done over `R`, `CartierPairing.lean`): base change `S ⊗ A`;
   then `T_p(G^∨) ≅ Hom(T_p G, ℤ_p(1))` (needs the Cartier dual of a `p`-divisible group, i.e.
   the quotient maps `[p] : G_{v+1} → G_v`).
3. ~~Constant `p`-divisible group `ℚ_p/ℤ_p`~~ **done** (`ConstPDiv*.lean`). Next: morphisms
   and base change of `p`-divisible groups, the étale `p`-divisible groups over `O_K` (unramified
   `T_p`, weight `0` via Hilbert 90 for `\hat{K^{ur}}`).
4. **Formal Lie groups** of connected `p`-divisible groups and Tate's Hodge–Tate decomposition
   `T_p G ⊗ ℂ_p ≅ ℂ_p(1)^d ⊕ ℂ_p^{h-d}`; then full faithfulness ([Tate] Thm. 4). [Tate] is not
   available locally; its arguments must be reconstructed and written up.
