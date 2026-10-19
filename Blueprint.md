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
* **done** `GroupScheme/HaarIntegral.lean` (19th session; [Farnsteiner, *Hopf modules and
  integrals: the fundamental theorem*, Theorem = Larson–Sweedler Prop. 1], local copy
  `~/iut-scratch/lit/dl/quotients/`): over **any** commutative ring, for `K = Spec E` finite
  flat, `haarProj b f = ∑ₖ bₖ^* ⇀ (bₖ f)` is an integral (`mul_haarProj`) and
  `∑ⱼ (bⱼ^* ∘ S) ⇀ haarProj b (bⱼ) = 1` (`sum_hit_haarProj`); applied to `H^∨`:
  **`exists_invariant_forms`**: `H`-invariant forms `tᵢ` on `O(H)` and `Λᵢ` with
  `∑ tᵢ(Λᵢ x) = ε(x)`.
* **done** `GroupScheme/Quotient.lean` (19th session; Kreimer–Takeuchi argument via integrals,
  [Böhm, arXiv:math/0409513, Intro/§4]): for a closed immersion `i : H → G` (`O(G) ↠ O(H)`) over
  **any** commutative ring: coaction `Hom.coact`, invariants `B = Hom.invariants`, `B`-linear
  traces, dual basis `a = ∑ xₛ trⱼ(yₛ a)`, **`Hom.projective_invariants`** (`A` f.g. projective
  over `B`) and **`Hom.canEquiv : A ⊗_B A ≃ₐ[A] A ⊗_R C`** (`G ×_{G/H} G ≅ G × H`).
* **done** `GroupScheme/QuotientGroup.lean` (19th session): **[Hong, Thm. 1.1.9]** over a local
  PID (`O_{K'}`, `ℤ_p`, fields): `B` a finite free sub-Hopf algebra, **`Hom.quotient i = G/H`**,
  `Hom.quotientHom : G → G/H`, `A` free of rank `|H|` over `B` (`nonempty_basis_invariants`),
  **`Hom.order_eq_mul : |G| = |H| · |G/H|`**, `ker i = A · B⁺` (`mem_span_of_apply_eq_zero`),
  **exactness of `H(T) → G(T) → (G/H)(T)`** for every `R`-algebra `T`
  (`mapPoints_quotientHom_eq_one_iff`, `mapPoints_injective_of_surjective`). No debt.
* **done** `GroupScheme/QuotientMap.lean` (19th session): functoriality `Hom.quotientMap`
  (`f : G → G'`, `f(H) ⊆ H'` gives `G/H → G'/H'`); for `K ⊆ H ⊆ G`: `H/K → G/K` is a closed
  immersion (`surjective_subQuot`; retraction `A → A^K` by Nakayama, `exists_retraction`, written
  through the dual basis), `(A^K)^{H/K} = A^H` (`mem_invariants_subQuot_iff`) and the **third
  isomorphism theorem on points** (`mapPoints_quotQuot_eq_one_iff`: a point of `G/K` dies in
  `G/H` iff it comes from `H/K`).
* **done** `GroupScheme/Closure.lean` (19th session): **scheme-theoretic closure** of a closed
  subgroup `j : H̃ ↪ G_K` of the generic fibre over a PID `R` with fraction field `K`:
  `closureIdeal = ker(A → C̃)` is a Hopf ideal (`A/I ⊗_R A/I ↪ C̃ ⊗_K C̃` via
  `IsLocalization.moduleTensorEquiv`), `Hom.closure j` finite free with closed immersion
  `closureHom`, `closureGeneric : K ⊗_R A/I ≃ₐ[K] C̃` and `order_closure : |H| = |H̃|`.
* **done** `FormalGroup/OLFraction.lean` (19th session): `IsFractionRing (OL L) L`
  (`OL.toL_injective`, `z = x / p^n`), so `Closure.lean` applies over `O_{K'}`.
* **done** `GroupScheme/ClosureMap.lean` (20th session): functoriality of closures
  (`Hom.closureInduced`: `f : G → G'` with `j ∘ f_K = g ∘ j'` restricts to `H → H'`;
  `mapPoints_closureInduced`, surjective for closed immersions) and **points over the generic
  fibre** (`closurePtEquiv : H̃(Ω) ≃* H(Ω)` for a `K`-algebra `Ω`, `y ↦ y ∘ (A/I ↪ C̃)`;
  compatible with `closureHom`/`j` and with `closureInduced`). The bialgebra iso
  `K ⊗ O(H) ≅ O(H̃)` (hand-off 19, item 2) is not needed: every comparison is made on points.
* **done** `GroupScheme/QuotientPoints.lean` (20th session): `Hom.ext_univPt`, `Hom.ext_points`,
  `KilledBy G n` (`univPt^n = 1`; inherited by closed subgroups, quotients and base changes;
  `G_Ω` étale and `#G(Ω) = |G|` over a separably closed `Ω` with `n ≠ 0`), `Hom.quotientLift`
  (`G → X` trivial on `H` factors through `G/H`), `ext_quotient` (`G → G/H` is an epimorphism),
  `surjective_quotientMap_of_comp`, **`quotientHom_mapPoints_surjective`** (`G(Ω) ↠ (G/H)(Ω)`
  by counting, from exactness).
* **done** `GroupScheme/DiscriminantChain.lean` (20th session):
  `discIdeal_le_of_bijective_baseChange` (`disc(B) = det(α)² disc(A) ⊆ disc(A)` for an order
  `B ↪ A` of the same rank), `traceForm_nondegenerate_of_etale`, `discIdeal_ne_bot_of_etale`.
* **done** `GroupScheme/ClosurePDiv.lean` (20th session; [Hong, proof of Prop. 3.5.3], first
  half): for `ι : H̃ → G_K` (`p`-divisible groups, levelwise closed immersions) over a local PID
  `R` with fraction field `K`: closures `clo v = H_v`, `cloIncl`, `cloQuot` (restrictions of
  `i_v`, `quot_v`; `cloIncl ∘ cloQuot = [p] = cloQuot ∘ cloIncl` on points), `|H_v| = p^{hv}`,
  `#H_v(Ω) = p^{hv}`; `Q v = H_{v+1}/H_v` of order `p^h`, killed by `p^{v+1}`;
  `delta v : Q_{v+1} → Q_v` from `quot` (`quotientMap`; [Hong] uses `[p]`), bijective on
  `Ω`-points and after `Ω ⊗ -`; **`exists_delta_bijective`** (stabilisation through the
  ascending chain `disc(Q_v) ⊆ disc(Q_{v+1})` in the noetherian `R` and
  `bijective_of_discIdeal_eq`; replaces [AM, Prop. 5.17], lead decision 2026-10-19).
* **done** `GroupScheme/SubPDiv.lean` (20th session): `H'_v = H_{v₀+v}/H_{v₀}` (`Hp`), closed
  immersions `inclH` (`subQuot`), `[p^v] = j ∘ Δ ∘ quotQuot` on `H'_{v+1}` (`pow_eq_jj_Delta`,
  with `Δ = δ_{v₀} ∘ ⋯` bijective and `j : Q_{v₀} ↪ H'_{v+1}`), kernel condition
  `Hp_range_eq`; `subPDiv` (height `h(H̃)`), `subPDivHom : H' → G` (`[p^{v₀}]` via
  `quotientLift` and `cloQuotLE`, then `H_v → G_v`); **[Hong, Prop. 3.5.3], generic-fibre form:
  `PDivGroup.Hom.exists_pdivGroup_closure`**: `H'` of height `h(H̃)` and `ι' : H' → G` equal to
  `ι` on `Ω`-points at every level through isomorphisms `H'_v(Ω) ≅ H̃_v(Ω)`. **Still to do
  (lead decision, separate later step, only if needed downstream):** the Galois-descent input
  `M ⊆ T_p G` Γ-stable direct summand `↦ H̃` ([Hong, Prop. 2.1.14]).
* **done** `FormalGroup/FullyFaithful.lean` (20th session): **[Hong, Thm. 3.5.4] (Tate) over
  `O_{K'}`: `PDivGroup.Hom.baseChange_bijective_OL`** (`Hom(G, H) → Hom(G_L, H_L)` bijective).
  Graph `FFGroupScheme.graphBC` / `PDivGroup.Hom.graph : G_L → (G × H)_L` (`z ↦ (z, f̃ z)`,
  levelwise closed immersion), `exists_pdivGroup_closure` gives `ι : G' → G × H`, `π₁ ∘ ι`
  bijective on `ℚ̄_p`-points ⇒ levelwise bijective (Lemma 3.5.2,
  `bijective_of_mapPoints_bijective_OL`), inverse `PDivGroup.Hom.inv`,
  `f = π₂ ∘ ι ∘ (π₁ ∘ ι)⁻¹`, `f_L = f̃` by `Hom.ext_of_mapTate`; uniqueness
  `Hom.ext_of_baseChange`. No use of [Hong, Prop. 2.1.14] (the generic-fibre form of
  Prop. 3.5.3 takes the graph directly).
* **done** `GroupScheme/GaloisDescent.lean` (20th session): **fullness part of [Hong,
  Prop. 2.1.14]** (via [Hong, Prop. 1.3.1]) over a field `F` with `ℚ̄_p/F` Galois:
  `ℚ̄_p ⊗_F O(G) ≅ Map(G(ℚ̄_p), ℚ̄_p)` (`evAll_bijective`, `G` killed by `n ≠ 0`),
  `exists_eq_of_equivariant` (equivariant functions are evaluations; `σ ⊗ 1`-invariants via a
  basis and `InfiniteGalois.mem_range_algebraMap_iff_fixed`), `homOfEquivariant` (equivariant
  group homomorphisms of `ℚ̄_p`-points come from homomorphisms of group schemes),
  `TateModule.exists_pow_eq_of_val_eq_one` (`ker(T_p → G_v) = p^v T_p`), and
  **`PDivGroup.exists_hom_of_galTate`** (an equivariant `T_p G → T_p H` comes from `G → H`).
* **done** `FormalGroup/FullyFaithful.lean`: **[Hong, Cor. 3.5.5] over `O_{K'}`:
  `PDivGroup.Hom.mapTate_bijective_OL`** (`Hom(G, H) → GalTateHom G H`, the
  `Γ_L`-equivariant homomorphisms `T_p(G_L)(ℚ̄_p) → T_p(H_L)(ℚ̄_p)`, is bijective).
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
* **done** `GroupScheme/DualTateField.lean`: over a field `S` with `#G_v(S) = #G_v^∨(S) = |G_v|`:
  `i_v^∨ : G_{v+1}^∨(S) → G_v^∨(S)` surjective (`dual_incl_surjective_of_card`: its kernel is the
  annihilator of `i_v(G_v(S))`, which embeds into the characters of the quotient; counting),
  `T_p(G^∨)(S) → G_v^∨(S)` surjective (`DualTate.proj_surjective_of_card`, via the generic
  `exists_compat_of_surjective` for inverse sequences of surjections), `i_v^∨ ∘ quot_v^∨ = [p]`,
  `quot_v^∨` injective, kernel condition (`exists_dual_quot_eq_of_card`), and **`y ∈ T_p(G^∨)(S)`
  with `y_1 = 1` is a `p`-th power** (`DualTate.exists_pow_eq_of_card`).
* **done** `GroupScheme/DualTateOC.lean`: the same over `O_{ℂ_p}` for `G` over `R → O_{ℂ_p}`
  (via `ℂ_p`: `card_points_Cp`, `card_dual_points_Cp'`, `pointsOCEquiv`):
  **`DualTate.proj_surjective_OC`**, **`DualTate.exists_pow_eq_OC`**, `dualTateOCEquiv :
  T_p(G^∨)(O_C) ≃* T_p(G^∨)(ℂ_p)`, and the surjective half of perfectness over `O_C`
  (**`exists_pairing_eq_OC`**: every character of `G^∨(O_C)` is `⟨t, ·⟩`).
* **done** `FormalGroup/AlphaInj.lean` (**[Hong, Prop. 3.4.9]: `α` is injective on
  `G(O_K)`, `K = ℚ_p`**): `α` injective on torsion points (`eq_zero_of_alpha_torsion`, from
  `alpha_torsion`, `proj_surjective_OC`, `eq_one_of_pairing_OC`); a `p`-torsion character `α(x)` is
  `α(t)` with `t ∈ F[p]` (`exists_torsion_alpha_eq`: it kills `p T_p(G^∨) = ker(T_p(G^∨) → G_1^∨)`,
  factors through `G_1^∨(O_C)`, perfectness, `layerPt_surjective`); divisibility step
  (`exists_p_nsmul_eq_of_alpha`: an invariant `z ∈ ker α` is `p x'` with `x'` invariant in
  `ker α`; `σ x' − x' ∈ ker α ∩ F[p] = 0` by `alpha_gal`); **`eq_zero_of_alpha_eq_one`**: a
  `Gal(ℚ̄_p/ℚ_p)`-invariant `x` with `α(x) = 1` is `0` ([Hong, Lemma 3.4.2] over `ℚ_p`:
  `coord_mem_Qp_of_fixed`; [Hong, Lemma 3.4.3]: `eq_zero_of_forall_pow_nsmul_Qp`). The snake
  lemma of [Hong] is avoided.
* **done** `FormalGroup/DAlphaInj.lean`: **`dα` is injective on `t_G(ℚ_p) = ℚ_p^d`**
  (`dalpha_injective_Qp`; [Hong, Prop. 3.4.9, proof]): scale `z` into the polydisc of radius
  `|p|^2` where `log_F` is bijective ([Hong, Prop. 3.3.6 (2)], `exists_logF_eq`, `logF_injOn`);
  the preimage `x` is Galois-invariant by uniqueness; `log(α(x)(y)) = dα(z)(y) = 0` in the same
  disc of `Ĝ_m` gives `α(x) = 1`, so `x = 0` by `eq_zero_of_alpha_eq_one`.
* **done** `GroupScheme/DualBaseChange.lean`: **Cartier duality commutes with base change on
  points**: `f ↦ f_S` (`dualBC`, Mathlib's `Module.Dual.baseChange`) is an algebra map
  `A^∨ → (S ⊗ A)^∨` compatible with the comultiplications (`comulD_dualBC`); with
  `IsBaseChange.dual` this gives **`dualBaseChangePointsEquiv : (G_S)^∨(T) ≃* G^∨(T)`** (natural,
  `dualBaseChangePointsEquiv_mapPoints`) and **`PDivGroup.dualTateBaseChangeEquiv :
  T_p((G_S)^∨)(T) ≃* T_p(G^∨)(T)`**.
* **done** `FormalGroup/DualTateZp.lean`: for `G` over `ℤ_p` (`ZpD`, now also a `ℚ_p`- and
  `ℚ̄_p`-coefficient ring): `#G^∨(Ω) = |G|` over separably closed `Ω`
  (`card_dual_points_sepClosed`), `G_v^∨(ℚ̄_p) ≃* G_v^∨(ℂ_p)`, and **`dualTateZpEquiv :
  T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_{ℚ_p}^∨)(ℚ̄_p)`** (the Tate module of `dualPDiv` of the generic
  fibre), identifying the source of `α` with the `ℤ_p`-lattice of `V_p(G^∨)`.
* **done** `FormalGroup/PDeriv.lean` (generic, Mathlib-style, candidate for upstreaming):
  **partial derivatives of multivariate power series** `MvPowerSeries.pderiv R i` (an
  `R`-derivation; `coeff_pderiv`, `pderiv_coe` = `MvPolynomial.pderiv`, `pderiv_X`,
  `constantCoeff_pderiv`; Leibniz rule by truncation to polynomials, `coeff_mul_congr`), the
  **chain rule for polynomials** `MvPolynomial.derivation_aeval` (any derivation) and **for
  substitution** `MvPowerSeries.pderiv_subst`: `∂_i f(a) = ∑_j (∂_j f)(a) · ∂_i a_j` for families
  `a` without constant terms (`coeff_subst_congr`: coefficients of `f(a)` up to total degree `k`
  only depend on those of `f`); `subst_zero_eq_C`, `constantCoeff_subst_of_constantCoeff_zero`.
* **done** `FormalGroup/InvDeriv.lean`: `[n]_F(Φ(f, g)) = Φ([n]f, [n]g)` (`mulPS_subst_addPS`);
  **invariant derivations** `D_j g = ∂_{U_j} g(Φ(T, U))|_{U=0} = ∑_l ∂_l g · M_{lj}` with `M(0) = 1`
  (`invDeriv_eq`, `isUnit_det_invMat`); `D_j [n] = 0` if `n = 0` in `k`, hence **`∂_m [p]_F = 0`
  in characteristic `p`** (`pderiv_mulPS_eq_zero`) and **`[p]_F(T) ∈ (T_1^p, …, T_d^p)`**
  (`mulPS_p_mem`; [Hong, Prop. 1.5.10, proof], via `mem_span_X_pow_of_pderiv` and the generic
  `MvPowerSeries.mem_span_X_pow`).
* **done** `FormalGroup/FrobKernel.lean`: `R[[T]]/(T_j^N)` is free with basis the monomials
  `T^m`, `m_j < N` (`boxBasis`, `finrank_quot_spanXPow = N^d`); **the Frobenius kernel
  `Spec k[[T]]/([p]_F, T^p)` of `F[p]` has order `p^d`** (`finrank_frobKernel`; [Hong,
  Cor. 1.5.11, Cor. 2.2.18]).
* **done** `GroupScheme/Frobenius.lean` (over a field `k` of char. `p` with `x^p = x`, e.g.
  `𝔽_p`): relative Frobenius `φ_G = frob` (`a ↦ a^p`, a bialgebra map; [Hong, Def. 1.5.1,
  Lemma 1.5.2, Cor. 1.5.4]); **`f^p(d^p) = f([p]^* d)`** for `f ∈ A^∨`, `d ∈ A`
  (`pow_apply_pow`; via `hat(univPt)^p = Σ (e_i^*)^p ⊗ e_i^p` in the char-`p` ring `A^∨ ⊗ A`
  and the transpose of Frobenius being multiplicative: the `Verschiebung ∘ Frobenius = [p]` half
  of [Hong, Prop. 1.5.8] in dual form, no symmetric tensors), hence `d^p = 0 ⇒ [p]^* d = 0`;
  general Nakayama bound **`|G| ≤ |ker f| · |im f|` for connected `G`**
  (`order_le_finrank_mul_finrank_range`); **`|G| ≤ |ker φ_G| · |ker φ_{G^∨}|` for connected `G`
  killed by `p`** (`order_le_frobKer_mul`, `frobKerIdeal`): the inequality `h ≤ d + d^∨` of
  [Hong, Thm. 2.2.19] (the only direction used in [Hong, proof of Thm. 3.4.10]), proved without
  exact sequences: `Frob(A)` is annihilated by the ideal `(f^p : f(1) = 0)` of `A^∨`.
  **Perfect fields** (fourteenth session; e.g. the residue field `𝔽_q` of `O_{K'}`):
  `univPt_pow_apply` needs only characteristic `p`; `perfT f = σ⁻¹ ∘ f ∘ Frob` is `k`-linear and
  multiplicative for convolution (`perfT_mul`, `Δ(a^p) = Δ(a)^p`), and
  `f([p]^* d) = (perfT f)^p(d) = σ⁻¹(f^p(d^p))` (`apply_univPt_pow_perfect`), so **`d^p = 0 ⇒
  [p]^* d = 0` over any perfect field** (`univPt_pow_apply_eq_zero_of_perfect`).
* **done** `FormalGroup/DualTateGal.lean`: the Galois action `galDualZp` on `T_p(G^∨)(O_{ℂ_p})`
  for any `G` over `ℤ_p`; **`dualTateZpEquiv` is Galois-equivariant** (`dualTateZpEquiv_gal`,
  `dualTateZpEquiv'_gal` into `DualTate` of the generic fibre, where `tatePairingZp` lives);
  `ℤ_p`-module structure on `DualTate` (`instModuleZpDual`) with `dualTateZpLinearEquiv`;
  **`dα` is `ℤ_p`-linear in `y`** (`dalpha_zpSmul`, via `y_v = 1 ⇒ y` is a `p^v`-th power over
  `O_C` and `p`-adic separatedness) — [Hong, Prop. 3.4.9] (“evidently `ℤ_p`-linear and
  `Γ_K`-equivariant”).
* **done** `FormalGroup/DerivStable.lean` (generic, `MvPowerSeries` over a perfect field `k` of
  char. `p` (since the fourteenth session; `γ_m` carries `σ⁻¹ = frobInv` on coefficients); towards [Hong, Prop. 2.2.13] by a derivation argument instead of order counting):
  Frobenius decomposition `f = Σ_{m < p} γ_m^p X^m` (`frob_decomp`); for `∂`-stable ideals the
  `γ_m^p` lie in the ideal (`pow_mem_of_sum_mem`); **if ideals `𝔞_v ⊆ (X)` are `∂`-stable and
  `h^p ∈ 𝔞_{v+1} ⇒ h ∈ 𝔞_v`, then `𝔞_v ⊆ (X_i^{p^w})` for `w ≤ v`** (`le_spanXPow_of_derivStable`,
  `iInf_eq_bot_of_derivStable`); `∂`-stability of `ker ρ` from derivations of the target with an
  invertible matrix of values on `ρ(X_i)` (`derivStable_ker`).
* **done** `FormalGroup/InvariantsK.lean`, `FormalGroup/AlphaInjK.lean` (base `O_{K'}`, `K'/ℚ_p`
  finite, as `L : IntermediateField ℚ_p ℚ̄_p`): discreteness `|z| < 1 ⇒ |z| ≤ p^{-1/[L:ℚ_p]}` on
  `L` (`exists_norm_le_of_mem_cpSubmodule`); [Hong, Lemma 3.4.3] over `L`
  (`FGL.eq_zero_of_forall_pow_nsmul_mem`); [Hong, Lemma 3.4.2] over `L` (`FGL.coord_mem_of_fixed`);
  per-`σ` Galois action (`CoeffFixed`, `GalFixedOver p R L`, `galFixedOver_of_mem`); **injectivity
  of `α` on `G(O_L)` and of `dα` on `t_G(L)` using only `Gal(ℚ̄_p/L)`**
  (`eq_zero_of_alpha_eq_one_K`, `dalpha_injective_K`; [Hong, Prop. 3.4.9] with `K = L`).
  The concrete `O_{K'}` is `OK.lean` below.
* **done** `FormalGroup/OK.lean`: **the concrete coefficient ring `O_L = L ∩ O_{ℂ_p}`** (`OL L`,
  discrete uniformity, as `ZpD`): local, uniformiser (`OL.exists_uniformizer`,
  `OL.maximalIdeal_eq`), `𝔪`-adically complete, `O_C` complete for `𝔪_L O_C`, `GalFixedOver`;
  for `P : PDivFGL (OL L) d p`: `alphaK` (both squares, Galois equivariance for `σ` fixing `L`),
  **`eq_zero_of_alphaK_eq_one`**, **`dalpha_injective_OL`** ([Hong, Prop. 3.4.9] over `O_{K'}`).
  Missing: Tate-module / Hodge–Tate wiring (`tateRep`, `dualPDiv`, `tatePairingZp`) over `K'`.
* **done** `FormalGroup/OLCompact.lean`: `O_L` is compact for the subspace topology of
  `O_{ℂ_p}` (`OL.isCompact_unitBall`, `OL.compactSpace_OLSub`; `L` is a proper `ℚ_p`-space) — the
  compact companion topology for Serre–Tate over `O_{K'}` (hand-off 14, item 1).
* **done** `GroupScheme/SpecialFibre.lean`, `GroupScheme/SerreTateSpecial.lean` (**[Hong,
  Prop. 2.2.13]** for a connected `p`-divisible group `H` over a perfect field `k` (e.g. `𝔽_q`;
  `[PerfectRing k p]` since the fourteenth session, before `x^p = x`), by a
  derivation argument instead of [Hong]'s order counting): `quot_v^*` injective
  (`quot_injective_of_isConnected`: Nakayama `|G| ≤ |ker f|·|im f|` and `ker quot_v = G_1`), `a^p = 0 ⇒
  i_v^*(a) = 0` (`incl_eq_zero_of_pow_eq_zero`, from `f([p]^*d) = σ⁻¹(f^p(d^p))`), `ker φ ⊆ G[p]`
  and cotangent stabilisation, compatible coordinates and surjections
  `ρ_v : k[[t_1..t_d]] ↠ A_v`, invariant derivations `(id ⊗ ℓ_j)∘Δ` making `ker ρ_v` `∂`-stable;
  **`exists_coords`**: `ker ρ_v ⊆ (t_i^{p^w})` for `w ≤ v`, `⋂ ker ρ_v = 0`
  (i.e. `lim A_v ≅ k[[t]]` up to surjectivity onto the limit).
* **done** `GroupScheme/SerreTateCompact.lean`, `SerreTateFGL.lean`, `SerreTatePDiv.lean`,
  `SerreTateLift.lean`, `SerreTateEss.lean`: **Serre–Tate, essential surjectivity [Hong,
  Thm. 2.2.16]**: every connected `p`-divisible group over `ℤ_p` is `F[p^∞]` for a
  `p`-divisible formal group law: **`PDivGroup.exists_pdivFGL_iso`** (`H ≅ P.pdivGroup` with
  inverse homomorphisms). Proof: special fibre via `exists_coords` over `𝔽_p`; Hong's lifting
  of coordinates (`liftSeq`); compactness of `ℤ_p^{ℕ^σ}` instead of Chevalley's lemma for
  `ℤ_p[[t]] ↠ lim A_v` and kernels `→ 0` (`exists_forall_eq`, `exists_ker_le_coeffFilt`);
  injectivity by dividing out the largest power of `p`; `Φ` from the comultiplications
  (`Coords.fgl`), `p`-divisibility by levelwise bijectivity `A_v^{p^h} → A_{v+1}`
  (`Coords.isPDivisible`), levelwise bialgebra isomorphisms (`levelEquiv`). With
  `FGL.Hom.pdivEquiv` this is the Serre–Tate equivalence over `ℤ_p`.
* **done (15th session) coefficient-ring refactor**: the lifting files are stated over a
  **coefficient ring** `R` (`SerreTate.CoeffRing`, `SerreTateCompact.lean`: uniformiser `π ≠ 0`
  with `𝔪 = (π)`, compact companion topology `Cpt R` in which the cosets of `𝔪^w` are open; plus
  the instances `IsDomain R`, `IsAdicComplete 𝔪 R`); `finite_residueField` (compactness),
  `isDiscreteValuationRing`. Instances: `ZpD p` (`p`-adic topology) and `OL L`
  (`OL.instCoeffRing`, subspace topology of `O_{ℂ_p}`; `OL.instIsDomain`,
  `OL.instIsPrincipalIdealRing`). **`PDivGroup.exists_pdivFGL_iso_of_coeffRing`** (`p ∈ 𝔪_R`;
  special fibre over the finite, hence perfect, residue field) and
  **`PDivGroup.exists_connPart_iso_of_coeffRing`**; the `ℤ_p` statements
  (`exists_pdivFGL_iso`, `exists_connPart_iso`, `isConnected_baseChange`, …) are
  specialisations with unchanged names. `GroupScheme/SerreTateOL.lean`:
  **`PDivGroup.exists_pdivFGL_iso_OL`**, **`PDivGroup.exists_connPart_iso_OL`** (Serre–Tate over
  `O_{K'}`), **`PDivFGL.exists_connPart_dual_iso_height_le_OL`** (`h ≤ d + d'` over `O_{K'}`).
* **done (15th session) `h ≤ d + d'` over a coefficient ring** (`HeightIneq.lean`,
  `PDivFGL.height_le_add_of_connPart_iso_of_coeffRing`): `Frobenius.lean` is stated for a
  **Frobenius exponent** `q` (`FrobExp k q`: `q = ℓ^{n+1}`, `ℓ = char k`; instance for `q = p`),
  so `frobAlg`, `frobT`, `order_le_frobKer_mul` hold for the `q`-power Frobenius when `c^q = c`
  on `k`; over the residue field `𝔽_q` of `R` it is applied to `X = F[q] ⊗ 𝔽_q` (killed by `q`,
  order `q^h`): `q^h ≤ q^d q^{d'}`.
* **done (15th session) base field of the generic-fibre Tate machinery, first increment**: the
  following hold for a `p`-divisible group over any field `K` of characteristic `0` with
  `K → ℚ̄_p` (`{K : Type} [Field K] [CharZero K] [Algebra K (PadicAlgCl p)]`, e.g. `ℚ_p` or
  `↥K'`) instead of `ℚ_p` only (same names, `ℚ_p` call sites unchanged): `galPoints`,
  `PDivGroup.galTate`, `galLin` (`σ ∈ Gal(ℚ̄_p/K)`), `card_points_padicAlgCl`,
  `quot_surjective_padicAlgCl`, `card_points_padicAlgCl_of_isEtale`, `isEtale_dual`,
  `levelPairingHom_bijective`, the Cartier dual `p`-divisible group `dualPDiv` and
  `tateModule_dualPDiv` (`CartierDualPDiv.lean`), `tateEquivZp`, `exists_tateBasis`,
  `exists_perfect_tatePairing`, `nonempty_dualTate_equiv`, `tatePairingZp`, `galDualTate`,
  `tatePairing_gal`, `nonempty_tateLinearEquiv`, `finrank_tate`; new
  **`PDivGroup.tateRepOver`**: `V_p G` as a representation of `Gal(ℚ̄_p/K)`. Still over `ℚ_p`
  only: `tatePairingZp_gal` (`χ` of `σ|_{ℚ_p}`), `tateRep L` (restriction from `ℚ_p`),
  `TateDual`, `TateDualRep`, `TateCont`, `ConstPDivTate.constTate_charRep`, `DualTateZp`
  (`ZpD → ℚ_p` generic fibre), `DualTateGal`.
* **done** `GroupScheme/DualPDivFree.lean`, `FormalGroup/DualPDivFGL.lean`: **the Cartier dual
  `p`-divisible group over the base** ([Hong, Prop. 2.1.7 (2), Def. 2.1.8]) for `G = F[p^∞]`
  over a complete local `R` (e.g. `ℤ_p`): `PDivFGL.dualPDiv` (layers `G_v^∨`, transitions
  `quot_v^∨`, height `h`), from `DualPDivData` (a `quot^*`-linear retraction with `retr 1 = 1`,
  `ker(A_{v+1} ↠ A_1) ⊆ (quot^*(I_v))`, `[p^v]^*` split through `A_1`): closed immersion
  (`dual_quot_surjective`), kernel condition over every `S` (`exists_dual_quot_eq`; characters
  killed by `p^v` are `G_1`-invariant, invariants descend via an explicit inverse-Galois-map
  argument, `HopfInvariants.eq_of_invariant`); `T_p(G^∨) = DualTate`, base change to `ℚ_p`
  agrees with `dualPDiv` of the generic fibre on points and Tate modules.
* **done** `HodgeTate/Orthogonal.lean` (**step (3.11) of [Hong, proof of Thm. 3.4.10]**): for a
  representation `V` and `q + q' ≠ 0`, invariants of `V ⊗ ℂ_p(q)` and `V^∨ ⊗ ℂ_p(q')` are
  orthogonal (`dualEquiv_eq_zero_of_mem_DHT`, via `ℂ_p(j)^{G_L} = 0` [Hong, Thm. 3.1.12]), so
  `dim D_q(V) + dim D_{q'}(V^∨) ≤ dim V` (`finrank_DHT_add_finrank_DHT_dual_le`, [Hong,
  Lemma 3.1.13]); **`bijective_of_finrank_le_add_fin`**: injections `L^d ↪ D_{-1}(V)`,
  `L^{d'} ↪ D_0(V^∨)` with `dim V ≤ d + d'` are bijective (equality in (3.9), (3.10)).
* **done** `GroupScheme/ConnectedPDiv.lean` (connected part of a `p`-divisible group, [Hong,
  Prop. 2.1.10]; counting is a standard argument written up here): functoriality of `G ↦ G°`
  (`connectedComponentMap`), Nakayama over the local base (`order_le_mul_of_surjective`),
  `#G(Ω) = |G^{et}|` over an algebraically closed residue field extension; `c_{v+1} ≤ c_1 c_v`
  and `n_{v+1} ≤ n_1 n_v` force `|G_v°| = p^{h°v}` (`exists_order_connectedComponent`);
  **`PDivGroup.connPart`** (layers `G_v°`, kernel condition `connIncl_range_eq`) with the closed
  immersion `connPartHom : G° → G`, and **`exists_connPart_iso`**: `G° ≅ F[p^∞]` over `ℤ_p`
  (Serre–Tate). Missing: uniqueness of `d` / [Hong, Def. 2.2.17]; `G^{et}` as a `p`-divisible
  group.
* **done** `FormalGroup/DAlphaHT.lean` (**(3.9) of [Hong, proof of Thm. 3.4.10]**): for
  `P : PDivFGL ℤ_p d p`, `dα_K` as an `L`-linear map `L^d → D_0(V_p(G^∨)^∨) = W^Γ`
  (`dalphaK`, via `dualTateZpLinearEquiv`, `dalpha_zpSmul`, Galois equivariance
  `dalpha_galDualZp`), injective for `L = ℚ_p` (`dalphaK_injective`); twisted version into
  `D_{-1}(V_p G)` via `V_p(G^∨)^∨ ≅ V_p(G)(-1)` (`tateRepDualDualEquiv`, `dalphaKTwist`), and
  **`d ≤ dim D_{-1}(V_p G)`** (`le_finrank_DHT_tateRep`).
* **done** `FormalGroup/HeightIneq.lean` (**`h ≤ d + d^∨`, [Hong, Thm. 2.2.19]**, the direction
  used in [Hong, proof of Thm. 3.4.10]): for `P : PDivFGL ℤ_p d p`,
  **`PDivFGL.exists_connPart_dual_iso_height_le`**: `(G^∨)° ≅ P'.pdivGroup` with `P'` of dimension
  `d'` and `h ≤ d + d'`. Via `order_le_frobKer_mul` on `X = G_1 ⊗ 𝔽_p`: `|ker φ_X| ≤ p^d`
  (`finrank_baseChange_frobKer_le`, coordinates `ℤ_p[[T]] ↠ A_1`) and `|ker φ_{X^∨}| ≤ p^{d'}`
  (`finrank_frobKer_dual_baseChange_le`: Cartier duality and base change, the Frobenius kernel
  only sees `(G_1^∨)°`, Serre–Tate iso).
* **done** `FormalGroup/DAlphaDual.lean` (**step (3.10)**, **[Hong, Thm. 3.4.10] (`dα_K` half),
  Cor. 3.4.11** for `G = F[p^∞]` over `ℤ_p`): morphisms of `p`-divisible groups over `ℚ_p` are
  Galois equivariant and `ℤ_p`-linear on Tate modules (`Hom.tateLin`); `F'[p^∞] ≅ (G^∨)° ↪ G^∨`
  gives an injective equivariant `T_p(F'[p^∞]_{ℚ_p}) → T_p((G_{ℚ_p})^∨)` (`dualConnTateLin`,
  levelwise injectivity, flatness of `ℚ_p / ℤ_p`); composing `dα_K` for `F'` with the twist-`0`
  map and the twist-`(-1)` map along `V_p(G^∨) ≅ V^∨ ⊗ ℚ_p(1)` gives **`dalphaDual : ℚ_p^{d'} ↪
  D_0(V^∨)`** (no double duality). With (3.9), (3.11) and `h ≤ d + d'`: **`tate_dalpha`**
  (both maps bijective, `dim D_{-1}(V) = d`, `dim D_0(V^∨) = d'`, `h = d + d'`),
  **`dalphaK_bijective`** ([Hong, Thm. 3.4.10] for `dα_K`), **`finrank_DHT_tateRepDual_dual`**,
  **`finrank_DHT_tateRep_neg_one`** ([Hong, Cor. 3.4.11]).
* **done** `GroupScheme/TateCont.lean`: **`continuous_tateRep`**: `V_p G` is a continuous
  representation of `G_L` (points over `ℚ̄_p` are fixed by open subgroups,
  `ker(T_p G → G_n) = p^n T_p G`, `ℤ_p`-linear forms on `T_p G` are bounded).
* **done** `HodgeTate/OrthSplit.lean` ([Hong, proof of Thm. 3.4.12]): `exists_DHT_of_defect`
  (lifting along a `ℂ_p`-span of eigenvectors of other weights, Tate's `H¹(G_L, ℂ_p(j)) = 0`);
  **`isHodgeTate_dual_of_finrank_add_eq`**: `dim D_q(V) + dim D_{q'}(V^∨) = dim V`, `q + q' ≠ 0`
  ⇒ `V^∨` Hodge–Tate with `dim D_{-q}(V^∨) = dim D_q(V)`; `isHodgeTate_of_dual`.
* **done** `FormalGroup/HodgeTateFGL.lean`: **[Hong, Thm. 3.4.12]** (`hodgeTate_decomposition`:
  `ℂ_p ⊗ V^∨ = Hom(T_p G, ℂ_p)` is Hodge–Tate with weight-`0` part of dimension `d' = h − d`
  and weight-`1` part of dimension `d`) and **[Hong, Cor. 3.4.14]** (`isHodgeTate_tateRep`) for
  `G = F[p^∞]` over `ℤ_p`.
* **done** `FormalGroup/TateNonConn.lean` (**[Hong, Cor. 3.4.11] for non-connected `G` over
  `ℤ_p`**, the input of [Hong, Lemma 3.5.2]): **`PDivGroup.finrank_DHT_tateRep_neg_one_of_iso`**,
  **`exists_finrank_DHT_tateRep_neg_one`**: `dim D_{-1}(V_p G) = d` where `G⁰ ≅ F[p^∞]`, `F` of
  dimension `d`. Lower bound: `V_p(F[p^∞]) ≅ V_p(G⁰) ↪ V_p G` (`connTateLin`,
  `tateLin_baseChange_injective`). Upper bound by the direct Hilbert 90 route (no `G^{et}` as a
  `p`-divisible group): `T⁰ = T_p(G⁰) ⊆ T` is characterised levelwise (`mem_connTate_iff`;
  points of `G_v⁰` are those killing `1 - e₀`, and `i_v^*(e₀) = e₀`), so `T/T⁰` is torsion free
  (`mem_connTate_of_smul_mem`), hence free; `etCoordField G k = ℚ_p(x(a) : x ∈ G_w(ℚ̄_p),
  a ∈ A_w^{et}, w ≤ k)` is `IsUnrStable` (`isUnrStable_etCoordField`, as in `EtaleHT`, since
  `A_w^{et}` is finite étale); for `ν` fixing it `ν x − x ∈ T⁰ + p^k T` (`exists_galLin_sub`:
  kernel of `G_k → G_k^{et}` is `G_k⁰`, `T_p(G⁰) ↠ G_k⁰(ℚ̄_p)`, `ker(T → G_k) = p^k T`), so
  `exists_hilbert90` trivialises `V_p G / V_p(G⁰)` (`etRep`, `isHodgeTate_etRep`: Hodge–Tate of
  weight `0`), and `0 → D_{-1}(V_p G⁰) → D_{-1}(V_p G) → D_{-1}(V_p G/V_p G⁰) = 0`.
  `ZpD p` vs `ℤ_[p]`: everything is stated over `ZpD p`; `exists_frobenius_period_zpD` transports
  the one `ℤ_[p]`-specific input (Frobenius periodicity) by definitional unfolding.
* **done (16th session) base field `K'`** (generic fibre over a field `F ⊆ ℚ̄_p`, `G_L` acting
  through `ι : G_L → G_F` with `ι σ = σ` pointwise and representations given by
  `ρ(σ)(a ⊗ t) = a ⊗ (ι σ) t`; the `ℤ_p` statements are specialisations with
  `ι = restrictScalars`, `ρ = tateRep L`, the `O_{K'}` ones with `ι = id`, `ρ = tateRepOver`):
  `TateDualRep` (`baseChangeDualEquiv_gal` for abstract lattices; `tateRepDualEquiv_galOver`,
  `tateRepDualEquiv_galVia`, `isHodgeTate_tateRepOver_dualPDiv`), `DAlphaHT` (abstract
  `dualDualEquiv`, `DHTdualDualMap`, `finrank_DHT_dualDual`; `dalphaKGen`, injective for every
  `L` with `GalFixedOver` via `dalpha_injective_K`), `DualTateZp`/`DualTateGal`
  (`dualTateGenEquiv : T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_F^∨)(ℚ̄_p)` for `R → F` compatible with
  `R ⊆ O_{ℂ_p}`, `galDualGen`, `dualTateGenEquiv_gal`, `dualTateGenLinearEquiv`; `dU_smul`,
  `dalpha_zpSmul` over any `R` by a norm estimate), `DualPDivFree`/`DualPDivFGL` (Cartier dual
  commutes with base change to any `F`), `DAlphaDual` (`dalphaDualGen`, **`tate_dalphaGen`**),
  `TateCont` (`continuous_tateRep_of`, `continuous_tateRepOver`), `TateRep`
  (`finrank_tateRep` over any `F`). New: `FormalGroup/DAlphaHTOL.lean` (`OL.toL : O_L →+* L`,
  algebras `O_L → L → ℚ̄_p`, `OL.algebraMap_qbar_cp`; `genericFibreOL`, `dalphaKOL`,
  `dalphaKTwistOL`, (3.9) over `K'`) and `FormalGroup/HodgeTateOL.lean`: **[Hong, Thm. 3.4.10]
  over `K'`** (`tate_dalphaOL`, `dalphaKOL_bijective`), **Cor. 3.4.11** (`finrank_DHT_tateRepOL_neg_one`),
  **Thm. 3.4.12** (`hodgeTate_decompositionOL`), **Cor. 3.4.14** (`isHodgeTate_tateRepOL`) for
  `F[p^∞]` over `O_{K'}`, `V_p` as a `Gal(ℚ̄_p/K')`-representation.
* **done (17th session) Hilbert 90 and the étale part over `K'`**: `Hilbert90/` is generalised
  in place from `(ℚ_p, p, Gal(ℚ̄_p/ℚ_p))` to a base field `F` with `ℚ_p → F → ℚ̄_p` (a type, so
  `F = ℚ_p` and `F = ↥K'` are both instances), `π ∈ F` with `0 < |π| < 1` and
  `G_F = GalOver p F = (ℚ̄_p ≃ₐ[F] ℚ̄_p)`: `IsUnrStableOver F π M` (`M : IntermediateField F ℚ̄_p`,
  `|z| < 1 ⇒ |z| ≤ |π|`), `exists_trace_one` over the `F`-embeddings, `exists_additive` and
  `exists_GL_mod_p` modulo `π`, **`exists_hilbert90_over`** (approximation by powers of `π`;
  conclusion `A(σ) σ(X) = X` with `σ` acting on `ℂ_p` by `autCp (σ.restrictScalars ℚ_p)`,
  i.e. `galCp`). The `ℚ_p` statements are specialisations (`IsUnrStable`, `IsUnrStable.over`,
  `exists_hilbert90` unchanged for the callers). New files:
  - `Hilbert90/UnrOver.lean`: `FrobPeriodicMod F π` (Frobenius periodic mod `π` on `O_F`),
    `FrobClosedOver F π S`, **`unr_adjoin_over`** (`F(S)` unramified relative to `π` via
    `|d| ∈ |π|^ℕ` on `ℤ_p[S ∪ O_F]`), **`isUnrStableOver_adjoin`** (stability + rigidity);
  - `FormalGroup/OLFrob.lean`: `norm_coeff_minpoly_le_one` (spectral norm: `|z| ≤ 1` ⇒ minimal
    polynomial over `ℤ_p`), **`OL.instFiniteResidueField`** (`κ_{K'}` finite),
    `OL.exists_frobenius_period_OL`, `OL.frobPeriodicMod`, `OL.ofL`, `OL.uniformizerL`,
    **`Hilbert90.exists_frobenius_period_local`** (Frobenius periodic mod `π` on finite free
    étale algebras over a local ring with finite residue field; generalises
    `exists_frobenius_period`);
  - `GroupScheme/EtaleHTOL.lean`: `coordFieldOL G k = K'(G_w(ℚ̄_p), w ≤ k)`,
    `isUnrStableOver_coordFieldOL`, `tateMatrixOL_fix`, **`isHodgeTate_tateRepOver_of_etale_OL`**
    (étale `G` over `O_{K'}`: `V_p(G_{K'})` Hodge–Tate, all weights `0`, as a
    `Gal(ℚ̄_p/K')`-representation);
  - `FormalGroup/TateNonConnOL.lean`: **[Hong, Cor. 3.4.11] over `K'` for non-connected `G`**
    (**`finrank_DHT_tateRepOver_neg_one_of_iso_OL`**,
    **`exists_finrank_DHT_tateRepOver_neg_one_OL`**: `dim_{K'} D_{-1}(V_p G_{K'}) = dim G⁰`),
    the proof of `TateNonConn` with `etCoordFieldOL` over `K'` and `exists_hilbert90_over`.
    Elaboration: instance terms over `L = ↥K'` are large; shortcut instances for
    `Additive (H.TateModule ℚ̄_p)` and `DHT`, `let` instead of `set`, and two documented heartbeat
    bumps (`galQMatrix_fixOL`, `finrank_DHT_tateRepOver_neg_one_of_iso_OL`, ~0.5 s per step).
* **done (17th session) `GroupScheme/Discriminant.lean`** (§3.5 start): `discIdeal R A`
  (basis-independent, `discIdeal_eq_span_discr`), `trace_algebraMap_of_bijective_baseChange`
  (a map of finite free algebras bijective after `K ⊗_R -` preserves traces), and the algebraic
  core of [Hong, Lemma 3.5.2]: **`bijective_of_discIdeal_eq`** (same rank, `K ⊗ α` bijective,
  `disc(A/R) = disc(B/R) ≠ 0` ⇒ `α` bijective), `bijective_of_discr`; `discr_baseChange`
  (discriminants commute with base change), **`discIdeal_tensorProduct`**
  (`disc(A ⊗ B / R) = disc(A/R)^{rk B} disc(B/R)^{rk A}`, via `trace_tmul_tmul` and
  `Matrix.det_kronecker`; an ingredient of the multiplicativity [Haines, Lemmas 2.3.1–2.3.2]).
* **done (18th session) [Hong, Prop. 3.5.1] over `O_{K'}`** (the discriminant formula, stated
  in [Hong] without proof): **`PDivGroup.discIdeal_eq_of_iso_OL`**,
  **`PDivGroup.exists_discIdeal_eq_OL`**: for `G` over `O_L` with `G⁰ ≅ F[p^∞]`, `dim F = d`,
  `disc(A_v/O_L) = ((p^v)^{d p^{hv}})`; connected case `PDivFGL.discIdeal_eq_OL`.
  **Deviation from Tate's proof** ([Tate, §(2.2) Prop. 2], [Haines, §2.3], [Lipnowski, App.]):
  Tate's Lemma 1 (`disc(A/A') = N(Jacobian)`) rests on Tate's trace theorem for complete
  intersections [Lipnowski, Claim 2'] = [Tate, Thm. A.3, appendix to Mazur–Roberts], not
  available; instead (standard Hopf-algebra arguments, written up here):
  - `GroupScheme/HopfTrace.lean`: `trace_pi_eq_sum` (traces on `K^X`, the missing product
    lemma), `trace_eq_sum_algHom` (finite étale over separably closed `Ω`),
    `algebraMap_trace_eq_sum` (`Tr_{A/R}(x) = ∑_{k ∈ G(Ω)} k(x)` for `R ↪ Ω`, `G_Ω` étale),
    `eq_of_forall_points`, integrals `IsIntegral Λ` (`aΛ = ε(a)Λ`; `apply_integral`:
    `Λ = ε(Λ)δ_1` pointwise) and **the trace formula `trL_mul_comul_integral`**:
    `(Tr ⊗ id)((x ⊗ 1)Δ(Λ)) = ε(Λ) S(x)`; `antipode_antipode` (`S² = 1`);
  - `GroupScheme/HopfDisc.lean`: **`discIdeal_eq_of_trace_eq_smul`**: if moreover
    `Tr = c λ`, `c = ε(Λ) ≠ 0`, then `disc = (c^N)` (the trace form composed with the Fourier map
    `φ ↦ (φ ⊗ id)Δ(Λ)` is `c S`, so `det(λ-form)` is a unit; the linear algebra of [Haines,
    Lemma 2.3.3]); **`trace_eq_smul_of_dual_integral`**: an integral `λ` of the Cartier dual
    with `c λ(1) = N` gives `Tr = c(λ ∘ S)` (`c λ(Sx) = λ(Λ) Tr(x)`);
    `discIdeal_eq_of_integral_of_trace_mem`, `trace_eq_smul_of_integrals`;
  - `FormalGroup/LayerIntegral.lean`: **Cramer's integral** `Λ = det(b_{ij})` of
    `A_v = R[[T]]/[p^v]` (`[p^v]_i = ∑_j t_j b_{ij}`, `FGL.exists_eq_sum_X_mul`),
    `isIntegral_layerDet`, `counit_layerDet : ε(Λ) = (p^v)^d` ([Hong, Lemma 2.2.14]);
  - `GroupScheme/IntegralConn.lean`: integrals along surjective bialgebra maps, lifting from
    `G⁰` by `e₀` (`exists_isIntegral_of_connectedComponent`), and **the connected–étale
    reduction `trace_mem_of_connectedComponent`** (`Tr(A⁰) ⊆ I ⇒ Tr(A) ⊆ I`, via
    `Tr_{A/R} = Tr_{A^{et}/R} ∘ Tr_{A/A^{et}}`, the Galois isomorphism and faithful flatness);
  - `FormalGroup/DiscFormula.lean`: for `F[p^∞]` the dual integral comes from Cramer for the
    connected part `F'[p^∞]` of the Cartier dual, and `h = d + d'`
    (`exists_connPart_dual_iso_height_eq_OL`, from Tate's theorem `tate_dalphaGen`), so
    `ε(Λ) λ(1) = (p^v)^h = |G_v|`.
  No transitivity formula and no multiplicativity in general exact sequences are needed.
* **done (18th session) [Hong, Lemma 3.5.2] over `O_{K'}`** (`FormalGroup/GenericIso.lean`):
  **`PDivGroup.Hom.bijective_of_mapPoints_bijective_OL`**: `f : G → H` over `O_L` bijective on
  `ℚ̄_p`-points at every level (e.g. an isomorphism on generic fibres) has all `α_v`
  bijective. Inputs: `bijective_of_bijective_comp_algHom` (maps of finite étale algebras over a
  separably closed field bijective on points are bijective), `bijective_baseChange_of_mapPoints`,
  `Hom.mapTate_bijective`, `Hom.dim_eq_of_mapPoints_bijective_OL` (same `d` via `V_p(G_L) ≅
  V_p(H_L)` and Cor. 3.4.11 over `L`), heights by counting points, Prop. 3.5.1,
  `bijective_of_discIdeal_eq`.
  Generic-fibre form: **`PDivGroup.Hom.bijective_of_baseChange_inverse_OL`** (`f_L` has an
  inverse homomorphism over `L`).
* **done (18th session) `GroupScheme/Product.lean`** (for the graph in [Hong, proof of
  Thm. 3.5.4]): `FFGroupScheme.prod` (`A ⊗_R B`), `order_prod`, `prodPointsEquiv : (G × H)(S) ≃*
  G(S) × H(S)`, `prodMap`, projections `fst`, `snd`; `PDivGroup.prod` (height `h_G + h_H`,
  kernel condition componentwise), `PDivGroup.fst`, `PDivGroup.snd`, **`prodTateEquiv :
  T_p(G × H)(S) ≃* T_p G(S) × T_p H(S)`**.

## PH5. Inputs for MR7 ([LocAn] / [TopSurr] Thm 4.12) — wip (21st session on)

Lead decision (2026-10-19): Tate's Theorem 4 over `O_{K'}` is done (PH3/PH4); MR6 now serves
MR7 (MR7-plan "What MR7 needs from MR6" (b), (d)). `α_K` bijectivity is deferred.

* **done (21st session) (b) Kummer maps** (needed by [TopSurr] l.2269–2287: Kummer classes of
  points of the formal group of `J`, compared via Tate's theorem):
  - `Cohomology/Kummer.lean` (general): `Kummer.Tp M p = lim M[p^n]` with the inverse limit
    topology of the discrete `M[p^n]` (`IsTopologicalAddGroup`), `Kummer.tpRep`;
    `ContH1.map` (coefficients), `ContH1.comap` (pull-back along continuous `Γ' → Γ`);
    **`Kummer.kummer : M^Γ → H¹_cont(Γ, T_p M)`** for `p`-divisible `M` with `StabHyp`
    (`p`-th roots of points with open stabiliser have open stabiliser), `kummer_eq` (any
    compatible system of roots), **`map_kummer`** (naturality in `M`), **`comap_kummer`**
    (restriction), `stabHyp_of_finite` (compact `Γ`, closed stabilisers, `M[p]` finite;
    orbit–stabiliser in `Stab(p z)` plus "closed of finite index ⇒ open").
  - `FormalGroup/Kummer.lean`: `FGL.galRep` (action of a subgroup `Γ ⊆ Gal(ℚ̄_p/ℚ_p)` fixing
    the coefficients on `F(m_{ℂ_p})`), `FGL.isClosed_stab`, `PDivFGL.finite_torsion`
    (`F(m_{ℂ_p})[p] ↪ F[p](ℂ_p)`), **`PDivFGL.kummer`**, **`PDivFGL.map_kummer`**
    (functoriality in `F`), **`PDivFGL.comap_kummer`**, `tpToPDiv` (+ `tpToPDiv_bijective`):
    `T_p F ≅ T_p(F[p^∞])(O_{ℂ_p})`, **`tpToPDiv_map`** (`T_p(f) = T_p(f[p^∞])`),
    **`exists_fglHom_tpToPDiv`** (every `ψ : F[p^∞] → F'[p^∞]` is `f[p^∞]`, Serre–Tate);
    over `O_{K'}`: **`kummerOL : F(m_{K'}) → H¹_cont(G_{K'}, T_p F)`**,
    `mem_invariants_galRepOL_iff` (invariants = points with coordinates in `K'`),
    **`comap_kummerOL`** (base change `K' ⊆ K''`).
  - Scope note: `G(O_{K'})` for a non-connected `p`-divisible group is not defined; for
    `ℚ_p`-coefficient Kummer theory only `G⁰(O_{K'}) = F(m_{K'})` matters
    (`exists_connPart_iso_OL`), and [TopSurr] l.2282–2284 passes to a multiple lying in the
    formal group. `H¹` is over `ℤ` (no `ℤ_p`-module structure on `Kummer.Tp` yet).
* **wip (d) [Fo] integral Hodge–Tate** (MR7-plan A7). Consumer: [LocAn] §9 item (1)
  (l.2669–2697): a `Γ_K`-equivariant `Ω^inv_G ⊗ (p^{n₀}O/p^{n₀+n}O) → H^Ω_G ⊗ ℤ/p^n` with an
  inverse up to `p^{n₀}`, `n₀ = n₀″ + ord_p(g!) + 2`, `p^{n₀″}` bounding the different of `K/ℚ_p`
  (l.2669–2672), the "`1/(p−1)`" and "`(e−1)/e`" being [Fo] Thm 1′. Statements checked in the
  scan `~/iut-scratch/lit/dl/mr7-d5/fontaine-varab-1982.pdf` (pages rendered; the OCR is
  garbled): [Fo] §1.1 setting (complete discretely valued `K`, perfect residue field); Thm 1′
  (p. 383): `ξ : K̄(1) → Ω = Ω_{O_K̄/O_K}`, `p^{-r}a ⊗ (ε_n) ↦ a · dε_r/ε_r`, is
  `O_K`-linear, `G`-equivariant, surjective with kernel `𝔞_K(1)`,
  `𝔞_K = {v(a) ≥ −v(𝔇_{K/K₀}) − 1/(p−1)}` (`v(p) = 1`, `K₀ = Frac W(k)`); §4.5–4.8 (pp. 395–398):
  `φ_J = (φ⁰_J, φ¹_J) : O_K̄ ⊗_{ℤ_p} J(O_K̄) → t*_{J'}(O_K̄) ⊕ t_J(Ω)` for finite flat
  commutative `J` (`J'` the Cartier dual, `t_J(M) = Hom(ω_J, M)`, `φ¹_J(u)(ω) = u*ω`
  (Prop. 6)); Thm 3 + Corollaire (p. 400–401): kernel and cokernel of `φ_J` are killed by `a`
  with `v(a) = 1/(p−1) + v(𝔇_{K/K₀})`; §5.6 Prop. 9 (p. 404): `ρ_H : K ⊗ ω_H →
  Hom_{ℤ_p[G]}(T_p H, V_p(Ω))` injective, §5.7: `V_p(Ω) ≅ C(1)`, `ρ_H` an isomorphism onto
  `t*_H(K) ≅ Hom_G(T_p H, C(1))`; §5.8 Prop. 10: `0 → t*_H(O_K) →p^n→ t*_H(O_K) → t*_{H_n}(O_K)
  → 0`. Plan (Lean steps, MLF base `K' = L`, `O_E = OL E` for `L ⊆ E ⊆ ℚ̄_p` finite):
  1. **done (21st session)** [Fo] Lemme 1 (i) for DVRs: `Fontaine/Differentials.lean`
     (`Ω_{B/R}` of `B = R[b]` cyclic with annihilator `(P'(b))`; `= 𝔇_{B/A}` for Dedekind
     domains) and `Fontaine/Monogenic.lean` (**`exists_adjoin_eq_top`**: `B = A[x]` for a DVR
     `B` finite over local `A` with separable residue extension, Serre III §6 Prop. 12;
     **`exists_kaehler_cyclic`**).
  2. Instances for `OL E` over `OL L` (DVR, `Module.Finite`, `IsIntegralClosure`, fraction
     fields, residue fields finite hence perfect); `𝔇_{E/L}` multiplicative in towers (Mathlib
     `differentIdeal_eq_differentIdeal_mul_differentIdeal`), [Fo] Lemme 2–4 (`Ω_{O_E/O_L} →
     Ω_{O_{E'}/O_L}` injective, annihilators), Lemme 5–6, `Ω = colim_E Ω_{O_E/O_L}`.
  3. [Fo] Lemme 7 for `Ĝ_m` (§1.7): `v(Ann(dε_r/ε_r)) = r − 1/(p−1)` over `K₀`, i.e.
     `v(𝔇_{K₀(ζ_{p^r})/K₀}) = r − 1/(p−1)` (`Φ_{p^r}'(ζ)`, `v(ζ_p − 1) = 1/(p−1)`; repo
     `Cyclotomic/`); then Thm 1′ (§2.8).
  4. §4: invariant differentials `ω_J ≅ t*_J(O_K)` of a finite flat group scheme (§4.3),
     `φ_J`, Prop. 6–8, Thm 3, Corollaire (or only the kernel bound, Remarque 4.11, plus a
     separate cokernel bound if that suffices for [LocAn]).
  5. §5: `ω_H`, Prop. 10, `ρ_H`, the integral form used by [LocAn] §9 (1) for `H = G[p^∞]`.

## Hand-off (2026-10-19, twentieth session)

Lead decisions applied: discriminant chain instead of finiteness of the integral closure;
Prop. 3.5.3 in generic-fibre form (Galois-descent input `M ↦ H̃` deferred).

Done this session (pushed, validated; see PH3 "20th session" entries):
* `7725c7e`: **[Hong, Prop. 3.5.3], generic-fibre form** (`PDivGroup.Hom.exists_pdivGroup_closure`,
  over any local PID `R` with fraction field `K` and separably closed `Ω ⊇ K`, `p ≠ 0` in `Ω`):
  `ClosureMap.lean` (functoriality of closures, `H̃(Ω) ≃* H(Ω)`), `QuotientPoints.lean`
  (`KilledBy`, `quotientLift`, `ext_quotient`, `G(Ω) ↠ (G/H)(Ω)`), `DiscriminantChain.lean`
  (`disc(B) ⊆ disc(A)` for orders, `disc ≠ 0` for étale generic fibre), `ClosurePDiv.lean`
  (closures `H_v`, `Q_v = H_{v+1}/H_v`, `δ_v`, **stabilisation `exists_delta_bijective`**),
  `SubPDiv.lean` (`H'_v = H_{v₀+v}/H_{v₀}`, kernel condition via `[p^v] = j ∘ Δ ∘ quotQuot`,
  `ι' : H' → G` through `[p^{v₀}]`). Deviations from the 19th hand-off: the bialgebra iso
  `K ⊗ O(H_v) ≅ O(H̃_v)` (item 2) is not needed (all comparisons on points via
  `closurePtEquiv`); `δ_v` is induced by `quot` (not `[p]`), so "`[p]` trivial on `Q_v`" is not
  needed either.
* `868f870`: **[Hong, Thm. 3.5.4] over `O_{K'}`** (`PDivGroup.Hom.baseChange_bijective_OL`),
  `FullyFaithful.lean` (graph `Hom.graph`, inverse `Hom.inv`).
* `9e1fa4d`: **[Hong, Cor. 3.5.5] over `O_{K'}`** (`PDivGroup.Hom.mapTate_bijective_OL`:
  `Hom(G, H) ≅ GalTateHom G H`, the `Γ_L`-equivariant homomorphisms of Tate modules) and
  `GaloisDescent.lean` (**fullness of [Hong, Prop. 2.1.14] over `L`**:
  `PDivGroup.exists_hom_of_galTate`, via `homOfEquivariant` / `exists_eq_of_equivariant`,
  `ker(T_p → G_v) = p^v T_p`). This is Tate's Theorem 4 over `O_{K'}` (MR6 scope item A2).
* this commit: hand-off only.

Still to do / next steps:
1. **`α_K` bijective** ([Hong, Thm. 3.4.10], first half; off the critical path). Available:
   `dalphaK_bijective` (over `ℤ_p`, `ZpD p`, only injectivity over `O_L`: `dalphaKOL_injective`),
   `exact_logHom` (`log_F` onto, kernel = torsion), `alpha_gal`/`alphaK_gal`, `alpha_torsion`,
   `exists_torsion_alpha_eq` (`p`-torsion characters only), `eq_zero_of_alpha_eq_one_K`
   (injectivity of `α` on `Γ`-fixed points). Plan (hand-off 13, item 1, refined): decide the
   codomain (`ℤ_p`-linear Γ-equivariant `T_p(G^∨)(O_C) → 1 + m_C`); `log ∘ f = dα(z)` by
   `dalphaK_bijective`; `x` with `log_F x = z`; `g = α(x)/f` is `μ_{p^∞}`-valued and
   `ℤ_p`-linear, hence factors through `T_p/p^v` (finite generation) and is a Cartier pairing
   with `t ∈ F[p^v]` (generalise `exists_torsion_alpha_eq` from `p` to `p^v`, perfectness
   `levelPairingHom_bijective`); `x - t` is Γ-fixed since `α(σ(x - t)) = α(x - t)` — this needs
   injectivity of `α` on all of `F(m_C)` ([Hong, Prop. 3.4.9]; the repo only has it on
   Γ-fixed points, `eq_zero_of_alpha_eq_one_K`). Over `O_{K'}` it additionally needs `dα_K`
   surjective over `L`.
2. Galois-descent input for Prop. 3.5.3 (`M ⊆ T_p G` Γ-stable direct summand `↦ H̃` over `K'`,
   [Hong, Prop. 2.1.14] essential surjectivity): not needed by Thm. 3.5.4 / Cor. 3.5.5; only if a
   downstream user wants Prop. 3.5.3 in Hong's form. `GaloisDescent.lean` has the fullness half.
3. Cleanup (unchanged): `TateNonConn`/`TateNonConnOL` duplication.

MR7 compatibility: Prop. 3.5.3 and the descent lemmas are stated over a general local PID
(resp. a general field `F ⊆ ℚ̄_p` with `ℚ̄_p/F` Galois); Thm. 3.5.4 and Cor. 3.5.5 over `OL L`
with `Ω = ℚ̄_p` (Lemma 3.5.2 / Prop. 3.5.1 are only available over `OL L`).

No WIP branch; nothing unpushed after the final commit.

## Hand-off (2026-10-19, nineteenth session; superseded)

Lead decision (option (i)): prove [Hong, Thm. 1.1.9] for real. **Done, no debt.**

Done this session (pushed, validated; see PH3 "19th session" entries):
* `969f316`: `HaarIntegral.lean` (Larson–Sweedler over any ring: integrals `haarProj`, Fourier
  inversion; `exists_invariant_forms`: `H`-invariant forms `tᵢ` and `Λᵢ` with `∑ tᵢ(Λᵢ x) = ε(x)`),
  `Quotient.lean` (over any ring: dual basis `a = ∑ xₛ trⱼ(yₛ a)`, `projective_invariants`,
  `canEquiv : A ⊗_B A ≅ A ⊗_R C`), `QuotientGroup.lean` (**[Hong, Thm. 1.1.9]** over a local PID:
  `Hom.quotient i = G/H`, `quotientHom`, `nonempty_basis_invariants` (rank `|H|`),
  `order_eq_mul : |G| = |H| |G/H|`, `ker i = A·B⁺`, exactness of `H(T) → G(T) → (G/H)(T)`).
  Route (deviation from the hand-off's suggestions): not Stix's characteristic-polynomial proof
  (needs infinite residue fields) nor Mumford over a field + fibrewise flatness, but the
  Kreimer–Takeuchi argument via Hopf integrals, which works over any base once `can` is onto.
  Sources: Farnsteiner's FTHM notes and Böhm arXiv:math/0409513 (statement of KT Thm 1.7) in
  `~/iut-scratch/lit/dl/quotients/`; Stix §6 (local) for the classical statement.
* `4c90e20`: `QuotientMap.lean` (`quotientMap` functoriality; `K ⊆ H ⊆ G`: `subQuot : H/K → G/K`
  closed immersion, `quotQuot : G/K → G/H`, third isomorphism theorem on points).
* final commit of the session: `Closure.lean` (scheme-theoretic closure of `j : H̃ ↪ G_K` over a
  PID with fraction field `K`: Hopf ideal, finite free, `closureGeneric`, `order_closure`),
  `OLFraction.lean` (`IsFractionRing (OL L) L`) and this hand-off.

Next steps for [Hong, Prop. 3.5.3] (generic-fibre form: input `H̃` over `L = K'` with levelwise
closed immersions `H̃_v ↪ G_{v,L}`; the Galois-descent construction of `H̃` from `M ⊆ T_p G` is a
separate step, not needed for Thm. 3.5.4 where `H̃_v` is the graph of `f̃_v`):
1. (done: `IsFractionRing (OL L) L`.)
2. Closure Hopf compatibility: `closureGeneric` is a bialgebra iso (so `H_{v,L} ≅ H̃_v` as group
   schemes, `H_v(Ω) ≅ H̃_v(Ω)`); closures `H_v ⊆ H_{v+1}` (closed immersions induced by `i_v`,
   ideal inclusion from the generic diagram); `[p]`/`quot` maps restrict to closures.
3. Quotients `Q_v = H_{v+1}/H_v` (order `p^h`), `δ_v : Q_{v+1} → Q_v` from `quot` via
   `quotientMap`; `[p]` trivial on `Q_v` (check after `⊗ L`, `B ⊆ L ⊗ B`); `δ_v` generic iso ⇒
   `B_v ↪ B_{v+1}` injective.
4. **Stabilisation without integral closures**: `disc(B_v) ⊆ disc(B_{v+1})` (inclusion of
   free orders of equal rank, `disc = det² · disc`), ascending chain in the Noetherian `O_{K'}`
   stabilises; equal nonzero discriminants ⇒ `δ_v` bijective (`bijective_of_discIdeal_eq`,
   already used for Lemma 3.5.2). Deviation from [Hong] (integral closure, [AM, Prop. 5.17]):
   the lead's item "finiteness of the integral closure" is then not needed.
5. `H'_v = H_{v₀+v}/H_{v₀}`: inclusions via `subQuot`; orders by `order_eq_mul`; `range_eq` from
   `[p^v] = j ∘ (iso) ∘ (H_{v₀+v+1}/H_{v₀} → H_{v₀+v+1}/H_{v₀+v})` and
   `mapPoints_quotQuot_eq_one_iff`; `ι_v = [p^{v₀}] : H'_v → G_v`; `T_p H' ≅ T_p H̃`.
6. Thm. 3.5.4 (graph `H̃_v = Γ(f̃_v) ⊆ G_v × H_v`, `PDivGroup.prod`, Lemma 3.5.2 points form),
   Cor. 3.5.5, then `α_K`.

No WIP branch.

## Hand-off (2026-10-18, eighteenth session; superseded)

Done this session (pushed, validated): `65de82d` (**[Hong, Prop. 3.5.1]** over `O_{K'}`,
`PDivGroup.discIdeal_eq_of_iso_OL` / `exists_discIdeal_eq_OL`, proved for real via Hopf
integrals; **[Hong, Lemma 3.5.2]** over `O_{K'}`, `PDivGroup.Hom.bijective_of_mapPoints_bijective_OL`),
`0374df9` (generic-fibre form `bijective_of_baseChange_inverse_OL`), and the commit with
`Product.lean` + this hand-off. See PH3 "18th session" entries. The lead's route suggestions for
Prop. 3.5.1 (transitivity formula, étale ⇒ disc = 1, multiplicativity in exact sequences,
Lipnowski's `v = 1` connected case) were replaced by the integral argument: Lipnowski's Claim 2'
needs Tate's Thm. A.3 (appendix to Mazur–Roberts; not available), whereas the integrals need
only Cramer's rule, the trace formula over `ℚ̄_p`, `h = d + d'` (already proved via Tate's
theorem) and the connected–étale trace reduction. Discriminants of `G` itself are never compared
along exact sequences.

**Blocker for Prop. 3.5.3 / Thm. 3.5.4 (decision needed):** both [Hong, proof of Prop. 3.5.3]
and [Tate, proof of Prop. 12, p. 182] use quotients `H_{v+1}/H_v`, `E_{i+ν}/E_i` of finite flat
group schemes by closed finite flat subgroups, i.e. **[Hong, Thm. 1.1.9] (Grothendieck)**, stated
in [Hong] without proof ([Tate] cites Raynaud, *Passage au quotient par une relation
d'équivalence plate*). In Hopf terms: for a closed finite flat subgroup `H ⊆ G` over `O_{K'}`
(`A ↠ C`), `A` is finite locally free over the invariants `A^H` of rank `|H|` and the kernel of
`G → Spec A^H` is `H`. The repo has this only for `H = G⁰` (`EtaleQuotient*.lean`, special
arguments: formal unramifiedness of `A^{et}`). Analysis this session:
* A quotient-free reformulation does not avoid it: with `S_v ⊆ G_v(ℚ̄_p)` the image of `M`,
  closures `C_v = im(A_v → ℚ̄_p^{S_v})` and the orders
  `D_v = ⋃_i {f : [p^i]^* f ∈ C_{i+v}}` (functions on `S_v`; increasing in `i`, inside the
  integral closure, hence stabilising), one gets Hopf orders (saturation:
  `(C ⊗ C) ∩ (V ⊗ V) = (C ∩ V) ⊗ (C ∩ V)` over a PID) with the right generic fibres, and the
  invariants `D_{v+1}^{S_v} = [p^v]^*(D_1)`; but the kernel condition `range_eq` for `(D_v)` is
  again "`D_{v+1}` is free over its `S_v`-invariants", and surjectivity of `D_{v+1} → D_v` is
  also open.
* Options: (i) formalise [Hong, Thm. 1.1.9] over a complete DVR (references: SGA 3, Exp. V,
  Thm. 4.1; Mumford, *Abelian varieties*, §12, Thm. 1 over a field + fibrewise flatness
  over `O_{K'}`), several sessions; (ii) enter Thm. 1.1.9 (in the Hopf form above) as an
  explicit, honestly named theorem argument recorded as a debt (rule 4), if the lead agrees that
  it is a prerequisite not currently provable cheaply.
* Also needed for Prop. 3.5.3 (independent of the blocker): the closed subgroup schemes
  `H̃_v ⊆ G_{v,K'}` from a `Γ_{K'}`-stable direct summand `M ⊆ T_p G` ([Hong, Prop. 2.1.14]
  direction "Galois module → group scheme"; Galois descent for finite étale `K'`-algebras:
  an element of `K'⊗A` vanishing on a Galois-stable `S` and not at `x ∉ S`, via a norm over a
  finite Galois `L'/K'`), and the integral closure of `O_{K'}` in a finite étale `K'`-algebra
  being finite. `Product.lean` (graph) and Lemma 3.5.2 in the points form are ready for
  [Hong, proof of Thm. 3.5.4]: with `ι : G' → G × H`, `π_1 ∘ ι` is bijective on `ℚ̄_p`-points,
  so `bijective_of_mapPoints_bijective_OL` applies without Prop. 2.1.14.

Next steps, in order:
1. Lead decision on [Hong, Thm. 1.1.9] (prove vs. named debt). Then Prop. 3.5.3 (closures, the
   orders `D_v` / Tate's `Γ_v = E_{i₀+v}/E_{i₀}`, kernel condition from the stabilisation),
   Thm. 3.5.4 (graph via `PDivGroup.prod`, `prodTateEquiv`; `Hom.ext_of_mapTate` for
   uniqueness), Cor. 3.5.5.
2. `α_K` bijective (hand-off 13, item 1).
3. Cleanup (not done, not cheap): `TateNonConn`/`TateNonConnOL` are parallel 550-line files
   (`ZpD p` vs `OL L`); unifying them needs an abstract coefficient-ring/base-field version of
   `etCoordField` and of the Hilbert 90 wiring, with the two heartbeat bumps.

MR7 compatibility: everything new is over `O_{K'}` (`OL L`), with `Ω = ℚ̄_p`; the Hopf-level
lemmas (`HopfTrace`, `HopfDisc`, `IntegralConn`) are over a general domain `R` with an injection
into a separably closed field. No ℤ_p (`ZpD p`) versions of Prop. 3.5.1 / Lemma 3.5.2 were made
(`O_{ℚ_p}` is the case `K' = ℚ_p`).

No WIP branch; nothing unpushed after the final commit.

## Hand-off (2026-10-18, seventeenth session; superseded)

Done this session (pushed, validated): `b72c142` (Hilbert 90 over a base field `F`/`K'`:
`exists_hilbert90_over`, `unr_adjoin_over`, `isUnrStableOver_adjoin`; `OLFrob`: `κ_{K'}`
finite, Frobenius on `O_{K'}` and on finite étale `O_{K'}`-algebras; `EtaleHTOL`: étale `G` over
`O_{K'}` is Hodge–Tate of weight `0`), `0e3fdaf` (`TateNonConnOL`: [Hong, Cor. 3.4.11] over
`K'` for non-connected `G` over `O_{K'}`), and the commit with `Discriminant.lean` + this
hand-off. See PH4 "17th session" above. Lead order item 1 (Hilbert 90 over `K'`, `etCoordField`
over `K'`, `TateNonConn`/`EtaleHT` over `K'`) is complete.

MR7 compatibility: the general base is a field `F` (type) with `ℚ_p → F → ℚ̄_p` and an element
`π`; the coefficient ring of the group schemes is `OL L`. `exists_frobenius_period_local` is
stated for any local ring with finite residue field (usable for finite étale algebras over
`O_{K'}` in Kummer-map arguments). Tate modules stay `ℤ_p`-modules (matrices in `GL_h(ℤ_p)`).

Next steps, in order:

1. **§3.5 over `O_{K'}`** (`R = OL L`, also `ZpD p`):
   (a) [Hong, Prop. 3.5.1] `disc(A_v/O_K) = (p^{d v p^{hv}})` — the hard input; plan in hand-off
       10 (multiplicativity in exact sequences [Tate §(2.2) Prop. 2], [Haines §2.3]; reduction to
       `v = 1`, connected; `disc(A_1) = N(det J)` [Lipnowski App., Claims 2', 2'']; `det J =
       p^d · unit` via invariant differentials). `Discriminant.lean` has the ideal, its
       basis independence, base change and the tensor-product formula; still missing: the
       transitivity formula `disc(C/R) = disc(B/R)^{rk C/B} N_{B/R}(disc(C/B))`, and étale ⇒
       `disc = (1)` (reduce mod `𝔪` with `discr_baseChange`; over the residue field use
       Mathlib's `Algebra.Etale.iff_exists_algEquiv_prod` and `traceForm_nondegenerate` on each
       separable factor; a lemma for traces on finite products is not in Mathlib).
   (b) [Hong, Lemma 3.5.2] = `bijective_of_discIdeal_eq` (done) + (a) + Cor. 3.4.11 over `K'`
       (`exists_finrank_DHT_tateRepOver_neg_one_OL`, done) + height from `T_p` (`finrank_tateRep`):
       remaining wiring: a hom `f : G → H` over `O_K` whose generic fibre is an isomorphism gives
       `α_v : B_v → A_v` with `K ⊗ α_v` bijective; ranks `p^{hv}` equal.
   (c) [Hong, Prop. 3.5.3] (scheme-theoretic closure of `\tilde H_v ⊆ G_v ⊗ K`, quotients
       `H_{v+1}/H_v`, the increasing chain of orders `B_v` stabilises because the integral
       closure of `O_K` in the étale `K`-algebra `B_1 ⊗ K` is noetherian), then Thm. 3.5.4 and
       Cor. 3.5.5 (graph of `τ`, products of `p`-divisible groups, Prop. 2.1.14).
2. `α_K` bijective (hand-off 13, item 1).
3. Possible cleanup: prove `TateNonConn`/`TateNonConnOL` once for an abstract coefficient ring and
   base field (the two files are parallel copies; the `OL` names carry an `OL` suffix), which
   would also remove the two heartbeat bumps.

No WIP branch; nothing unpushed after the final commit.

## Hand-off (2026-10-18, sixteenth session; superseded)

Done this session (pushed, validated): `f2d5f87` (Tate duality over `K'`: the `WIP` branch
`wip-tatedual-over` finished; the slowdown was not one unfolding but every `rw` motive carrying
the larger generic instance terms, so the equivariance is now proved once for abstract lattices
(`baseChangeDualEquiv_gal`) and abstract representations (`dualDualEquiv`); no heartbeat
bumps), `eaad429` (generic fibre over `O_{K'}`: Tate's theorem, Cor. 3.4.11, Thm. 3.4.12,
Cor. 3.4.14 for `F[p^∞]` over `O_{K'}`; see PH4 "base field `K'`" above).

Elaboration note (`HodgeTateOL`): `obtain pat := f args` and `finrank L (DHT …)` over `L = ↥K'`
are slow (instance search for `Module L (DHT ρ q)` tries normed-space paths, ~0.3 s each);
`have h := f args; obtain pat := h` and the local shortcut instances `instModuleDHT`,
`instAddCommGroupDHT` fix this.

Next steps, in order:

1. Remaining `K'` versions: `TateNonConn` (non-connected `G` over `O_{K'}`) and `EtaleHT` need
   **Hilbert 90 over `K'`**: generalise `Hilbert90/` from `(ℚ_p, p, GalQp)` to
   `(K', π_{K'}, Gal(ℚ̄_p/K'))`: `IsUnrStable` relative to `K'` (`|z| < 1 ⇒ |z| ≤ |π|`, stability
   and rigidity for `Gal(ℚ̄_p/K')`), `exists_trace_one` relative to `K'`
   (`∑_{e : M →_{K'} ℚ̄_p} e(b) = 1`, Dedekind on `κ_M`), `exists_additive` mod `π`
   (unchanged proof), `exists_GL_mod_p` over `κ_M/κ_{K'}`, and the approximation in `Main` by
   powers of `π`. Then `etCoordField` over `K'` (`K'(x(a))`, unramified over `K'` since
   `A_w^{et}` is finite étale over `O_{K'}`; `exists_frobenius_period` with `q = #κ_{K'}`).
   Alternative (not chosen): induce from `G_{K'_0}` (`K'_0` maximal unramified) to `G_{ℚ_p}` and use
   Mackey; needs induced representations.
2. §3.5 (plan in hand-off 10), written over the general base.
3. `α_K` bijective (hand-off 13, item 1).

No WIP branch; nothing unpushed.

## Hand-off (2026-10-18, fifteenth session; superseded)

Lead decision (binding): coefficient-ring refactor first, then `exists_connPart_iso` over
`O_{K'}`, then `K'` versions; §3.5 and `α_K` bijectivity after.

Done this session (pushed, validated):

* `bd553c0` **(1) refactor done**: `SerreTate.CoeffRing R` (`SerreTateCompact.lean`; uniformiser
  `π ≠ 0`, `𝔪 = (π)`, compact companion topology on `Cpt R` with open cosets of `𝔪^w`; with the
  instances `IsDomain R`, `IsAdicComplete 𝔪 R`), instances for `ZpD p` and `OL L`
  (`OLCompact.lean`, also `IsDomain`, `IsPrincipalIdealRing` via
  `SerreTate.isDiscreteValuationRing`); `finite_residueField` by compactness. `SerreTateFGL`,
  `SerreTatePDiv`, `SerreTateLift`, `SerreTateEss` are stated over `R`; all `ℤ_p` statements
  keep their names. **(2) done**: `PDivGroup.exists_pdivFGL_iso_of_coeffRing`,
  `exists_connPart_iso_of_coeffRing` (`p ∈ 𝔪_R`), and over `O_{K'}`:
  `GroupScheme/SerreTateOL.lean` (`exists_pdivFGL_iso_OL`, `exists_connPart_iso_OL`).
  **(3), first item done**: `HeightIneq` over `O_{K'}` with the `q`-power Frobenius
  (`FrobExp k q` in `Frobenius.lean`, applied to `F[q] ⊗ 𝔽_q`):
  `PDivFGL.height_le_add_of_connPart_iso_of_coeffRing`,
  `exists_connPart_dual_iso_height_le_of_coeffRing`, `exists_connPart_dual_iso_height_le_OL`.
* `53dd832` start of the **generic-fibre base-field refactor** (needed for every remaining
  `K'` version): the Tate-module machinery for `p`-divisible groups over a field
  `K ⊆ ℚ̄_p` of characteristic `0` (`galPoints`, `galTate`, `galLin`, `dualPDiv`,
  `tateEquivZp`, `exists_tateBasis`, `exists_perfect_tatePairing`, `tatePairingZp`,
  `galDualTate`, `tatePairing_gal`; new `PDivGroup.tateRepOver`, `V_p G` as a
  `Gal(ℚ̄_p/K)`-representation). Intended use: `K = ↥K'`, `G` the generic fibre of a
  `p`-divisible group over `O_{K'}`.

WIP (local branch `wip-tatedual-over`, `3c64d60`, not pushed): `tatePairingZp_galOver`,
`tateDualHom_galOver` (`TateDual` over `K`), `tateRepDualEquiv` over `K` and
`tateRepDualEquiv_galOver` / `isHodgeTate_tateRepOver_dualPDiv` for `G` over `↥L`. Builds up to
`TateDualRep` (the `↥L` proof needs `maxHeartbeats 1600000`), but makes
`DAlphaHT.tateRepDualDualEquiv_symm_gal` (over `ℚ_p`) time out at `whnf`: the generic
`tateRepDualEquiv`/`tateDualHom` slow down the `ℚ_p` defeq checks. Fix options: keep the `ℚ_p`
definitions as they were and add separate `…Over` definitions for `G` over `↥L`, or find the
slow unfolding (likely `LinearMap.congr_fun (H.tateRepDualEquiv_gal L σ⁻¹)` / `rw [he]`).

Next steps, in order:

1. Finish the base-field refactor (WIP above), then `K'` versions on the generic fibre: the
   generic fibre `O_{K'} → K'` of `PDivFGL (OL L)` (analogue of `ZpD → ℚ_p` in
   `DualTateZp.lean`/`DualTateGal.lean`: `dualTateZpEquiv` with `OL.galFixedOver`), then
   `DAlphaHT` (`dalphaK` with `dalpha_injective_OL` in place of `dalpha_injective_Qp`),
   `DAlphaDual`, `HodgeTateFGL`, `TateNonConn` (needs Hilbert 90 over `K'`), `EtaleHT`
   (unramified towers over `K'`). `HeightIneq` over `O_{K'}` is done.
2. §3.5 (plan in hand-off 10), written over the general base.
3. `α_K` bijective (hand-off 13, item 1).

Note: `.lake/packages/*` of this repo are symlinks into `~/iut/.lake/packages` (pre-existing
since 2026-10-16; all builds of this and earlier sessions used them; the lead may want to
replace them by pinned standalone clones when disk allows).

## Hand-off (2026-10-18, fourteenth session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians.
Lead decision (binding order): (1) non-connected `G` over `ℤ_p`; (2) Serre–Tate over `O_{K'}`,
then `K'` versions; (3) §3.5; (4) `α_K` bijectivity last.

Done this session (pushed, validated): `4735899` **(1) done**: `FormalGroup/TateNonConn.lean`,
`dim D_{-1}(V_p G) = dim G⁰` for every `G` over `ℤ_p` (`exists_finrank_DHT_tateRep_neg_one`), by
the direct Hilbert 90 route (no `G^{et}` as a `p`-divisible group needed); the `ZpD p` / `ℤ_[p]`
mismatch is handled by stating everything over `ZpD p` and transporting the single `ℤ_[p]` input
(`exists_frobenius_period_zpD`, definitional). `a325297` **(2), first part**: [Hong,
Prop. 2.2.13] (special-fibre coordinates, `PDivGroup.exists_coords`) now holds over any perfect
field (`[PerfectRing k p]` instead of `x^p = x`), in particular over the residue field `𝔽_q` of
`O_{K'}`: `univPt_pow_apply_eq_zero_of_perfect` (`perfT`, `apply_univPt_pow_perfect`),
`frob_decomp` with `frobInv` on coefficients.

Next steps, in order:

1. **Serre–Tate essential surjectivity over `O_{K'}`** (`OL L`): generalise the lifting files
   `SerreTateCompact`, `SerreTateFGL`, `SerreTatePDiv`, `SerreTateLift`, `SerreTateEss` (≈1700
   lines, almost all generic algebra) from `ZpD p` to a coefficient ring `R` with: `IsLocalRing`,
   `IsDomain`, `IsPrincipalIdealRing`, `IsAdicComplete`, discrete uniformity (formal group laws),
   `𝔪 = (π)`, and a **compact companion topology** on the underlying set (for `ZpD` the metric of
   `ℤ_[p]`; for `OL L` the subspace topology of `OLSub L ⊆ O_{ℂ_p}`, compact since `L` is a
   finite-dimensional, hence proper, `ℚ_p`-space and `O_L` is its closed unit ball) in which the
   `𝔪^w` are open (`mem_pow_iff`: for `OL` this is `OL.mem_span_pow_iff`; compactness of
   `OLSub L` is done: `OL.compactSpace_OLSub`, `FormalGroup/OLCompact.lean`). ZpD-specific places:
   `ofPi/toPi`, `mem_pow_iff`, `ballSet` (`SerreTateCompact`); `isDomain_zpD`, `p_ne_zero`,
   "divide by the largest power of `p`" in `eq_zero_of_forall_red` (use `π`); `toZModD`,
   `algebraZModD` in `SerreTateEss` (use the residue field `𝔪`-quotient, `PerfectRing` from
   `PerfectRing.ofFiniteOfIsReduced` as it is finite). Suggested shape: a `structure`/class of
   such data with instances for `ZpD p` and `OL L`, keeping all `ZpD` statements as
   specialisations. Then `PDivGroup.exists_connPart_iso` over `O_{K'}` is immediate
   (`ConnectedPDiv` is generic).
2. `K'` versions: `HeightIneq` uses the relative Frobenius `frob hk` (`k`-linear only for
   `x^p = x`); over `𝔽_q` either use the `q`-power Frobenius (`k`-linear, kernel killed by `q`,
   apply to `G_f = G[q]`: `hf ≤ fd + fd'`) or the twisted transpose `perfT` from this session;
   then `DAlphaHT`, `DAlphaDual`, `HodgeTateFGL`, `TateNonConn`, `EtaleHT` with `L = K'`
   (`AlphaInjK`/`OK` already give injectivity of `α`, `dα` over `O_{K'}`; `EtaleHT`/Hilbert 90
   need `Gal(ℚ̄_p/K')` and unramified towers over `K'`).
3. §3.5: discriminant formula [Hong, Prop. 3.5.1], Lemma 3.5.2 (input
   `exists_finrank_DHT_tateRep_neg_one` is now available over `ℤ_p`), Prop. 3.5.3,
   Thm. 3.5.4; plan in hand-off 10.
4. `α_K` bijective (hand-off 13, item 1), off the critical path.

No WIP branch; nothing unpushed.

## Hand-off (2026-10-18, thirteenth session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians.

Done this session (file summaries in PH4 above): `DAlphaDual` (step (3.10); **[Hong,
Thm. 3.4.10]** for `dα_K` and **Cor. 3.4.11** for `G = F[p^∞]` over `ℤ_p`; `h = d + d^∨`),
`TateCont` (`V_p G` is continuous), `OrthSplit` (splitting of the orthogonal-complement sequence by
Tate's `H¹`), `HodgeTateFGL` (**[Hong, Thm. 3.4.12, Cor. 3.4.14]** for `F[p^∞]` over `ℤ_p`).

Next steps, in order:

1. **`α_K` bijective** ([Hong, Thm. 3.4.10], first half; not needed for full faithfulness): for a
   Γ-equivariant character `f` of `T_p(G^∨)(O_C)` with values in `1 + m_C`, continuous for the
   `p`-adic topology (needed: additive maps `ℤ_p^h → ℂ_p` need not be `ℤ_p`-linear), `log ∘ f`
   is `dα(z)` with `z ∈ ℚ_p^d` (`dalphaK_bijective`); take `x` with `log_F x = z`
   (`exact_logHom`), then `α(x)/f` is `μ_{p^∞}`-valued and factors through some `G_v^∨`, so it is
   `α(t)` for a torsion `t` (generalise `exists_torsion_alpha_eq` from `p` to `p^v`); `x − t` is
   Γ-invariant by injectivity of `α` and `alpha_gal`.
2. **Non-connected `G` over `ℤ_p`: Cor. 3.4.11 `dim D_{-1}(V_p G) = dim G°`** (this is what
   Lemma 3.5.2 needs). Lower bound: `V_p(G°) ↪ V_p G` (as in `dualConnTateLin`). Upper bound:
   `ker(T_p G → lim G_v^{et}(ℚ̄_p)) = T_p(G°)` (`mapPoints_etaleQuotientHom_eq_one_iff`,
   lifting along `T_p(G°) ↠ G_k°`), `T/T°` torsion free, and `D_{-1}(T/T° ⊗ ℚ_p) = 0`. For the
   last point either build `G^{et}` as a `PDivGroup` (hard part: `range_eq` for all `S`, i.e. the
   schematic image of `G_v` in `G_{v+1}^{et}` is `G_{v+1}^{et}[p^v]`; compare orders using
   faithful flatness of `A` over `A^{et}`) and use `isHodgeTate_tateRep_of_etale`, or run
   `Hilbert90.exists_hilbert90` directly on a basis of `T/T°` (`A(ν) ≡ 1 mod p^k` on
   `Gal(/coordField(G^{et}, k))`, since `ν t − t ∈ T° + p^k T`). Note `EtaleHT` is stated over
   `ℤ_[p]`, the formal-group files over `ZpD p` (a type synonym).
3. Base `O_{K'}`: Serre–Tate over `O_{K'}` (residue field `𝔽_q`: Frobenius twists), then redo
   `HeightIneq`, `DAlphaHT`, `DAlphaDual` with `L = K'` (`AlphaInjK` already gives injectivity).
4. §3.5: discriminant formula [Hong, Prop. 3.5.1] (Tate §(2.2) Prop. 2, Haines §2.3, Lipnowski
   appendix in `lit/dl/padic-hodge/disc/`), Lemma 3.5.2, Prop. 3.5.3 (scheme-theoretic closure),
   Thm. 3.5.4; plan in hand-off 10.

## Hand-off (2026-10-18, twelfth session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians.

Done this session (all pushed with green validation; file-level summaries in PH2–PH4 above):
`b4ac238` (`Frobenius`: `f^p(d^p) = f([p]^*d)`, Nakayama `|G| ≤ |ker f|·|im f|`,
`|G| ≤ |ker φ_G|·|ker φ_{G^∨}|`; `DualTateGal`: Galois equivariance and `ℤ_p`-linearity of
`dualTateZpEquiv`, `dα` `ℤ_p`-linear; `DerivStable`), `3c31409` (`InvariantsK`, `AlphaInjK`:
Lemmas 3.4.2/3.4.3 and injectivity of `α`, `dα` over `K'`), `06ba89e` (`OK`: concrete
`O_{K'}`), `5694efa` (`SpecialFibre`, `SerreTateSpecial`: [Hong, Prop. 2.2.13] by
derivations), `415abe8` (**Serre–Tate essential surjectivity over `ℤ_p`**,
`exists_pdivFGL_iso`), `d66f85d` (**Cartier dual `p`-divisible group over `ℤ_p`** for
`F[p^∞]`, `PDivFGL.dualPDiv`), `8a5c3da` (`Orthogonal`: step (3.11)), `a1780c8`
(`ConnectedPDiv`: **`G°` is a `p`-divisible group**, `G° ≅ F[p^∞]`), `1fb5567` (`DAlphaHT`:
(3.9), `d ≤ dim D_{-1}(V_p G)`), and the commit adding `HeightIneq` (**`h ≤ d + d'`** with
`(G^∨)° ≅ P'.pdivGroup`) and this hand-off.

Next steps, in order:

1. **Tate's theorem [Hong, Thm. 3.4.10] for connected `G = F[p^∞]` over `ℤ_p`** — only one
   input is missing: (3.10), an injective `ℚ_p`-linear map `ℚ_p^{d'} → D_0(V_p(G)^∨)`.
   Planned route (no double duality, no surjectivity): `P'.dalphaK ⊥ : ℚ_p^{d'} ↪
   D_0(V_p(P'^∨)^∨)`; `DHTdualTateEquivMap` for `P'` into `D_{-1}(V_p P')`; a twist-0
   `DHTtwistMap` along the injective Γ-equivariant `ℤ_p`-linear map `V_p(P'_{ℚ_p}) →
   V_p((G_{ℚ_p})^∨)` from `mapTate` of `connPartHom ∘ ψ` (`exists_connPart_iso`) and the
   base-change identifications (`baseChangeTateEquiv`, `dualPDivBaseChangeTateEquiv`;
   injective since `connPartHom_mapPoints_injective` levelwise; Galois-equivariance and
   `ℤ_p`-linearity still to prove); `DHTtwistMap (-1)` along `rid ∘ tateRepDualEquiv` into
   `D_0(V_p(G)^∨)`. Then `bijective_of_finrank_le_add_fin` (Orthogonal.lean) with
   `dalphaKTwist ⊥`, this map and `exists_connPart_dual_iso_height_le` gives **`dα_K`
   bijective** and **Cor. 3.4.11** (`d = dim D_{-1}(V_p G)`); bijectivity of `α_K` from
   [Hong]'s snake-lemma diagram (`logGm_alpha`, `exact_logHom`); then **Thm. 3.4.12**
   (Hodge–Tate decomposition, weights `{0, 1}`; `htWeights`).
2. **General (non-connected) `G` over `ℤ_p`**: `α` via `G° = F[p^∞]` (`exists_connPart_iso`) as
   in [Hong, Prop. 3.4.9, proof]; `G^∨` over `ℤ_p` for general `G` (`DualPDivData` for
   non-connected layers — or via the connected–étale sequence; `G^{et}` as a `p`-divisible
   group is not yet done); uniqueness of `d` ([Hong, Def. 2.2.17]).
3. Base `O_{K'}`: `OK.lean` gives `α`, `dα` injectivity; still to generalise to `O_{K'}`:
   Serre–Tate (`SerreTateEss` uses `ℤ_p` compactness and `𝔽_p` with `x^p = x`; residue field
   `𝔽_q` needs Frobenius twists or restriction of scalars), `DualPDivFGL` (already general
   complete local `R`), Tate modules / Hodge–Tate over `K'` (`tateRep L`, `galPoints` over
   `ℚ_p`).
4. Discriminant formula and full faithfulness ([Hong, Prop. 3.5.1, Lemma 3.5.2, Prop. 3.5.3,
   Thm. 3.5.4]): proof plan in hand-off 10.

## Hand-off (2026-10-18, eleventh session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians.

Done this session (`63cf447`, pushed with green validation; see PH4 above for the file-level
summary):

* **Injectivity of `α` on `G(ℤ_p)`** ([Hong, Prop. 3.4.9], `K = ℚ_p`, connected `G = F[p^∞]`):
  `PDivFGL.eq_zero_of_alpha_eq_one` (`AlphaInj.lean`), via `T_p(G^∨)(O_C) → G_v^∨(O_C)`
  surjective and `ker(T_p(G^∨) → G_1^∨) = p T_p(G^∨)` (`DualTateField.lean`, `DualTateOC.lean`,
  counting over `ℂ_p`), perfectness of the level-1 pairing over `O_C` (both halves), and
  [Hong, Lemmas 3.4.2, 3.4.3] over `ℚ_p`. **Injectivity of `dα` on `t_G(ℚ_p)`**
  (`DAlphaInj.lean`, local inverse of `log_F` instead of the snake lemma).
* **`d + d^∨ = h` sub-project started**: `MvPowerSeries.pderiv` and the chain rule
  `pderiv_subst` (`PDeriv.lean`, generic, upstreamable); invariant derivations and
  **`[p]_F(T) ∈ (T^p)` in characteristic `p`** (`InvDeriv.lean`); **order `p^d` of the Frobenius
  kernel of `F[p]`** (`FrobKernel.lean`).
* **`T_p(G^∨)(O_{ℂ_p}) ≃* T_p(G_{ℚ_p}^∨)(ℚ̄_p)`** for `G` over `ℤ_p` (`DualTateZp.lean`), from
  Cartier duality commuting with base change on points (`DualBaseChange.lean`).

Next steps, in order:

1. **`d + d^∨ = h`** ([Hong, Thm. 2.2.19]), remaining: (c) Frobenius `φ` and Verschiebung
   `ψ = (φ_{G^∨})^∨` for finite flat group schemes over a perfect field `k` of char. `p`
   (`A^{(p)} = A ⊗_{k,Frob} k`; for `k = 𝔽_p`, `A^{(p)} = A` and `φ^*(a) = a^p`), `ψ ∘ φ = [p]`
   ([Hong, Prop. 1.5.8], via symmetric tensors after [Pink, §14]); (d) orders in exact sequences
   of finite `k`-group schemes (faithful flatness over Hopf subalgebras) and exactness of Cartier
   duality; (e) `d^∨` for non-connected `G^∨`: the Cartier dual `p`-divisible group over `ℤ_p`
   (only `dualPDiv` over `ℚ_p` exists), the connected–étale sequence and Serre–Tate essential
   surjectivity for `(G^∨)°` ([Hong, Thm. 2.2.16, second half]). Note: only `h ≤ d + d^∨` is
   needed in [Hong, proof of Thm. 3.4.10] (the reverse inequality follows from (3.9)–(3.11)).
2. **Tate [Hong, Thm. 3.4.10], Cor. 3.4.11, Thm. 3.4.12** for `G` over `ℤ_p`: inputs now
   available: injectivity of `α_K`, `dα_K` (this session), Galois equivariance (`alpha_gal`),
   `dualTateZpEquiv` (still to do: its Galois equivariance, `galDual ↔ galDualTate`, and the
   compatibility of `α` on torsion with `tatePairing` through it), `tateDualHom`,
   `sum_finrank_DHT_le`. Missing: (3.10) for `G^∨` (needs `α`, `dα` for the possibly
   non-connected `G^∨`, i.e. item 1(e) and [Hong, Prop. 3.4.9] for general `G` via `G°`), and
   item 1.
3. Base `O_{K'}` ([Hong] with `K = K'`): `AlphaInj` uses `GalFixed` for all of `Γ_{ℚ_p}` and
   [Hong, Lemma 3.4.3] over `ℚ_p` (`eq_zero_of_forall_pow_nsmul_Qp`); for `K'` one needs the
   bound `|x| ≤ |π_{K'}|` on `m_{K'}` (discreteness of the value group of a finite `K'/ℚ_p`;
   `Cyclotomic/Norms.lean` has value groups of finite extensions) and `galPt_fixed_iff` with
   `L = K'`; plus the concrete `O_{K'}` coefficient ring (hand-off 10, item 4).
4. Discriminant formula and full faithfulness ([Hong, Prop. 3.5.1, Lemma 3.5.2, Prop. 3.5.3,
   Thm. 3.5.4]): proof plan in hand-off 10 (Tate §(2.2) Prop. 2, Haines §2.3, Lipnowski App.).

## Hand-off (2026-10-18, tenth session; superseded)

Scope (unchanged, `~/iut-scratch/multiradial/MR6-scoping.md`, item A2): [LocAn] needs Tate's
Theorem 4 (full faithfulness of `G ↦ T_p G` over `O_{K'}`) for `p`-divisible groups of Jacobians
(dimension `d = g`).

Done this session (pushed with green validation): `33a51f4` (`CartierChar`, `Alpha`, `MapFGL`,
`AlphaLog`, `AlphaGal`: **`α` for connected `G = F[p^∞]`** — `T_p(G^∨)(O_C)` points give
group-like `χ_{y_v} ∈ O_C ⊗ A_v`, hence `U_y ∈ O_C[[T]]` with `U_y(Φ) = U_y U_y`,
`α(x)(y) = U_y(x)` bimultiplicative with values in `1 + m_C`, left square = Cartier pairing on
torsion, `u_y = U_y − 1 : F_{O_C} → Ĝ_m`, `dα`, right square via `LogNat`, Galois equivariance)
`addf7c1` (`Zp`: all hypotheses discharged for `R = ℤ_p`; this hand-off), `9fbfffa`
(`OCAdicPi`: `O_C` is `π`-adically complete; `alpha_gal` for each `σ` fixing the coefficients),
`dcce379` (`IntegralPoints`: `G(O_C) ≃* G(ℂ_p)`; `CartierPerfectOC`: the Cartier pairing over
`O_C` separates points of `G` killed by `n ≠ 0`), and the commit updating this hand-off.

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
   `exists_dual_quot_eq_padicAlgCl`; for `G` over `ℤ_p` either extend characters from
   `G_v(ℂ_p)` to `G_{v+1}(ℂ_p)` — via `pairingHom_bijective` both duals are character groups —
   or prove `Dual(ℚ_p ⊗ A) ≅ ℚ_p ⊗ Dual(A)` to reuse `dualPDiv`), (iii) `α(t) = 1 ⇒ t = 0` for
   torsion `t`: from `alpha_torsion`, (ii) and `eq_one_of_pairing_OC` (plus `layerPt` of `0`
   is the unit point and `layerPt_injective`).
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
