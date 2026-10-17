# padic-hodge

p-adic Hodge theory in Lean 4 / Mathlib, as needed for Mochizuki's relative p-adic
Grothendieck conjecture ([LocAn] Theorem A), which feeds the formalisation of the multiradial
algorithm of IUT III, Theorem 3.11.

Mathlib pin: `v4.32.0` (commit 81a5d25), the same as `iut`. One further dependency:
`lana-agents/padic-log-volume` (pinned at `9a190da`, the same pin as `iut`), for the `p`-adic
logarithm `PadicLogVolume.padicLog`.

## Status

Phase PH0 (skeleton), PH1 (Tate's `H⁰` and `H¹` of `ℂ_p(j)`, including almost étaleness), and the core of PH2 (see `Blueprint.md`):

* `PadicHodge/Galois/Basic.lean`: the Galois group `G_L = PadicAlgCl p ≃ₐ[L] PadicAlgCl p`
  of an intermediate field `L` of `ℚ̄_p/ℚ_p` acts on `ℂ_[p]` by isometric continuous ring
  automorphisms (`PadicHodge.galCp`).
* `PadicHodge/AxSenTate/`: **Ax's lemma** (`PadicHodge.ax`: if all `G_L`-conjugates of
  `α ∈ ℚ̄_p` lie within `c` of `α`, then `α` lies within `p^{p/(p-1)²} c` of `L`), the
  **Ax–Sen–Tate theorem** `ℂ_[p]^{G_L} = closure L` (`galCp_eq_self_iff_mem_closure`), `= L` for
  `L/ℚ_p` finite (`galCp_eq_self_iff_mem`), and `H⁰_cont(G_L, ℂ_[p]) ≅ L` (`H0CpIso`, Mathlib's
  `continuousCohomology`).
* `PadicHodge/Cyclotomic/`, `PadicHodge/TateSen/`: **Tate's theorem** `ℂ_p(j)^{G_L} = 0` for
  `j ≠ 0` and `L/ℚ_p` finite (`cpTwistRep_invariants_eq_bot`, `H0CpTwistIso`), via the
  cyclotomic tower `ℚ_p(μ_{p^∞})` (`[ℚ_p(ζ_{p^n}) : ℚ_p] = φ(p^n)`), Tate's normalised traces with
  estimates uniform in the level, and the norm trick from `G_{ℚ_p}` to `G_L`.
* `PadicHodge/HodgeTate/`: Hodge–Tate representations: the Serre–Tate lemma, `D_q(V)`,
  `IsHodgeTate`, the Hodge–Tate decomposition criterion, stability under sub- and quotient
  representations, and `Hom_{G_L}(ℂ_p(a), ℂ_p(b)) = 0` for `a ≠ b`; duals and tensor products
  (`isHodgeTate_dual`, `isHodgeTate_tprod`); Hodge–Tate weights (`htWeights`); extensions with
  disjoint weights are Hodge–Tate (`isHodgeTate_of_exact_of_disjoint`, `HodgeTate/Splitting.lean`,
  the existence half of the splitting, via Tate's `H¹`).
* `PadicHodge/Cohomology/ContH1.lean`: continuous `H¹` via crossed homomorphisms, restriction,
  inflation, degree-one inflation–restriction, finite-index averaging.
* `PadicHodge/TateSen/H1Gamma*.lean`: `H¹(Γ, (ℂ_p(j))^{H}) = 0` for `j ≠ 0` over `ℚ_p`
  (`Γ = Gal(ℚ_p(μ_{p^∞})/ℚ_p)`), from the uniform solution of `χ(γ)^j γ m − m = z` on the
  completion of `ℚ_p(μ_{p^∞})` (`exists_twist_eq`); and `H¹(Γ, ℂ_p^{H}) ≅ ℚ_p`, spanned by
  `log χ` (`H1QuotientZeroEquiv`, `finrank_H1_quotient_zero`, `TateSen/H1GammaZero.lean`), via
  Tate's decomposition `\hat{ℚ_p(μ_{p^∞})} = (γ - 1)(…) + ℚ_p(μ_{p^n})` (`Cyclotomic/Decomp.lean`)
  and the logarithm of the cyclotomic character (`Cyclotomic/LogChi.lean`, reusing
  `padic-log-volume`). For finite `K / ℚ_p`: `H¹(Gal(K_∞/K), \hat K_∞(j)) = 0` (`j ≠ 0`) and
  `≅ K` (`j = 0`) (`TateSen/H1K.lean`, `TateSen/H1KZero.lean`, via coordinates on `\hat K_∞`
  over `\hat F_∞`, `TateSen/Coord.lean`).
* `PadicHodge/AlmostEtale/`: **Tate's almost-étaleness theorem** for `K_∞ = K(μ_{p^∞})` via
  Faltings' commutative-algebra route ([BC, Exercise 13.7.4], `d = 0`), with explicit monogenic
  generators instead of Kähler differentials: Euler's lemma for the trace dual of `O_F[z]`
  (`Euler.lean`), `O_L = ℤ_p[z]` for finite `L/ℚ_p` (`Mono.lean`), Faltings' inductive step
  `‖a‖² ≤ ‖b‖² max(‖a‖, ‖p‖)` (`Step.lean`), the cyclotomic input `O_{F_{n+1}} = O_{F_n}[ζ]`,
  `𝔇 = (p)` and transitivity of the different (`Cyclo.lean`), `δ_n → 0` and the trace estimate
  (`Tower.lean`, `exists_trace_large`), descent to finite layers (`TraceOne.lean`,
  `exists_trace_one`), and **`H¹(Gal(ℚ̄_p/K_∞), ℂ_p) = 0`** (`H1.lean`, `exists_coboundary`).
* `PadicHodge/TateSen/TateH1.lean`: **Tate's theorem** for finite `K/ℚ_p`:
  `H¹_cont(G_K, ℂ_p(j)) = 0` for `j ≠ 0` (`subsingleton_H1_twist`) and
  `H1ZeroEquiv : K ≃ₗ[ℚ_p] H¹_cont(G_K, ℂ_p)`, `s ↦ [s log χ]` (`finrank_H1_zero`).

* `PadicHodge/GroupScheme/`: finite flat group schemes (Hopf form), `p`-divisible groups, Tate
  modules, `μ_{p^∞}`, and `T_p μ_{p^∞} ≅ ℤ_p(1)` (`tateMuZpEquiv`, `tateMuZpEquiv_gal`).
  **Cartier duality** (`Cartier.lean`: the dual Hopf algebra `A^∨`, `FFGroupScheme.dual`;
  `CartierDouble.lean`: `G ≅ G^∨∨`; `CartierDiag.lean`: `D(M)^∨ ≅ M_R`); `ℚ_p(j)` is Hodge–Tate of
  weight `-j` (`HodgeTate/Character.lean`), hence `T_p μ_{p^∞} ⊗ ℂ_p ≅ ℂ_p(1)` (`TateMuHT.lean`).
  Connected component `G⁰` over a complete local ring (`Connected*.lean`), the étale quotient
  `G^{et}` and `|G| = |G⁰| · |G^{et}|` (`EtaleQuotient*.lean`); Cartier pairing over any
  `R`-algebra (`CartierPairingBase.lean`); quotient maps, morphisms and base change of
  `p`-divisible groups (`PDivisibleHom.lean`, `BaseChange.lean`); the Galois-equivariant pairing
  `T_p G × T_p G^∨ → ℤ_p(1)` (`TatePairing.lean`); étaleness of group schemes killed by an
  invertible integer and `#G_v(ℚ̄_p) = p^{hv}` (`EtaleInvertible.lean`, `EtalePoints.lean`,
  `PDivisiblePoints.lean`).

No `sorry`, no `axiom`. All builds use `lake build --wfail`.

## Reused Mathlib material

`PadicAlgCl`, `PadicComplex` (`ℂ_[p]`, algebraically closed), `spectralNorm_eq_of_equiv`
(Galois automorphisms are isometries), `continuousCohomology` and `TopRep`,
`cyclotomicCharacter`, Krasner's lemma (`Mathlib/Analysis/Normed/Field/Krasner.lean`),
`BDeRhamPlus`/`BDeRham` and Fontaine's `θ` (`Mathlib/RingTheory/Perfectoid/`), Witt vectors.

## References

See `references/README.md`.
