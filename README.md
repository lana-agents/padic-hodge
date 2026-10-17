# padic-hodge

p-adic Hodge theory in Lean 4 / Mathlib, as needed for Mochizuki's relative p-adic
Grothendieck conjecture ([LocAn] Theorem A), which feeds the formalisation of the multiradial
algorithm of IUT III, Theorem 3.11.

Mathlib pin: `v4.32.0` (commit 81a5d25), the same as `iut`. One further dependency:
`lana-agents/padic-log-volume` (pinned at `9a190da`, the same pin as `iut`), for the `p`-adic
logarithm `PadicLogVolume.padicLog`.

## Status

Phase PH0 (skeleton), the `H⁰` part of PH1 (all twists), and the core of PH2 (see `Blueprint.md`):

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
  (`isHodgeTate_dual`, `isHodgeTate_tprod`); Hodge–Tate weights (`htWeights`).
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
  over `\hat F_∞`, `TateSen/Coord.lean`). The remaining input for Tate's `H¹(G_K, ℂ_p(j))` is almost étaleness
  (`Blueprint.md`, PH1.AE).

No `sorry`, no `axiom`. All builds use `lake build --wfail`.

## Reused Mathlib material

`PadicAlgCl`, `PadicComplex` (`ℂ_[p]`, algebraically closed), `spectralNorm_eq_of_equiv`
(Galois automorphisms are isometries), `continuousCohomology` and `TopRep`,
`cyclotomicCharacter`, Krasner's lemma (`Mathlib/Analysis/Normed/Field/Krasner.lean`),
`BDeRhamPlus`/`BDeRham` and Fontaine's `θ` (`Mathlib/RingTheory/Perfectoid/`), Witt vectors.

## References

See `references/README.md`.
