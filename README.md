# padic-hodge

p-adic Hodge theory in Lean 4 / Mathlib, as needed for Mochizuki's relative p-adic
Grothendieck conjecture ([LocAn] Theorem A), which feeds the formalisation of the multiradial
algorithm of IUT III, Theorem 3.11.

Mathlib pin: `v4.32.0` (commit 81a5d25), the same as `iut`. No other dependencies.

## Status

Phase PH0 (skeleton) and the `H⁰` part of PH1 (all twists) (see `Blueprint.md`):

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

No `sorry`, no `axiom`. All builds use `lake build --wfail`.

## Reused Mathlib material

`PadicAlgCl`, `PadicComplex` (`ℂ_[p]`, algebraically closed), `spectralNorm_eq_of_equiv`
(Galois automorphisms are isometries), `continuousCohomology` and `TopRep`,
`cyclotomicCharacter`, Krasner's lemma (`Mathlib/Analysis/Normed/Field/Krasner.lean`),
`BDeRhamPlus`/`BDeRham` and Fontaine's `θ` (`Mathlib/RingTheory/Perfectoid/`), Witt vectors.

## References

See `references/README.md`.
