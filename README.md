# padic-hodge

p-adic Hodge theory in Lean 4 / Mathlib, as needed for Mochizuki's relative p-adic
Grothendieck conjecture ([LocAn] Theorem A), which feeds the formalisation of the multiradial
algorithm of IUT III, Theorem 3.11.

Mathlib pin: `v4.32.0` (commit 81a5d25), the same as `iut`. No other dependencies.

## Status

Phase PH0 (skeleton) and the first part of PH1 (see `Blueprint.md`):

* `PadicHodge/Galois/Basic.lean`: the Galois group `G_L = PadicAlgCl p ≃ₐ[L] PadicAlgCl p`
  of an intermediate field `L` of `ℚ̄_p/ℚ_p` acts on `ℂ_[p]` by isometric continuous ring
  automorphisms (`PadicHodge.galCp`).

No `sorry`, no `axiom`. All builds use `lake build --wfail`.

## Reused Mathlib material

`PadicAlgCl`, `PadicComplex` (`ℂ_[p]`, algebraically closed), `spectralNorm_eq_of_equiv`
(Galois automorphisms are isometries), `continuousCohomology` and `TopRep`,
`cyclotomicCharacter`, Krasner's lemma (`Mathlib/Analysis/Normed/Field/Krasner.lean`),
`BDeRhamPlus`/`BDeRham` and Fontaine's `θ` (`Mathlib/RingTheory/Perfectoid/`), Witt vectors.

## References

See `references/README.md`.
