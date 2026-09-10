export Semiring, ℕ, 𝔹

# Sets versus multisets
#----------------------
#
# A side of a sequent is a formal sum of terms with coefficients in a
# commutative semiring `K`, and the positions of a frame form the monoid
# `K[X]²`. Two semirings are in play:
#
# - `ℕ`: multisets, `ℕ[X]²`, where `x + x ≠ x`. This is the monoid of the paper,
#   with exchange as the only structural rule built in.
# - `𝔹`: the Booleans `{0, 1}` with `1 + 1 = 1`, so that `𝔹[X] = 𝒫_fin(X)` and a
#   side is a *set* of terms. Addition is union, and contraction `x + x = x`
#   holds. These are the paper's idempotent frames, `I ⊆ 𝒫[X + X]`.
#
# Both are stored as `MultiSet`s; with `𝔹` coefficients every multiplicity is `1`,
# which the `Sequent` constructor checks. The semiring is a type parameter of
# `Sequent`, `Constructible`, `Frame`, `Role` and `RolePair`, so the two theories
# never mix, and what differs between them is confined to a few methods: `+`
# (`add`), the constructor from a list of terms (`side`), and, for the reflexive
# weakening `ℛ`, `refl_leq`, `refl_meet`, `residual_strict`, `residual_refl`,
# `refl_predecessors` and `stack` (`SingletonResidual.jl`, `NormalForm.jl`).
# Everything else is written once, for `Sequent{K}`.
#
# Why the reflexive part is where they differ: `t ∈ ℛ(m)` means `t = m + ρ` for
# some `ρ ∈ R`. With `ℕ` coefficients `ρ = t - m` is determined and the test is
# `imb(t) = imb(m)`; with `𝔹` coefficients `m + ρ` may absorb part of `ρ` into
# `m` (`a⁺ + a⁺a⁻ = a⁺a⁻`), so `ρ` is not determined and the imbalance is not
# additive. The characterization becomes `m ≼ t` with `t⁺ ∖ m⁺ ⊆ t⁻` and
# `t⁻ ∖ m⁻ ⊆ t⁺`, and a singleton residual `{s} ⊸ ℛ(m)`, or `{s} ⊸ {k}`, has
# several generators rather than one.
#
# The support map `q : ℕ[X]² → 𝔹[X]²` (`Sequent{𝔹}(::Sequent{ℕ})`) is a
# surjective monoid homomorphism, and for a frame `(X, I′)` with `𝔹` coefficients
# the frame `(X, q⁻¹(I′))` with `ℕ` coefficients has the same Girard quantale:
# `A^⊥ = q⁻¹(q(A)^⊥′)` for every `A ⊆ ℕ[X]²`, so `q⁻¹` is an isomorphism of the
# closed roles commuting with `⊗`-closure, `∩`, the quantifiers and `⊨`. The
# frames `q⁻¹(I′)` are exactly the *contractive* ones of the paper, those with
# `{2s}^⊥ = {s}^⊥` for all `s`, i.e. `I = q⁻¹(q(I))`; adding a doubled rule to
# `I`, as the courtroom's contractive court does, does not make a frame
# contractive in this sense (`test/Contraction.jl`).
# Semantically, then, sets reduce to multisets. Presentations do not:
# `q⁻¹({k})` and `q⁻¹(ℛ(m))` are not constructible triples (they contain elements
# of every multiplicity yet are not up-closed); only `q⁻¹(𝒲(l)) = 𝒲(l)` is. So a
# `𝔹` frame with weakening, `I′ = 𝒲(λ′)`, may equally be computed with `ℕ`
# coefficients and the results read off through `q` (`test/Contraction.jl` does
# this as a cross-check), whereas `κ` or `ℛ` generators need the `𝔹` methods.

""" The coefficients of a side of a sequent; see the note above """
abstract type Semiring end

""" Multisets: the free commutative monoid, without contraction """
struct ℕ <: Semiring end

""" Sets: the free commutative idempotent monoid, with contraction """
struct 𝔹 <: Semiring end
