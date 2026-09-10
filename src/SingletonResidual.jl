export residual, enlarge_context, ≼, ∸, ∨, ∧, refl_dominator, refl_core, imbalance,
       isreflexive, refl_leq, refl_above, refl_meet, core, →ₒ

# The building block for residuation: the residual `{s} ⊸ C` of a
# constructible triple `C` by a *single* element `s` of `M = K[X]²`,
#
#     {s} ⊸ C  =  {t | s + t ∈ C}  =  {c - s | c ∈ C, c ≥ s}.
#
# this is again a constructible triple, and gives its
# three generator lists in closed form. Residuals by orbit-finite subobjects are
# intersections of these and live in `Residual.jl`.
# here everything is a computation on generators.
#
# This file also holds the methods that distinguish `ℕ` from `𝔹` coefficients
# (`Semiring.jl`): `refl_leq`, `refl_meet`, `residual_strict`, `residual_refl`
# and `refl_predecessors`, each given for both semirings side by side.



# The reflexive submonoid R ⊆ M
#-----------------------------

# `R` consists of the sequents `Z ⊢ Z` with the same side twice.
# Every `s` is sandwiched by reflexive elements, `sᵣ ≼ s ≼ ŝ`,
# and these two bounds together with the imbalance are the "gadgets" that make
# `ℛ` computable (`lemma:reflprops`).

""" Is `s ∈ R`, i.e. `s⁺ = s⁻`? """
isreflexive(s::Sequent)::Bool = s.prem == s.conc

"""
The *least reflexive dominator* `ŝ := (s⁺ ∨ s⁻)⁺ + (s⁺ ∨ s⁻)⁻`, the least
element of `R` above `s`. For `ρ ∈ R`: `ρ ≽ s  iff  ρ ≽ ŝ`, and then `ρ - ŝ ∈ R`
"""
function refl_dominator(s::Sequent{K})::Sequent{K} where K
  z = s.prem ∨ s.conc
  Sequent{K}(z, copy(z))
end

"""
The greatest reflexive element below `s`, `sᵣ := Σ_y min(s(y⁺), s(y⁻)) (y⁺ + y⁻)`.
With `ℕ` coefficients the *core* `s_c := s - sᵣ` is what is left, and `|s_c| = |imb(s)|`.
"""
function refl_core(s::Sequent{K})::Sequent{K} where K
  z = (s.prem ∧ s.conc)
  Sequent{K}(z, copy(z))
end

"""
The *imbalance* `imb(s) := s⁺ - s⁻`, a ℤ-valued multiset on `X`. It is
equivariant and vanishes exactly on `R`. With `ℕ` coefficients it is moreover
additive, so that `t ∈ ℛ(m)` iff `m ≼ t` and `imb(m) = imb(t)`; with `𝔹`
coefficients it is not (`imb(a⁺ + a⁺a⁻) = 0 ≠ imb(a⁺) + imb(a⁺a⁻)`), and `ℛ`
membership is `refl_leq` instead. `|imb(s)| = Σ_y |imb(s)(y)|` counts the
unbalanced signed claimables of `s` either way.
"""
imbalance(s::Sequent)::Dict{Term,Int} = s.prem - s.conc

"""
The unique *core* with a given imbalance: the `s_c` with `imb(s_c) = i` and
`s_c ∩ R = 0`, i.e. positive counts on the left and negative ones on the right.
Inverse to `imbalance` on cores, so `core(imbalance(s)) == s - refl_core(s)`.
"""
core(i::Dict{Term,Int})::Sequent{ℕ} =
  Sequent{ℕ}(MultiSet(Dict{Term,Int}(t => n for (t, n) in i if n > 0)),
             MultiSet(Dict{Term,Int}(t => -n for (t, n) in i if n < 0)))

# The order ≤_ℛ, in both semirings
#---------------------------------

"""
The order `m ≤_ℛ t`, i.e. `t ∈ ℛ(m)`: `t = m + ρ` for some `ρ ∈ R`.

With `ℕ` coefficients `ρ` can only be `t - m`, so the test is that `t - m` be
reflexive. With `𝔹` coefficients `m + ρ` may absorb part of `ρ` into `m`, so the
test is that `m ≼ t` and every signed claimable of `t` outside `m` be balanced
in `t`: `t⁺ ∖ m⁺ ⊆ t⁻` and `t⁻ ∖ m⁻ ⊆ t⁺`. (Then `ρ := (t⁺ ∖ m⁺) ∪ (t⁻ ∖ m⁻)`,
on both sides, works, and conversely any `ρ` satisfies these.)
"""
refl_leq(m::Sequent{ℕ}, t::Sequent{ℕ})::Bool = m ≼ t && isreflexive(t - m)
refl_leq(m::Sequent{𝔹}, t::Sequent{𝔹})::Bool =
  m ≼ t && (t.prem ∸ m.prem) ≼ t.conc && (t.conc ∸ m.conc) ≼ t.prem

"""
The least element of `ℛ(m)` above `w`, namely `m + (w ∸ m)^`
(`lemma:reflprops` e). In both semirings: `m + ρ ≽ w` iff `ρ ≽ w ∸ m` iff
`ρ ≽ (w ∸ m)^`, for `ρ ∈ R`.
"""
(refl_above(m::Sequent{K}, w::Sequent{K})::Sequent{K}) where K =
  m + refl_dominator(w ∸ m)

"""
A generator of `ℛ(m₁) ∩ ℛ(m₂)`, or `nothing` if that is empty.

With `ℕ` coefficients the intersection is `ℛ(m₁ ∨ m₂)` when the imbalances
agree and empty otherwise (`lemma:reflprops` d). With `𝔹` coefficients it is
never empty: by `refl_leq`, `t` lies in both iff `t ≽ m₁ ∨ m₂` and every signed
claimable of `t` outside `m₁ ∧ m₂` is balanced in `t`, i.e.
`t ∈ ℛ(m₁ ∧ m₂) ∩ 𝒲(m₁ ∨ m₂)`, which `refl_above` generates. E.g.
`ℛ(a⁺) ∩ ℛ(b⁺) = ℛ(a⁺b⁺a⁻b⁻)`.
"""
refl_meet(m₁::Sequent{ℕ}, m₂::Sequent{ℕ}) =
  imbalance(m₁) == imbalance(m₂) ? m₁ ∨ m₂ : nothing
refl_meet(m₁::Sequent{𝔹}, m₂::Sequent{𝔹}) = refl_above(m₁ ∧ m₂, m₁ ∨ m₂)

"""
The elements one step below `g` in the order `≤_ℛ`: the `g′` with `g′ ≤_ℛ g`
differing from `g` by a single balanced pair. With `ℕ` coefficients these are
`g - x⁺x⁻` for the balanced pairs of `g`; with `𝔹` coefficients `g′ + x⁺x⁻ = g`
also when `g′` keeps one of the two, so `g` less either or both of them.
Used to test `≤_ℛ`-minimality inside a set absorbing `R` (`normal_form`).
"""
refl_predecessors(g::Sequent{ℕ}) = Sequent{ℕ}[g - ρ for ρ in balanced_pairs(g)]
refl_predecessors(g::Sequent{𝔹}) =
  Sequent{𝔹}[g ∸ u for ρ in balanced_pairs(g) for u in [ρ; atoms(ρ)]]


# The singleton residual
#-----------------------

"""
The generators of `{s} ⊸ {k} = {t | s + t = k}`. With `ℕ` coefficients this is
`{k - s}` if `s ≼ k` and empty otherwise. With `𝔹` coefficients every
`t = (k ∖ s) + u` with `u ≼ s ∧ k` solves `s + t = k`: the interval
`[k ∖ s, k]`, listed element by element (there is no constructible shorthand
for an interval).
"""
residual_strict(s::Sequent{ℕ}, k::Sequent{ℕ}) = s ≼ k ? [k - s] : Sequent{ℕ}[]
residual_strict(s::Sequent{𝔹}, k::Sequent{𝔹}) =
  s ≼ k ? Sequent{𝔹}[(k ∸ s) + u for u in subsequents(s ∧ k)] : Sequent{𝔹}[]

""" Every `u ≼ s`, with `𝔹` coefficients: all pairs of subsets of the two sides """
subsequents(s::Sequent{𝔹})::Vector{Sequent{𝔹}} =
  Sequent{𝔹}[Sequent{𝔹}(collect(p), collect(c))
             for p in powerset(collect(keys(s.prem))) for c in powerset(collect(keys(s.conc)))]

"""
The generators of `{s} ⊸ ℛ(m) = {t | s + t = m + ρ for some ρ ∈ R}`, the union
of `{s} ⊸ {m + ρ}` over `ρ ∈ R`.

With `ℕ` coefficients (`lemma:reflresidual`) `ρ` must bring `m` above `s`, the
least such is `(s ∸ m)^`, every other differs from it by an element of `R`, and
`{s} ⊸ {m + ρ}` is a singleton: so `{s} ⊸ ℛ(m) = ℛ(m + (s ∸ m)^ - s)`.

With `𝔹` coefficients `{s} ⊸ {m + ρ}` is an interval (`residual_strict`), and
`ρ = Z ⊢ Z` must contain `Z₀`, the terms of `s ∸ m`. Only its part within the
terms `U` of `s` and `m` matters: a term `z ∉ U` of `Z` appears in both sides
of `m + ρ`, hence of `t`, so `t` is `t′ + z⁺z⁻` for the solution `t′` with `z`
dropped from `Z`, and the residual is closed under adding balanced pairs
(`s + t + z⁺z⁻ = (m + ρ) + z⁺z⁻ ∈ ℛ(m)`). Hence the generators are the
intervals `{s} ⊸ {m + Z⁺Z⁻}` for `Z₀ ⊆ Z ⊆ U`, and the `≤_ℛ`-dominated ones
among them are dropped. E.g. `{a⁺} ⊸ ℛ(a⁺b⁻) = ℛ(b⁻) ∪ ℛ(a⁺b⁻) ∪ ℛ(a⁻b⁻)`:
`a⁺ + a⁺b⁻ = a⁺b⁻` by contraction, and `a⁺ + a⁻b⁻ = a⁺b⁻ + a⁺a⁻`.
"""
residual_refl(s::Sequent{ℕ}, m::Sequent{ℕ}) = Sequent{ℕ}[refl_above(m, s) - s]
function residual_refl(s::Sequent{𝔹}, m::Sequent{𝔹})::Vector{Sequent{𝔹}}
  Z₀ = terms(s ∸ m)
  U = collect(setdiff(terms(s) ∪ terms(m), Z₀))
  cands = Sequent{𝔹}[]
  for Z₁ in powerset(U)
    Z = collect(Z₀ ∪ Z₁)
    append!(cands, residual_strict(s, m + Sequent{𝔹}(Z, Z)))
  end
  unique!(cands)
  Sequent{𝔹}[t for t in cands if !any(t′ != t && refl_leq(t′, t) for t′ in cands)]
end

""" The terms occurring in `s`, on either side """
terms(s::Sequent)::Set{Term} = Set{Term}(keys(s.prem)) ∪ Set{Term}(keys(s.conc))

"""
The residual `{s} ⊸ C = {t | s + t ∈ C}` of a constructible triple by a single
element `s ∈ M`, as a constructible triple over `C.context ∪ supp(s)`
(`lemma:reflresidual`). Writing `C = ⟨κ, μ, λ⟩`, the residual is `⟨κ′, μ′, λ′⟩`
with

    κ′ = ⋃_{k ∈ κ} {s} ⊸ {k}          (`residual_strict`)
    μ′ = ⋃_{m ∈ μ} gens({s} ⊸ ℛ(m))    (`residual_refl`)
    λ′ = {l ∸ s | l ∈ λ}

each read off generator by generator; with `ℕ` coefficients the first two are
`{k - s | k ≽ s}` and `{m + (s ∸ m)^ - s}`. That this is legitimate rests on
`supp(s) ⊆ Δ`: then every `π ∈ G_Δ` fixes `s`, so `{s} ⊸` commutes with the
action and passes through orbits to their generators. When `C` is given at a
smaller context (e.g. the equivariant, `∅`-supported incompatibility set of a
frame) it is first re-presented over `C.context ∪ supp(s)` by `enlarge_context`.

Why the `λ′` clause: `s + t ≽ l  iff  t ≽ l ∸ s`, so `{s} ⊸ 𝒲(l) = 𝒲(l ∸ s)`.

The generators are returned canonicalized at the result's context. No
normalization beyond that is attempted: a `κ′` generator may well lie in
`ℛ(μ′) ∪ 𝒲(λ′)`, and a `μ′` generator in `𝒲(λ′)`; see `prune` in `Residual.jl`.
"""
function residual(s::Sequent{K}, C::Constructible{K})::Constructible{K} where K
  C = enlarge_context(C, s.supp)
  κ′ = Sequent{K}[t for k in C.strict for t in residual_strict(s, k)]
  μ′ = Sequent{K}[t for m in C.refl for t in residual_refl(s, m)]
  λ′ = C.weak ∸ s
  Constructible{K}(κ′, μ′, λ′, C.context)
end

# Infix notation
→ₒ(a,b) = residual(a, b)
