export covers,  top_residual, normal_form, contained

# The normal form of a constructible subobject `S`:
#
#     κ_nf := S ∖ (R ⊸ S)
#     μ_nf := Min_{≤ℛ}(R ⊸ S) ∖ (⊤ ⊸ S)
#     λ_nf := Min_≤(⊤ ⊸ S)
#
# As much as possible goes into `𝒲`, then into `ℛ`, and only what remains is
# listed explicitly. It depends on `S` alone, so it decides equality of
# presentations, and it is what `residual(A, C)` needs of its right-hand
# argument. Unlike everything before it, it depends on the
# signature: `⊤ = M` is the set of *all* sequents, so which elements can be
# added to a given one — and hence which up-sets lie inside `S` — is a question
# about `X`, not just about the generators of `S`.

# Atoms
#------

maxsize(gens::Set{<:Sequent})::Int = maximum(length, gens; init=0)

# Covering tests
#---------------

# Both tests ask whether the *complement* of `𝒲(λ′)`, a down-set `D`, lies in
# `κ′ ∪ ℛ(μ′)` — on all of `M`, or on `R`. The lemma says an element avoiding
# `E` can be shrunk to one of size at most `B₂ := β + 2s_κ′ + 2` (β the largest
# imbalance in `μ′`), staying reflexive if it was. So it suffices to walk `D`
# breadth-first from `0`, adding an atom (or, for `R`, a balanced pair) at a
# time up to `G_Δ`, and stopping at size `B₂`: `D` is down-closed, so every
# element of `D ∩ R` (resp. `D`) of that size is reached from `0` this way.
# The walk fails on the first element outside `κ′ ∪ ℛ(μ′)`.
#
# With `𝔹` coefficients the same walk (which never repeats an atom, as
# `u + x = u` for `x ≼ u`) and the same bound serve, though a smaller one
# would do: an avoiding `t` may lose a balanced pair, `t - x⁺x⁻ ∈ ℛ(πm)` would
# put `t` there too, or an unbalanced atom while more than `β + 1` remain, since
# then `t ∈ ℛ(πm)` would need every one of them inside `πm`; so
# `max(β + 1, s_κ′ + 2)` suffices, as does `s_κ′ + 2` for ({\bf ii}).

"""
Is `E = κ′ ∪ ℛ(μ′) ∪ 𝒲(λ′)` all of `M` (`lemma:covertest` i)? With
`reflexive = true`, does it contain `R` (`lemma:covertest` ii)? These decide
`𝒲(z) ⊆ C` and `ℛ(z) ⊆ C` as `covers({z} ⊸ C)` and `covers({z} ⊸ C; reflexive = true)`.
"""
function covers(E::Constructible{K}, Σ::Signature; reflexive::Bool=false)::Bool where K
  Δ = E.context
  β = maximum(m -> sum(abs, values(imbalance(m)); init=0), E.refl; init=0)
  bound = β + 2 * maxsize(E.strict) + 2
  # Quick failure: a stack of `max(s_κ′, β) + 1` copies of an atom is too
  # big for κ′ and too unbalanced for ℛ(μ′), so it had better be in 𝒲(λ′).
  if !reflexive
    n = max(maxsize(E.strict), β) + 1
    for x in atoms(K, Σ, Δ)
      u = stack(x, n, Δ)
      isnothing(u) || in_weak(u, E.weak, Δ) || return false
    end
  end
  step = reflexive ? 2 : 1
  seen = Set{Sequent{K}}([zero(Sequent{K})])
  queue = [zero(Sequent{K})]
  while !isempty(queue)
    u = popfirst!(queue)
    in_weak(u, E.weak, Δ) && continue                 # u ∉ D
    in_strict(u, E.strict, Δ) || in_refl(u, E.refl, Δ) || return false
    length(u) + step ≤ bound || continue
    for x in (reflexive ? balanced_pairs(K, Σ, Δ ∪ u.supp) : atoms(K, Σ, Δ ∪ u.supp))
      u′ = canonicalize(u + x, Δ)
      u′ ∈ seen && continue
      push!(seen, u′)
      push!(queue, u′)
    end
  end
  true
end

"""
An element of size `n` with `n` unbalanced signed claimables, built on the atom
`x`: with `ℕ` coefficients `n` copies of `x`; with `𝔹` coefficients, where
nothing stacks, `n` instances of the same signed predicate at pairwise disjoint
fresh names outside `Δ`, or `nothing` for a nullary predicate.
"""
stack(x::Sequent{ℕ}, n::Int, ::Set{Int}) = sum(fill(x, n); init=zero(Sequent{ℕ}))
function stack(x::Sequent{𝔹}, n::Int, Δ::Set{Int})
  t = only(terms(x))
  k = pred(t).arity
  k == 0 && return nothing
  names = fresh(Δ, n * k)
  ts = [Term(pred(t), names[(i-1)*k+1:i*k]) for i in 1:n]
  isempty(x.prem) ? Sequent{𝔹}([], ts) : Sequent{𝔹}(ts, [])
end

"""
Is `S ⊆ T`, for two presentations over any contexts? Generator by generator
(`T` first re-presented over the union of the contexts): `k ∈ T`, and
`𝒲(l) ⊆ T` resp. `ℛ(m) ⊆ T` by the covering tests. Together with its converse
this decides equality of the presented subobjects without normal forms.
"""
function contained(S::Constructible{K}, T::Constructible{K}, Σ::Signature)::Bool where K
  Δ = S.context ∪ T.context
  S, T = enlarge_context(S, Δ), enlarge_context(T, Δ)
  all(k ∈ T for k in S.strict) &&
    all(covers(residual(l, T), Σ) for l in S.weak) &&
    all(covers(residual(m, T), Σ; reflexive=true) for m in S.refl)
end

# The absorption ⊤ ⊸ S
#--------------------

# `⊤ ⊸ S = {t | 𝒲(t) ⊆ S}` is the largest up-set inside `S`, i.e. the greatest
# fixpoint of `X ↦ {t ∈ S | t + x ∈ X for every atom x}`. Writing the atoms up
# to `G_Γ` as orbits `G_Γ • x`, one step is
#
#     X ↦ S ∩ ⋂_x (G_Γ • x) ⊸ X  =  S ∩ ⋂_x ⋂_{π ∈ G_Γ} π({x} ⊸ X),
#
# a singleton residual and an orbit intersection per atom orbit. Iterating from
# `X₀ = S` gives `Xₙ = {t | t + u ∈ S for all |u| ≤ n}`, and by
# `lemma:boundedobligation` (for the `ℛ` part) and `lemma:covertest` applied to
# `{z} ⊸ S` (for the `κ` part) this is already `⊤ ⊸ S` once
# `n ≥ max(2s_μ + 2s_κ + 2, s_μ + 3s_κ + 2)`; the `𝒲` part is in every `Xₙ`.
# (With `𝔹` coefficients an obligation `t + u ∉ S` shrinks to `|u| ≤ max(β + 1,
# s_κ + 2)`, `β` the largest imbalance in `μ`, by the argument for the covering
# test: drop from `u` its terms already in `t`, its balanced pairs, and the
# atoms whose mate lies in `t`, none of which can put `t + u` into `ℛ(μ)` — so
# the same bound is safe.) Usually it stabilizes far sooner, which is detected
# generator by generator: `Xₙ₊₁ ⊆ Xₙ` always, and `Xₙ ⊆ Xₙ₊₁` iff each `κ`
# generator is in `Xₙ₊₁` and each `ℛ` generator `m` has `ℛ(m) ⊆ Xₙ₊₁` — the `𝒲`
# generators come along automatically, `𝒲(l) + x ⊆ 𝒲(l)`.

"""
The absorption `⊤ ⊸ S = {t | 𝒲(t) ⊆ S}` of a constructible triple, as a
constructible triple over the same context. This iterates the one-atom
obligation to its fixpoint.
"""
function top_residual(S::Constructible{K}, Σ::Signature)::Constructible{K} where K
  Γ = S.context
  S = prune(S)
  xs = unique(canonicalize(x, Γ) for x in atoms(K, Σ, Γ))
  s_κ, s_μ = maxsize(S.strict), maxsize(S.refl)
  X = S
  for _ in 1:max(2s_μ + 2s_κ + 2, s_μ + 3s_κ + 2)
    X′ = S
    for x in xs
      X′ = X′ ∩ orbit_intersection(residual(x, X), Γ)
    end
    if all(k ∈ X′ for k in X.strict) &&
       all(covers(residual(m, X′), Σ; reflexive=true) for m in X.refl)
      return X′
    end
    X = X′
  end
  X
end

# The normal form
#----------------

"""
The normal form `⟨κ_nf, μ_nf, λ_nf⟩` of the subobject presented by `S`:
the unique presentation with as much as possible in the
`𝒲` part, then the `ℛ` part. Two presentations of one subobject have equal
normal forms, and `residual(A, C)` requires its right argument in this form.

Each component is filtered out of a finite candidate list by decidable tests:
- `κ_nf = S ∖ (R ⊸ S)`: the generators `k` of `κ` with `ℛ(k) ⊄ S`;
- `μ_nf`: those `g` among the generators of `μ` and `κ` with `ℛ(g) ⊆ S`,
  `𝒲(g) ⊄ S`, and nothing one `≤_ℛ`-step below `g` (`refl_predecessors`)
  keeping `ℛ(g) ⊆ S` (`R ⊸ S` absorbs `R`, so single steps suffice for
  `≤ℛ`-minimality);
- `λ_nf`: the generators of a presentation of `⊤ ⊸ S` from which no atom can be
  removed staying inside `⊤ ⊸ S` (it is an up-set, so single atoms suffice).
"""
function normal_form(S::Constructible{K}, Σ::Signature)::Constructible{K} where K
  Γ = S.context
  S = prune(S)
  A = top_residual(S, Σ)
  in_R(g) = covers(residual(g, S), Σ; reflexive=true)   # ℛ(g) ⊆ S, i.e. g ∈ R ⊸ S
  canon(gens) = Set{Sequent{K}}(canonicalize(g, Γ) for g in gens)
  κ = canon(k for k in S.strict if !in_R(k))
  μ = canon(g for g in S.refl ∪ S.strict
            if in_R(g) && g ∉ A && !any(in_R(g′) for g′ in refl_predecessors(g)))
  λ = canon(g for g in A.strict ∪ A.refl ∪ A.weak
            if !any((g - x) ∈ A for x in atoms(g)))
  Constructible{K}(κ, μ, λ, Γ; canonical=true)
end

""" `A ⊸ C` for an equivariant `C` given by any presentation, normalizing it first """
(residual(A::Constructible{K}, C::Constructible{K}, Σ::Signature)::Constructible{K}) where K =
  residual(A, normal_form(C, Σ))
