export orbit_subset, orbit_intersection, prune

# The residual `A ⊸ C = {t | ∀a ∈ A: a + t ∈ C}` of a constructible `A`
# supported by a context Γ by an equivariant constructible `C`.
# Residuals turn unions into intersections, so decomposing `A` into the orbits
# of its generators reduces everything to
#
#     (G_Γ • g) ⊸ D  =  ⋂_{π ∈ G_Γ} π({g} ⊸ D),
#
# a singleton residual (`SingletonResidual.jl`) followed by an intersection
# over the whole group `G_Γ`. This file supplies the two intersections needed:
# the binary one and the orbit one, then assembles the residual.

# Orbits relative to a smaller context
#------------------------------------

"""
Is `G_Γ • t ⊆ C`, for `C` supported by a context containing `Γ`?
The orbit meets only finitely many `G_{C.context}`-orbits, one per partial
injection from the names of `t` outside `Γ` into `C.context ∖ Γ` (`refine`),
so this is a finite conjunction of memberships. It is `t ∈ ⋂_{π ∈ G_Γ} π C`
(i.e. `t ∈ ∀^Δ_Γ(C)` for `Δ := C.context ∖ Γ`).
"""
function orbit_subset(t::Sequent{K}, C::Constructible{K}, Γ::Set{Int})::Bool where K
  Γ ⊆ C.context || error("Context $Γ is not contained in $(C.context)")
  all(t′ ∈ C for t′ in refine(t, Γ, setdiff(C.context, Γ)))
end


# Orbit intersection
#-------------------

# `⋂_{π ∈ G_Γ} π C` for `C` supported by `Γ + Δ`: the elements `t` with
# `π t ∈ C` for every permutation `π` fixing `Γ` pointwise. We need to find
# representative generators of all elements of this intersection to get a
# presentation.
#
# The answer is supported by `Γ`, hence closed under renaming the names outside
# `Γ`, so it suffices to consider one `t` per orbit; take the one whose names
# outside `Γ` avoid `Δ` (there are always enough names to rename into). Given
# such a `t` and a generator `d₀ ∈ λ ∪ μ` with `d₀ ≤ t` (and `d₀ ≤_ℛ t`
# if `d₀ ∈ μ`), sort the permutations `π ∈ G_Γ` by where they send the names
# of `d₀` outside `Γ`:
#
# * If `π` sends none of them into `Δ`, then `π d₀` lies in the same
#  `G_{Γ+Δ}`-orbit as `d₀`, hence is again a generator,
#   and `π t ∈ 𝒲(λ) ∪ ℛ(μ)`. The single generator `d₀` handles all such `π`.
# * Otherwise `π` sends some name `a` of `d₀` to some `z ∈ Δ`. Fixing one
#   permutation `ρ_{az} ∈ G_Γ` with `a ↦ z`, every such `π` factors as
#   `σ ∘ ρ_{az}` with `σ ∈ G_{Γ+z}`. So all these `π t` lie in `𝒲(λ) ∪ ℛ(μ)`
#   iff the whole `G_{Γ+z}`-orbit of `ρ_{az} t` does: the same problem with
#   context `Γ + z` and the names `Δ ∖ z` left over.
#
# Hence `G_Γ • t ⊆ 𝒲(λ) ∪ ℛ(μ)` iff some `d₀ ≤ t` as above exists and, for each
# name `a` of `d₀` outside `Γ` and each `z ∈ Δ`, the element `ρ_{az} t` passes
# the test one context larger. Only names of `d₀` are involved: a `π` sending
# other names of `t` into `Δ` but none of `d₀`'s falls under the first case.
#
# Read as a recipe for generators: the problem at `Γ + z` is this very function
# one context up, `D_z := orbit_intersection(C, Γ + z)`, and `ρ_{az} t` passes
# iff it dominates a generator of `D_z.weak`, or `≤_ℛ`-dominates one of
# `D_z.refl`. Undoing `ρ_{az}`, `t` must dominate a copy of such a generator `p`
# with `z` renamed to `a` and the remaining names of `p` outside `Γ + z`
# renamed, injectively, to names already in `t` or to names used nowhere. A
# minimal `t` is therefore `d₀` joined with one such copy per pair `(a, z)`,
# over all choices of `p` and of renaming; `assemble` builds these joins and
# `placements` lists the renamings. Each reflexive piece `p` (a `d₀ ∈ μ`, or a
# piece from an `ℛ` part below) demands `t ∈ ℛ(p)`; these demands combine into
# one, `t ∈ ℛ(P)` with `P` the running `refl_meet` of the pieces (`ℛ(P) ∩ ℛ(p) =
# ℛ(refl_meet(P, p))`, empty with `ℕ` coefficients when the imbalances differ),
# and the join `w` is finally raised to `refl_above(P, w)`, the least element
# of `ℛ(P)` above it. Every `≤`-minimal element of the `𝒲` part and every
# `≤_ℛ`-minimal element of the `ℛ` part arises this way, and every candidate so
# built lies in the intersection, so the candidates present it.
#
# The two parts are computed together because the `ℛ` part genuinely depends on
# both `λ` and `μ`: the renamings of one `t` may land in `𝒲(λ)` for some `π` and
# in `ℛ(μ)` for others. The `𝒲` part depends on `λ` alone, and its search is the
# sub-tree of branches below that never pick a reflexive piece.

"""
The constructible triple supported by `Γ ⊆ C.context` presenting `⋂_{π ∈ G_Γ} π C`,
i.e. `{t | G_Γ • t ⊆ C}`. Its strict part is those generators of `κ` whose
`G_Γ`-orbit lies in `C`; its `𝒲` and `ℛ` parts are the witnesses described
above. When `Γ = C.context` nothing is intersected and `C` is returned as is.

Recursive on `Δ := C.context ∖ Γ`: `assemble` needs the same intersection at
each context `Γ + z`, so the results are cached in `memo` by context. Callers
pass only `C` and `Γ`.
"""
function orbit_intersection(C::Constructible{K}, Γ::Set{Int},
                            memo::Dict{Set{Int},Constructible{K}}
                             = Dict{Set{Int},Constructible{K}}()
                           )::Constructible{K} where K
  Γ ⊆ C.context || error("Context $Γ is not contained in $(C.context)")
  Γ == C.context && return C  # everything is already G_Γ-invariant
  haskey(memo, Γ) && return memo[Γ]
  Δ = setdiff(C.context, Γ)
  κ = Set{Sequent{K}}(k for k in C.strict if orbit_subset(k, C, Γ))
  W, R = Set{Sequent{K}}(), Set{Sequent{K}}()  # candidate 𝒲 and ℛ generators
  # Every 𝒲/ℛ gen of the answer lies above some d₀ ∈ λ ∪ μ: search above each.
  for (d₀, refl) in [[(l, false) for l in C.weak]; [(m, true) for m in C.refl]]
    isdisjoint(d₀.supp, Δ) || continue  # d₀ ≤ t and t avoids Δ, so d₀ does too
    # Names which a Γ-fixing π is allowed to move
    movable_names = sort(collect(setdiff(d₀.supp, Γ)))
    # All ways a Γ-fixing π can send a name of d₀ into Δ. These are the π not
    # handled by d₀ alone, so each pair is one req `assemble` must discharge.
    pairs = [(a, z) for a in movable_names for z in sort(collect(Δ))]
    P = refl ? d₀ : nothing
    for (w, P′) in assemble(d₀, P, pairs, C, Γ, memo)
      isnothing(P′) ? push!(W, w) : push!(R, refl_above(P′, w))
    end
  end
  memo[Γ] = prune(Constructible{K}(κ, R, W, Γ))  # canonicalizes and minimizes
end

"""
All ways of extending the partial witness `w` so that, for each remaining pair
`(a, z)` in `pairs`, the renamed element `ρ_{az} w` has its `G_{Γ+z}`-orbit
inside the target: one piece from the solution at `Γ + z` per pair. Returns
pairs `(w, P)` of the joined witness and the reflexive demand `t ∈ ℛ(P)` its
reflexive pieces impose on the element `t` finally generated (`nothing` if none
so far).

A pair the partial witness already satisfies gets no piece: if the element it
would currently generate (`w`, or `refl_above(P, w)` under a demand `P`)
already passes the test at `Γ + z` after renaming `a ↦ z`, so does anything the
remaining pairs add to it, and any candidate built by adding a piece here would
only be larger. This is what keeps the search small — an equivariant `C` needs
no pieces at all — and loses no minimal witness.
"""
function assemble(w::Sequent{K}, P::Union{Nothing,Sequent{K}}, pairs::Vector,
                  C::Constructible{K}, Γ::Set{Int}, 
                  memo::Dict{Set{Int},Constructible{K}}) where K
  isempty(pairs) && return [(w, P)]
  (a, z), rest = pairs[1], pairs[2:end]
  D_z = orbit_intersection(C, Γ ∪ Set([z]), memo)  # target after renaming a ↦ z
  u = isnothing(P) ? w : refl_above(P, w)
  ρu = rename(u, Renaming(a => z))
  if in_weak(ρu, D_z) || (!isnothing(P) && in_refl(ρu, D_z))
    return assemble(w, P, rest, C, Γ, memo)
  end
  res = Tuple{Sequent{K},Union{Nothing,Sequent{K}}}[]
  for (piece, refl) in [[(l, false) for l in D_z.weak]; [(m, true) for m in D_z.refl]]
    for p in placements(piece, a, z, w, Γ, C.context)
      P′ = P
      if refl
        P′ = isnothing(P) ? p : refl_meet(P, p)
        isnothing(P′) && continue  # the demands ℛ(P) and ℛ(p) cannot both be met
      end
      append!(res, assemble(w ∨ p, P′, rest, C, Γ, memo))
    end
  end
  res
end

"""
The ways of positioning a `piece` supported by `Γ + z` (a generator of the
solution there) back at `Γ` as something below an element `t ≥ w` whose renaming
`ρ_{az} t` lies above `piece`: rename `z` to `a`, and send the other names of
`piece` outside `Γ + z` injectively to names of `w` outside `Γ` other than
`a`, or to names used nowhere (outside `full` and `w`).
"""
function placements(piece::Sequent{K}, a::Int, z::Int, w::Sequent{K}, Γ::Set{Int},
                    full::Set{Int})::Vector{Sequent{K}} where K
  ctx = Γ ∪ Set([z])
  N = setdiff(w.supp, Γ ∪ Set([a]))
  k = length(setdiff(piece.supp, ctx))
  pool = ctx ∪ N ∪ Set{Int}(fresh(full ∪ w.supp, k))
  [rename(p, Renaming(z => a)) for p in orbit(piece, ctx, pool)]
end

# The general residual
#---------------------

"""
The residual `A ⊸ C = {t | ∀a ∈ A: a + t ∈ C}` as a constructible triple
supported by `A.context`. `C` must be equivariant
(context `∅`), as the incompatibility set of a frame is, and in normal form,
which lets the residuals by `𝒲`- and `ℛ`-generators curry into the two
absorptions of `C` read off from its presentation:

    𝒲(g) ⊸ C = {g} ⊸ (⊤ ⊸ C) = {g} ⊸ 𝒲(λ_C)
    ℛ(g) ⊸ C = {g} ⊸ (R ⊸ C) = {g} ⊸ (𝒲(λ_C) ∪ ℛ(μ_C))

Each generator `g` of `A` then contributes the factor `⋂_{π ∈ G_Γ} π({g} ⊸ D)`
for the appropriate `D`, computed by `residual` at the context `Γ ∪ supp(g)` and
`orbit_intersection` back down to `Γ`; the factors are combined by `intersect`.
With no generators `A = ∅` and the residual is `⊤`.

Membership in `A ⊸ C` could be decided directly, generator by generator via
`refine`; what this computes is a presentation.
"""
function residual(A::Constructible{K}, C::Constructible{K}
                 )::Constructible{K} where K
  isempty(C.context) || 
    error("The residuand must be equivariant, got context $(C.context)")
  Γ = A.context
  ∅ = Set{Sequent{K}}()
  W = Constructible{K}(∅, ∅, C.weak, C.context; canonical=true)        # ⊤ ⊸ C
  WR = Constructible{K}(∅, C.refl, C.weak, C.context; canonical=true)  # R ⊸ C
  factor(g, D) = orbit_intersection(enlarge_context(residual(g, D), Γ), Γ)
  # The factors are independent (each builds its own memo), so compute them on
  # separate tasks; the fold stays serial so `prune` runs between each step.
  jobs = [[(g, C) for g in A.strict]; [(g, W) for g in A.weak]; [(g, WR) for g in A.refl]]
  tasks = [Threads.@spawn factor(g, D) for (g, D) in jobs]
  res = top(K, Γ)
  for t in tasks; res = res ∩ fetch(t) end
  res
end
