export Constructible, κ, ℛ, 𝒲, top, bottom

"""
A subobject κ ∪ ℛ(μ) ∪ 𝒲(λ) of `M = K[Σ]²` (where K = 𝔹 or ℕ)

Here the context can be smaller than the contexts of the sequents. It
represents the context Δ of A↣δ^Δ(K[Σ]²), i.e. an element of 𝒫(K[Σ]²) supported
by Δ. The underlying Σ is not part of the data of this struct.

So P(4)⊢Q(2,3) in context {1,2} is implicitly {P(4)⊢Q(2,3), P(4)⊢Q(3,2), 
                                               P(4)⊢Q(3,4)}

Invariant: generators are stored in canonical form at `context`, so that `κ`
membership is a lookup (see `in_strict`) and equal orbits never appear twice.
The constructor enforces this; anything changing the context must rebuild.
Callers that have just canonicalized at `context` themselves, or that pass
subsets of an existing triple's generators at the same context, may say so with
`canonical=true` to skip the (comparatively expensive) second pass.
"""
@struct_hash_equal struct Constructible{K<:Multiplicity}
  strict::Set{Sequent{K}}
  refl::Set{Sequent{K}}
  weak::Set{Sequent{K}}
  context::Set{Int}
  function Constructible{K}(strict::Set{Sequent{K}}, refl::Set{Sequent{K}},
                            weak::Set{Sequent{K}}, context::Set{Int};
                            canonical::Bool=false) where K<:Multiplicity
    canonical && return new{K}(strict, refl, weak, context)
    canon(gens) = Set{Sequent{K}}(canonicalize(g, context) for g in gens)
    new{K}(canon(strict), canon(refl), canon(weak), context)
  end
end

Constructible(strict::Set{Sequent{K}}, refl::Set{Sequent{K}}, 
              weak::Set{Sequent{K}}, context::Set{Int}; kw...) where K =
  Constructible{K}(strict, refl, weak, context; kw...)

const SV = Union{AbstractSet,AbstractVector}

# For user-friendliness, accept either Sequents or Exprs
to_sequent(::Type{K}, s::Sequent{K}) where K = s
to_sequent(::Type{K}, e::Expr) where K = Sequent{K}(e)

"""
The multiplicity type of the sequents among the generators; the default (`default_multiplicity`) if none of the
generators is a sequent (e.g. all are bare expressions).
"""
function multiplicity(gens::SV...)
  Ks = unique(multiplicity(g) for g in Iterators.flatten(gens) if g isa Sequent)
  length(Ks) ≤ 1 || error("Generators with different multiplicities: $Ks")
  isempty(Ks) ? default_multiplicity() : only(Ks)
end

""" 
Build from generators given as sequents or expressions, in any collections 
"""
Constructible{K}(s::SV, r::SV, w::SV, c::SV=Int[]) where K =
  Constructible{K}(Set{Sequent{K}}(to_sequent(K, x) for x in s),
                   Set{Sequent{K}}(to_sequent(K, x) for x in r),
                   Set{Sequent{K}}(to_sequent(K, x) for x in w), Set{Int}(c))

Constructible(s::SV, r::SV, w::SV, c::SV=Int[]) = 
  Constructible{multiplicity(s, r, w)}(s, r, w, c)

# Build a triple from just one of the components
κ(strict::SV, context::SV=Int[]) = Constructible(strict, [], [], context)
ℛ(refl::SV, context::SV=Int[]) = Constructible([], refl, [], context)
𝒲(weak::SV, context::SV=Int[]) = Constructible([], [], weak, context)

κ(expr::Union{Expr,Sequent}, context::SV=Int[]) = κ([expr], context)
ℛ(expr::Union{Expr,Sequent}, context::SV=Int[]) = ℛ([expr], context)
𝒲(expr::Union{Expr,Sequent}, context::SV=Int[]) = 𝒲([expr], context)



# Project out one of the components
κ(c::Constructible{K}) where K = 
  Constructible{K}(c.strict, Set{Sequent{K}}(), Set{Sequent{K}}(), c.context; 
                   canonical=true)

ℛ(c::Constructible{K}) where K = 
  Constructible{K}(Set{Sequent{K}}(), c.refl, Set{Sequent{K}}(), c.context; 
                   canonical=true)

𝒲(c::Constructible{K}) where K = 
  Constructible{K}(Set{Sequent{K}}(), Set{Sequent{K}}(), c.weak, c.context; 
                   canonical=true)

# Visualization of power elems
#-----------------------------

"""
Rendering as `κ{…} ∪ ℛ{…} ∪ 𝒲{…} @ {names}`, omitting empty parts (`∅` if all
are), with generators in their `isless` order.
"""
function Base.show(io::IO, ::MIME"text/plain", C::Constructible)
  gens(xs) = "{" * join(sprint.(show, sort(collect(xs))), ", ") * "}"
  parts = String[]
  isempty(C.strict) || push!(parts, "κ" * gens(C.strict))
  isempty(C.refl) || push!(parts, "ℛ" * gens(C.refl))
  isempty(C.weak) || push!(parts, "𝒲" * gens(C.weak))
  print(io, isempty(parts) ? "∅" : join(parts, " ∪ "))
  isempty(C.context) || 
    print(io, " @ {", join(sort(collect(C.context)), ","), "}")
end

Base.show(io::IO, C::Constructible) = show(io, "text/plain", C)


""" The presentation of `⊤ = M` itself: `𝒲(0)`, everything dominates `0` """
top(::Type{K}, Δ::Set{Int}) where K =
  Constructible{K}(Set{Sequent{K}}(), Set{Sequent{K}}(), 
                   Set{Sequent{K}}([zero(Sequent{K})]), Δ)

top(Δ::Set{Int}) = top(default_multiplicity(), Δ)

""" The presentation of `⊥ = ∅` """
bottom(::Type{K}, Δ::Set{Int}) where K =
  Constructible{K}(Set{Sequent{K}}(), Set{Sequent{K}}(), Set{Sequent{K}}(), Δ)

bottom(Δ::Set{Int}) = bottom(default_multiplicity(), Δ)

Base.zero(::Type{Constructible{K}}) where K = bottom(K, Set{Int}())
Base.zero(::Type{Constructible}) = zero(Constructible{default_multiplicity()})

# Between the multiplicities
#---------------------------

"""
The image `q(C)` under the support map `q : ℕ[X]² → 𝔹[X]²`, generator by
generator: `q({k}) = {q(k)}`, `q(ℛ(m)) = ℛ(q(m))` and `q(𝒲(l)) = 𝒲(q(l))`, as
`q` is a surjective monoid map with `q(R) = R` and `q(M) = M`, and it commutes
with renaming. So this presents the image of the subobject `C` presents.
"""
Constructible{𝔹}(C::Constructible{ℕ}) =
  Constructible{𝔹}(Sequent{𝔹}.(collect(C.strict)), Sequent{𝔹}.(collect(C.refl)),
                   Sequent{𝔹}.(collect(C.weak)), C.context)

# Deciding membership
#--------------------

"""
Per predicate symbol, how many terms of `d` (with multiplicity) use it.
This is a coarsening which forgets the arguments to a term
"""
function profile(d::MultiSet{Term})::MultiSet{Predicate}
  res = MultiSet{Predicate}()
  for (t, n) in d
    res[pred(t)] = get(res, pred(t), 0) + n
  end
  res
end

""" Could some element of `G_Δ • g` lie below `t`? A necessary condition """
fits(g::Sequent, t::Sequent, Δ::Set{Int})::Bool =
  length(g) ≤ length(t) && (g.supp ∩ Δ) ⊆ t.supp &&
  (profile(g.prem) ≼ profile(t.prem)) && (profile(g.conc) ≼ profile(t.conc))

"""
The renamings `ρ ∈ G_Δ` (given on the moving names of `g`) with `ρg ≼ t`: the
ways `g` embeds into `t`. Found by matching the terms of `g` one at a time to
terms of `t` with the same symbol and side and enough multiplicity left, while
extending `ρ` consistently — frozen names must match themselves, moving names go
injectively to non-frozen names of `t`.
"""
function embeddings(g::Sequent{K}, t::Sequent{K}, Δ::Set{Int}
                   )::Vector{Renaming} where K
  res = Renaming[]
  fits(g, t, Δ) || return res
  items = [[(x, n, :prem) for (x, n) in g.prem]; 
           [(x, n, :conc) for (x, n) in g.conc]]
  left = (prem=copy(t.prem), conc=copy(t.conc))
  function go(i::Int, ρ::Renaming)
    i > length(items) && return push!(res, copy(ρ))
    x, n, side = items[i]
    avail = getfield(left, side)
    for (y, m) in avail
      m ≥ n && pred(y) == pred(x) || continue
      ρ′ = extend(ρ, args(x), args(y), Δ)
      isnothing(ρ′) && continue
      avail[y] -= n
      go(i + 1, ρ′)
      avail[y] += n
    end
    res
  end
  go(1, Renaming())
end

"""
Extend `ρ` so that it sends the names `as` to `bs` pointwise, or `nothing` if
that conflicts with `ρ`, moves a frozen name, or breaks injectivity.
"""
function extend(ρ::Renaming, as::Vector{Int}, bs::Vector{Int}, Δ::Set{Int})
  ρ = copy(ρ)
  for (a, b) in zip(as, bs)
    if a ∈ Δ
      a == b || return nothing
    elseif haskey(ρ, a)
      ρ[a] == b || return nothing
    else
      (b ∉ Δ && b ∉ values(ρ)) || return nothing
      ρ[a] = b
    end
  end
  ρ
end

"""
Is `t ∈ κ`, for `κ` the union of the `G_Δ`-orbits of `gens`? Since `gens` are
canonical, this is orbit equality: a lookup of the canonical form of `t`.
"""
in_strict(t::Sequent{K}, gens::Set{Sequent{K}}, Δ::Set{Int}) where K =
  canonicalize(t, Δ) ∈ gens

""" 
Is `t ∈ 𝒲(λ)`, i.e. does `t` dominate some element of some orbit of `gens`? 
"""
in_weak(t::Sequent{K}, gens::Set{Sequent{K}}, Δ::Set{Int}) where K =
  any(!isempty(embeddings(l, t, Δ)) for l in gens)

"""
Is `t ∈ ℛ(μ)`? This is the previous search with the extra demand that the
witness `ρm` lie `≤_ℛ`-below `t` (`refl_leq`): what is left of `t` outside the
embedding is reflexive.
"""
function in_refl(t::Sequent{K}, gens::Set{Sequent{K}}, Δ::Set{Int}) where K
  any(gens) do m
    any(embeddings(m, t, Δ)) do ρ
      refl_leq(rename(m, ρ), t)
    end
  end
end

in_strict(t::Sequent{K}, c::Constructible{K}) where K = 
  in_strict(t, c.strict, c.context)

in_refl(t::Sequent{K}, c::Constructible{K}) where K = 
  in_refl(t, c.refl, c.context)

in_weak(t::Sequent{K}, c::Constructible{K}) where K = 
  in_weak(t, c.weak, c.context)

Base.in(t::Sequent{K}, C::Constructible{K}) where K =
  in_strict(t, C) || in_refl(t, C) || in_weak(t, C)


# Pruning
#---------

"""
Drop candidates dominating an element of another candidate's orbit. The
candidates are the generators of a `Constructible` at `Γ`, hence canonical, so
distinct candidates are distinct orbits and only strictly smaller ones need
checking for domination.
"""
function minimal_weak(cands::Set{Sequent{K}}, Γ::Set{Int}
                     )::Set{Sequent{K}} where K
  bysize = sort(collect(cands); by=length)
  Set{Sequent{K}}(l for (i, l) in enumerate(bysize)
                  if !in_weak(l, Set{Sequent{K}}(l′ for l′ in bysize[1:i-1]
                              if length(l′) < length(l)), Γ))
end

"""
Drop candidates `≤_ℛ`-dominating an element of another candidate's orbit, or
lying in `𝒲(L)`. Canonical candidates, as in `minimal_weak`.
"""
function minimal_refl(cands::Set{Sequent{K}}, L::Set{Sequent{K}}, Γ::Set{Int}
                     )::Set{Sequent{K}} where K
  bysize = sort(collect(cands); by=length)
  Set{Sequent{K}}(m for (i, m) in enumerate(bysize)
                  if !in_weak(m, L, Γ) &&
                     !in_refl(m, Set{Sequent{K}}(m′ for m′ in bysize[1:i-1]
                              if length(m′) < length(m)), Γ))
end


"""
The same subobject with redundant generators dropped: a `λ` generator above
another's orbit, a `μ` generator in `𝒲(λ)` or `≤_ℛ`-above another's orbit, and
a `κ` generator in `ℛ(μ) ∪ 𝒲(λ)`.
"""
function prune(C::Constructible{K})::Constructible{K} where K
  Δ = C.context
  λ = minimal_weak(C.weak, Δ)
  μ = minimal_refl(C.refl, λ, Δ)
  κ = Set{Sequent{K}}(k for k in C.strict 
                      if !in_weak(k, λ, Δ) && !in_refl(k, μ, Δ))
  Constructible{K}(κ, μ, λ, Δ; canonical=true)
end

# Binary intersection
#--------------------

"""
An element of 𝒫(X)(Γ) is also an element of 𝒫(X)(Γ ∪ Δ), at the price of more
generators. The orbit `G_Γ • g` splits into finitely many `G_{Γ+Δ}`-orbits, one
for each partial injection from the moving names of `g` into `Δ`.
"""
function enlarge_context(C::Constructible{K}, Δ::Set{Int}
                        )::Constructible{K} where K
  Γ = C.context
  new_names = setdiff(Δ, Γ)
  isempty(new_names) && return C
  ref(gens) = Sequent{K}[g′ for g in gens for g′ in refine(g, Γ, new_names)]
  Constructible{K}(ref(C.strict), ref(C.refl), ref(C.weak), Γ ∪ new_names)
end

"""
The intersection of two constructible triples over the union of their contexts.
The nine cells of the distributed intersection are:

- the five involving a `κ`: filter the generators of one `κ` by membership in
  the other triple (or in the relevant part of it);
- `ℛ(μ₁) ∩ ℛ(μ₂) = ℛ(refl_meet(m₁, m₂))`, one generator per pair or none
  (`refl_meet`: with `ℕ` coefficients `m₁ ∨ m₂` when `imb(m₁) = imb(m₂)`);
- `ℛ(μ) ∩ 𝒲(λ) = ℛ(m + (l ∸ m)^)`, the least element of `ℛ(m)` above `l`
  (`refl_above`);
- `𝒲(λ₁) ∩ 𝒲(λ₂) = 𝒲(l₁ ∨ l₂)`.

In the last three the pairs range over *elements* of the orbits, not just the
listed generators: one representative per kind of overlap with the fixed
generator's names, which is what `refine` supplies.
"""
function Base.intersect(A::Constructible{K}, B::Constructible{K}
                       )::Constructible{K} where K
  Δ = A.context ∪ B.context
  A, B = enlarge_context(A, Δ), enlarge_context(B, Δ)
  canon(gens) = Set{Sequent{K}}(canonicalize(g, Δ) for g in gens)
  κ = canon(Iterators.flatten((
        (k for k in A.strict if k ∈ B),
        (k for k in B.strict if in_refl(k, A.refl, Δ) || in_weak(k, A.weak, Δ)))))
  μ = canon(Iterators.flatten((
        (g for g in (refl_meet(m, m′) for m in A.refl 
                                      for m′ in refine(B.refl, Δ, m.supp))
           if !isnothing(g)),
        (refl_above(m, l) for m in A.refl for l in refine(B.weak, Δ, m.supp)),
        (refl_above(m, l) for m in B.refl for l in refine(A.weak, Δ, m.supp)))))
  λ = canon(l ∨ l′ for l in A.weak for l′ in refine(B.weak, Δ, l.supp))
  prune(Constructible{K}(κ, μ, λ, Δ; canonical=true))
end
