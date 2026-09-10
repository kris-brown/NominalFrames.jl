export Predicate, Signature, Term, Sequent, refl_sequents, small_sequents, atoms

using DataStructures: DefaultDict

@struct_hash_equal struct Predicate
  name::Symbol
  arity::Int
  function Predicate(name::Symbol, arity::Int)
    @assert arity ≥ 0
    new(name, arity)
  end
end

function Base.isless(x::Predicate, y::Predicate)
  if x.name == y.name
    @assert x.arity == y.arity
    return false
  else
    return x.name ≤ y.name
  end
end

""" A set of predicates, indexed by arity and in some canonical order """
struct Signature
  predicates::Dict{Int, Vector{Predicate}}
  function Signature(predicates::Vector{Predicate})
    d = DefaultDict{Int,Vector{Predicate}}(()->Predicate[])
    for p in predicates
      push!(d[p.arity], p)
    end
    new(d)
  end
end

Base.length(s::Signature) = sum(length.(values(s.predicates)))
Base.iterate(s::Signature, x...) = iterate(collect(s), x...)
function Base.collect(s::Signature)
  res = []
  for (_, ps) in sort(collect(s.predicates))
    append!(res, ps)
  end
  res
end

@struct_hash_equal struct Term
  pred::Predicate
  args::Vector{Int}
  function Term(pred::Predicate, args::Vector{Int})
    @assert length(args) == pred.arity
    @assert allunique(args)
    new(pred, args)
  end
end

pred(t::Term) = t.pred
args(t::Term) = t.args

""" Order terms by predicate symbol, then by arguments """
Base.isless(x::Term, y::Term) =
  pred(x) == pred(y) ? isless(args(x), args(y)) : isless(pred(x), pred(y))

function Term(x::Expr)::Term
  x.head == :call || error("Bad term $x")
  x.args[1] isa Symbol || error("Bad head $x")
  all(==(Int), typeof.(x.args[2:end])) || error("Bad args $x: $(typeof.(x.args[2:end]))")
  Term(Predicate(x.args[1], length(x.args)-1), Vector{Int}(x.args[2:end]))
end


const subs = ["₁","₂","₃","₄","₅","₆","₇","₈","₉"]

function Base.show(io::IO, ::MIME"text/plain", t::Term)
  print(io, t.pred.name)
  for arg in args(t)
    print(io, subs[arg])
  end
end

""" Canonical term associated with predicate (in a canonical support) """
Term(p::Predicate) = Term(p, collect(1:p.arity))


"""
A position `s = (s⁺, s⁻) ∈ K[X]²`, written `s⁺ ⊢ s⁻`: a pair of formal sums of
terms with coefficients in the semiring `K` (`Semiring.jl`): multisets for
`K = ℕ`, sets for `K = 𝔹`. Both sides are stored as multisets; with `𝔹`
coefficients every multiplicity is `1`.

The support is *derived* data, not to be specified unless already known.
"""
@struct_hash_equal struct Sequent{K<:Semiring}
  prem::MultiSet{Term}
  conc::MultiSet{Term}
  supp::Set{Int} # this is derived data
  function Sequent{K}(prem::MultiSet{Term}, conc::MultiSet{Term}) where K<:Semiring
    check_side(K, prem)
    check_side(K, conc)
    # Seeded with an empty set so that the empty sequent `0` has support ∅
    supp = union(Set{Int}(), Set.(args.(keys(prem)))..., Set.(args.(keys(conc)))...)
    new{K}(prem, conc, supp)
  end
end

""" With no semiring named, multisets """
Sequent(prem::MultiSet{Term}, conc::MultiSet{Term}) = Sequent{ℕ}(prem, conc)

""" Any multiset is a side with `ℕ` coefficients; with `𝔹` coefficients, only sets """
check_side(::Type{ℕ}, ::MultiSet{Term}) = nothing
check_side(::Type{𝔹}, m::MultiSet{Term}) =
  all(==(1), values(m)) || error("A side with 𝔹 coefficients has no multiplicities: $m")

"""
The formal sum of a list of terms. With `𝔹` coefficients a repeated term counts
once: that is contraction.
"""
side(::Type{ℕ}, ts::AbstractVector) = MultiSet(Vector{Term}(ts))
side(::Type{𝔹}, ts::AbstractVector) = MultiSet(unique(Vector{Term}(ts)))

Sequent{K}(p::AbstractVector, c::AbstractVector) where K = Sequent{K}(side(K, p), side(K, c))
Sequent(p::AbstractVector, c::AbstractVector) = Sequent{ℕ}(p, c)
Sequent{K}() where K = Sequent{K}(Term[], Term[])
Sequent() = Sequent{ℕ}()

"""
The support `q(s)` of a multiset sequent: the terms occurring in it, each once,
as a sequent with `𝔹` coefficients. `q : ℕ[X]² → 𝔹[X]²` is a surjective
homomorphism of monoids commuting with the action on names.
"""
Sequent{𝔹}(s::Sequent{ℕ}) = Sequent{𝔹}(support(s.prem), support(s.conc))

"""
The multiset sequent with the same terms, each of multiplicity `1`: the
inclusion `ι` of sets into multisets, a section of `q` but not a monoid map
(`ι(x) + ι(x) ≠ ι(x + x)`).
"""
Sequent{ℕ}(s::Sequent{𝔹}) = Sequent{ℕ}(copy(s.prem), copy(s.conc))

Sequent{K}(s::Sequent{K}) where K = s

""" Ordering sequents (a total order, not the meaningful partial order) """
Base.isless(x::Sequent, y::Sequent) =
  isless((sorted(x.prem), sorted(x.conc)),
         (sorted(y.prem), sorted(y.conc)))

# `Sequent{K}` is a partially ordered monoid (≼,+,0)

""" The empty sequent `0`, unit of `+` """
Base.zero(::Type{Sequent{K}}) where K = Sequent{K}()
Base.zero(::Type{Sequent}) = zero(Sequent{ℕ})
Base.zero(s::Sequent) = zero(typeof(s))
Base.iszero(s::Sequent) = isempty(s.prem) && isempty(s.conc)

""" Size `|s|`: the total number of signed claimables, with multiplicity """
Base.length(s::Sequent)::Int = sum(values(s.prem); init=0) + sum(values(s.conc); init=0)

""" Meaningful (partial) ordering: being a sub-multiset on both sides """
≼(s::Sequent{K}, t::Sequent{K}) where K = ≼(s.prem, t.prem) && ≼(s.conc, t.conc)

""" Addition of sides: the sum of multisets with `ℕ` coefficients, the union with `𝔹` """
add(::Type{ℕ}, x::MultiSet{Term}, y::MultiSet{Term}) = x + y
add(::Type{𝔹}, x::MultiSet{Term}, y::MultiSet{Term}) = x ∨ y

""" Monoid operation of `M = K[X]²`: addition on each side """
Base.:(+)(x::Sequent{K}, y::Sequent{K}) where K =
  Sequent{K}(add(K, x.prem, y.prem), add(K, x.conc, y.conc))

"""
Partial subtraction `t - s`, defined only when `s ≼ t`: the least `u` with
`s + u = t`. With `ℕ` coefficients sequents form a cancellative monoid and this
`u` is the *unique* solution; with `𝔹` coefficients it is `t ∖ s`, and `s + u = t`
has the further solutions `u + v` for `v ≼ s ∧ t` (see `residual_strict`).
"""
function Base.:-(t::Sequent{K}, s::Sequent{K})::Sequent{K} where K
  s ≼ t || error("Subtraction undefined: $s ⋠ $t")
  Sequent{K}((t.prem ∸ s.prem), (t.conc ∸ s.conc))
end

"""
Truncated subtraction `t ∸ s`, i.e. `x ↦ max(0, t(x) - s(x))` at every signed
claimable `x`. Total, and equal to `t - s` when that is defined. Its
characteristic property: `u ≽ t ∸ s  iff  s + u ≽ t`.
"""
∸(t::Sequent{K}, s::Sequent{K}) where K =
  Sequent{K}(t.prem ∸ s.prem, t.conc ∸ s.conc)

∸(ts::Set{Sequent{K}}, s::Sequent{K}) where K = Set{Sequent{K}}(t ∸ s for t in ts)

""" Join in the pointwise order: `x ↦ max(s(x), t(x))` at every signed claimable """
∨(s::Sequent{K}, t::Sequent{K}) where K =
  Sequent{K}((s.prem ∨ t.prem), (s.conc ∨ t.conc))

""" Meet in the pointwise order: `x ↦ min(s(x), t(x))` at every signed claimable """
∧(s::Sequent{K}, t::Sequent{K}) where K =
  Sequent{K}((s.prem ∧ t.prem), (s.conc ∧ t.conc))

# Visualization

""" Add a suffix (used in visualization for ⁺ and ⁻) """
annotate(t::Term, s::String) = Term(annotate(t.pred, s), t.args)
annotate(p::Predicate, s::String) = Predicate(Symbol("$(p.name)$s"), p.arity)

"""
Compact rendering in the paper's notation: `P⁺₁Q⁻₁₂` for `P(1) ⊢ Q(1,2)`, with
a multiplicity prefix where needed and `0` for the empty sequent.
"""
function Base.show(io::IO, ::MIME"text/plain", s::Sequent)
  isempty(s.prem) && isempty(s.conc) && return print(io, "0")
  for (p, n) in sort(collect(s.prem))
    n == 1 || print(io, n)
    show(io, "text/plain", annotate(p, "⁺"))
  end
  for (c, n) in sort(collect(s.conc))
    n == 1 || print(io, n)
    show(io, "text/plain", annotate(c, "⁻"))
  end
end

Base.show(io::IO, s::Sequent) = show(io, "text/plain", s)

"""
Parse `A₁ + ... ⊢ B₁ + ...` into a sequent. Sides are written additively, with
`n*T` (or `nT`) for multiplicity and `0` for the empty side, e.g.
`Sequent(:(P(a) + 2Q(a,b) ⊢ 0))`. With `𝔹` coefficients multiplicities
collapse: `Sequent{𝔹}(:(2P(1) ⊢ 0)) == Sequent{𝔹}(:(P(1) ⊢ 0))`.
"""
function Sequent{K}(x::Expr) where K
  if x.head == :call && length(x.args) == 3 && x.args[1] == :⊢
    Sequent{K}(side_terms(x.args[2]), side_terms(x.args[3]))
  else
    Sequent{K}([], side_terms(x))
  end
end

Sequent(x::Expr) = Sequent{ℕ}(x)

""" The multiset of `Term`s denoted by one side of a sequent expression """
function side_terms(x)::Vector{Term}
  x == 0 && return Term[]
  x isa Symbol && return [Term(Predicate(x, 0), Int[])] # bare nullary predicate
  x isa Expr && x.head == :call || error("Cannot parse sequent side $x")
  op = x.args[1]
  op == :+ && return reduce(vcat, side_terms.(x.args[2:end]))
  op == :* && length(x.args) == 3 && x.args[2] isa Integer &&
    return repeat(side_terms(x.args[3]), x.args[2])
  [Term(x)]
end


# Generating sequents
#####################

""" The sequents `p(x⃗) ⊢ p(x⃗)`, one per predicate symbol """
refl_sequents(::Type{K}, Σ::Signature) where K =
  Sequent{K}[Sequent{K}([Term(p)], [Term(p)]) for p in Σ]

refl_sequents(Σ::Signature) = refl_sequents(ℕ, Σ)

""" Every sequent of size ≤ `n` whose names are drawn from `names` """
function small_sequents(::Type{K}, Σ::Signature, names::Vector{Int}, n::Int) where K
  terms = [Term(p, Int[ρ[i] for i in 1:p.arity])
           for p in Σ for ρ in NominalFrames.injections(collect(1:p.arity), names)]
  signed = [(t, side) for t in terms for side in (:prem, :conc)]
  res = Sequent{K}[]
  for k in 0:n, choice in Iterators.product(fill(signed, k)...)
    push!(res, Sequent{K}(Term[t for (t, side) in choice if side == :prem],
                          Term[t for (t, side) in choice if side == :conc]))
  end
  unique(res)
end

small_sequents(Σ::Signature, names::Vector{Int}, n::Int) = small_sequents(ℕ, Σ, names, n)

"""
The atoms of `M`: the sequents `x⁺` and `x⁻` with a single signed claimable,
over names drawn from `names` or fresh (as many fresh names as the arity, so
every pattern of overlap with `names` occurs). Every element of `M` is a sum of
atoms, and every up-set is closed under adding them.
"""
function atoms(::Type{K}, Σ::Signature, names::Set{Int}) where K
  res = Sequent{K}[]
  for p in Σ
    pool = sort(collect(names ∪ Set{Int}(fresh(names, p.arity))))
    for ρ in injections(collect(1:p.arity), pool)
      t = Term(p, Int[ρ[i] for i in 1:p.arity])
      push!(res, Sequent{K}([t], []), Sequent{K}([], [t]))
    end
  end
  res
end

atoms(Σ::Signature, names::Set{Int}) = atoms(ℕ, Σ, names)

""" The balanced pairs `x⁺ + x⁻`: the atoms of the reflexive submonoid `R` """
balanced_pairs(::Type{K}, Σ::Signature, names::Set{Int}) where K =
  Sequent{K}[Sequent{K}([t],[t]) for x in atoms(K, Σ, names) for t in keys(x.prem)]

balanced_pairs(Σ::Signature, names::Set{Int}) = balanced_pairs(ℕ, Σ, names)

""" The atoms below `s`, i.e. the signed claimables occurring in it """
atoms(s::Sequent{K}) where K =
  Sequent{K}[[Sequent{K}([t], []) for t in keys(s.prem)];
             [Sequent{K}([], [t]) for t in keys(s.conc)]]

""" The balanced pairs below `s` """
balanced_pairs(s::Sequent{K}) where K =
  Sequent{K}[Sequent{K}([t], [t]) for t in keys(s.prem) if haskey(s.conc, t)]
