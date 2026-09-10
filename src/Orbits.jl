export Renaming, rename, orbit, canonicalize, same_orbit, fresh, injections, refine

using Combinatorics: permutations, combinations, powerset

# A term (or sequent) can represent many such terms in virtue of being acted
# upon by permutations of its names.

# Throughout, `frozen` ⊆ ℕ is a context Δ and the group acting is
# `G_frozen = {π ∈ Perm(ℕ) | π(a) = a ∀ a ∈ frozen}`. Because π is a bijection
# fixing `frozen` pointwise it restricts to a bijection of ℕ∖frozen: a name
# outside the context may go to *any* other name outside the context, and never
# to one inside it.

# Renamings
#----------

"""
An injection ℕ ↣ ℕ given by its action on a finite set of names, taken to be the
identity elsewhere. Every `π ∈ G_frozen` we need is determined by such a finite
restriction, so this is the only representation of the action.
"""
const Renaming = Dict{Int, Int}

rename(n::Int, ρ::Renaming) = get(ρ, n, n)

rename(t::Term, ρ::Renaming) = Term(pred(t), Int[rename(a, ρ) for a in args(t)])

rename(s::Set{Int}, ρ::Renaming) = Set{Int}(rename(n, ρ) for n in s)

rename(s::Set{Term}, ρ::Renaming) = Set{Term}(rename(t, ρ) for t in s)

"""
Renamings are injective, so distinct terms stay distinct and multiplicities
are preserved
"""
rename(d::MultiSet{Term}, ρ::Renaming)::MultiSet{Term} =
  MultiSet(Dict{Term, Int}(rename(t, ρ) => n for (t, n) in d))

rename(s::Sequent{K}, ρ::Renaming) where K = Sequent{K}(rename(s.prem, ρ), rename(s.conc, ρ))

""" The `n` least names not frozen """
function fresh(frozen, n::Int)::Vector{Int}
  res = Int[]
  i = 1
  while length(res) < n
    i ∈ frozen || push!(res, i)
    i += 1
  end
  res
end

"""
Every injection `dom ↣ cod`, as a `Renaming`: an ordered choice of `|dom|`
images out of `cod`. There are `|cod|!/(|cod|-|dom|)!` of them, and none at all
if `dom` is the larger.
"""
injections(dom::AbstractVector{Int}, cod::AbstractVector{Int})::Vector{Renaming} =
  [Renaming(zip(dom, image)) for image in permutations(cod, length(dom))]

# Orbits
#-------

"""
All the terms in the orbit of a term under some frozen set of names, i.e.
`G_frozen • t`.

That orbit is **infinite** as soon as `t` mentions a name outside `frozen`,
since such a name may go to any of the infinitely many non-frozen names (e.g.
`Q(1,2)` frozen at `{1}` has orbit `{Q(1,α) | α ≠ 1}`, the `Q⁻_{a=}` of the
paper). So we enumerate only the part of the orbit whose names are drawn from
the finite pool `names`; `frozen` is always in play, but its elements are never
available as *images* of the moving names.

The default pool is the names already occurring in `t`, giving the part of the
orbit that introduces nothing new.
"""
orbit(t::Term, frozen::Set{Int}, names=Set{Int}(args(t)))::Set{Term} =
  Set{Term}(rename(t, ρ) for ρ in orbit_renamings(Set(args(t)), frozen, names))

""" All the sequents in `G_frozen • s`, under the same caveats as for `Term` """
orbit(s::Sequent{K}, frozen::Set{Int}, names=s.supp) where K =
  Set{Sequent{K}}(rename(s, ρ) for ρ in orbit_renamings(s.supp, frozen, names))

"""
The renamings realizing the part of an orbit supported by `frozen ∪ names`: the
moving names (those of `supp` outside `frozen`) go injectively to the non-frozen
names of the pool.
"""
orbit_renamings(supp::Set{Int}, frozen::Set{Int}, names::Set{Int}) =
  injections(sort(collect(setdiff(supp, frozen))),
             sort(collect(setdiff(names, frozen))))

# Finite representatives of an orbit
#-----------------------------------

# An orbit `G_Γ • g` is infinite, but relative to a finite set of names `Δ` it
# has only finitely many *kinds* of element: two elements that agree on how
# their moving names meet `Δ` differ by a permutation fixing `Γ ∪ Δ`. `refine`
# lists one representative per kind. That is all that is ever needed of an
# orbit: as the generators of `G_Γ • g` over the larger context `Γ + Δ`
# (`enlarge_context`), as the elements to test one by one (`orbit_subset`), or as
# the `l′` to combine with a fixed `l` whose names are `Δ` — the joins `l ∨ l′`
# of `lemma:tripleintersectbin` and the sums of the Minkowski product — since the
# result is canonicalized at `Γ` afterwards and a permutation fixing `Γ ∪ supp(l)`
# fixes `l`.

"""
The generators `α g` of `G_Γ • g` as a subobject over `Γ + Δ` (with `Δ ∩ Γ = ∅`),
one for each partial injection `α : supp(g) ∖ Γ ⇀ Δ`.
Here `α g := π_α g` where `π_α` applies `α` where it is defined and sends every
other moving name to a fresh name outside `Γ ∪ Δ ∪ supp(g)`; the choice of
fresh names does not affect the orbit `G_{Γ+Δ} • α g`.

Distinct `α` may still yield the same orbit when `g` has a symmetry
(`P(2) + P(3)` with `2` sent into `Δ`, or with `3`).
"""
function refine(g::Sequent{K}, Γ::Set{Int}, Δ::Set{Int})::Vector{Sequent{K}} where K
  isdisjoint(Γ, Δ) || error("Context $Γ and new names $Δ must be disjoint")
  moving = sort(collect(setdiff(g.supp, Γ)))
  F = fresh(Γ ∪ Δ ∪ g.supp, length(moving))
  Δs = sort(collect(Δ))
  [rename(g, merge(α, Renaming(zip(setdiff(moving, keys(α)), F))))
   for k in 0:min(length(moving), length(Δs)) for dom in combinations(moving, k)
   for α in injections(dom, Δs)]
end

"""
The representatives of every `G_Γ • g`, `g ∈ gens`, relative to the names `N` of
some fixed element they are to be combined with; `N` may include names of `Γ`,
which are not new.
"""
refine(gens::Set{Sequent{K}}, Γ::Set{Int}, N::Set{Int}) where K =
  Iterators.flatten(refine(g, Γ, setdiff(N, Γ)) for g in gens)

# Canonicalization
#-----------------

# `canonicalize` picks the least element of an orbit, so it is a *complete*
# invariant of the orbit: two elements are `same_orbit` iff their canonical
# forms agree. That is what makes `κ`-membership (`lemma:matching`) decidable
# without enumerating anything.
#
# It is built greedily: read the names off in a canonical order and hand each
# new one the least name still available. A name read earlier dominates the
# ordering, so there is never anything to reconsider.

"""
The renaming sending each name of `ns` — in order of first appearance, and
extending `ρ` — to the least name that is neither frozen nor already in use.
"""
function canonical_renaming(ns::AbstractVector{Int}, frozen::Set{Int},
                            ρ::Renaming=Renaming())::Renaming
  ρ = copy(ρ)
  for n in ns
    if n ∉ frozen && !haskey(ρ, n)
      ρ[n] = only(fresh(frozen ∪ Set(values(ρ)), 1))
    end
  end
  ρ
end

"""
The lexicographically smallest term given a term being acted by permutations
fixing some set. A term's arguments are distinct and already ordered, so a
single greedy pass along them is the whole story.
"""
canonicalize(t::Term, frozen::Set{Int})::Term =
  rename(t, canonical_renaming(args(t), frozen))

"""
The least sequent in `G_frozen • s`.

Why one symbol at a time settles it: `isless` on sequents compares
`sorted` of each side, and that sorts terms by predicate symbol first. So
the comparison is decided symbol by symbol, premises before conclusions — which
is the order `groups` reads them in. A renaming beaten on an earlier symbol can
never be redeemed by a later one, so it is discarded as soon as that symbol has
been read.

Why ties survive: the terms sharing one symbol have no canonical order among
themselves, so each `arrangement` of them is tried. Two arrangements may
`render` a group identically while assigning different names — `Q(1,2) + Q(3,4)`
renders as itself either way, but maps `1 ↦ 1` one way and `3 ↦ 1` the other —
and only a later symbol tells them apart. Discarding either one at the Q group
would be wrong, so both go forward.
"""
function canonicalize(s::Sequent{K}, frozen::Set{Int})::Sequent{K} where K
  # Invariant: `candidates` holds every renaming still tied for least on the
  # symbols read so far. It starts as the one renaming that has decided nothing.
  candidates = [Renaming()]
  for group in groups(s)
    branched = unique(ρ′ for ρ in candidates
                         for ρ′ in extensions(ρ, group, frozen))
    candidates = least_by(ρ -> render(group, ρ), branched)
  end
  # Survivors render every group alike, so they all give the same sequent.
  @assert allequal(rename(s, ρ) for ρ in candidates) "Tied renamings disagree"
  rename(s, first(candidates))
end

"""
A sequent's terms in the order the comparison reads them: premises then
conclusions, each split into the groups that share a predicate symbol, ordered
by that symbol.
"""
groups(s::Sequent)::Vector{MultiSet{Term}} = [bysymbol(s.prem); bysymbol(s.conc)]

"""
Partition a multiset by its predicate symbol.
E.g. `P(1) + Q(1,2) + Q(3,4)` splits as `[{P(1)}, {Q(1,2), Q(3,4)}]`.
"""
function bysymbol(d::MultiSet{Term})::Vector{MultiSet{Term}}
  gs = DefaultDict{Predicate, MultiSet{Term}}(() -> MultiSet{Term}())
  for (t, n) in d
    gs[pred(t)][t] = n
  end
  [gs[p] for p in sort(collect(keys(gs)))]
end

"""
Every way of extending `ρ` to name the terms of `group`: one per arrangement of
the group, reading each arrangement's arguments left to right. A group holding a
single term — the usual case — yields exactly one extension.
"""
extensions(ρ::Renaming, group::MultiSet{Term}, frozen::Set{Int})::Vector{Renaming} =
  [canonical_renaming(Int[a for t in ts for a in args(t)], frozen, ρ)
   for ts in permutations(collect(keys(group)))]

""" How `group` looks under `ρ`: its contribution to `isless` on the sequent """
render(group::MultiSet{Term}, ρ::Renaming) = sorted(rename(group, ρ))

""" Those elements of `xs` tied for the least `f`; as many as are tied """
function least_by(f, xs::AbstractVector)
  vs = map(f, xs)
  [x for (v, x) in zip(vs, xs) if v == minimum(vs)]
end

"""
Are two elements in the same `G_frozen`-orbit? Decided by comparing canonical
forms rather than by enumerating an (infinite) orbit.
"""
same_orbit(x::T, y::T, frozen::Set{Int}) where T <: Union{Term, Sequent} =
  canonicalize(x, frozen) == canonicalize(y, frozen)
