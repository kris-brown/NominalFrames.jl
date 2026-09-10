export Role, RolePair, minkowski, unfreeze, perp, closure, tensor, par, vee,
       meet, lolli, forall, exists, zero_role, unit_role, top_role, entails,
       ∀, ∃, ⊗, ⊕, ⅋, ⇒, ¬, ∧, roles_equal, context, in_context, ⊩, ⊮

# Implication-space semantics over a nominal frame `(X, I)` (`sec:instant`).
#
# A *role* is a subobject of `M = K[X]²` at some context Γ, here always a
# `Constructible`. The frame's incompatibility set `I` (the point `⊥` of the
# pointed quantale `𝒫M`) residuates roles, `S^⊥ = S ⊸ I`, and the closed roles
# `S = S^⊥⊥` form the Girard quantale `𝒢`  with
#
#  S ⊠ T = (S ⊗ T)^⊥⊥        ¬S = S^⊥      S ∨ T = (S ∪ T)^⊥⊥    S ∧ T = S ∩ T
#
# where `⊗` is the Minkowski product `{s + t}`. A formula is interpreted as a
# *pair* of closed roles `⟨a₊, a₋⟩`, premisory and conclusory, an element of
# `X̂ = 𝒢²`, with the connectives of `tab:connectives`, the quantifiers of
# `sec:quantifiers`, and the consequence relation `⊨`:
# `A₁, …, Aₙ ⊨ B₁, …, Bₘ` iff `⨂ aᵢ₊ ⊗ ⨂ bⱼ₋ ⊆ I`.
#
# Closed roles are represented lazily (`Role`): as a presentation `S` standing
# for `S^⊥⊥`, the closure being computed only when something asks for it. This
# rests on `S ↦ S^⊥⊥` being a quantic nucleus, i.e. on the identities
#
#     (S^⊥⊥ ⊗ T^⊥⊥)^⊥⊥ = (S ⊗ T)^⊥⊥      (S^⊥⊥ ∪ T^⊥⊥)^⊥⊥ = (S ∪ T)^⊥⊥
#     (S^⊥⊥)^⊥ = S^⊥                      π(S^⊥⊥) = (πS)^⊥⊥ for π ∈ G_∅
#
# (the last as `I` is equivariant), and on `S ⊆ I  iff  S^⊥⊥ ⊆ I` since `I` is
# closed. So `⊠`, `∨`, `∃`, and `⊨` never residuate; only `¬`, `∧`, `∀`, and
# membership do.
#
# Nothing here depends on the coefficients `K` (`Semiring.jl`): the same code
# runs for multisets and for sets, the difference sitting in `+` and `residual`.

# Operations on presentations that need no frame
#-----------------------------------------------

"""
The Minkowski product `A ⊗ B = {a + b | a ∈ A, b ∈ B}` of two constructible
triples, over the union of their contexts. Distributing over the three parts,
`κ ⊗ κ` stays strict, anything meeting `𝒲` is `𝒲` (`⊤ ⊗ - = ⊤`), and the rest is
`ℛ` (`R ⊗ R = R`); the sums range over elements of the orbits, one generator
held fixed and the other's representatives (`refine`) relative to it.
"""
function minkowski(A::Constructible{K}, B::Constructible{K})::Constructible{K} where K
  Δ = A.context ∪ B.context
  A, B = enlarge_context(A, Δ), enlarge_context(B, Δ)
  sums(X, Y) = (a + b for a in X for b in refine(Y, Δ, a.supp))
  canon(gens) = Set{Sequent{K}}(canonicalize(g, Δ) for g in gens)
  κ = canon(sums(A.strict, B.strict))
  μ = canon(Iterators.flatten((sums(A.strict, B.refl), sums(A.refl, B.strict),
                               sums(A.refl, B.refl))))
  λ = canon(Iterators.flatten((sums(A.weak, B.strict ∪ B.refl ∪ B.weak),
                               sums(A.strict ∪ A.refl, B.weak))))
  prune(Constructible{K}(κ, μ, λ, Δ; canonical=true))
end

""" The union `A ∪ B`: componentwise, over the union of the contexts """
function Base.union(A::Constructible{K}, B::Constructible{K})::Constructible{K} where K
  Δ = A.context ∪ B.context
  A, B = enlarge_context(A, Δ), enlarge_context(B, Δ)
  prune(Constructible{K}(A.strict ∪ B.strict, A.refl ∪ B.refl, A.weak ∪ B.weak, Δ;
                         canonical=true))
end

"""
`G_Γ • S = ⋃_{π ∈ G_Γ} π S` for `S` over a context containing `Γ`, as a
constructible over `Γ`: the same generators, now read at the smaller context
(`lemma:orbitrefine`). This is the union at the heart of `∃`.
"""
function unfreeze(S::Constructible{K}, Γ::Set{Int})::Constructible{K} where K
  Γ ⊆ S.context || error("Context $Γ is not contained in $(S.context)")
  canon(gens) = Set{Sequent{K}}(canonicalize(g, Γ) for g in gens)
  prune(Constructible{K}(canon(S.strict), canon(S.refl), canon(S.weak), Γ; canonical=true))
end

# Operations on presentations of roles
#-------------------------------------

"""
`S^⊥ = S ⊸ I`, the residual by the point. The generators of `S`
lying in `0 = 𝒲(λ_I)` are dropped first (`off_zero`): `(S′ ∪ 0)^⊥ = S′^⊥ ∩ 0^⊥`
and `0^⊥ = ⊤^⊥⊥ = ⊤`, so each of them would only add a trivial factor to the
intersection computed by `residual`.
"""
perp(F::Frame{K}, S::Constructible{K}) where K = residual(off_zero(F, S), F.sequents)

""" `S^⊥⊥`, the least closed role containing `S` """
closure(F::Frame{K}, S::Constructible{K}) where K = perp(F, perp(F, S))

"""
`S` without the generators lying in `0 = 𝒲(λ_I)`, the least closed role. Every
closed role contains `0`, and `0` is absorbing for `⊗` (`S ⊗ 0 ⊆ 0`) and
contained in every closed role, so for `X = S ⊗ T` with `S = S′ ∪ 0` and
`T = T′ ∪ 0` one has `X ⊆ S′ ⊗ T′ ∪ 0`, whence `X^⊥⊥ = (S′ ⊗ T′)^⊥⊥`,
`X^⊥ = (S′ ⊗ T′)^⊥`, and `X ⊆ I` iff `S′ ⊗ T′ ⊆ I`. A `Role` therefore keeps
its presentation stripped, which keeps every product and residual small.
"""
function off_zero(F::Frame{K}, S::Constructible{K})::Constructible{K} where K
  Δ = S.context
  keep(gens) = Set{Sequent{K}}(g for g in gens if !in_weak(g, F.sequents.weak, Set{Int}()))
  Constructible{K}(keep(S.strict), keep(S.refl), keep(S.weak), Δ; canonical=true)
end


""" `0 = ⊤^⊥ = ⊤ ⊸ I`, the least closed role (`sec:ex`) """
zero_role(F::Frame{K}, Γ::Set{Int}) where K = perp(F, top(K, Γ))

""" `1 = I^⊥ = {0}^⊥⊥`, the unit of `⊠` """
unit_role(F::Frame{K}, Γ::Set{Int}) where K = perp(F, point(F, Γ))

""" `⊤ = M`, the greatest role, closed as `0^⊥` """
top_role(::Type{K}, Γ::Set{Int}) where K = top(K, Γ)
top_role(Γ::Set{Int}) = top(ℕ, Γ)

""" Semantic equality of two presentations: mutual containment (`contained`) """
roles_equal(F::Frame{K}, S::Constructible{K}, T::Constructible{K}) where K =
  contained(S, T, F.signature) && contained(T, S, F.signature)

"""
Is `S ⊆ I`? Generator by generator, using that `I` is equivariant (so a
generator stands for its whole orbit) and in normal form (so `𝒲(l) ⊆ I` iff
`l ∈ 𝒲(λ_I)` and `ℛ(m) ⊆ I` iff `m ∈ 𝒲(λ_I) ∪ ℛ(μ_I)`, `cor:nfabsorption`).
"""
function below_point(F::Frame{K}, S::Constructible{K})::Bool where K
  I, ∅ = F.sequents, Set{Int}()
  all(k ∈ I for k in S.strict) &&
    all(in_weak(l, I.weak, ∅) for l in S.weak) &&
    all(in_weak(m, I.weak, ∅) || in_refl(m, I.refl, ∅) for m in S.refl)
end

# Closed roles
#-------------

"""
An element of `𝒢`: the closed role `S^⊥⊥`, given by a presentation `S` of any
role with that closure, stripped of the generators in `0` (`off_zero`). The
residual `S^⊥` and the closure `S^⊥⊥` are computed on demand (`perp`,
`Constructible`) and remembered; `⊠`, `∨`, and `∃` never need them, by the
nucleus identities at the top of the file.

Equality `==` is semantic, so it is not cheap and there is no matching `hash`.
"""
mutable struct Role{K<:Semiring}
  const F::Frame{K}
  const pres::Constructible{K}
  perp::Union{Nothing,Constructible{K}}      # S^⊥, once computed (not stripped)
  closure::Union{Nothing,Constructible{K}}   # S^⊥⊥, once computed (not stripped)
end

""" The closed role `S^⊥⊥`, nothing computed yet """
Role(F::Frame{K}, S::Constructible{K}) where K = Role{K}(F, off_zero(F, S), nothing, nothing)

""" A role `S` already known to be closed, so that `S^⊥⊥ = S` """
closed(F::Frame{K}, S::Constructible{K}) where K = Role{K}(F, off_zero(F, S), nothing, S)

context(a::Role) = a.pres.context

""" `S^⊥`, as a presentation """
function perp_of(a::Role{K})::Constructible{K} where K
  isnothing(a.perp) && (a.perp = residual(a.pres, a.F.sequents))
  a.perp
end

""" The closure `S^⊥⊥` itself, as a presentation """
function Constructible(a::Role{K})::Constructible{K} where K
  isnothing(a.closure) && (a.closure = perp(a.F, perp_of(a)))
  a.closure
end

Base.in(t::Sequent{K}, a::Role{K}) where K = t ∈ Constructible(a)

Base.show(io::IO, a::Role) =
  isnothing(a.closure) ? print(io, "(", a.pres, ")^⊥⊥") : print(io, a.closure)

function same_frame(a::Role{K}, b::Role{K}) where K
  a.F === b.F || error("Roles belong to different frames")
  a.F
end

"""
`S^⊥⊥ ⊆ T^⊥⊥` iff `T^⊥ ⊆ S^⊥`, which needs one residual on each side rather than
two; the generators of `0` in `T^⊥` are skipped, `0` lying in every closed role.
"""
contained(a::Role{K}, b::Role{K}) where K =
  contained(off_zero(same_frame(a, b), perp_of(b)), perp_of(a), a.F.signature)

roles_equal(a::Role{K}, b::Role{K}) where K = contained(a, b) && contained(b, a)

Base.:(==)(a::Role{K}, b::Role{K}) where K = a.F === b.F && roles_equal(a, b)

""" `¬S = S^⊥`, closed already """
perp(a::Role) = closed(a.F, perp_of(a))

""" `S ⊠ T = (S ⊗ T)^⊥⊥`, the product of `𝒢`: presented by the Minkowski product """
tensor(a::Role{K}, b::Role{K}) where K = Role(same_frame(a, b), minkowski(a.pres, b.pres))

""" `S ⅋ T = ¬(¬S ⊠ ¬T) = (S^⊥ ⊗ T^⊥)^⊥` """
par(a::Role{K}, b::Role{K}) where K = perp(tensor(perp(a), perp(b)))

""" The join `S ∨ T = (S ∪ T)^⊥⊥` of `𝒢`: presented by the union """
vee(a::Role{K}, b::Role{K}) where K = Role(same_frame(a, b), a.pres ∪ b.pres)

""" The meet `S ∧ T = S ∩ T` of `𝒢`; closed roles are closed under intersection """
meet(a::Role{K}, b::Role{K}) where K =
  closed(same_frame(a, b), Constructible(a) ∩ Constructible(b))

""" Linear implication `S ⊸ T = ¬(S ⊠ ¬T) = (S ⊗ T^⊥)^⊥` in `𝒢` """
lolli(a::Role{K}, b::Role{K}) where K = perp(tensor(a, perp(b)))

"""
`∀^Δ_Γ S = ⋂_{π ∈ G_Γ} π S`, the greatest role over `Γ` below `S` (over `Γ + Δ`);
closed when `S` is. This is `orbit_intersection`, of the closure.
"""
forall(a::Role, Γ::Set{Int}) =
  closed(a.F, orbit_intersection(Constructible(a), Γ))

"""
`∃^Δ_Γ S = (⋃_{π ∈ G_Γ} π S)^⊥⊥`, the least closed role over `Γ` above `S`:
presented by the orbit union `unfreeze` of the presentation.
"""
exists(a::Role, Γ::Set{Int}) = Role(a.F, unfreeze(a.pres, Γ))

""" The same closed role presented at a larger context `Γ ⊇ context(a)` """
function enlarge_context(a::Role{K}, Γ::Set{Int})::Role{K} where K
  enl(S) = isnothing(S) ? nothing : enlarge_context(S, Γ)
  Role{K}(a.F, enlarge_context(a.pres, Γ), enl(a.perp), enl(a.closure))
end

∀(Γ, a::Role) = forall(a, Γ)
∃(Γ, a::Role) = exists(a, Γ)

# Pairs of roles
#---------------

"""
A semantic value: a pair `⟨a₊, a₋⟩` of a premisory and a conclusory role over a
common context, i.e. an element of `X̂ = 𝒢²`. Formulas are interpreted here via
the base case `η(x) = ⟨{x⁺}^⊥⊥, {x⁻}^⊥⊥⟩` and the connectives below. Equality
`==` is semantic (mutual containment of the presented roles), so it is not
cheap and there is no matching `hash`.
"""
struct RolePair{K<:Semiring}
  F::Frame{K}
  prem::Role{K}
  conc::Role{K}
  function RolePair(F::Frame{K}, prem::Role{K}, conc::Role{K}) where K
    context(prem) == context(conc) ||
      error("Roles have different contexts: $(context(prem)) vs $(context(conc))")
    new{K}(F, prem, conc)
  end
end

context(a::RolePair) = context(a.prem)

""" The base case `⟦x⟧ = η(x) = ⟨{x⁺}^⊥⊥, {x⁻}^⊥⊥⟩` at context `supp(x)` """
function RolePair(F::Frame{K}, x::Term) where K
  Γ = Set{Int}(args(x))
  single(s) = Constructible{K}(Set{Sequent{K}}([s]), Set{Sequent{K}}(), Set{Sequent{K}}(), Γ)
  RolePair(F, Role(F, single(Sequent{K}([x], []))), Role(F, single(Sequent{K}([], [x]))))
end

RolePair(F::Frame, x::Expr) = RolePair(F, Term(x))
RolePair(F::Frame, x::Symbol) = RolePair(F, Term(Predicate(x, 0), Int[]))

function Base.show(io::IO, ::MIME"text/plain", a::RolePair)
  print(io, "⟨ ", a.prem, "\n  ", a.conc, " ⟩")
end
Base.show(io::IO, a::RolePair) = show(io, "text/plain", a)

function same_frame(a::RolePair{K}, b::RolePair{K}) where K
  a.F === b.F || error("Role pairs belong to different frames")
  a.F
end

Base.:(==)(a::RolePair{K}, b::RolePair{K}) where K =
  a.F === b.F && roles_equal(a.prem, b.prem) && roles_equal(a.conc, b.conc)

# Connectives: MALL and classical
#----------------------------------

""" `⟦¬A⟧ = ⟨a₋, a₊⟩` """
¬(a::RolePair) = RolePair(a.F, a.conc, a.prem)

""" `⟦A ⊗ B⟧ = ⟨a₊ ⊠ b₊, a₋ ⅋ b₋⟩` """
function ⊗(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, tensor(a.prem, b.prem), par(a.conc, b.conc))
end

""" `⟦A ⊕ B⟧ = ⟨a₊ ∨ b₊, a₋ ∧ b₋⟩` """
function ⊕(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, vee(a.prem, b.prem), meet(a.conc, b.conc))
end

""" `⟦A ⅋ B⟧ = ⟦¬(¬A ⊗ ¬B)⟧ = ⟨a₊ ⅋ b₊, a₋ ⊠ b₋⟩` """
function ⅋(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, par(a.prem, b.prem), tensor(a.conc, b.conc))
end

""" `⟦A & B⟧ = ⟦¬(¬A ⊕ ¬B)⟧ = ⟨a₊ ∧ b₊, a₋ ∨ b₋⟩` """
function Base.:&(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, meet(a.prem, b.prem), vee(a.conc, b.conc))
end

""" `⟦A ⊸ B⟧ = ⟦¬A ⅋ B⟧ = ⟨a₋ ⅋ b₊, a₊ ⊠ b₋⟩` """
function lolli(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, par(a.conc, b.prem), tensor(a.prem, b.conc))
end

""" Classical `⟦A ∧ B⟧ = ⟨a₊ ⊠ b₊, a₋ ∧ b₋ ∧ (a₋ ⊠ b₋)⟩` """
function ∧(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, tensor(a.prem, b.prem),
              meet(meet(a.conc, b.conc), tensor(a.conc, b.conc)))
end

""" Classical `⟦A ∨ B⟧ = ⟦¬(¬A ∧ ¬B)⟧ = ⟨a₊ ∧ b₊ ∧ (a₊ ⊠ b₊), a₋ ⊠ b₋⟩` """
function ∨(a::RolePair{K}, b::RolePair{K}) where K
  F = same_frame(a, b)
  RolePair(F, meet(meet(a.prem, b.prem), tensor(a.prem, b.prem)),
              tensor(a.conc, b.conc))
end

""" Classical `⟦A ⇒ B⟧ = ⟦¬A ∨ B⟧` """
⇒(a::RolePair, b::RolePair) = ¬a ∨ b

# Quantifiers (`sec:quantifiers`)
#--------------------------------

"""
`⟦∀Δ. φ⟧_Γ = ⟨∀^Δ_Γ(a₊), ∃^Δ_Γ(a₋)⟩`, binding the names `Δ` of `⟦φ⟧_{Γ+Δ}`.
"""
function forall(a::RolePair, Δ)
  Γ = setdiff(context(a), Set{Int}(Δ))
  RolePair(a.F, forall(a.prem, Γ), exists(a.conc, Γ))
end

∀(Δ, a::RolePair) = forall(a, Δ)

""" `⟦∃Δ. φ⟧ = ⟦¬∀Δ. ¬φ⟧ = ⟨∃^Δ_Γ(a₊), ∀^Δ_Γ(a₋)⟩` """
function exists(a::RolePair, Δ)
  Γ = setdiff(context(a), Set{Int}(Δ))
  RolePair(a.F, exists(a.prem, Γ), forall(a.conc, Γ))
end

∃(Δ, a::RolePair) = exists(a, Δ)

"""
The same value viewed at a larger context `Γ ⊇ context(a)`: the inclusion
`ι : X̂(context) ↪ X̂(Γ)`, which re-presents both roles over `Γ`. It matters
before quantifying: `forall(in_context(a, Γ ∪ Δ), Δ)` binds `Δ` with the
bound names ranging over names *outside* `Γ`, whereas `forall(a, Δ)` uses the
smallest context. The two agree iff the frame is substitution-equivariant
(`prop:hyper`, Beck–Chevalley); otherwise the value of a formula genuinely
depends on which names are in scope.
"""
function in_context(a::RolePair, Γ)
  Γ = Set{Int}(Γ)
  context(a) ⊆ Γ || error("Context $Γ does not contain $(context(a))")
  RolePair(a.F, enlarge_context(a.prem, Γ), enlarge_context(a.conc, Γ))
end

# Semantic consequence
#---------------------

"""
`A₁, …, Aₙ ⊨ B₁, …, Bₘ` iff `a₁₊ ⊗ ⋯ ⊗ aₙ₊ ⊗ b₁₋ ⊗ ⋯ ⊗ bₘ₋ ⊆ I`. The Minkowski
product of the roles' presentations suffices: `I` is closed, so a role lies in
it iff its closure does, and the closure of a product of closures is the closure
of the product.
"""
function entails(prems::AbstractVector{RolePair{K}}, concs::AbstractVector{RolePair{K}})::Bool where K
  isempty(prems) && isempty(concs) && error("Nothing to decide")
  F = first([prems; concs]).F
  all(a.F === F for a in [prems; concs]) || error("Role pairs belong to different frames")
  roles = [[a.prem.pres for a in prems]; [b.conc.pres for b in concs]]
  unit = Constructible{K}(Set{Sequent{K}}([zero(Sequent{K})]), Set{Sequent{K}}(),
                          Set{Sequent{K}}(), Set{Int}())
  below_point(F, reduce(minkowski, roles; init=unit))
end

entails(a::RolePair{K}, b::RolePair{K}) where K = entails([a], [b])
entails(b::RolePair{K}) where K = entails(RolePair{K}[], [b])

⊮(x, y) = !(x ⊩ y)
⊩(a::RolePair{K}, b::RolePair{K}) where K = entails(a, b)
⊩(a::AbstractVector, b::AbstractVector) = entails(pairs_of(a, b), pairs_of(b, a))
⊩(a::AbstractVector, b::RolePair{K}) where K = entails(Vector{RolePair{K}}(a), [b])
⊩(a::RolePair{K}, b::AbstractVector) where K = entails([a], Vector{RolePair{K}}(b))

""" `xs` as a vector of role pairs, its element type taken from `ys` if `xs` is empty """
function pairs_of(xs::AbstractVector, ys::AbstractVector)
  K = semiring_of(isempty(xs) ? ys : xs)
  Vector{RolePair{K}}(xs)
end

semiring_of(xs::AbstractVector) = isempty(xs) ? error("Nothing to decide") : semiring(first(xs))
semiring(::RolePair{K}) where K = K
