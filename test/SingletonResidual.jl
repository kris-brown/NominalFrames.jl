module TestSingletonResidual

using Test, NominalFrames

ψ′,P′,Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
ψ = Term(ψ′)
P(i) = Term(P′,[i])
Q(i,j) = Term(Q′,[i,j])

Σ = Signature([ψ′, P′, Q′])

∅, Γ1 = Set{Int}(), Set([1])

S(x) = Sequent(x)
C(κ, μ, λ, ctx) = Constructible(Set{Sequent}(S.(κ)), Set{Sequent}(S.(μ)),
                                Set{Sequent}(S.(λ)), Set{Int}(ctx))

# The reflexive submonoid
#------------------------
P⁺₁Q⁻₁₂ = S(:(P(1) ⊢ Q(1,2)))

@test isreflexive(S(:(P(1) + Q(1,2) ⊢ Q(1,2) + P(1))))
@test isreflexive(zero(Sequent))
@test !isreflexive(S(:(P(1) ⊢ P(2))))

@test refl_dominator(P⁺₁Q⁻₁₂) == S(:(P(1) + Q(1,2) ⊢ P(1) + Q(1,2)))
@test refl_dominator(S(:(2P(1) ⊢ P(1)))) == S(:(2P(1) ⊢ 2P(1)))
@test refl_core(S(:(2P(1) + ψ ⊢ P(1)))) == S(:(P(1) ⊢ P(1)))
for x in S.([:(P(1) ⊢ Q(1,2)), :(2P(1) + ψ ⊢ P(1)), :(ψ ⊢ ψ), :(0 ⊢ 0)])
  @test refl_core(x) ≼ x && x ≼ refl_dominator(x)
  @test isreflexive(refl_dominator(x) - x) == isreflexive(x)
  # |s_c| = |imb(s)|
  @test length(x - refl_core(x)) == sum(abs, values(imbalance(x)); init=0) 
end

@test imbalance(S(:(2P(1) + ψ ⊢ P(1) + Q(1,2)))) ==
      Dict(P(1) => 1, ψ => 1, Q(1,2) => -1)
@test isempty(imbalance(S(:(ψ ⊢ ψ))))
@test refl_leq(S(:(P(1) ⊢ 0)), S(:(P(1) + ψ ⊢ ψ)))
@test !refl_leq(S(:(P(1) ⊢ 0)), S(:(P(1) + ψ ⊢ 0)))

# Enlarging the context (`refine` itself is tested in Orbits.jl)
#----------------------

refl = refl_sequents(Σ)
I𝒪, Iℛ, I𝒲 = 𝒲(refl), ℛ(refl), 𝒲([refl; P⁺₁Q⁻₁₂])
I𝒟 = Constructible([P⁺₁Q⁻₁₂], [], refl, [])

@test enlarge_context(I𝒪, ∅) === I𝒪

new_gens = [:(ψ ⊢ ψ), :(P(1) ⊢ P(1)), :(P(2) ⊢ P(2)),
            :(Q(1,2) ⊢ Q(1,2)), :(Q(2,1) ⊢ Q(2,1)), :(Q(2, 3) ⊢ Q(2, 3))]
@test enlarge_context(I𝒪, Γ1) == C([], [], new_gens, Γ1)

# The singleton residual
#-----------------------

s₁ = S(:(P(1) ⊢ 0))

# {s} ⊸ 𝒲(λ) = 𝒲(λ ∸ s)
@test (s₁ →ₒ I𝒪) == 𝒲(enlarge_context(I𝒪, Γ1).weak ∸ s₁, Γ1)

# What this is, concretely:
@test enlarge_context(I𝒪, Γ1).weak ∸ s₁ == Set(S.([
  :(ψ ⊢ ψ), :(0 ⊢ P(1)), :(P(2) ⊢ P(2)),
  :(Q(1,2) ⊢ Q(1,2)), :(Q(2,1) ⊢ Q(2,1)), :(Q(2,3) ⊢ Q(2,3))
]))

# {s} ⊸ ℛ(m) = ℛ(m + (s ∸ m)^ - s): a `P(1)` on the left is paid for either by
# the generator itself (`P(1) ⊢ P(1) ↦ 0 ⊢ P(1)`) or by a reflexive
# `P(1) ⊢ P(1)` factor, which leaves `P(1)` behind on the right.
@test (s₁ →ₒ Iℛ) == ℛ([:(ψ ⊢ ψ + P(1)), :(0 ⊢ P(1)), :(P(2) ⊢ P(2) + P(1)),
                       :(Q(1,2) ⊢ Q(1,2) + P(1)), :(Q(2,1) ⊢ Q(2,1) + P(1)),
                       :(Q(2, 3) ⊢ Q(2, 3) + P(1))], Γ1)

# e.g. (Iℛ.refl .+ refl_dominator(s₁ ∸ Iℛ.refl) .- s₁)

# {s} ⊸ κ keeps only generators above `s`, and subtracts it
@test (s₁ →ₒ I𝒟).strict == Set([S(:(0 ⊢ Q(1,2)))])
@test (S(:(P(2) ⊢ 0)) →ₒ I𝒟).strict == Set([S(:(0 ⊢ Q(2,1)))])
@test isempty((S(:(ψ ⊢ 0)) →ₒ I𝒟).strict)
@test (S(:(0 ⊢ Q(1,2))) →ₒ I𝒟).strict == Set([S(:(P(1) ⊢ 0))])
@test (S(:(0 ⊢ Q(2,1))) →ₒ I𝒟).strict == Set([S(:(P(2) ⊢ 0))])
@test (s₁ →ₒ I𝒟).context == Γ1

# Residuating by 0 changes nothing but the presentation's context
@test (zero(Sequent) →ₒ I𝒟) == I𝒟

# The result is a constructible triple over context ∪ supp(s)
@test (S(:(P(1) ⊢ Q(2, 3))) →ₒ I𝒪).context == Set([1, 2, 3])

# Brute-force oracle: `t ∈ {s} ⊸ C  iff  s + t ∈ C`
#--------------------------------------------------

"""
Membership `t ∈ κ ∪ 𝒲(λ) ∪ ℛ(μ)` by exhaustive search (`lemma:matching`): a
witness below `t` can only use names of `t` and of the context.
"""
function member(t::Sequent, C::Constructible)::Bool
  Δ = C.context
  pool = t.supp ∪ Δ
  any(same_orbit(t, k, Δ) for k in C.strict) ||
    any(l′ ≼ t for l in C.weak for l′ in orbit(l, Δ, pool)) ||
    any(refl_leq(m′, t) for m in C.refl for m′ in orbit(m, Δ, pool))
end

""" Every sequent of size ≤ `n` whose names are drawn from `names` """
function small_sequents(Σ::Signature, names::Vector{Int}, n::Int)::Vector{Sequent}
  terms = [Term(p, collect(a)) for p in Σ for a in injections_args(p.arity, names)]
  signed = [(t, side) for t in terms for side in (:prem, :conc)]
  res = Sequent[]
  for k in 0:n, choice in Iterators.product(fill(signed, k)...)
    prem = Term[t for (t, side) in choice if side == :prem]
    conc = Term[t for (t, side) in choice if side == :conc]
    push!(res, Sequent(prem, conc))
  end
  unique(res)
end

injections_args(arity::Int, names::Vector{Int}) =
  [Int[ρ[i] for i in 1:arity] for ρ in injections(collect(1:arity), names)]

ts = small_sequents(Σ, [1, 2, 3], 2)
@test length(ts) == 1 + 20 + 20 + binomial(20, 2)

# Enlarging the context presents the same subobject
for I in [I𝒪, Iℛ, I𝒲, I𝒟], Δ in [Γ1, Set([1, 2])], t in ts
  @test member(t, I) == member(t, enlarge_context(I, Δ))
end

for I in [I𝒪, Iℛ, I𝒲, I𝒟],
    s in S.([:(P(1) ⊢ 0), :(0 ⊢ P(1)), :(ψ ⊢ 0), :(P(1) ⊢ P(1)), :(0 ⊢ Q(1,2)),
             :(P(2) ⊢ Q(2,1)), :(2P(1) ⊢ ψ), :(P(1) + P(2) ⊢ 0)])
  R = s →ₒ I
  for t in ts
    @test member(t, R) == member(s + t, I)
  end
end

end # module
