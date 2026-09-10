module TestSingletonResidual

using Test, NominalFrames
using NominalFrames: refl_above, refl_meet, refl_predecessors, residual_strict,
                     residual_refl, terms, powerset

default_multiplicity!(ℕ)

ψ′,P′,Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
ψ = Term(ψ′)
P(i) = Term(P′,[i])
Q(i,j) = Term(Q′,[i,j])

Σ = Signature([ψ′, P′, Q′])

∅, Γ1 = Set{Int}(), Set([1])

S(x) = Sequent(x)

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
@test enlarge_context(I𝒪, Γ1) == 𝒲(new_gens, Γ1)

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
@test only((s₁ →ₒ I𝒟).strict) == S(:(0 ⊢ Q(1,2)))
@test only((S(:(P(2) ⊢ 0)) →ₒ I𝒟).strict) == S(:(0 ⊢ Q(2,1)))
@test isempty((S(:(ψ ⊢ 0)) →ₒ I𝒟).strict)
@test only((S(:(0 ⊢ Q(1,2))) →ₒ I𝒟).strict) == S(:(P(1) ⊢ 0))
@test only((S(:(0 ⊢ Q(2,1))) →ₒ I𝒟).strict) == S(:(P(2) ⊢ 0))
@test (s₁ →ₒ I𝒟).context == Γ1

# Residuating by 0 changes nothing but the presentation's context
@test (zero(Sequent) →ₒ I𝒟) == I𝒟

# The result is a constructible triple over context ∪ supp(s)
@test (S(:(P(1) ⊢ Q(2, 3))) →ₒ I𝒪).context == Set([1, 2, 3])

# Brute-force oracle: `t ∈ {s} ⊸ C  iff  s + t ∈ C`
#--------------------------------------------------

"""
Membership `t ∈ κ ∪ 𝒲(λ) ∪ ℛ(μ)` by exhaustive search: a
witness below `t` can only use names of `t` and of the context.
"""
function member(t::Sequent, C::Constructible)::Bool
  Δ = C.context
  pool = t.supp ∪ Δ
  any(same_orbit(t, k, Δ) for k in C.strict) ||
    any(l′ ≼ t for l in C.weak for l′ in orbit(l, Δ, pool)) ||
    any(refl_leq(m′, t) for m in C.refl for m′ in orbit(m, Δ, pool))
end

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

# With 𝔹 coefficients
#####################
#
# Sides are sets, so `t = m + ρ` no longer determines `ρ ∈ R`: `a⁺ + a⁺a⁻ = a⁺a⁻`.
# The `𝔹` methods of `refl_leq`, `refl_above`, `refl_meet`, `refl_predecessors`,
# `residual_strict` and `residual_refl` are checked by hand where they differ
# from the `ℕ` ones, and against brute force.

S′(x) = Sequent{𝔹}(x)
S′(x::Sequent{𝔹}) = x
C′(κ, μ, λ, ctx) = Constructible{𝔹}(S′.(κ), S′.(μ), S′.(λ), Set{Int}(ctx))
Σψ = Signature([ψ′])

# The order ≤_ℛ
#--------------

# `a⁺ + a⁺a⁻ = a⁺a⁻`, so `a⁺ ≤_ℛ a⁺a⁻` with 𝔹 coefficients and not with ℕ
@test refl_leq(S′(:(ψ ⊢ 0)), S′(:(ψ ⊢ ψ)))
@test !refl_leq(S(:(ψ ⊢ 0)), S(:(ψ ⊢ ψ)))
@test refl_leq(S′(:(ψ ⊢ 0)), S′(:(ψ + P(1) ⊢ P(1))))
@test !refl_leq(S′(:(ψ ⊢ 0)), S′(:(ψ + P(1) ⊢ 0)))
@test !refl_leq(S′(:(ψ ⊢ 0)), S′(:(0 ⊢ ψ)))
# Brute force: `t ∈ ℛ(m)` iff `t = m + (Z ⊢ Z)` for some set `Z` of terms of `t`
function refl_leq_bf(m::Sequent{𝔹}, t::Sequent{𝔹})
  Z = collect(terms(t))
  any(t == m + Sequent{𝔹}(collect(z), collect(z)) for z in powerset(Z))
end
all′ = small_sequents(𝔹, Σ, [1, 2], 3)
for m in small_sequents(𝔹, Σ, [1, 2], 2), t in all′
  @test refl_leq(m, t) == refl_leq_bf(m, t)
end

# Least element of ℛ(m) above w, and ℛ(m₁) ∩ ℛ(m₂)
@test refl_above(S′(:(ψ ⊢ 0)), S′(:(0 ⊢ P(1)))) == S′(:(ψ + P(1) ⊢ P(1)))
@test refl_meet(S′(:(ψ ⊢ 0)), S′(:(P(1) ⊢ 0))) == S′(:(ψ + P(1) ⊢ ψ + P(1)))  # never empty
@test isnothing(refl_meet(S(:(ψ ⊢ 0)), S(:(P(1) ⊢ 0))))
for m₁ in small_sequents(𝔹, Σψ, Int[], 2), m₂ in small_sequents(𝔹, Σψ, Int[], 2),
    t in small_sequents(𝔹, Σψ, Int[], 2)
  @test refl_leq(refl_meet(m₁, m₂), t) == (refl_leq(m₁, t) && refl_leq(m₂, t))
end
for m in small_sequents(𝔹, Σ, [1, 2], 2), w in small_sequents(𝔹, Σ, [1, 2], 2)
  u = refl_above(m, w)
  @test refl_leq(m, u) && w ≼ u
  @test all(!(refl_leq(m, t) && w ≼ t) || u ≼ t for t in all′)
end

# One ≤_ℛ-step down: either or both halves of a balanced pair
@test Set(refl_predecessors(S′(:(ψ + P(1) ⊢ ψ)))) ==
      Set(S′.([:(P(1) ⊢ ψ), :(ψ + P(1) ⊢ 0), :(P(1) ⊢ 0)]))
@test refl_predecessors(S(:(ψ + P(1) ⊢ ψ))) == [S(:(P(1) ⊢ 0))]

# Singleton residuals, generator by generator
#--------------------------------------------

# `{s} ⊸ {k}` is an interval
@test Set(residual_strict(S′(:(ψ ⊢ 0)), S′(:(ψ + P(1) ⊢ 0)))) ==
      Set(S′.([:(P(1) ⊢ 0), :(ψ + P(1) ⊢ 0)]))
@test residual_strict(S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ 0))) == [S(:(P(1) ⊢ 0))]
@test isempty(residual_strict(S′(:(ψ ⊢ 0)), S′(:(P(1) ⊢ 0))))
# `{a⁺} ⊸ ℛ(a⁺b⁻) = ℛ(b⁻) ∪ ℛ(a⁺b⁻) ∪ ℛ(a⁻b⁻)`
@test Set(residual_refl(S′(:(ψ ⊢ 0)), S′(:(ψ ⊢ P(1))))) ==
      Set(S′.([:(0 ⊢ P(1)), :(ψ ⊢ P(1)), :(0 ⊢ ψ + P(1))]))
@test only(residual_refl(S(:(ψ ⊢ 0)), S(:(ψ ⊢ P(1))))) == S(:(0 ⊢ P(1)))

# Brute-force oracle: `t ∈ {s} ⊸ C  iff  s + t ∈ C`
#--------------------------------------------------

""" `member`, with the brute-force `refl_leq_bf` in place of `refl_leq` """
function member′(t::Sequent{𝔹}, C::Constructible{𝔹})::Bool
  Δ = C.context
  pool = t.supp ∪ Δ
  any(same_orbit(t, k, Δ) for k in C.strict) ||
    any(l′ ≼ t for l in C.weak for l′ in orbit(l, Δ, pool)) ||
    any(refl_leq_bf(m′, t) for m in C.refl for m′ in orbit(m, Δ, pool))
end

refl′ = refl_sequents(𝔹, Σ)
s₀′ = S′(:(P(1) ⊢ Q(1,2)))
frames′ = [𝒲(refl′), ℛ(refl′), 𝒲([refl′; s₀′]), κ(s₀′) ∪ 𝒲(refl′)]
ts′ = small_sequents(𝔹, Σ, [1, 2, 3], 2)

for I in [frames′; C′([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [:(Q(1,2) ⊢ 0)], ∅);
          C′([:(ψ ⊢ P(1))], [:(ψ ⊢ P(1))], [], ∅)],
    s in S′.([:(P(1) ⊢ 0), :(0 ⊢ P(1)), :(ψ ⊢ 0), :(P(1) ⊢ P(1)), :(0 ⊢ Q(1,2)),
              :(P(2) ⊢ Q(2,1)), :(P(1) ⊢ ψ), :(P(1) + P(2) ⊢ 0)])
  R = s →ₒ I
  @test R.context == I.context ∪ s.supp
  for t in ts′
    @test member′(t, R) == member′(s + t, I)
  end
end

end # module
