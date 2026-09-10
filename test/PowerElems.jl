module TestPowerElems

using NominalFrames, Test
using NominalFrames: embeddings, in_strict, in_weak, in_refl, terms, powerset

default_multiplicity!(ℕ)

# Example signature and terms

ψ′,P′,Q′,R′ = ps = Predicate.([:ψ,:P,:Q,:R], [0,1,2,2])
Σ = Signature([ψ′,P′,Q′])
ψ, P₁, Q₁₂, R₁₂ = Term.(ps)
P(i) = Term(P′, [i])
Q(i,j) = Term(Q′, [i,j])
R(i,j) = Term(R′, [i,j])

ts = small_sequents(Σ, [1, 2, 3], 2)

# Example power elements 
#-----------------------

refl = refl_sequents(Σ)
s₀ = Sequent([P₁], [Q₁₂])
I𝒪 = 𝒲(refl)
I𝒲 = 𝒲([refl; s₀])
Iℛ = ℛ(refl)
I𝒟 = κ(s₀) ∪ I𝒪

∅, Γ1 = Set{Int}(), Set([1])
⊤, ⊥ = top(∅), bottom(∅)


# Embeddings
############

s₀ = Sequent([P(1)], [Q(1,2)])

@test embeddings(s₀, Sequent(:(P(3) ⊢ Q(3,4))), ∅) == [Renaming(1=>3, 2=>4)]
@test isempty(embeddings(s₀, Sequent([P(3)], [Q(3,4)]), Γ1)) # 1 frozen
@test embeddings(s₀, Sequent(:(P(1) ⊢ Q(1,4))), Γ1) == [Renaming(2=>4)]
@test length(embeddings(Sequent(:(Q(1,2))), Sequent(:(Q(3,4) + Q(4,3))), ∅)) == 2
@test isempty(embeddings(Sequent(:(P(1) + P(2))), Sequent(:(P(3) + P(3))), ∅)) # injectivity
@test embeddings(Sequent(), s₀, ∅) == [Renaming()]

# Checking strict
#################
@test in_strict(s₀, I𝒟)
@test in_strict(Sequent(:(P(6)⊢Q(6,4))), I𝒟) # normalizes
@test !in_strict(s₀, I𝒲)
@test !in_strict(s₀, ⊤)

# Checking weak
###############
@test in_weak(s₀, ⊤)
@test in_weak(s₀, I𝒲)

@test in_weak(Sequent(:(P(1)+Q(1,2)+P(3) ⊢ 2P(1)+R(1,2)+R(2,3))), I𝒲)


# Checking refl
################

@test in_refl(s₀ + Sequent(:(Q(2,3)⊢Q(2,3))), ℛ(s₀))

@test !in_refl(s₀, ⊤) 

# Membership 
#-----------

@test s₀ ∈ I𝒟 
@test Sequent(:(P(3) ⊢ Q(3,1))) ∈ I𝒟 
@test Sequent(:(P(1) ⊢ Q(2,1))) ∉ I𝒟
@test Sequent(:(P(1) + ψ ⊢ Q(1,2))) ∈ I𝒲 
@test Sequent(:(P(1) + ψ ⊢ Q(1,2))) ∉ I𝒟
@test Sequent(:(P(1) + ψ ⊢ ψ + P(1))) ∈ Iℛ 
@test Sequent(:(P(1) + ψ ⊢ ψ)) ∉ Iℛ 
@test Sequent(:(P(1) + ψ ⊢ ψ + P(1) + ψ)) ∉ Iℛ
@test zero(Sequent) ∉ Iℛ && zero(Sequent) ∈ ⊤ && zero(Sequent) ∉ ⊥
@test all(t ∈ ⊤ for t in ts)
@test !any(t ∈ ⊥ for t in ts)

# With a context, names in it are rigid: `Q(2,3)` at {1} covers Q(a,b) with a,b ≠ 1
D = κ(:(Q(2, 3) ⊢ 0), [1])
@test Sequent(:(Q(3,2) ⊢ 0)) ∈ D 
@test Sequent(:(Q(1,2) ⊢ 0)) ∉ D 
@test Sequent(:(Q(2,1) ⊢ 0)) ∉ D


# Checking pruning 
###################


# Pruning keeps the subobject and drops redundant generators: `P⁺ ψ⁺ ψ⁻ ∈ ℛ(P⁺)`
# `QQ ∈ 𝒲(Q)` go; `P⁺P⁻` and `P⁺Q⁻` stay, their imbalances differing from P⁺
G = Constructible(Sequent.([:(P(1) ⊢ P(1)), :(P(1) ⊢ Q(1,2))]), 
                  Sequent.([:(P(1) ⊢ 0), :(P(1) + ψ ⊢ ψ)]),
                  Sequent.([:(Q(1,2) ⊢ 0), :(Q(1,2) + Q(3,4) ⊢ 0)]))

@test prune(G) == Constructible(Sequent.([:(P(1) ⊢ P(1)), :(P(1) ⊢ Q(1,2))]), 
                                Sequent.([:(P(1) ⊢ 0)]), 
                                Sequent.([:(Q(1,2) ⊢ 0)]))
@test all((t ∈ G) == (t ∈ prune(G)) for t in ts)


# Binary intersection 
#--------------------

# A few by hand
@test (I𝒪 ∩ Iℛ) == Iℛ  # ℛ(p ⊢ p) ⊆ 𝒲(p ⊢ p)
@test (I𝒪 ∩ I𝒲) == I𝒪
@test (I𝒟 ∩ I𝒲).strict == Set([s₀]) && isempty((I𝒟 ∩ I𝒲).refl)
@test (⊤ ∩ I𝒟) == I𝒟
@test (⊥ ∩ I𝒟) == ⊥
# 𝒲(P⁺_a) ∩ 𝒲(P⁺_b) = 𝒲(P⁺_a) ∪ 𝒲(P⁺_a P⁺_b) = 𝒲(P⁺_a), once pruned
@test only((𝒲(:(P(1) ⊢ 0)) ∩ 𝒲(:(P(1) ⊢ 0))).weak) ==
      Sequent(:(P(1) ⊢ 0))

      # ℛ(ψ⁺) ∩ 𝒲(P⁺_a) = ℛ(ψ⁺ P⁺_a P⁻_a)
@test only((ℛ(:(ψ ⊢ 0)) ∩ 𝒲(:(P(1) ⊢ 0))).refl) == Sequent(:(ψ + P(1) ⊢ P(1)))
# ℛ(ψ⁺) ∩ ℛ(P⁺_a) = ∅: imbalances never agree
@test ℛ(:(ψ ⊢ 0)) ∩ ℛ(:(P(1) ⊢ 0)) == ⊥


# Brute force intersection test
As = [I𝒪,I𝒲,Iℛ,I𝒟, ⊤, ⊥, 
      Constructible([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [:(Q(1,2) ⊢ 0)]),
      Constructible([], [:(P(1) ⊢ 0)], [:(P(1) ⊢ ψ)]),
      𝒲(:(P(1) ⊢ 0), [1])]
for A in As, B in As, t in ts
  @test (t ∈ A ∩ B) == (t ∈ A && t ∈ B)
end

# With 𝔹 coefficients
#####################

S′(x) = Sequent{𝔹}(x)
S′(x::Sequent{𝔹}) = x
C′(κ, μ, λ, ctx) = Constructible{𝔹}(S′.(κ), S′.(μ), S′.(λ), Set{Int}(ctx))
⊤′, ⊥′ = top(𝔹, ∅), bottom(𝔹, ∅)

refl′ = refl_sequents(𝔹, Σ)
s₀′ = S′(:(P(1) ⊢ Q(1,2)))
I𝒪′, I𝒲′, Iℛ′ = 𝒲(refl′), 𝒲([refl′; s₀′]), ℛ(refl′)
I𝒟′ = κ(s₀′) ∪ I𝒪′
frames′ = [I𝒪′, Iℛ′, I𝒲′, I𝒟′]
@test all(F isa Constructible{𝔹} for F in frames′)

# Between the multiplicities: `q` generator by generator
#-------------------------------------------------------

for (I, I′) in zip([I𝒪, Iℛ, I𝒲, I𝒟], frames′)
  @test Constructible{𝔹}(I) == I′
end
@test Constructible{𝔹}(𝒲(:(2P(1) ⊢ 0), [1])) == 𝒲(S′(:(P(1) ⊢ 0)), [1])
@test Constructible{𝔹}(⊤) == ⊤′ && Constructible{𝔹}(⊥) == ⊥′

# Membership
#-----------

ts′ = small_sequents(𝔹, Σ, [1, 2, 3], 2)
@test length(ts′) == 1 + 20 + binomial(20, 2)   # no `2x` sequents

@test S′(:(P(1) + ψ ⊢ ψ + P(1))) ∈ Iℛ′
@test S′(:(P(1) + ψ ⊢ ψ)) ∉ Iℛ′
@test S′(:(P(1) + ψ ⊢ 0)) ∉ Iℛ′
@test S′(:(ψ ⊢ ψ)) ∈ ℛ(S′(:(ψ ⊢ 0)))     # ψ⁺ + ψ⁺ψ⁻ = ψ⁺ψ⁻, so ψ⁺ ≤_ℛ ψ⁺ψ⁻ ...
@test Sequent(:(ψ ⊢ ψ)) ∉ ℛ(Sequent(:(ψ ⊢ 0))) # ... but not w/ multiplicities
@test all(t ∈ ⊤′ for t in ts′) && !any(t ∈ ⊥′ for t in ts′)

"""
Membership `t ∈ κ ∪ 𝒲(λ) ∪ ℛ(μ)` by exhaustive search: a witness below `t` can
only use names of `t` and of the context, and `t ∈ ℛ(m)` iff `t = m + (Z ⊢ Z)`
for some set `Z` of terms of `t`.
"""
function member′(t::Sequent{𝔹}, C::Constructible{𝔹})::Bool
  Δ = C.context
  pool = t.supp ∪ Δ
  refl_leq_bf(m, t) = any(t == m + Sequent{𝔹}(collect(z), collect(z))
                          for z in powerset(collect(terms(t))))
  any(same_orbit(t, k, Δ) for k in C.strict) ||
    any(l′ ≼ t for l in C.weak for l′ in orbit(l, Δ, pool)) ||
    any(refl_leq_bf(m′, t) for m in C.refl for m′ in orbit(m, Δ, pool))
end

for I in frames′, t in ts′
  @test (t ∈ I) == member′(t, I)
end
# Enlarging the context presents the same subobject
for I in frames′, Δ in [Γ1, Set([1, 2])], t in ts′
  @test member′(t, I) == member′(t, enlarge_context(I, Δ))
end

# Binary intersection
#--------------------

As′ = [I𝒪′, I𝒲′, Iℛ′, I𝒟′, ⊤′, ⊥′,
       C′([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [:(Q(1,2) ⊢ 0)], []),
       C′([], [:(P(1) ⊢ 0)], [:(P(1) ⊢ ψ)], []),
       C′([], [:(P(1) ⊢ 0), :(ψ ⊢ 0)], [], []),
       𝒲(S′(:(P(1) ⊢ 0)), [1])]
for A in As′, B in As′, t in ts′
  @test (t ∈ A ∩ B) == (t ∈ A && t ∈ B)
end
# ℛ(ψ⁺) ∩ ℛ(P⁺ₐ) = ℛ(ψ⁺P⁺ₐψ⁻P⁻ₐ), nonempty unlike its ℕ counterpart above
@test only((ℛ(S′(:(ψ ⊢ 0))) ∩ ℛ(S′(:(P(1) ⊢ 0)))).refl
          ) == S′(:(ψ + P(1) ⊢ ψ + P(1)))

end # module
