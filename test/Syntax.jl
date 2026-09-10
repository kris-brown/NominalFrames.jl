module TestSyntax 

using NominalFrames, Test

using NominalFrames: balanced_pairs, name_to_int, int_to_name



# Multiset sequents
###################

default_multiplicity!(ℕ)

ψ′, P, Q = Predicate.([:ψ, :P, :Q],[0,1,2])
Σ = Signature([ψ′, P, Q])

@test length(Σ) == 3

ψ, P₁,Q₁₂ = Term.(Σ)

s = Sequent([P₁],[Q₁₂])
@test s == Sequent(:(P(1) ⊢ Q(1,2)))
@test s+s == Sequent([P₁,P₁],[Q₁₂,Q₁₂])

@test refl_sequents(Σ) == Sequent.([:(ψ⊢ψ),:(P(1)⊢P(1)),:(Q(1,2)⊢Q(1,2))])


@test Term(:(P(a))) == P₁
@test Term(:(Q(a,b))) == Q₁₂
@test Term(:(Q(a,2))) == Q₁₂                       # the two forms mix
@test Term(:(Q(b,a))) == Term(Q, [2,1])
@test_throws ErrorException Term(:(P(A)))
@test_throws ErrorException Term(:(P(1.5)))
@test Sequent(:(P(a) + 2Q(a,b) ⊢ ψ)) == Sequent(:(P(1) + 2Q(1,2) ⊢ ψ))
@test Sequent{𝔹}(:(P(a) ⊢ Q(a,b))) == Sequent{𝔹}(:(P(1) ⊢ Q(1,2)))

# Arithmetic 
#-----------

∅ = Set{Int}()

@test iszero(zero(Sequent))
@test zero(Sequent).supp == ∅
@test length(Sequent(:(P(1) + 2Q(1,2) ⊢ ψ))) == 4

@test Sequent(:(P(1) ⊢ 0)) ≼ Sequent(:(P(1) ⊢ Q(1,2)))
@test !(Sequent(:(P(2) ⊢ 0)) ≼ Sequent(:(P(1) ⊢ Q(1,2))))
@test !(Sequent(:(2P(1) ⊢ 0)) ≼ Sequent(:(P(1) ⊢ Q(1,2))))

@test Sequent(:(P(1) ⊢ Q(1,2))) - Sequent(:(P(1) ⊢ 0)) == Sequent(:(0 ⊢ Q(1,2)))
@test Sequent(:(P(1) ⊢ 0)) - Sequent(:(P(1) ⊢ 0)) == zero(Sequent)
@test_throws ErrorException Sequent(:(P(1) ⊢ 0)) - Sequent(:(P(2) ⊢ 0))

@test Sequent(:(P(1) ⊢ Q(1,2))) ∸ Sequent(:(P(1) + P(2) ⊢ 0)) == Sequent(:(0 ⊢ Q(1,2)))
@test Sequent(:(P(1) ⊢ 0)) ∸ Sequent(:(P(1) ⊢ Q(1,2))) == zero(Sequent)
# `u ≽ t ∸ s  iff  s + u ≽ t`
t, s = Sequent(:(2P(1) ⊢ Q(1,2))), Sequent(:(P(1) + ψ ⊢ 0))
for u in Sequent.([:(P(1) ⊢ Q(1,2)), :(2P(1) ⊢ Q(1,2)), :(P(1) ⊢ 0), :(ψ ⊢ Q(1,2))])
  @test ((t ∸ s) ≼ u) == (t ≼ s + u)
end

# Atoms
#------

@test length(atoms(Σ, ∅)) == 2*(1+1+2) # ψ, P(1), Q(1,2), Q(2,1), each signed
@test length(atoms(Σ, Set([1]))) == 2*(1+2+6)  # P(1),P(2); Q on {1,2,3} injectively
@test Set(atoms(Sequent(:(P(1) + ψ ⊢ P(1))))) == Set(Sequent.([:(P(1) ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ P(1))]))
@test balanced_pairs(Sequent(:(P(1) + ψ ⊢ P(1)))) == [Sequent(:(P(1) ⊢ P(1)))]

# Set-based sequents
####################
default_multiplicity!(𝔹)

S = Sequent{𝔹}
s′ = S([P₁],[Q₁₂])

# Constructors
@test s′ == S(:(P(1) ⊢ Q(1,2)))
@test s′ == Sequent(Set([P₁]), Set([Q₁₂]))               # sets give 𝔹 coefficients
@test Sequent(Set([P₁]), Set([Q₁₂])) isa Sequent{𝔹}
@test s′ != s                                            # never equal across K
@test s′.supp == Set([1,2])
@test_throws ErrorException S([P₁, P₁], [Q₁₂])           # max multiplicity = 1
@test_throws ErrorException S(:(2P(1) ⊢ Q(1,2)))         # ... also when parsed
@test S(:(P(1))) == S(:(0 ⊢ P(1)))                       # no `⊢`: a conclusion
@test S(:(ψ + P(1) ⊢ ψ)) == S([ψ, P₁], [ψ])              # bare nullary predicate
@test S(:(0 ⊢ 0)) == S() == zero(S) == zero(s′)
@test iszero(zero(S)) && !iszero(s′)
@test zero(S) isa Sequent{𝔹}
@test S(s′) === s′
@test_throws ErrorException S(MultiSet([P₁, P₁]), MultiSet(Term[]))
@test_throws ErrorException S(MultiSet(Term[]), MultiSet([P₁, P₁]))

# Length counts each term once
@test length(S(:(P(1) + Q(1,2) ⊢ ψ))) == 3
@test length(S(:(P(1) ⊢ P(1)))) == 2              # opposite signs are distinct

# Rendering: no multiplicity prefixes
@test sprint(show, s′) == (default_view()==Int ? "P⁺₁Q⁻₁₂" : "P⁺(a)Q⁻(a,b)")
@test sprint(show, S(:(ψ ⊢ 0))) == "ψ⁺"                   # nullary: no parentheses
@test sprint(show, zero(S)) == "0"

# Order: sub-set on both sides
@test S(:(P(1) ⊢ 0)) ≼ s′
@test !(S(:(P(2) ⊢ 0)) ≼ s′)
@test zero(S) ≼ s′ && !(s′ ≼ zero(S))

# `isless` is a total order on 𝔹 sequents too, so they can be sorted
@test sort([s′, zero(S), S(:(P(1) ⊢ 0))]) == sort([S(:(P(1) ⊢ 0)), s′, zero(S)])
@test allunique(sort([s′, zero(S), S(:(P(1) ⊢ 0))]))

# Monoid: addition is union, idempotent, commutative, with unit 0
a, b = S(:(P(1) ⊢ ψ)), S(:(P(1) + Q(1,2) ⊢ 0))
@test a + b == S(:(P(1) + Q(1,2) ⊢ ψ))
@test a + a == a
@test a + b == b + a
@test a + zero(S) == a
@test a ≼ a + b && b ≼ a + b
@test (a + b).supp == Set([1,2])
# ℕ and 𝔹 never mix
@test_throws MethodError S(:(P(1) ⊢ 0)) + Sequent{ℕ}(:(P(1) ⊢ 0))   

# `q : ℕ[X]² → 𝔹[X]²` (the support) and `ι` back
@test S(Sequent{ℕ}(:(2P(1) + ψ ⊢ 3ψ))) == S(:(P(1) + ψ ⊢ ψ))
@test Sequent{ℕ}(S(:(P(1) + ψ ⊢ ψ))) == Sequent(:(P(1) + ψ ⊢ ψ))
for x in S.([:(P(1) + ψ ⊢ ψ), :(0 ⊢ 0), :(Q(1,2) ⊢ Q(2,1))])
  @test S(Sequent{ℕ}(x)) == x                            # q ∘ ι = id
end
x, y = Sequent(:(P(1) ⊢ ψ)), Sequent(:(P(1) + Q(1,2) ⊢ 0))
@test S(x + y) == S(x) + S(y)                            # q is a monoid map ...
@test Sequent{ℕ}(S(:(P(1) ⊢ 0)) + S(:(P(1) ⊢ 0))) !=
      Sequent{ℕ}(S(:(P(1) ⊢ 0))) + Sequent{ℕ}(S(:(P(1) ⊢ 0)))  # ... ι is not

# Subtraction, truncated subtraction, join and meet
@test s′ - S(:(P(1) ⊢ 0)) == S(:(0 ⊢ Q(1,2)))
@test s′ - s′ == zero(S)
@test_throws ErrorException S(:(P(1) ⊢ 0)) - S(:(P(2) ⊢ 0))
@test S(:(P(1) ⊢ 0)) + (s′ - S(:(P(1) ⊢ 0))) == s′
# `t - s` is the least solution of `s + u = t`, not the unique one
t₁, s₁ = S(:(P(1) + ψ ⊢ Q(1,2))), S(:(P(1) ⊢ Q(1,2)))
@test t₁ - s₁ == S(:(ψ ⊢ 0))
@test all(s₁ + u == t₁ for u in [S(:(ψ ⊢ 0)), S(:(ψ + P(1) ⊢ 0)), S(:(ψ ⊢ Q(1,2))), t₁])
@test t₁ ∸ S(:(P(1) + P(2) ⊢ 0)) == S(:(ψ ⊢ Q(1,2)))
@test S(:(P(1) + ψ ⊢ 0)) ∧ S(:(ψ ⊢ P(1))) == S(:(ψ ⊢ 0))
@test s′ ∸ S(:(P(1) + P(2) ⊢ 0)) == S(:(0 ⊢ Q(1,2)))
@test S(:(P(1) ⊢ 0)) ∸ s′ == zero(S)
@test Set([s′, a]) ∸ S(:(P(1) ⊢ 0)) == Set([S(:(0 ⊢ Q(1,2))), S(:(0 ⊢ ψ))])
@test a ∨ b == a + b                                     # join is union
@test a ∧ b == S(:(P(1) ⊢ 0))
@test a ∧ zero(S) == zero(S)
@test (a ∧ b) ≼ a && a ≼ (a ∨ b)
# `u ≽ t ∸ s  iff  s + u ≽ t`, now with 𝔹 coefficients
t′, s″ = S(:(P(1) ⊢ Q(1,2))), S(:(P(1) + ψ ⊢ 0))
for u in S.([:(P(1) ⊢ Q(1,2)), :(P(1) ⊢ 0), :(ψ ⊢ Q(1,2)), :(0 ⊢ Q(1,2)), :(0 ⊢ 0)])
  @test ((t′ ∸ s″) ≼ u) == (t′ ≼ s″ + u)
end

# Generators with 𝔹 coefficients
@test refl_sequents(𝔹, Σ) == S.([:(ψ⊢ψ),:(P(1)⊢P(1)),:(Q(1,2)⊢Q(1,2))])
@test eltype(refl_sequents(𝔹, Σ)) == Sequent{𝔹}

@test length(atoms(𝔹, Σ, ∅)) == 2*(1+1+2)
@test length(atoms(𝔹, Σ, Set([1]))) == 2*(1+2+6)
@test Set(atoms(𝔹, Σ, ∅)) == Set(S.(atoms(Σ, ∅)))       # q of the ℕ atoms
@test eltype(atoms(𝔹, Σ, ∅)) == Sequent{𝔹}
@test Set(atoms(S(:(P(1) + ψ ⊢ P(1))))) == Set(S.([:(P(1) ⊢ 0), :(ψ ⊢ 0), :(0 ⊢ P(1))]))
@test balanced_pairs(S(:(P(1) + ψ ⊢ P(1)))) == [S(:(P(1) ⊢ P(1)))]
@test Set(balanced_pairs(𝔹, Σ, ∅)) == Set(S.(balanced_pairs(Σ, ∅)))
@test eltype(balanced_pairs(𝔹, Σ, ∅)) == Sequent{𝔹}

# Small sequents: the image of the ℕ ones under q, so fewer of them
ΣP = Signature([P])
smallℕ, small𝔹 = small_sequents(ℕ, ΣP, [1], 2), small_sequents(𝔹, ΣP, [1], 2)
@test Set(small𝔹) == Set(S.(smallℕ))
@test allunique(small𝔹)
@test length(smallℕ) == 6          # 0, P⁺, P⁻, 2P⁺, P⁺P⁻, 2P⁻
@test length(small𝔹) == 4          # 0, P⁺, P⁻, P⁺P⁻
@test eltype(small𝔹) == Sequent{𝔹}
@test small_sequents(ΣP, [1], 2) == small𝔹



# Symbol / Natural number bijection
###################################

@test name_to_int(:a) == 1 && name_to_int(:z) == 26
@test name_to_int(:aa) == 27 && name_to_int(:ab) == 28 && name_to_int(:ba) == 53
@test int_to_name(1) == :a && int_to_name(26) == :z && int_to_name(27) == :aa
@test all(name_to_int(int_to_name(n)) == n for n in 1:1000)
@test allunique(int_to_name.(1:1000))
@test_throws ErrorException name_to_int(:A)
@test_throws ErrorException name_to_int(:a1)
@test_throws ErrorException int_to_name(0)

end # module
