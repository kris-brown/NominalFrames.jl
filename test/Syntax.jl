module TestSyntax 

using NominalFrames, Test

using NominalFrames: balanced_pairs

ψ′, P, Q = Predicate(:ψ,0),Predicate(:P,1),Predicate(:Q,2)
Σ = Signature([ψ′, P, Q])

@test length(Σ) == 3

ψ, P₁,Q₁₂ = Term.(Σ)

s = Sequent([P₁],[Q₁₂])
@test s == Sequent(:(P(1) ⊢ Q(1,2)))
@test s+s == Sequent([P₁,P₁],[Q₁₂,Q₁₂])

@test refl_sequents(Σ) == Sequent.([:(ψ⊢ψ),:(P(1)⊢P(1)),:(Q(1,2)⊢Q(1,2))])

# Arithmetic 

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

end # module
