module TestOrbits

using Test, NominalFrames
using NominalFrames: rename, injections, fresh

ψ′,P′,Q′,R′ = ps = Predicate.([:ψ,:P,:Q,:R], [0,1,2,2])
ψ, P₁, Q₁₂, R₁₂ = Term.(ps)
P(i) = Term(P′, [i])
Q(i,j) = Term(Q′, [i,j])
R(i,j) = Term(R′, [i,j])

# Frequently occurring contexts
const ∅ = Set{Int}()  
const Γ1 = Set([1])

default_multiplicity!(ℕ)



# Orbits
########

# Orbits where the set of names is implicitly only the names mentioned + frozen names
@test orbit(P(1), Γ1) == Set([P(1)])
@test orbit(ψ, ∅) == Set([ψ])
@test orbit(Q₁₂, Γ1) == orbit(Q₁₂, Set([2])) == Set([Q₁₂])
@test orbit(Q₁₂, ∅) == Set([Q₁₂, Q(2,1)])


# {Q⁻₁₌}₁ re-presented over the enlarged context {1,2} PLUS a fresh name
@test orbit(Q₁₂, Γ1, Set([1,2,3])) == Set([Q₁₂, Q(1,3)])

@test same_orbit(Q(1, 9), Q(1,4), Γ1)
@test !same_orbit(Q(1, 9), Q(9, 1), Γ1)
@test same_orbit(Q(1, 9), Q(9, 1), ∅)



# Minimal elements of the orbit
#------------------------------

@test canonicalize(Q(5, 3), ∅) == Q₁₂
@test canonicalize(Q(5, 3), Γ1) == Q(2, 3)
@test canonicalize(Q(1, 7), Γ1) == Q₁₂
@test canonicalize(ψ, ∅) == ψ

const s₀ = Sequent(:(P(1) ⊢ Q(1,2))) #  P⁺ₐQ⁻ₐᵦ

@test canonicalize(s₀, Γ1) == s₀
@test canonicalize(Sequent(:(P(4) ⊢ Q(4, 7))), ∅) == s₀
@test canonicalize(Sequent(:(P(3) ⊢ Q(3,2))), Set([2])) == s₀

# Orbits of sequents 
#-------------------

# Frozen at {1}, only 2 moves; frozen at ∅, P⁺₂Q⁻₂₁ joins in.
@test orbit(s₀, Γ1) == Set([s₀])
@test orbit(s₀, Γ1, Set([1, 2, 3])) ==
      Set([s₀, Sequent(:(P(1) ⊢ Q(1,3)))])
@test orbit(s₀, ∅) == Set([s₀, Sequent(:(P(2) ⊢ Q(2,1)))])

@test same_orbit(s₀, Sequent(:(P(1) ⊢ Q(1, 9))), Γ1)
@test !same_orbit(s₀, Sequent(:(P(2) ⊢ Q(2, 9))), Γ1)

# Terms sharing a predicate symbol have no canonical order among themselves, so
# the greedy pass must carry every arrangement that ties. Reading the Q terms in
# either order renders the group as `Q(1,2) + Q(3,4)`, but the two readings name
# things differently (1 ↦ 1 vs 3 ↦ 1), and only the P⁺(-) tells them apart.
#
# Reading `Q(1,2)` first fixes the identity renaming and leaves `P(3)`, which is
# what a single left-to-right pass returns. The least element of the orbit is
# reached only by reading `Q(3,4)` first.
@test canonicalize(Sequent(:(Q(1,2) + Q(3,4) ⊢ P(3))), ∅) ==
      Sequent(:(Q(1,2) + Q(3,4) ⊢ P(1)))
# Now the first Q instance now needs to be interpreted as coming first
@test canonicalize(Sequent(:(Q(1,2) + Q(3,4) ⊢ P(1))), ∅) ==
      Sequent(:(Q(1,2) + Q(3,4) ⊢ P(1)))

# Multiplicity is part of a group's rendering, not just the arguments
@test canonicalize(Sequent(:(Q(1,2) + 2Q(3,4) ⊢ 0)), ∅) ==
      Sequent(:(Q(1,2) + 2Q(3,4) ⊢ 0))
@test canonicalize(Sequent(:(2Q(1,2) + Q(3,4) ⊢ 0)), ∅) ==
      Sequent(:(Q(1,2) + 2Q(3,4) ⊢ 0))

# Canonical forms are a complete orbit invariant
seqs = Sequent.([:(P(1) ⊢ Q(1,2)), :(Q(3,4) ⊢ Q(4,3)),
                 :(Q(1,2) + Q(2, 3) ⊢ P(3)), :(Q(3,2) + Q(2,1) ⊢ P(1)),
                 :(P(1) + 2Q(1,2) ⊢ R(2, 3) + Q(3,1)),
                 :(Q(1,2) + Q(3,4) + Q(5, 6) ⊢ P(6) + R(1, 5))])

for s in seqs, frozen in [∅, Γ1, Set([1, 2])]
  c = canonicalize(s, frozen)
  for s′ in orbit(s, frozen, s.supp ∪ Set(1:4))
    @test canonicalize(s′, frozen) == c
    @test same_orbit(s, s′, frozen)
  end
end

# `canonicalize` reads names off in one canonical pass rather than searching all
# renamings; check it against the exhaustive search it replaces.
""" Least element over *every* bijection of the moving names onto the least
available ones """
function oracle(s::Sequent, frozen::Set{Int})
  moving = sort(collect(setdiff(s.supp, frozen)))
  minimum(rename(s, ρ) for ρ in injections(moving, fresh(frozen, length(moving))))
end

for s in seqs, frozen in [Set{Int}(), Γ1, Set([2]), Set([1, 2]), Set([3, 5])]
  @test canonicalize(s, frozen) == oracle(s, frozen)
end

# Finite representatives of an orbit
#-----------------------------------

""" The `G_Δ`-orbits met, as a set of canonical forms """
orbits(xs, Δ) = Set{Sequent}(canonicalize(x, Δ) for x in xs)

# `P(1) ⊢ P(1)` at ∅ pins 1 into Δ = {1} or leaves it out.
@test Set(refine(Sequent(:(P(1) ⊢ P(1))), ∅, Γ1)) ==
      Set(Sequent.([:(P(1) ⊢ P(1)), :(P(2) ⊢ P(2))]))
# Neither, either, but not both names of `Q(1,2)` can be pinned into Δ = {2}.
# The unpinned names go to fresh names outside Γ ∪ Δ ∪ supp(g) = {1, 2}.
@test Set(refine(Sequent(:(Q(1,2) ⊢ 0)), ∅, Set([2]))) ==
      Set(Sequent.([:(Q(3,4) ⊢ 0), :(Q(2, 3) ⊢ 0), :(Q(3,2) ⊢ 0)]))
@test orbits(refine(Sequent(:(Q(1,2) ⊢ 0)), ∅, Set([2])), Set([2])) ==
      Set(Sequent.([:(Q(1,3) ⊢ 0), :(Q(2,1) ⊢ 0), :(Q(1,2) ⊢ 0)]))
# Nothing to do when no name moves.
@test refine(Sequent(:(P(1) ⊢ 0)), Γ1, Set([2])) == [Sequent(:(P(1) ⊢ 0))]
# A symmetric generator reaches the same orbit by two partial injections.
@test length(refine(Sequent(:(P(1) + P(2) ⊢ 0)), ∅, Set([3]))) == 3
@test length(orbits(refine(Sequent(:(P(1) + P(2) ⊢ 0)), ∅, Set([3])), Set([3]))) == 2
@test_throws ErrorException refine(s₀, Γ1, Γ1)

# Relative to the names `N` of a fixed element, names of `Γ` are not new.
@test Set(refine(Set([Sequent(:(Q(1,2) ⊢ 0))]), Γ1, Set([1, 2]))) ==
      Set(Sequent.([:(Q(1,3) ⊢ 0), :(Q(1,2) ⊢ 0)]))

# `refine(g, Γ, Δ)` meets every `G_{Γ+Δ}`-orbit of `G_Γ • g`:
# every element of the orbit with names in a bounded pool lands in one of them.
for s in seqs, Γ in [∅, Γ1, Set([1, 2])], Δ in [∅, Set([3]), Set([3, 5]), Set([2, 5])]
  Δ = setdiff(Δ, Γ)
  full = Γ ∪ Δ
  reps = orbits(refine(s, Γ, Δ), full)
  length(s.supp) ≤ 4 || continue  # the exhaustive part only for small sequents
  for s′ in orbit(s, Γ, s.supp ∪ full ∪ Set([7]))
    @test canonicalize(s′, full) ∈ reps
  end
end

end # module
