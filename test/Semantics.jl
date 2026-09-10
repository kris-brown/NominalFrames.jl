module TestSemantics

using Test, NominalFrames

ψ′, P′, Q′ = ps = Predicate.([:ψ,:P,:Q], [0,1,2])
Σ = Signature(ps)

S(x) = Sequent(x)
S(x::Sequent) = x
C(κ, μ, λ, ctx) = Constructible(Set{Sequent}(S.(κ)), Set{Sequent}(S.(μ)),
                                Set{Sequent}(S.(λ)), Set{Int}(ctx))

refl = refl_sequents(Σ)
s₀ = S(:(P(1) ⊢ Q(1,2)))
I𝒪 = 𝒲(refl)
I𝒲 = 𝒲([refl; s₀])
I𝒟 = κ([s₀]) ∪ I𝒪

∅, Γ1, Γ12 = Set{Int}(), Set([1]),  Set([1,2])
⊤, ⊥ = top(∅), bottom(∅)

# The three frames, whose closed roles form the Girard quantales 𝒢
𝒢𝒪, 𝒢𝒲, 𝒢𝒟 = Frame.(Ref(Σ), [I𝒪, I𝒲, I𝒟])

ts = small_sequents(Σ, [1, 2, 3], 2)
A ≃ B = normal_form(A, Σ) == normal_form(B, Σ)   # equality of the presented roles

# The Girard quantale and its constants
#--------------------------------------

@test 𝒢𝒟.sequents == ℛ([s₀]) ∪ I𝒪       # I𝒟 in normal form
# 0 = M^⊥ and 1 = ⊥^⊥
@test zero_role(𝒢𝒪, ∅) ≃ I𝒪 && unit_role(𝒢𝒪, ∅) ≃ ⊤
@test zero_role(𝒢𝒲, ∅) ≃ I𝒲 && unit_role(𝒢𝒲, ∅) ≃ ⊤
@test zero_role(𝒢𝒟, ∅) ≃ I𝒪 && unit_role(𝒢𝒟, ∅) ≃ κ([:(0 ⊢ 0)]) ∪ I𝒪
# Closure is a closure operator and ⊥ is closed
for G in [𝒢𝒪, 𝒢𝒲, 𝒢𝒟], A in [κ([:(P(1) ⊢ 0)], Γ1), 𝒲([:(0 ⊢ Q(1,2))], Γ12),
                             ℛ([:(ψ ⊢ 0)])]
  A⊥⊥ = closure(G, A)
  @test all(t ∈ A⊥⊥ for t in ts if t ∈ A)
  @test roles_equal(G, closure(G, A⊥⊥), A⊥⊥)
  @test roles_equal(G, closure(G, point(G, A.context)), point(G, A.context))
end

# Minkowski product and union
#----------------------------

for A in [C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], []), 𝒲([:(Q(1,2) ⊢ 0)], Γ1),
          C([:(P(1) ⊢ P(1))], [], [:(0 ⊢ ψ)], Γ1)],
    B in [κ([:(0 ⊢ Q(1,2))]), ℛ([:(P(1) ⊢ 0)], Γ1), ⊤, ⊥]
  AB = minkowski(A, B)
  for t in ts
    # t ∈ A ⊗ B iff t = a + b with a ∈ A, b ∈ B: search over sub-multisets a ≼ t
    @test (t ∈ AB) == any(a ∈ A && (t - a) ∈ B for a in ts if a ≼ t)
    @test (t ∈ A ∪ B) == (t ∈ A || t ∈ B)
  end
end
@test minkowski(⊤, κ([:(P(1) ⊢ 0)])) == 𝒲([:(P(1) ⊢ 0)])  # ⊤ ⊗ A = 𝒲(A)
@test minkowski(κ([:(P(1) ⊢ 0)]), κ([:(0 ⊢ Q(1,2))])).strict ==
      Set(S.([:(P(1) ⊢ Q(1,2)), :(P(1) ⊢ Q(2,1)), :(P(1) ⊢ Q(2, 3))]))
@test unfreeze(κ([:(Q(2, 3) ⊢ 0), :(Q(1,2) ⊢ 0)], Γ1), ∅) == κ([:(Q(1,2) ⊢ 0)])

# The table of (-)^⊥ computations 
#--------------------------------

# Row ∅: A = {φ⁺} (our ψ)
A = κ([:(ψ ⊢ 0)])
for G in [𝒢𝒪, 𝒢𝒲, 𝒢𝒟]
  @test perp(G, A) ≃ 𝒲([:(0 ⊢ ψ)]) ∪ zero_role(G, ∅)
  @test closure(G, A) ≃ 𝒲([:(ψ ⊢ 0)]) ∪ zero_role(G, ∅)
end
# Row {a}: A = {P⁺_a}_a
A = κ([:(P(1) ⊢ 0)], Γ1)
z(G) = zero_role(G, Γ1)
𝒢𝒪0, 𝒢𝒲0, 𝒢𝒟0 = z.([𝒢𝒪,𝒢𝒲,𝒢𝒟])
@test perp(𝒢𝒪, A) ≃ 𝒲([:(0 ⊢ P(1))], Γ1) ∪ 𝒢𝒪0
@test closure(𝒢𝒪, A) ≃ 𝒲([:(P(1) ⊢ 0)], Γ1) ∪ 𝒢𝒪0
@test perp(𝒢𝒲, A) ≃ 𝒲([:(0 ⊢ P(1)), :(0 ⊢ Q(1,2))], Γ1) ∪ 𝒢𝒲0
@test closure(𝒢𝒲, A) ≃ 𝒲([:(P(1) ⊢ 0)], Γ1) ∪ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ C([:(0 ⊢ Q(1,2))], [], [:(0 ⊢ P(1))], Γ1) ∪ 𝒢𝒟0
@test closure(𝒢𝒟, A) ≃ κ([:(P(1) ⊢ 0)], Γ1) ∪ 𝒢𝒟0

# Row {a,b}: A = {Q⁻_ab}
A = κ([:(0 ⊢ Q(1,2))], Γ12)
z2(G) = zero_role(G, Γ12)
𝒢𝒪0, 𝒢𝒲0, 𝒢𝒟0 = z2.([𝒢𝒪,𝒢𝒲,𝒢𝒟])

@test perp(𝒢𝒪, A) ≃ 𝒲([:(Q(1,2) ⊢ 0)], Γ12) ∪ 𝒢𝒪0
@test closure(𝒢𝒪, A) ≃ 𝒲([:(0 ⊢ Q(1,2))], Γ12) ∪ 𝒢𝒪0
@test perp(𝒢𝒲, A) ≃ 𝒲([:(P(1) ⊢ 0), :(Q(1,2) ⊢ 0)], Γ12) ∪ 𝒢𝒲0
@test closure(𝒢𝒲, A) ≃ 𝒲([:(0 ⊢ Q(1,2))], Γ12) ∪ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ C([:(P(1) ⊢ 0)], [], [:(Q(1,2) ⊢ 0)], Γ12) ∪ 𝒢𝒟0
@test closure(𝒢𝒟, A) ≃ C([:(0 ⊢ Q(1,2))], [], [:(0 ⊢ P(1) + Q(1,2))], Γ12) ∪ 𝒢𝒟0

# Row {b}: A = {P⁺_= Q⁻_=b}_b, the orbit of s₀ with b = 2 frozen
A = κ([s₀], [2])
zb(G) = zero_role(G, Set([2]))
𝒢𝒲0, 𝒢𝒟0 = zb.([𝒢𝒲,𝒢𝒟])

@test perp(𝒢𝒪, A) ≃ zb(𝒢𝒪) && closure(𝒢𝒪, A) ≃ top(Set([2]))
@test perp(𝒢𝒲, A) ≃ top(Set([2])) && closure(𝒢𝒲, A) ≃ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ κ([:(0 ⊢ 0)], [2]) ∪ 𝒢𝒟0
# The table's `{s₀}` here is the full orbit P⁺₋Q⁻₋₌, so A⊥⊥ = I𝒟 itself
@test closure(𝒢𝒟, A) ≃ point(𝒢𝒟, Set([2]))

# Row {b}: 𝒲(A)
A = 𝒲([s₀], [2])
@test perp(𝒢𝒪, A) ≃ zb(𝒢𝒪) && closure(𝒢𝒪, A) ≃ top(Set([2]))
@test perp(𝒢𝒲, A) ≃ top(Set([2])) && closure(𝒢𝒲, A) ≃ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ 𝒢𝒟0 && closure(𝒢𝒟, A) ≃ top(Set([2]))

# Pairs and connectives
#----------------------

for G in [𝒢𝒪, 𝒢𝒲, 𝒢𝒟]
  p, q, r = RolePair(G, :(P(1))), RolePair(G, :(Q(1,2))), RolePair(G, :ψ)
  @test context(p) == Γ1 && context(q) == Γ12 && context(r) == ∅
  @test ¬¬p == p
  @test p ⊗ q == q ⊗ p && p ⊕ q == q ⊕ p && (p & q) == (q & p)
  @test ¬(p ⊗ q) == ¬p ⅋ ¬q && ¬(p ⊕ q) == ¬p & ¬q # De Morgan by construction
  @test lolli(p, q) == ¬p ⅋ q && (p ⇒ q) == ¬p ∨ q
  @test context(p ⊗ q) == Γ12
  # ⊕ is above both, & below both, in each component the right way round
  pq = p ⊕ q
  @test all(t ∈ pq.prem for t in ts if t ∈ p.prem || t ∈ q.prem)
  @test all(t ∈ p.conc && t ∈ q.conc for t in ts if t ∈ pq.conc)
  # Every atom entails itself, since refl ⊆ I
  @test (p ⊩ p) && (q ⊩ q) && (r ⊩ r)
  @test ([p, r] ⊩ [r]) && ([r] ⊩ [r, q])
end

# Conservativity: ⊨ ∀Θ. ⨂aᵢ ⊸ ⅋bⱼ iff the sequent is in I
#-------------------------------------------------------------------------------

function formula(G::Frame, s::Sequent)
  atoms(d) = [RolePair(G, t) for (t, n) in d for _ in 1:n]
  prem, conc = atoms(s.prem), atoms(s.conc)
  isempty(prem) && return reduce(⅋, conc)
  isempty(conc) && return ¬reduce(⊗, prem)
  lolli(reduce(⊗, prem), reduce(⅋, conc))
end

for (G, I) in zip([𝒢𝒪, 𝒢𝒲, 𝒢𝒟], [I𝒪, I𝒲, I𝒟]),
    s in S.([:(P(1) ⊢ Q(1,2)), :(P(1) ⊢ Q(2,1)), :(ψ ⊢ ψ), :(P(1) ⊢ P(1)), :(ψ ⊢ P(1)),
             :(P(1) + Q(1,2) ⊢ Q(1,2)), :(Q(1,2) ⊢ Q(2,1)), :(P(1) + ψ ⊢ Q(1,2) + ψ)])
  φ = formula(G, s)
  @test ([] ⊩ φ) == (s ∈ I)
  # Quantifying over all the names leaves theoremhood alone: I is equivariant
  @test ([] ⊩ ∀(s.supp, φ)) == (s ∈ I)
  # ... and as a consequence relation, premises on the left
  @test ([RolePair(G, t) for (t, _) in s.prem] ⊩ [RolePair(G, t) for (t, _) in s.conc]) == (s ∈ I)
end

# The semantic evaluation example: ⊨_{b} ∀a. P(a) ⊸ Q(a,b)
#-------------------------------------------------------------------------

for (G, expected) in [(𝒢𝒪, false), (𝒢𝒲, true), (𝒢𝒟, true)]
  φ = forall(lolli(RolePair(G, :(P(1))), RolePair(G, :(Q(1,2)))), Γ1)
  @test context(φ) == Set([2])
  @test ([] ⊩ φ) == expected
end
# The inner conclusory role, as computed there: 𝒲(P⁺_aQ⁻_ab) ∪ 0, resp. {P⁺_aQ⁻_ab} ∪ 0
for (G, inner) in [(𝒢𝒪, 𝒲([s₀], Γ12)), (𝒢𝒲, 𝒲([s₀], Γ12)), (𝒢𝒟, κ([s₀], Γ12))]
  φ = lolli(RolePair(G, :(P(1))), RolePair(G, :(Q(1,2))))
  @test Constructible(φ.conc) ≃ inner ∪ zero_role(G, Γ12)
end

# The prime-minister example
#---------------------------

φ₀, J = Predicate.([:φ, :J], [0,1])
Σ′ = Signature([φ₀, P′, J])
λℛ = refl_sequents(Σ′)
𝒫𝒥 = Frame(Σ′, κ([:(P(1) ⊢ J(1))]) ∪ 𝒲(λℛ))
A ≃′ B = normal_form(A, Σ′) == normal_form(B, Σ′)

Pa, Ja, φ = RolePair(𝒫𝒥, :(P(1))), RolePair(𝒫𝒥, :(J(1))), RolePair(𝒫𝒥, :φ)
zero0 = zero_role(𝒫𝒥, ∅)
@test zero0 ≃′ 𝒲(λℛ)                    # 0 = I_ℛ
@test Constructible(φ.prem) ≃′ 𝒲([:(φ ⊢ 0)]) ∪ zero0   # ⟦φ⟧ = ⟨𝒲(φ⁺) ∨ 0, 𝒲(φ⁻) ∨ 0⟩
@test Constructible(φ.conc) ≃′ 𝒲([:(0 ⊢ φ)]) ∪ zero0
@test [] ⊮ φ
@test Constructible(Pa.prem) ≃′ C([:(P(1) ⊢ 0)], [], [:(P(1) + J(1) ⊢ 0)], Γ1) ∪ zero_role(𝒫𝒥, Γ1)
@test Constructible(Pa.conc) ≃′ 𝒲([:(0 ⊢ P(1))], Γ1) ∪ zero_role(𝒫𝒥, Γ1)
# Both quantified atoms collapse to 0 in the relevant component
@test Constructible(∃(Γ1, Pa).conc) ≃′ zero0
@test Constructible(∀(Γ1, Pa).prem) ≃′ zero0
# Theorems produced by the quantifiers alone ...
@test [] ⊩ lolli(∀(Γ1, Pa), φ)
@test [] ⊩ lolli(φ, ∃(Γ1, Pa))
@test [] ⊩ exists(Pa, Γ1)
# ... while at the atomic level φ neither entails nor follows
@test ([]⊮lolli(φ, Pa)) && ([]⊮lolli(Pa, φ))
@test (φ ⊮ Pa) && (Pa ⊮ φ)
# The informative theorems: ∀x. P(x) ⊸ J(x), but not ∀x∀y. P(x) ⊗ P(y) ⊸ J(x)
@test [] ⊩ (∀(Γ1, lolli(Pa, Ja)))
@test Pa ⊩ Ja
Pb = RolePair(𝒫𝒥, :(P(2)))
@test [] ⊮ ∀(Γ12, lolli(Pa ⊗ Pb, Ja))
@test [Pa, Pb] ⊮ [Ja]

end # module
