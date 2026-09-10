module TestSemantics

using Test, NominalFrames

default_multiplicity!(ℕ)

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
I𝒟 = κ(s₀) ∪ I𝒪

∅, Γ1, Γ12 = Set{Int}(), Set([1]),  Set([1,2])
⊤, ⊥ = top(∅), bottom(∅)

# The three frames, whose closed roles form the Girard quantales 𝒢
𝒢𝒪, 𝒢𝒲, 𝒢𝒟 = Frame.(Ref(Σ), [I𝒪, I𝒲, I𝒟])

ts = small_sequents(Σ, [1, 2, 3], 2)
A ≃ B = normal_form(A, Σ) == normal_form(B, Σ)   # equality of the presented roles

# The Girard quantale and its constants
#--------------------------------------

@test 𝒢𝒟.sequents == ℛ(s₀) ∪ I𝒪       # I𝒟 in normal form
# 0 = M^⊥ and 1 = ⊥^⊥
@test zero_role(𝒢𝒪, ∅) ≃ I𝒪 && unit_role(𝒢𝒪, ∅) ≃ ⊤
@test zero_role(𝒢𝒲, ∅) ≃ I𝒲 && unit_role(𝒢𝒲, ∅) ≃ ⊤
@test zero_role(𝒢𝒟, ∅) ≃ I𝒪 && unit_role(𝒢𝒟, ∅) ≃ κ([:(0 ⊢ 0)]) ∪ I𝒪
# Closure is a closure operator and ⊥ is closed
for G in [𝒢𝒪, 𝒢𝒲, 𝒢𝒟], A in [κ(:(P(1) ⊢ 0), Γ1), 𝒲(:(0 ⊢ Q(1,2)), Γ12),
                             ℛ(:(ψ ⊢ 0))]
  A⊥⊥ = closure(G, A)
  @test all(t ∈ A⊥⊥ for t in ts if t ∈ A)
  @test roles_equal(G, closure(G, A⊥⊥), A⊥⊥)
  @test roles_equal(G, closure(G, point(G, A.context)), point(G, A.context))
end

# Minkowski product and union
#----------------------------

for A in [C([:(P(1) ⊢ 0)], [:(ψ ⊢ 0)], [], ∅), 𝒲(:(Q(1,2) ⊢ 0), Γ1),
          C([:(P(1) ⊢ P(1))], [], [:(0 ⊢ ψ)], Γ1)],
    B in [κ(:(0 ⊢ Q(1,2))), ℛ(:(P(1) ⊢ 0), Γ1), ⊤, ⊥]
  AB = A ⊗ₘ B
  for t in ts
    # t ∈ A ⊗ B iff t = a + b with a ∈ A, b ∈ B: search over sub-multisets a ≼ t
    @test (t ∈ AB) == any(a ∈ A && (t - a) ∈ B for a in ts if a ≼ t)
    @test (t ∈ A ∪ B) == (t ∈ A || t ∈ B)
  end
end
@test (⊤ ⊗ₘ κ(:(P(1) ⊢ 0))) == 𝒲(:(P(1) ⊢ 0))  # ⊤ ⊗ A = 𝒲(A)
@test (κ(:(P(1) ⊢ 0)) ⊗ₘ κ(:(0 ⊢ Q(1,2)))).strict ==
      Set(S.([:(P(1) ⊢ Q(1,2)), :(P(1) ⊢ Q(2,1)), :(P(1) ⊢ Q(2, 3))]))
@test unfreeze(κ([:(Q(2, 3) ⊢ 0), :(Q(1,2) ⊢ 0)], Γ1), ∅) == κ(:(Q(1,2) ⊢ 0))

# The table of (-)^⊥ computations 
#--------------------------------

# Row ∅: A = {φ⁺} (our ψ)
A = κ(:(ψ ⊢ 0))
for G in [𝒢𝒪, 𝒢𝒲, 𝒢𝒟]
  @test perp(G, A) ≃ 𝒲(:(0 ⊢ ψ)) ∪ zero_role(G, ∅)
  @test closure(G, A) ≃ 𝒲(:(ψ ⊢ 0)) ∪ zero_role(G, ∅)
end
# Row {a}: A = {P⁺_a}_a
A = κ(:(P(1) ⊢ 0), Γ1)
z(G) = zero_role(G, Γ1)
𝒢𝒪0, 𝒢𝒲0, 𝒢𝒟0 = z.([𝒢𝒪,𝒢𝒲,𝒢𝒟])
@test perp(𝒢𝒪, A) ≃ 𝒲(:(0 ⊢ P(1)), Γ1) ∪ 𝒢𝒪0
@test closure(𝒢𝒪, A) ≃ 𝒲(:(P(1) ⊢ 0), Γ1) ∪ 𝒢𝒪0
@test perp(𝒢𝒲, A) ≃ 𝒲([:(0 ⊢ P(1)), :(0 ⊢ Q(1,2))], Γ1) ∪ 𝒢𝒲0
@test closure(𝒢𝒲, A) ≃ 𝒲(:(P(1) ⊢ 0), Γ1) ∪ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ C([:(0 ⊢ Q(1,2))], [], [:(0 ⊢ P(1))], Γ1) ∪ 𝒢𝒟0
@test closure(𝒢𝒟, A) ≃ κ(:(P(1) ⊢ 0), Γ1) ∪ 𝒢𝒟0

# Row {a,b}: A = {Q⁻_ab}
A = κ(:(0 ⊢ Q(1,2)), Γ12)
z2(G) = zero_role(G, Γ12)
𝒢𝒪0, 𝒢𝒲0, 𝒢𝒟0 = z2.([𝒢𝒪,𝒢𝒲,𝒢𝒟])

@test perp(𝒢𝒪, A) ≃ 𝒲(:(Q(1,2) ⊢ 0), Γ12) ∪ 𝒢𝒪0
@test closure(𝒢𝒪, A) ≃ 𝒲(:(0 ⊢ Q(1,2)), Γ12) ∪ 𝒢𝒪0
@test perp(𝒢𝒲, A) ≃ 𝒲([:(P(1) ⊢ 0), :(Q(1,2) ⊢ 0)], Γ12) ∪ 𝒢𝒲0
@test closure(𝒢𝒲, A) ≃ 𝒲(:(0 ⊢ Q(1,2)), Γ12) ∪ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ C([:(P(1) ⊢ 0)], [], [:(Q(1,2) ⊢ 0)], Γ12) ∪ 𝒢𝒟0
@test closure(𝒢𝒟, A) ≃ 
  C([:(0 ⊢ Q(1,2))], [], [:(0 ⊢ P(1) + Q(1,2))], Γ12) ∪ 𝒢𝒟0

# Row {b}: A = {P⁺_= Q⁻_=b}_b, the orbit of s₀ with b = 2 frozen
A = κ(s₀, [2])
zb(G) = zero_role(G, Set([2]))
𝒢𝒲0, 𝒢𝒟0 = zb.([𝒢𝒲,𝒢𝒟])

@test perp(𝒢𝒪, A) ≃ zb(𝒢𝒪) && closure(𝒢𝒪, A) ≃ top(Set([2]))
@test perp(𝒢𝒲, A) ≃ top(Set([2])) && closure(𝒢𝒲, A) ≃ 𝒢𝒲0
@test perp(𝒢𝒟, A) ≃ κ(:(0 ⊢ 0), [2]) ∪ 𝒢𝒟0

# The table's `{s₀}` here is the full orbit P⁺₋Q⁻₋₌, so A⊥⊥ = I𝒟 itself
@test closure(𝒢𝒟, A) ≃ point(𝒢𝒟, Set([2]))

# Row {b}: 𝒲(A)
A = 𝒲(s₀, [2])
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
  @test (p →ₒ q) == ¬p ⅋ q && (p ⇒ q) == ¬p ∨ q
  @test context(p ⊗ q) == Γ12
  # ⊕ is above both, & below both, in each component the right way round
  pq = p ⊕ q
  @test all(t ∈ pq.prem for t in ts if t ∈ p.prem || t ∈ q.prem)
  @test all(t ∈ p.conc && t ∈ q.conc for t in ts if t ∈ pq.conc)
  # Every atom entails itself, since refl ⊆ I
  @test (p ⊩ p) && (q ⊩ q) && (r ⊩ r)
  @test ([p, r] ⊩ r) && (r ⊩ [r, q])
end

# Conservativity: ⊨ ∀Θ. ⨂aᵢ ⊸ ⅋bⱼ iff the sequent is in I
#-------------------------------------------------------------------------------

function formula(G::Frame, s::Sequent)
  atoms(d) = [RolePair(G, t) for (t, n) in d for _ in 1:n]
  prem, conc = atoms(s.prem), atoms(s.conc)
  isempty(prem) && return reduce(⅋, conc)
  isempty(conc) && return ¬reduce(⊗, prem)
  (reduce(⊗, prem) →ₒ reduce(⅋, conc))
end

for (G, I) in zip([𝒢𝒪, 𝒢𝒲, 𝒢𝒟], [I𝒪, I𝒲, I𝒟]),
    s in S.([:(P(1) ⊢ Q(1,2)), :(P(1) ⊢ Q(2,1)), :(ψ ⊢ ψ), :(P(1) ⊢ P(1)), :(ψ ⊢ P(1)),
             :(P(1) + Q(1,2) ⊢ Q(1,2)), :(Q(1,2) ⊢ Q(2,1)), :(P(1) + ψ ⊢ Q(1,2) + ψ)])
  φ = formula(G, s)
  @test ([] ⊩ φ) == (s ∈ I)
  # Quantifying over all the names leaves theoremhood alone: I is equivariant
  @test ([] ⊩ ∀(s.supp, φ)) == (s ∈ I)
  # ... and as a consequence relation, premises on the left
  @test ([RolePair(G, t) for (t, _) in s.prem] ⊩ 
          [RolePair(G, t) for (t, _) in s.conc]) == (s ∈ I)
end

# The semantic evaluation example: ⊨_{b} ∀a. P(a) ⊸ Q(a,b)
#-------------------------------------------------------------------------

for (G, expected) in [(𝒢𝒪, false), (𝒢𝒲, true), (𝒢𝒟, true)]
  φ = forall(RolePair(G, :(P(1))) →ₒ RolePair(G, :(Q(1,2))), Γ1)
  @test context(φ) == Set([2])
  @test ([] ⊩ φ) == expected
end
# The inner conclusory role, as computed there: 𝒲(P⁺_aQ⁻_ab) ∪ 0, resp. {P⁺_aQ⁻_ab} ∪ 0
for (G, inner) in [(𝒢𝒪, 𝒲(s₀, Γ12)), (𝒢𝒲, 𝒲(s₀, Γ12)), (𝒢𝒟, κ(s₀, Γ12))]
  φ = (RolePair(G, :(P(1))) →ₒ RolePair(G, :(Q(1,2))))
  @test Constructible(φ.conc) ≃ inner ∪ zero_role(G, Γ12)
end

# The prime-minister example
#---------------------------

φ₀, J = Predicate.([:φ, :J], [0,1])
Σ′ = Signature([φ₀, P′, J])
λℛ = refl_sequents(Σ′)
𝒫𝒥 = Frame(Σ′, κ(:(P(1) ⊢ J(1))) ∪ 𝒲(λℛ))
A ≃′ B = normal_form(A, Σ′) == normal_form(B, Σ′)

Pa, Ja, φ = RolePair(𝒫𝒥, :(P(1))), RolePair(𝒫𝒥, :(J(1))), RolePair(𝒫𝒥, :φ)
zero0 = zero_role(𝒫𝒥, ∅)
@test zero0 ≃′ 𝒲(λℛ)                    # 0 = I_ℛ
@test Constructible(φ.prem) ≃′ 𝒲(:(φ ⊢ 0)) ∪ zero0   # ⟦φ⟧ = ⟨𝒲(φ⁺) ∨ 0, 𝒲(φ⁻) ∨ 0⟩
@test Constructible(φ.conc) ≃′ 𝒲(:(0 ⊢ φ)) ∪ zero0
@test [] ⊮ φ
@test Constructible(Pa.prem) ≃′ 
  C([:(P(1) ⊢ 0)], [], [:(P(1) + J(1) ⊢ 0)], Γ1) ∪ zero_role(𝒫𝒥, Γ1)

@test Constructible(Pa.conc) ≃′ 𝒲([:(0 ⊢ P(1))], Γ1) ∪ zero_role(𝒫𝒥, Γ1)

# Both quantified atoms collapse to 0 in the relevant component
@test Constructible(∃(Γ1, Pa).conc) ≃′ zero0
@test Constructible(∀(Γ1, Pa).prem) ≃′ zero0
# Theorems produced by the quantifiers alone ...
@test [] ⊩ (∀(Γ1, Pa) →ₒ φ)
@test [] ⊩ (φ →ₒ ∃(Γ1, Pa))
@test [] ⊩ exists(Pa, Γ1)
# ... while at the atomic level φ neither entails nor follows
@test ([]⊮(φ →ₒ Pa)) && ([]⊮(Pa →ₒ φ))
@test (φ ⊮ Pa) && (Pa ⊮ φ)
# The informative theorems: ∀x. P(x) ⊸ J(x), but not ∀x∀y. P(x) ⊗ P(y) ⊸ J(x)
@test [] ⊩ (∀(Γ1, Pa →ₒ Ja))
@test Pa ⊩ Ja
Pb = RolePair(𝒫𝒥, :(P(2)))
@test [] ⊮ ∀(Γ12, Pa ⊗ Pb →ₒ Ja)
@test [Pa, Pb] ⊮ [Ja]

# With 𝔹 coefficients
#####################

#
# Sides are sets and contraction holds: the paper's idempotent frames. Checked
# by brute force on a nullary signature, where `𝔹[X]²` is finite, and against
# the `ℕ` theory on the courtroom, where a frame with weakening may be computed
# with either coefficients.

S′(x) = Sequent{𝔹}(x)
S′(x::Sequent{𝔹}) = x
C′(κ, μ, λ, ctx) = Constructible{𝔹}(S′.(κ), S′.(μ), S′.(λ), Set{Int}(ctx))

# Brute force on a nullary signature
#-----------------------------------

a′, b′ = Predicate(:a, 0), Predicate(:b, 0)
Σab = Signature([a′, b′])
positions = Set(small_sequents(𝔹, Σab, Int[], 4))
@test length(positions) == 16

elements(C::Constructible{𝔹}) = Set(t for t in positions if t ∈ C)
bf_perp(I, A) = Set(t for t in positions if all(a + t ∈ I for a in A))
bf_closure(I, A) = bf_perp(I, bf_perp(I, A))
bf_tensor(A, B) = Set(a + b for a in A for b in B)

# The paper's idempotent frame `⊥_𝔹` on `X = {a, b}`
I_B = Set(S′.([:(0 ⊢ 0), :(0 ⊢ a), :(0 ⊢ a + b), :(a ⊢ a), :(a ⊢ a + b), :(b ⊢ b),
               :(b ⊢ a + b), :(a + b ⊢ 0), :(a + b ⊢ a), :(a + b ⊢ b), :(a + b ⊢ a + b)]))
F_B = Frame(Σab, κ(collect(I_B)))
@test elements(F_B.sequents) == I_B
# `(a⁺)^⊥ = ⊤ ∖ 𝒫[{a⁺, b⁻}]` and `(a⁻)^⊥ = ⊤ ∖ {b⁺, b⁺a⁻}`
@test elements(perp(F_B, κ([S′(:(a ⊢ 0))]))) ==
      setdiff(positions, S′.([:(0 ⊢ 0), :(a ⊢ 0), :(0 ⊢ b), :(a ⊢ b)]))
@test elements(perp(F_B, κ([S′(:(0 ⊢ a))]))) == setdiff(positions, S′.([:(b ⊢ 0), :(b ⊢ a)]))
# Not monotone: `⊢ a` holds, `b ⊢ a` does not
@test S′(:(0 ⊢ a)) ∈ F_B.sequents && S′(:(b ⊢ a)) ∉ F_B.sequents

# Brute-force implication-space semantics: pairs of closed subsets of positions
struct BF; prem::Set{Sequent{𝔹}}; conc::Set{Sequent{𝔹}}; end
function bf_semantics(I)
  cl(A) = bf_closure(I, A)
  pp(A) = bf_perp(I, A)
  atom(x) = BF(cl(Set([S′(:($x ⊢ 0))])), cl(Set([S′(:(0 ⊢ $x))])))
  tensor(A, B) = cl(bf_tensor(A, B))
  par(A, B) = pp(bf_tensor(pp(A), pp(B)))
  ops = Dict{Symbol,Function}(
    :¬ => (p) -> BF(p.conc, p.prem),
    :⊗ => (p, q) -> BF(tensor(p.prem, q.prem), par(p.conc, q.conc)),
    :⊕ => (p, q) -> BF(cl(p.prem ∪ q.prem), p.conc ∩ q.conc),
    :& => (p, q) -> BF(p.prem ∩ q.prem, cl(p.conc ∪ q.conc)),
    :⅋ => (p, q) -> BF(par(p.prem, q.prem), tensor(p.conc, q.conc)),
    :→ₒ => (p, q) -> BF(par(p.conc, q.prem), tensor(p.prem, q.conc)),
    :∧ => (p, q) -> BF(tensor(p.prem, q.prem), cl(p.conc ∪ q.conc ∪ tensor(p.conc, q.conc))),
    :∨ => (p, q) -> BF(cl(p.prem ∪ q.prem ∪ tensor(p.prem, q.prem)), tensor(p.conc, q.conc)))
  entails(ps, qs) = reduce(bf_tensor, [[p.prem for p in ps]; [q.conc for q in qs]];
                           init=Set([S′(:(0 ⊢ 0))])) ⊆ I
  (atom=atom, ops=ops, entails=entails)
end

lib_ops = Dict{Symbol,Function}(:¬ => ¬, :⊗ => ⊗, :⊕ => ⊕, :& => &, :⅋ => ⅋,
                                :→ₒ => →ₒ, :∧ => ∧, :∨ => ∨)
binary = [:⊗, :⊕, :&, :⅋, :→ₒ, :∧, :∨]
# Formulas: atoms, negated atoms, and one binary connective between two of those
leaves = [(:a,), (:b,), (:¬, :a), (:¬, :b)]
formulas = [[(o, l, r) for o in binary for l in leaves for r in leaves]; leaves]
function eval_formula(φ, atom, ops)
  length(φ) == 1 && return atom(φ[1])
  φ[1] == :¬ && return ops[:¬](atom(φ[2]))
  ops[φ[1]](eval_formula(φ[2], atom, ops), eval_formula(φ[3], atom, ops))
end

# Six more frames, arbitrary subsets of the positions given by bit patterns
sorted_positions = sort(collect(positions))
frame(bits) = Set(sorted_positions[i] for i in 1:16 if (bits >> (i - 1)) & 1 == 1)
more_frames = frame.([0x5A3C, 0x0F0F, 0x9999, 0x1E2D, 0x7331, 0xC4B2])
for I in [I_B; more_frames]
  F = Frame(Σab, κ(collect(I)))
  @test elements(F.sequents) == I
  bf = bf_semantics(I)
  lib_atom(x) = RolePair(F, x)
  for φ in formulas
    p = eval_formula(φ, bf.atom, bf.ops)
    q = eval_formula(φ, lib_atom, lib_ops)
    @test elements(Constructible(q.prem)) == p.prem
    @test elements(Constructible(q.conc)) == p.conc
  end
  # Consequence among a few formulas
  fs = [formulas[i] for i in [1, 8, 20, 33, 60, 100, 113, 114]]
  for φ in fs, χ in fs
    p, q = eval_formula(φ, bf.atom, bf.ops), eval_formula(χ, bf.atom, bf.ops)
    p′, q′ = eval_formula(φ, lib_atom, lib_ops), eval_formula(χ, lib_atom, lib_ops)
    @test (p′ ⊩ q′) == bf.entails([p], [q])
    @test ([] ⊩ q′) == bf.entails(BF[], [q])
    @test ([p′, p′] ⊩ [q′]) == bf.entails([p, p], [q])
  end
end

# A frame with weakening can be computed with either coefficients
#-----------------------------------------------------------------
#
# For `I′ = 𝒲(λ′)`, `q⁻¹(I′) = 𝒲(ι λ′)` is a constructible triple with ℕ
# coefficients presenting a frame with the same Girard quantale, and `q` of the
# ℕ presentation of `S^⊥` presents the 𝔹 residual. The
# courtroom's affine and contractive courts are such frames; its linear court is
# not, and there the two theories give different answers.

"""
The generators read as multisets, `ι` generator by generator. This presents
*some* `S` with `q(S) = C`, not `q⁻¹(C)`; the two agree only for `C = 𝒲(λ)`,
which is why only frames with weakening are compared below. As a role to be
residuated it is always fine: in a frame `q⁻¹(I′)`, `S^⊥` depends on `S` only
through `q(S)`.
"""
ι(C::Constructible{𝔹}) =
  Constructible{ℕ}(Sequent{ℕ}.(collect(C.strict)), Sequent{ℕ}.(collect(C.refl)),
                   Sequent{ℕ}.(collect(C.weak)), C.context)

W, Cv, R = Predicate(:W, 1), Predicate(:C, 0), Predicate(:R, 0)
Σc = Signature([W, Cv, R])
rule, twice = S(:(W(1) + W(2) ⊢ C)), S(:(2W(1) ⊢ C))
reflℕ = refl_sequents(Σc)
I_lin = ℛ([rule]) ∪ 𝒲(reflℕ)
I_aff = 𝒲([rule; reflℕ])
I_con = 𝒲([rule; twice; reflℕ])
courtsℕ = Frame.(Ref(Σc), [I_lin, I_aff, I_con])
courts𝔹 = [Frame(Σc, Constructible{𝔹}(I)) for I in [I_lin, I_aff, I_con]]
# With sets, "the same witness twice" is one witness: the court `q(I_con)` says a
# single witness convicts. `I_con` itself is not contractive in the paper's sense
# (`W⁺ₐC⁻ ∉ I_con` while `2W⁺ₐC⁻ ∈ I_con`), so it is not `q⁻¹` of anything; the ℕ
# frame with the quantale of `q(I_con)` is `q⁻¹(q(I_con)) = 𝒲(W⁺ₐC⁻, refl)`.
@test courts𝔹[3].sequents == 𝒲([S′(:(W(1) ⊢ C)); refl_sequents(𝔹, Σc)])
courtsℕ′ = [Frame(Σc, ι(F.sequents)) for F in courts𝔹[2:3]]
@test courtsℕ′[1].sequents == courtsℕ[2].sequents            # I_aff = q⁻¹(q(I_aff))
@test courtsℕ′[2].sequents == 𝒲([S(:(W(1) ⊢ C)); reflℕ])   # I_con ≠ q⁻¹(q(I_con))

# Residuals: `q(perp_ℕ(ι S′)) = perp_𝔹(S′)` for the frames with weakening
roles = [κ([S′(:(W(1) ⊢ 0))], Γ1), κ([S′(:(0 ⊢ C))]), ℛ([S′(:(W(1) ⊢ C))], Γ1),
         𝒲([S′(:(W(1) + W(2) ⊢ 0))], Γ12),
         C′([:(W(1) ⊢ 0)], [:(R ⊢ 0)], [:(W(2) ⊢ C)], Γ12)]
for (Fℕ, F𝔹) in zip(courtsℕ′, courts𝔹[2:3]), A in roles
  viaℕ = Constructible{𝔹}(perp(Fℕ, ι(A)))
  @test roles_equal(F𝔹, viaℕ, perp(F𝔹, A))
  @test roles_equal(F𝔹, Constructible{𝔹}(closure(Fℕ, ι(A))), closure(F𝔹, A))
end

# The courtroom's queries, in both theories
atoms_of(F) = (Wa=RolePair(F, :(W(1))), Wb=RolePair(F, :(W(2))), Wc=RolePair(F, :(W(3))),
               Cv=RolePair(F, :C), Rn=RolePair(F, :R))
queries = [
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); A.Wa ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wa] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); A.Wa ⊗ A.Wa ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Wc] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb, A.Rn] ⊩ [A.Cv ⅋ A.Rn]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv ⅋ A.Rn]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb ⊕ A.Wc] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb ⊕ A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [A.Wa, A.Wb & A.Rn] ⊩ [A.Cv]),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ12, A.Wa ⊗ A.Wb →ₒ A.Cv)),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ1, A.Wa ⊗ A.Wa →ₒ A.Cv)),
  F -> (A = atoms_of(F); [] ⊩ ∀(Γ1, A.Wa →ₒ A.Cv)),
  F -> (A = atoms_of(F); A.Wa ⊩ ∀(Set([2]), A.Wb →ₒ A.Cv)),
  F -> (A = atoms_of(F); A.Wa ⊩ ∀(Set([2]), in_context(A.Wb →ₒ A.Cv, Γ12))),
  F -> (A = atoms_of(F); ∃(Γ1, A.Wa) ⊩ ∀(Set([2]), A.Wb →ₒ A.Cv)),
  F -> (A = atoms_of(F); ∃(Γ12, A.Wa ⊗ A.Wb) ⊩ A.Cv),
  F -> (A = atoms_of(F); ∀(Γ1, A.Wa) ⊩ A.Cv),
  F -> (A = atoms_of(F); [A.Wa, A.Wb] ⊩ [A.Cv ⅋ A.Cv]),
]
answers(F) = [q(F) for q in queries]
for (Fℕ, F𝔹) in zip(courtsℕ′, courts𝔹[2:3])
  @test answers(Fℕ) == answers(F𝔹)
end
@test answers(courtsℕ[2]) == answers(courts𝔹[2])
@test answers(courtsℕ[3]) != answers(courts𝔹[3])    # e.g. `W(a) ⊨ C` only with sets
@test !queries[2](courtsℕ[3]) && queries[2](courts𝔹[3])
# The linear court has no ℕ counterpart. Against the ℕ linear court it agrees
# except where contraction bites: two witnesses convict twice over,
# `W(a), W(b) ⊨ C ⅋ C`, since `W⁺ₐW⁺ᵦC⁻C⁻ = W⁺ₐW⁺ᵦC⁻`.
linℕ, lin𝔹 = answers(courtsℕ[1]), answers(courts𝔹[1])
@test linℕ[1:19] == lin𝔹[1:19]
@test !linℕ[20] && lin𝔹[20]

end # module
