export Frame, point

"""
A frame is a choice of a signature (freely generating a nominal set, Σ) and
a subobject of `K[Σ]²`, its incompatibility set `I`; with `K = ℕ` positions are
pairs of multisets, with `K = 𝔹` pairs of sets (`Semiring.jl`). Any presentation
may be given; it is stored in normal form (`normal_form`), which is what
`residual` needs on its right and what makes the absorption tests of `⊨`
immediate. The closed roles `S = S^⊥⊥` of a frame form its Girard quantale `𝒢`
(`Semantics.jl`).
"""
struct Frame{K<:Semiring}
  signature::Signature
  sequents::Constructible{K}

  function Frame(signature::Signature, sequents::Constructible{K}) where K
    validate(signature, sequents)
    new{K}(signature, normal_form(sequents, signature))
  end
end


""" The point `⊥ = I` of `𝒢`, presented at context `Γ` """
point(F::Frame{K}, Γ::Set{Int}) where K = enlarge_context(F.sequents, Γ)


""" Validation of the incompatibility set. Throws error if invalid. """
function validate(signature::Signature, sequents::Constructible)
  @assert isempty(sequents.context)
  for seq in sequents.strict ∪ sequents.refl ∪ sequents.weak
    for t in keys(seq.prem) ∪ keys(seq.conc)
      @assert t.pred ∈ signature
    end
  end
end
