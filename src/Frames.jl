export Frame, point

"""
A frame is a choice of a signature (freely generating a nominal set, Σ) and a
subobject of `K[Σ]²`, its incompatibility set `I`; with `K = ℕ` positions are
pairs of multisets, with `K = 𝔹` pairs of sets. Any
presentation may be given; it is stored in normal form (`normal_form`). The
closed roles `S = S⊸I⊸I` of a frame form its Girard quantale `𝒢`.
"""
struct Frame{K<:Multiplicity}
  signature::Signature
  sequents::Constructible{K}

  function Frame(signature::Signature, sequents::Constructible{K}) where K
    validate(signature, sequents)
    new{K}(signature, normal_form(sequents, signature))
  end
end

# Coerce frame to be idempotent
Frame{𝔹}(F::Frame{ℕ}) = Frame(F.signature, Constructible{𝔹}(F.sequents))
Frame{K}(F::Frame{K}) where K = F


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
