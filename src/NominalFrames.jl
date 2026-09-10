module NominalFrames

using StructEquality

const Maybe{T} = Union{Nothing, T}

include("Multisets.jl")         # checked
include("Semiring.jl")          # ℕ (multisets) and 𝔹 (sets) coefficients
include("Syntax.jl")            # checked
include("Orbits.jl")            # checked
include("PowerElems.jl")        # checked
include("Frames.jl")            # checked
include("SingletonResidual.jl") # mostly checked
include("Residual.jl")          # spot checked
include("NormalForm.jl")        # spot checked
include("Semantics.jl")


end # module NominalFrames
