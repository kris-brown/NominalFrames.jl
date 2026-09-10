export MultiSet, ≼, ∨, ∧, sorted

""" Multisets represented by their finite support: i.e. all nonzero values """
@struct_hash_equal struct MultiSet{T}
  counts::Dict{T, Int}
  """ Convert a list to a multiset """
  function MultiSet(d::Dict{T, Int}) where T 
    all(>(0), values(d)) || error("Bad counts $d")
    new{T}(d)
  end
end

(MultiSet{T}()::MultiSet{T}) where T = MultiSet(Dict{T,Int}())

""" Convert list to multiset """
function MultiSet(vs::AbstractVector{T})::MultiSet{T} where T
  d = Dict{T,Int}()
  for v in vs
    haskey(d, v) ? (d[v]+=1) : (d[v] = 1) 
  end
  MultiSet(d)
end


Base.keys(m::MultiSet) = keys(m.counts)
(Base.haskey(m::MultiSet{T}, k::T)::Bool) where T = haskey(m.counts,k)
(Base.getindex(m::MultiSet{T}, k::T)::Int) where T = getindex(m.counts,k)
(Base.get(m::MultiSet{T}, k::T, def::Int)::Int) where T = get(m.counts,k, def)
(Base.setindex!(m::MultiSet{T}, v::Int, k::T)) where T = setindex!(m.counts,v,k)
Base.values(m::MultiSet) = values(m.counts)
Base.collect(m::MultiSet) = collect(m.counts)
Base.iterate(m::MultiSet, x...) = iterate(m.counts, x...)
Base.length(m::MultiSet) = length(m.counts)
Base.pairs(m::MultiSet) = pairs(m.counts)
Base.copy(m::MultiSet) = MultiSet(copy(m.counts))


function int_to_superscript(n::Integer)
  @assert n ≥ 0
  sup_digits = ['⁰', '¹', '²', '³', '⁴', '⁵', '⁶', '⁷', '⁸', '⁹']
  join(sup_digits[parse(Int, c) + 1] for c in string(n))
end

function Base.show(io::IO, ::MIME"text/plain", m::MultiSet)
  print(io, "{")
  for (k, v) in pairs(m) 
    show(io,"text/plain", k)
    print(io, int_to_superscript(v))
    print(io, ", ")
  end
  print(io, "\b\b}")
end

""" The support of a multiset, as the multiset with every multiplicity `1` """
(support(m::MultiSet{T})::MultiSet{T}) where T = MultiSet(Dict{T,Int}(k => 1 for k in keys(m)))

""" Ordering multisets as keys (a total order, not the meaningful partial order) """
(Base.isless(x::MultiSet{T}, y::MultiSet{T})::Bool) where T = 
  isless(x.counts, y.counts)

"""
A multiset as a sorted vector of `element => multiplicity` pairs: the canonical
serialization of a multiset over an ordered `T`, which is what lets multisets
themselves be compared (lexicographically, via `isless` on the pairs).
"""
(sorted(x::MultiSet{T})::Vector{Pair{T,Int}}) where T = sort!(collect(pairs(x)))

function Base.:(+)(x::MultiSet{T}, y::MultiSet{T})::MultiSet{T} where T
  res = copy(x)
  for (t, n) in pairs(y)
    if haskey(res, t)
      res[t] += n
    else
      res[t] = n
    end
  end
  res
end

""" `x ≤ y` pointwise: every element of `x` occurs at least as often in `y` """
(≼(x::MultiSet{T}, y::MultiSet{T})::Bool) where T =
  all(n ≤ get(y, t, 0) for (t, n) in pairs(x))

"""
Truncated subtraction `x ∸ y`, i.e. `t ↦ max(0, x(t) - y(t))`. Agrees with the
partial subtraction `x - y` whenever the latter is defined (`y ≤ x`).
"""
function ∸(x::MultiSet{T}, y::MultiSet{T})::MultiSet{T} where T
  res = MultiSet{T}()
  for (t, n) in pairs(x)
    m = n - get(y, t, 0)
    m > 0 && (res[t] = m)
  end
  res
end

""" Join in the pointwise order: `t ↦ max(x(t), y(t))` """
function ∨(x::MultiSet{T}, y::MultiSet{T})::MultiSet{T} where T
  res = copy(x)
  for (t, n) in pairs(y)
    res[t] = max(get(res, t, 0), n)
  end
  res
end

""" Meet in the pointwise order: `t ↦ min(x(t), y(t))` """
function ∧(x::MultiSet{T}, y::MultiSet{T})::MultiSet{T} where T 
  MultiSet(Dict{T,Int}(t => min(n, y[t]) for (t, n) in pairs(x) if haskey(y, t)))
end 

"""
The signed difference `x - y` as a ℤ-valued multiset, again without zero
entries. Unlike `∸` nothing is truncated, so it is additive.
"""
function Base.:(-)(x::MultiSet{T}, y::MultiSet{T})::Dict{T,Int} where T
  res = Dict{T,Int}()
  for t in union(keys(x), keys(y))
    d = get(x, t, 0) - get(y, t, 0)
    d == 0 || (res[t] = d)
  end
  res
end