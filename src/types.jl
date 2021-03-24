#--------------------
#--------------------
#### Symbolic
#--------------------
abstract type Symbolic{T} end

### Interface to be defined for `simplify` to work:

"""
    istree(x::T)

Check if `x` represents an expression tree. If returns true,
it will be assumed that `operation(::T)` and `arguments(::T)`
methods are defined. Definining these three should allow use
of `simplify` on custom types. Optionally `symtype(x)` can be
defined to return the expected type of the symbolic expression.
"""
istree(x) = false

"""
    operation(x::T)

Returns the operation (a function object) performed by an expression
tree. Called only if `istree(::T)` is true. Part of the API required
for `simplify` to work. Other required methods are `arguments` and `istree`
"""
function operation end

"""
    arguments(x::T)

Returns the arguments (a `Vector`) for an expression tree.
Called only if `istree(x)` is `true`. Part of the API required
for `simplify` to work. Other required methods are `operation` and `istree`
"""
function arguments end

"""
    symtype(x)

The supposed type of values in the domain of x. Tracing tools can use this type to
pick the right method to run or analyse code.

This defaults to `typeof(x)` if `x` is numeric, or `Any` otherwise.
For the types defined in this package, namely `T<:Symbolic{S}` it is `S`.

Define this for your symbolic types if you want `simplify` to apply rules
specific to numbers (such as commutativity of multiplication). Or such
rules that may be implemented in the future.
"""
function symtype end

symtype(x::Number) = typeof(x)

symtype(x) = typeof(x)

symtype(::Symbolic{T}) where {T} = T

function hasmetadata(s::Symbolic, ctx)
    s.metadata isa AbstractDict && haskey(s.metadata, ctx)
end

function getmetadata(s::Symbolic, ctx)
    if s.metadata isa AbstractDict
        s.metadata[ctx]
    else
        throw(ArgumentError("$s does not have metadata for $ctx"))
    end
end

function getmetadata(s::Symbolic, ctx, default)
    s.metadata isa AbstractDict ? get(s.metadata, ctx, default) : default
end

# pirated for Setfield purposes:
Base.ImmutableDict(d::ImmutableDict{K,V}, x, y)  where {K, V} = ImmutableDict{K,V}(d, x, y)

assocmeta(d::Dict, ctx, val) = (d=copy(d); d[ctx] = val; d)
function assocmeta(d::Base.ImmutableDict, ctx, val)::ImmutableDict{DataType,Any}
    # optimizations
    # If using upto 3 contexts, things stay compact
    if isdefined(d, :parent)
        d.key === ctx && return @set d.value = val
        d1 = d.parent
        if isdefined(d1, :parent)
            d1.key === ctx && return @set d.parent.value = val
            d2 = d1.parent
            if isdefined(d2, :parent)
                d2.key === ctx && return @set d.parent.parent.value = val
            end
        end
    end
    Base.ImmutableDict{DataType, Any}(d, ctx, val)
end

function setmetadata(s::Symbolic, ctx::DataType, val)
    if s.metadata isa AbstractDict
        @set s.metadata = assocmeta(s.metadata, ctx, val)
    else
        # fresh Dict
        @set s.metadata = Base.ImmutableDict{DataType, Any}(ctx, val)
    end
end

Base.isequal(s::Symbolic, x) = false
Base.isequal(x, s::Symbolic) = false

function Base.isequal(t1::Symbolic, t2::Symbolic)
    t1 === t2 && return true
    (istree(t1) && istree(t2)) || return false
    a1 = arguments(t1)
    a2 = arguments(t2)

    isequal(operation(t1), operation(t2)) &&
        length(a1) == length(a2) &&
        all(isequal(l,r) for (l, r) in zip(a1,a2))
end
### End of interface

function to_symbolic(x)
    Base.depwarn("`to_symbolic(x)` is deprecated, define the interface for your " *
                 "symbolic structure using `istree(x)`, `operation(x)`, `arguments(x)` " *
                 "and `similarterm(::YourType, f, args, symtype)`", :to_symbolic, force=true)

    x
end

Base.one( s::Symbolic) = one( symtype(s))

Base.zero(s::Symbolic) = zero(symtype(s))

"""
    promote_symtype(f, Ts...)

The result of applying `f` to arguments of [`symtype`](#symtype) `Ts...`

```julia
julia> promote_symtype(+, Real, Real)
Real

julia> promote_symtype(+, Complex, Real)
Number

julia> @syms f(x)::Complex
(f(::Number)::Complex,)

julia> promote_symtype(f, Number)
Complex
```

When constructing [`Term`](#Term)s without an explicit symtype,
`promote_symtype` is used to figure out the symtype of the Term.
"""
promote_symtype(f, Ts...) = Any

const NO_METADATA = nothing

#--------------------
#--------------------
#### Syms
#--------------------
"""
    Sym{T}(name::Symbol)

A named variable of type `T`. Type `T` can be `FnType{X,Y}` which
means the variable is a function with the type signature X -> Y where
`X` is a tuple type of arguments and `Y` is any type.
"""
struct Sym{T, M} <: Symbolic{T}
    name::Symbol
    metadata::M
end

Base.nameof(s::Sym) = s.name

ConstructionBase.constructorof(s::Type{<:Sym{T}}) where {T} = (n,m) -> Sym{T}(n, metadata=m)

function (::Type{Sym{T}})(name; metadata=NO_METADATA) where {T}
    Sym{T, typeof(metadata)}(name, metadata)
end

Base.hash(s::Sym{T}, u::UInt) where {T} = hash(T, hash(s.name, u))

Base.isequal(v1::Sym{T}, v2::Sym{T}) where {T} = v1 === v2

Base.show(io::IO, v::Sym) = Base.show_unquoted(io, v.name)

#---------------------------
#---------------------------
#### Function-like variables
#---------------------------

# Maybe don't even need a new type, can just use Sym{FnType}
struct FnType{X<:Tuple,Y} end

(f::Sym{<:FnType})(args...) = Term{promote_symtype(f, symtype.(args)...)}(f, [args...])

function (f::Sym)(args...)
    error("Sym $f is not callable. " *
          "Use @syms $f(var1, var2,...) to create it as a callable. " *
          "See ?@fun for more options")
end

"""
    promote_symtype(f::Sym{FnType{X,Y}}, arg_symtypes...)

The output symtype of applying variable `f` to arugments of symtype `arg_symtypes...`.
if the arguments are of the wrong type then this function will error.
"""
function promote_symtype(f::Sym{FnType{X,Y}}, args...) where {X, Y}
    if X === Tuple
        return Y
    end

    nrequired = fieldcount(X)
    ngiven    = nfields(args)

    if nrequired !== ngiven
        error("$f takes $nrequired arguments; $ngiven arguments given")
    end

    for i in 1:ngiven
        t = X.parameters[i]
        if !(args[i] <: t)
            error("Argument to $f at position $i must be of symbolic type $t")
        end
    end
    return Y
end

"""
    @syms <lhs_expr>[::T1] <lhs_expr>[::T2]...

For instance:

    @syms foo::Real bar baz(x, y::Real)::Complex

Create one or more variables. `<lhs_expr>` can be just a symbol in which case
it will be the name of the variable, or a function call in which case a function-like
variable which has the same name as the function being called. The Sym type, or
in the case of a function-like Sym, the output type of calling the function
can be set using the `::T` syntax.

# Examples:

- `@syms foo bar::Real baz::Int` will create
variable `foo` of symtype `Number` (the default), `bar` of symtype `Real`
and `baz` of symtype `Int`
- `@syms f(x) g(y::Real, x)::Int h(a::Int, f(b))` creates 1-arg `f` 2-arg `g`
and 2 arg `f`. The second argument to `h` must be a one argument function-like
variable. So, `h(1, g)` will fail and `h(1, f)` will work.
"""
macro syms(xs...)
    defs = map(xs) do x
        n, t = _name_type(x)
        :($(esc(n)) = Sym{$(esc(t))}($(Expr(:quote, n))))
    end

    Expr(:block, defs...,
         :(tuple($(map(x->esc(_name_type(x).name), xs)...))))
end

function syms_syntax_error()
    error("Incorrect @syms syntax. Try `@syms x::Real y::Complex g(a) f(::Real)::Real` for instance.")
end

function _name_type(x)
    if x isa Symbol
        return (name=x, type=Number)
    elseif x isa Expr && x.head === :(::)
        if length(x.args) == 1
            return (name=nothing, type=x.args[1])
        end
        lhs, rhs = x.args[1:2]
        if lhs isa Expr && lhs.head === :call
            # e.g. f(::Real)::Unreal
            type = map(x->_name_type(x).type, lhs.args[2:end])
            return (name=lhs.args[1], type=:($FnType{Tuple{$(type...)}, $rhs}))
        else
            return (name=lhs, type=rhs)
        end
    elseif x isa Expr && x.head === :call
        return _name_type(:($x::Number))
    else
        syms_syntax_error()
    end
end

function Base.show(io::IO, f::Sym{<:FnType{X,Y}}) where {X,Y}
    print(io, f.name)
    argrepr = join(map(t->"::"*string(t), X.parameters), ", ")
    print(io, "(", argrepr, ")")
    print(io, "::", Y)
end

#--------------------
#--------------------
#### Terms
#--------------------
"""
    Term{T}(f, args::AbstractArray)

or
    Term(f, args::AbstractArray)

Symbolic expression representing the result of calling `f(args...)`.

- `operation(t::Term)` returns `f`
- `arguments(t::Term)` returns `args`
- `symtype(t::Term)` returns `T`

If `T` is not provided during construction, it is queried by calling
`SymbolicUtils.promote_symtype(f, map(symtype, args)...)`.

See [promote_symtype](#promote_symtype)
"""
struct Term{T, M} <: Symbolic{T}
    f::Any
    arguments::Any
    metadata::M
    hash::Ref{UInt} # hash cache
end

function ConstructionBase.constructorof(s::Type{<:Term{T}}) where {T}
    function (f, args, meta, hash)
        Term{T, typeof(meta)}(f, args, meta, hash)
    end
end

function (::Type{Term{T}})(f, args; metadata=NO_METADATA) where {T}
    Term{T, typeof(metadata)}(f, args, metadata, Ref{UInt}(0))
end

istree(t::Term) = true

function Term(f, args; metadata=NO_METADATA)
    Term{_promote_symtype(f, args)}(f, args, metadata=metadata)
end

operation(x::Term) = getfield(x, :f)

arguments(x::Term) = getfield(x, :arguments)

## This is much faster than hash of an array of Any
hashvec(xs, z) = foldr(hash, xs, init=z)

function Base.hash(t::Term{T}, salt::UInt) where {T}
    !iszero(salt) && return hash(hash(t, zero(UInt)), salt)
    h = t.hash[]
    !iszero(h) && return h
    h′ = hashvec(arguments(t), hash(operation(t), hash(T, salt)))
    t.hash[] = h′
    return h′
end

isassociative(::Any) = false
isassociative(::Union{typeof(+),typeof(*)}) = true

_promote_symtype(f::Sym, args) = promote_symtype(f, map(symtype, args)...)
function _promote_symtype(f, args)
    if length(args) == 0
        promote_symtype(f)
    elseif length(args) == 1
        promote_symtype(f, symtype(args[1]))
    elseif length(args) == 2
        promote_symtype(f, symtype(args[1]), symtype(args[2]))
    elseif isassociative(f)
        mapfoldl(symtype, (x,y) -> promote_symtype(f, x, y), args)
    else
        promote_symtype(f, map(symtype, args)...)
    end
end


function term(f, args...; type = nothing)
    if type === nothing
        T = _promote_symtype(f, args)
    else
        T = type
    end
    Term{T}(f, [args...])
end

"""
    similarterm(t, f, args, symtype)

Create a term that is similar in type to `t`. Extending this function allows packages
using their own expression types with SymbolicUtils to define how new terms should
be created.

## Arguments

- `t` the reference term to use to create similar terms
- `f` is the operation of the term
- `args` is the arguments
- The `symtype` of the resulting term. Best effort will be made to set the symtype of the
  resulting similar term to this type.
"""
similarterm(t, f, args, symtype) = f(args...)
similarterm(t, f, args) = similarterm(t, f, args, _promote_symtype(f, args))
similarterm(::Term, f, args, symtype=nothing) = term(f, args...; type=symtype)

node_count(t) = istree(t) ? reduce(+, node_count(x) for x in  arguments(t), init=0) + 1 : 1

#--------------------
#--------------------
####  Pretty printing
#--------------------
const show_simplified = Ref(false)

Base.show(io::IO, t::Term) = show_term(io, t)

isnegative(t::Real) = t < 0
function isnegative(t)
    if istree(t) && operation(t) === (*)
        coeff = first(arguments(t))
        return isnegative(coeff)
    end
    return false
end

setargs(t, args) = Term{symtype(t)}(operation(t), args)
cdrargs(args) = setargs(t, cdr(args))

print_arg(io, x::Union{Complex, Rational}; paren=true) = print(io, "(", x, ")")
isbinop(f) = istree(f) && Base.isbinaryoperator(nameof(operation(f)))
function print_arg(io, x; paren=false)
    if paren && isbinop(x)
        print(io, "(", x, ")")
    else
        print(io, x)
    end
end
print_arg(io, s::String; paren=true) = show(io, s)
function print_arg(io, f, x)
    f !== (*) && return print_arg(io, x)
    if Base.isbinaryoperator(nameof(f))
        print_arg(io, x, paren=true)
    else
        print_arg(io, x)
    end
end

function show_add(io, args)
    negs = filter(isnegative, args)
    nnegs = filter(!isnegative, args)
    for (i, t) in enumerate(nnegs)
        i != 1 && print(io, " + ")
        print_arg(io, +,  t)
    end

    for (i, t) in enumerate(negs)
        if i==1 && isempty(nnegs)
            print_arg(io, -, t)
        else
            print(io, " - ")
            print_arg(io, -t, paren=true)
        end
    end
end

function show_pow(io, args)
    base, ex = args

    print_arg(io, base, paren=true)
    print(io, "^")
    print_arg(io, ex, paren=true)
end

function show_mul(io, args)
    length(args) == 1 && return print_arg(io, *, args[1])

    paren_scalar = args[1] isa Complex || args[1] isa Rational
    minus = args[1] isa Number && args[1] == -1
    unit = args[1] isa Number && args[1] == 1
    nostar = !paren_scalar && args[1] isa Number && !(args[2] isa Number)
    for (i, t) in enumerate(args)
        if i != 1
            if i==2 && nostar
            else
                print(io, "*")
            end
        end
        if i == 1 && minus
            print(io, "-")
        elseif i == 1 && unit
        else
            print_arg(io, *, t)
        end
    end
end

function show_call(io, f, args)
    fname = nameof(f)
    binary = Base.isbinaryoperator(fname)
    if binary
        for (i, t) in enumerate(args)
            i != 1 && print(io, " $fname ")
            print_arg(io, t)
        end
    else
        if f isa Sym
            Base.show_unquoted(io, nameof(f))
        else
            Base.show(io, f)
        end
        print(io, "(")
        for i=1:length(args)
            print(IOContext(io, :paren => false), args[i])
            i != length(args) && print(io, ", ")
        end
        print(io, ")")
    end
end

function show_term(io::IO, t)
    if get(io, :simplify, show_simplified[])
        return print(IOContext(io, :simplify=>false), simplify(t))
    end

    f = operation(t)
    args = arguments(t)

    if f === (+)
        show_add(io, args)
    elseif f === (*)
        show_mul(io, args)
    elseif f === (^)
        show_pow(io, args)
    else
        show_call(io, f, args)
    end

    return nothing
end

showraw(io, t) = Base.show(IOContext(io, :simplify=>false), t)
showraw(t) = showraw(stdout, t)


######   Add Mul and Pow


sdict(kv...) = Dict{Any, Number}(kv...)

# this cannot be Symbolic{<:Number} to make MTK Parameters work. See #155
const SN = Symbolic
"""
    Add(T, coeff, dict::Dict)

Represents `coeff + (key1 * val1) + (key2 * val2) + ...`

where keys and values come from the dictionary (`dict`).
where `coeff` and the vals are `<:Number` and keys are symbolic.

- `operation(::Add)` -- returns `+`.
- `symtype(::Add)` -- returns `T`.
- `arguments(::Add)` -- returns a totally ordered vector of arguments. i.e.
  `[coeff, keyM*valM, keyN*valN...]`
"""
struct Add{X, T<:Number, D, M} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
    hash::Ref{UInt}
    metadata::M
end

function Add(T, coeff, dict; metadata=NO_METADATA)
    if isempty(dict)
        return coeff
    elseif _iszero(coeff) && length(dict) == 1
        k,v = first(dict)
        return _isone(v) ? k : Mul(T, makemul(v, k)...)
    end

    Add{T, typeof(coeff), typeof(dict), typeof(metadata)}(coeff, dict, Ref{Any}(nothing), Ref{UInt}(0), metadata)
end

symtype(a::Add{X}) where {X} = X


istree(a::Add) = true

operation(a::Add) = +

function arguments(a::Add)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([v*k for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = iszero(a.coeff) ? args : vcat(a.coeff, args)
end

Base.isequal(a::Add, b::Add) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

Base.show(io::IO, a::Add) = show_term(io, a)

"""
    makeadd(sign, coeff::Number, xs...)

Any Muls inside an Add should always have a coeff of 1
and the key (in Add) should instead be used to store the actual coefficient
"""
function makeadd(sign, coeff, xs...)
    d = sdict()
    for x in xs
        if x isa Add
            coeff += x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
            continue
        end
        if x isa Number
            coeff += x
            continue
        end
        if x isa Mul
            k = Mul(symtype(x), 1, x.dict)
            v = sign * x.coeff + get(d, k, 0)
        else
            k = x
            v = sign + get(d, x, 0)
        end
        if iszero(v)
            delete!(d, k)
        else
            d[k] = v
        end
    end
    coeff, d
end

add_t(a,b) = promote_symtype(+, symtype(a), symtype(b))
sub_t(a,b) = promote_symtype(-, symtype(a), symtype(b))
sub_t(a) = promote_symtype(-, symtype(a))

function +(a::SN, b::SN)
    if a isa Add
        coeff, dict = makeadd(1, 0, b)
        T = promote_symtype(+, symtype(a), symtype(b))
        return Add(add_t(a,b), a.coeff + coeff, _merge(+, a.dict, dict, filter=_iszero))
    elseif b isa Add
        return b + a
    end
    Add(add_t(a,b), makeadd(1, 0, a, b)...)
end

+(a::Number, b::SN) = Add(add_t(a,b), makeadd(1, a, b)...)

+(a::SN, b::Number) = Add(add_t(a,b), makeadd(1, b, a)...)

+(a::SN) = a

+(a::Add, b::Add) = Add(add_t(a,b),
                        a.coeff + b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

+(a::Number, b::Add) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

+(b::Add, a::Number) = iszero(a) ? b : Add(add_t(a,b), a + b.coeff, b.dict)

-(a::Add) = Add(sub_t(a), -a.coeff, mapvalues((_,v) -> -v, a.dict))

-(a::SN) = Add(sub_t(a), makeadd(-1, 0, a)...)

-(a::Add, b::Add) = Add(sub_t(a,b),
                        a.coeff - b.coeff,
                        _merge(-, a.dict, b.dict, filter=_iszero))

-(a::SN, b::SN) = a + (-b)

-(a::Number, b::SN) = a + (-b)

-(a::SN, b::Number) = a + (-b)

"""
    Mul(T, coeff, dict)

Represents coeff * (key1 ^ val1) * (key2 ^ val2) * ....

where coeff is a <:Number and keys and values come from the dictionary (`dict`).
where `coeff` and the vals are `<:Number` and keys are symbolic.

- `symtype(::Add)` -- returns `T`.
- `operation(::Add)` -- returns `*`.
- `arguments(::Add)` -- returns a totally ordered vector of arguments. i.e.
  `[coeff, keyM^valM, keyN^valN...]`
"""
struct Mul{X, T<:Number, D, M} <: Symbolic{X}
    coeff::T
    dict::D
    sorted_args_cache::Ref{Any}
    hash::Ref{UInt}
    metadata::M
end

for S in [Add, Mul]
    @eval function ConstructionBase.constructorof(s::Type{<:$S{T}}) where {T}
        function (coeff, dict, argscache, hash, m)
            $S{T,
                typeof(coeff),
                typeof(dict),
                typeof(m)}(coeff,
            dict,
            argscache,
            hash,
            m)
        end
    end
end

function Mul(T, a,b; metadata=NO_METADATA)
    isempty(b) && return a
    if _isone(a) && length(b) == 1
        pair = first(b)
        if _isone(last(pair)) # first value
            return first(pair)
        else
            return Pow(first(pair), last(pair))
        end
    else
        Mul{T, typeof(a), typeof(b), typeof(metadata)}(a,b, Ref{Any}(nothing), Ref{UInt}(0), metadata)
    end
end

symtype(a::Mul{X}) where {X} = X

istree(a::Mul) = true

operation(a::Mul) = *

function arguments(a::Mul)
    a.sorted_args_cache[] !== nothing && return a.sorted_args_cache[]
    args = sort!([k^v for (k,v) in a.dict], lt=<ₑ)
    a.sorted_args_cache[] = isone(a.coeff) ? args : vcat(a.coeff, args)
end

Base.isequal(a::Mul, b::Mul) = isequal(a.coeff, b.coeff) && isequal(a.dict, b.dict)

Base.show(io::IO, a::Mul) = show_term(io, a)

function makemul(coeff, xs...; d=sdict())
    for x in xs
        if x isa Pow && x.exp isa Number
            d[x.base] = x.exp + get(d, x.base, 0)
        elseif x isa Number
            coeff *= x
        elseif x isa Mul
            coeff *= x.coeff
            _merge!(+, d, x.dict, filter=_iszero)
        else
            v = 1 + get(d, x, 0)
            if _iszero(v)
                delete!(d, x)
            else
                d[x] = v
            end
        end
    end
    (coeff, d)
end

mul_t(a,b) = promote_symtype(*, symtype(a), symtype(b))
mul_t(a) = promote_symtype(*, symtype(a))

*(a::SN) = a

*(a::SN, b::SN) = Mul(mul_t(a,b), makemul(1, a, b)...)

*(a::Mul, b::Mul) = Mul(mul_t(a, b),
                        a.coeff * b.coeff,
                        _merge(+, a.dict, b.dict, filter=_iszero))

*(a::Number, b::SN) = iszero(a) ? a : isone(a) ? b : Mul(mul_t(a, b), makemul(a, b)...)

*(b::SN, a::Number) = iszero(a) ? a : isone(a) ? b : Mul(mul_t(a, b), makemul(a, b)...)

"""
    Pow(base, exp)

Represents `base^exp`, a lighter version of `Mul(1, Dict(base=>exp))`
"""
struct Pow{X, B, E, M} <: Symbolic{X}
    base::B
    exp::E
    metadata::M
end

function ConstructionBase.constructorof(::Type{<:Pow{X}}) where {X}
    (base, exp, m) ->
    Pow{promote_symtype(^, symtype(base), symtype(exp)), typeof(base), typeof(exp), typeof(m)}(base,exp,m)
end

function (::Type{<:Pow{T}})(a, b; metadata=NO_METADATA) where {T}
    _iszero(b) && return 1
    _isone(b) && return a
    Pow{T, typeof(a), typeof(b), typeof(metadata)}(a,b,metadata)
end
function Pow(a, b; metadata=NO_METADATA)
    Pow{promote_symtype(^, symtype(a), symtype(b))}(a, b, metadata=metadata)
end
symtype(a::Pow{X}) where {X} = X

istree(a::Pow) = true

operation(a::Pow) = ^

arguments(a::Pow) = [a.base, a.exp]

Base.hash(p::Pow, u::UInt) = hash(p.exp, hash(p.base, u))

Base.isequal(p::Pow, b::Pow) = isequal(p.base, b.base) && isequal(p.exp, b.exp)

Base.show(io::IO, p::Pow) = show_term(io, p)

^(a::SN, b) = Pow(a, b)

^(a::SN, b::SN) = Pow(a, b)

^(a::Number, b::SN) = Pow(a, b)

function ^(a::Mul, b::Number)
    coeff = a.coeff isa Integer && b isa Integer ? (a.coeff//1) ^ b : a.coeff ^ b
    Mul(promote_symtype(^, symtype(a), symtype(b)),
        coeff, mapvalues((k, v) -> b*v, a.dict))
end

function *(a::Mul, b::Pow)
    if b.exp isa Number
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b.base=>b.exp), filter=_iszero))
    else
        Mul(mul_t(a, b),
            a.coeff, _merge(+, a.dict, Base.ImmutableDict(b=>1), filter=_iszero))
    end
end

*(a::Pow, b::Mul) = b * a

_merge(f, d, others...; filter=x->false) = _merge!(f, copy(d), others...; filter=filter)
function _merge!(f, d, others...; filter=x->false)
    acc = d
    for other in others
        for (k, v) in other
            v = f(v)
            if haskey(acc, k)
                v = acc[k] + v
            end
            if filter(v)
                delete!(acc, k)
            else
                acc[k] = v
            end
        end
    end
    acc
end

function mapvalues(f, d1::AbstractDict)
    d = copy(d1)
    for (k, v) in d
        d[k] = f(k, v)
    end
    d
end

function similarterm(p::Union{Mul, Add, Pow}, f, args, T=nothing)
    if T === nothing
        T = _promote_symtype(f, args)
    end
    if f === (+)
        Add(T, makeadd(1, 0, args...)...)
    elseif f == (*)
        Mul(T, makemul(1, args...)...)
    elseif f == (^) && length(args) == 2
        Pow{T, typeof.(args)...}(args...)
    else
        f(args...)
    end
end

function Base.hash(t::Union{Add,Mul}, u::UInt64)
    !iszero(u) && return hash(hash(t, zero(UInt64)), u)
    h = t.hash[]
    !iszero(h) && return h
    hashoffset = t isa Add ? 0xaddaddaddaddadda : 0xaaaaaaaaaaaaaaaa
    h′= hash(hashoffset, hash(t.coeff, hash(t.dict, u)))
    t.hash[] = h′
    return h′
end

import AbstractTrees

struct TreePrint
    op
    x
end
AbstractTrees.children(x::Term) = arguments(x)
AbstractTrees.children(x::Union{Add, Mul}) = map(y->TreePrint(x isa Add ? (:*) : (:^), y), collect(pairs(x.dict)))
AbstractTrees.children(x::Union{Pow}) = [x.base, x.exp]
AbstractTrees.children(x::TreePrint) = [x.x[1], x.x[2]]

print_tree(x; maxdepth=Inf, kw...) = print_tree(stdout, x; maxdepth=maxdepth, kw...)
function print_tree(_io::IO, x::Union{Term, Add, Mul, Pow}; kw...)
    AbstractTrees.print_tree(_io, x; withinds=true, kw...) do io, y, inds
        if istree(y)
            print(io, operation(y))
        elseif y isa TreePrint
            print(io, "(", y.op, ")")
        else
            print(io, y)
        end
    end
end
