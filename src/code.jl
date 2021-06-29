module Code

using StaticArrays, LabelledArrays, SparseArrays, LinearAlgebra

export toexpr, Assignment, (←), Let, Func, DestructuredArgs, LiteralExpr,
       SetArray, MakeArray, MakeSparseArray, MakeTuple, AtIndex,
       SpawnFetch, Multithreaded, cse

import ..SymbolicUtils
import SymbolicUtils: @matchable, Sym, Term, istree, operation, arguments,
                      symtype, similarterm

##== state management ==##

struct NameState
    symbolify::Dict{Any, Symbol}
end
NameState() = NameState(Dict{Any, Symbol}())
function union_symbolify!(n, ts)
    for t in ts
        n[t] = Symbol(string(t))
    end
end

struct LazyState
    ref::Ref{Any}
end
LazyState() = LazyState(Ref{Any}(nothing))

function Base.get(st::LazyState)
    s = getfield(st, :ref)[]
    s === nothing ? getfield(st, :ref)[] = NameState() : s
end

@inline Base.getproperty(st::LazyState, f::Symbol) = getproperty(get(st), f)

##========================##

"""
    toexpr(ex, [st,])

Convert a symbolic expression into an `Expr`, suitable to be passed into `eval`.

For example,

```julia
julia> @syms a b
(a, b)

julia> toexpr(a+b)
:((+)(a, b))

julia> toexpr(a+b) |> dump
Expr
  head: Symbol call
  args: Array{Any}((3,))
    1: + (function of type typeof(+))
    2: Symbol a
    3: Symbol b
```

Note that the function is an actual function object.

For more complex expressions, see other code-related combinators,

Namely `Assignment`, `Let`, `Func`, `SetArray`, `MakeArray`, `MakeSparseArray` and
`MakeTuple`.

To make your own type convertible to Expr using `toexpr` define `toexpr(x, st)` and
forward the state `st` in internal calls to `toexpr`. `st` is state used to know
when to leave something like `y(t)` as it is or when to make it `var"y(t)"`. E.g.
when `y(t)` is itself the argument of a function rather than `y`.

"""
toexpr(x) = toexpr(x, LazyState())
toexpr(s::Sym, st) = nameof(s)


@matchable struct Assignment
    lhs
    rhs
end

"""
    Assignment(lhs, rhs)

An assignment expression. Shorthand `lhs ← rhs` (`\\leftarrow`)
"""
Assignment

lhs(a::Assignment) = a.lhs
rhs(a::Assignment) = a.rhs

const (←) = Assignment

Base.convert(::Type{Assignment}, p::Pair) = Assignment(pair[1], pair[2])

toexpr(a::Assignment, st) = :($(toexpr(a.lhs, st)) = $(toexpr(a.rhs, st)))

function_to_expr(op, args, st) = nothing

function function_to_expr(::typeof(^), O, st)
    args = arguments(O)
    if length(args) == 2 && args[2] isa Real && args[2] < 0
        ex = args[1]
        if args[2] == -1
            return toexpr(Term{Any}(inv, [ex]), st)
        else
            return toexpr(Term{Any}(^, [Term{Any}(inv, [ex]), -args[2]]), st)
        end
    end
    return nothing
end

function function_to_expr(::typeof(SymbolicUtils.ifelse), O, st)
    args = arguments(O)
    :($(toexpr(args[1], st)) ? $(toexpr(args[2], st)) : $(toexpr(args[3], st)))
end

function_to_expr(::Sym, O, st) = get(st.symbolify, O, nothing)

function toexpr(O, st)
    !istree(O) && return O
    op = operation(O)
    expr′ = function_to_expr(op, O, st)
    if expr′ !== nothing
        return expr′
    else
        haskey(st.symbolify, O) && return st.symbolify[O]
        args = arguments(O)
        return Expr(:call, toexpr(op, st), map(x->toexpr(x, st), args)...)
    end
end

# Call elements of vector arguments by their name.
@matchable struct DestructuredArgs
    elems
    inds
    name
    inbounds::Bool
end

function DestructuredArgs(elems, name=gensym("arg"); inds=eachindex(elems), inbounds=false)
    DestructuredArgs(elems, inds, name, inbounds)
end

"""
    DestructuredArgs(elems, [name=gensym("arg")])

`elems` is a vector of symbols or call expressions.  When it appears as an argument in
`Func`, it expects a vector of the same length and de-structures the vector into its named
components. See example in `Func` for more information.

`name` is the name to be used for the argument in the generated function Expr.
"""
DestructuredArgs

toexpr(x::DestructuredArgs, st) = toexpr(x.name, st)
get_symbolify(args::DestructuredArgs) = ()
function get_symbolify(args::Union{AbstractArray, Tuple})
    cflatten(map(get_symbolify, args))
end
get_symbolify(x) = istree(x) ? (x,) : ()
cflatten(x) = Iterators.flatten(x) |> collect

function get_assignments(d::DestructuredArgs, st)
    name = toexpr(d, st)
    map(d.inds, d.elems) do i, a
        ex = (i isa Symbol ? :($name.$i) : :($name[$i]))
        ex = d.inbounds ? :(@inbounds($ex)) : ex
        a ← ex
    end   
end

@matchable struct Let
    pairs::Vector{Union{Assignment,DestructuredArgs}} # an iterator of pairs, ordered
    body
end

"""
    Let(assignments, body)

A Let block.

- `assignments` is a vector of `Assignment`s
- `body` is the body of the let block
"""
Let

function toexpr(l::Let, st)
    if all(x->x isa Assignment && !(x.lhs isa DestructuredArgs), l.pairs)
        dargs = l.pairs
    else
        dargs = map(l.pairs) do x
            if x isa DestructuredArgs
                get_assignments(x, st)
            elseif x isa Assignment && x.lhs isa DestructuredArgs
                [x.lhs.name ← x.rhs, get_assignments(x.lhs, st)...]
            else
                (x,)
            end
        end |> cflatten
        # expand and come back
        return toexpr(Let(dargs, l.body), st)
    end

    funkyargs = get_symbolify(map(lhs, dargs))
    union_symbolify!(st.symbolify, funkyargs)

    Expr(:let,
         Expr(:block, map(p->toexpr(p, st), dargs)...),
         toexpr(l.body, st))
end

@matchable struct Func
    args::Vector
    kwargs
    body
end

"""
    Func(args, kwargs, body)

A function.

- `args` is a vector of expressions
- `kwargs` is a vector of `Assignment`s
- `body` is the body of the function

**Special features in `args`**:

- args can contain `DestructuredArgs`
- call expressions

For example,

```julia

julia> @syms a b c t f(d) x(t) y(t) z(t)
(a, b, c, t, f(::Number)::Number, x(::Number)::Number, y(::Number)::Number, z(::Number)::Number)

julia> func = Func([a,x(t), DestructuredArgs([b, y(t)]), f], # args
                   [c ← 2, z(t) ← 42], # kwargs
                   f((a + b + c) / x(t) + y(t) + z(t)));

julia> toexpr(func)
:(function (a, var"x(t)", var"##arg#255", f; c = 2, var"z(t)" = 42)
      let b = var"##arg#255"[1], var"y(t)" = var"##arg#255"[2]
          f((+)(var"y(t)", var"z(t)", (*)((+)(a, b, c), (inv)(var"x(t)"))))
      end
  end)
```

- the second argument is a `DestructuredArgs`, in the `Expr` form, it is given a random name, and is expected to receive a vector or tuple of size 2 containing the values of `c` and `y(t)`. The let block that is automatically generated "destructures" these arguments.
- `x(t)` and `y(t)` have been replaced with `var"x(t)"` and `var"y(t)"` symbols throughout
the generated Expr. This makes sure that we are not actually calling the expressions `x(t)` or `y(t)` but instead passing the right values in place of the whole expression.
- `f` is also a function-like symbol, same as `x` and `y`, but since the `args` array contains `f` as itself rather than as say, `f(t)`, it does not become a `var"f(t)"`. The generated function expects a function of one argument to be passed in the position of `f`.

An example invocation of this function is:

```julia
julia> executable = eval(toexpr(func))
#10 (generic function with 1 method)

julia> exec(1, 2.0, [2,3.0], x->string(x); var"z(t)" = sqrt(42))
"11.98074069840786"
```
"""
Func

toexpr_kw(f, st) = Expr(:kw, toexpr(f, st).args...)

function toexpr(f::Func, st)
    funkyargs = get_symbolify(vcat(f.args, map(lhs, f.kwargs)))
    union_symbolify!(st.symbolify, funkyargs)
    dargs = filter(x->x isa DestructuredArgs, f.args)
    if !isempty(dargs)
        body = Let(dargs, f.body)
    else
        body = f.body
    end
    if isempty(f.kwargs)
        :(function ($(map(x->toexpr(x, st), f.args)...),)
              $(toexpr(body, st))
          end)
    else
        :(function ($(map(x->toexpr(x, st), f.args)...),;
                    $(map(x->toexpr_kw(x, st), f.kwargs)...))
              $(toexpr(body, st))
          end)
    end
end

@matchable struct SetArray
    inbounds::Bool
    arr
    elems  # Either iterator of Pairs or just an iterator
end

"""
    SetArray(inbounds, arr, elems)

An expression representing setting of elements of `arr`.

By default, every element of `elems` is copied over to `arr`,

but if `elems` contains `AtIndex(i, val)` objects, then `arr[i] = val`
is performed in its place.

`inbounds` is a boolean flag, `true` surrounds the resulting expression
in an `@inbounds`.
"""
SetArray

@matchable struct AtIndex
    i
    elem
end

function toexpr(a::AtIndex, st)
    toexpr(a.elem, st)
end

function toexpr(s::SetArray, st)
    ex = quote
        $([:($(toexpr(s.arr, st))[$(ex isa AtIndex ? ex.i : i)] = $(toexpr(ex, st)))
           for (i, ex) in enumerate(s.elems)]...)
        nothing
    end
    s.inbounds ? :(@inbounds $ex) : ex
end

@matchable struct MakeArray
    elems
    similarto # Must be either a reference to an array or a concrete type
    output_eltype
end

"""
    MakeArray(elems, similarto, [output_eltype=nothing])

An expression which constructs an array.

- `elems` is the output array
- `similarto` can either be a type, or some symbol that is an array whose type needs to
   be emulated. If `similarto` is a StaticArrays.SArray, then the output array is also
   created as an `SArray`, similarly, an `Array` will result in an `Array`, and a
   `LabelledArrays.SLArray` will result in a labelled static array.
- `output_eltype`: if set, then forces the element type of the output array to be this.
   by default, the output type is inferred automatically.

You can define:
```
@inline function create_array(A::Type{<:MyArray},a
                              ::Nothing, d::Val{dims}, elems...) where dims

# and

@inlline function create_array(::Type{<:MyArray}, T, ::Val{dims}, elems...) where dims
```

which creates an array of size `dims` using the elements `elems` and eltype `T`, to allow
`MakeArray` to create arrays similarto `MyArray`s.

"""
MakeArray

MakeArray(elems, similarto) = MakeArray(elems, similarto, nothing)

function toexpr(a::MakeArray, st)
    similarto = toexpr(a.similarto, st)
    T = similarto isa Type ? similarto : :(typeof($similarto))
    ndim = ndims(a.elems)
    elT = a.output_eltype
    quote
        $create_array($T,
                     $elT,
                     Val{$ndim}(),
                     Val{$(size(a.elems))}(),
                     $(map(x->toexpr(x, st), a.elems)...),)
    end
end

## Array
@inline function _create_array(::Type{<:Array}, T, ::Val{dims}, elems...) where dims
    arr = Array{T}(undef, dims)
    @assert prod(dims) == nfields(elems)
    @inbounds for i=1:prod(dims)
        arr[i] = elems[i]
    end
    arr
end

@inline function create_array(A::Type{<:Array}, T, ::Val, d::Val, elems...)
    _create_array(A, T, d, elems...)
end

@inline function create_array(A::Type{<:Array}, ::Nothing, ::Val, d::Val{dims}, elems...) where dims
    T = promote_type(map(typeof, elems)...)
    _create_array(A, T, d, elems...)
end

## Vector
#
@inline function create_array(::Type{<:Array}, ::Nothing, ::Val{1}, ::Val{dims}, elems...) where dims
    [elems...]
end

@inline function create_array(::Type{<:Array}, T, ::Val{1}, ::Val{dims}, elems...) where dims
    T[elems...]
end

## Matrix

@inline function create_array(::Type{<:Array}, ::Nothing, ::Val{2}, ::Val{dims}, elems...) where dims
    vhcat(dims, elems...)
end

@inline function create_array(::Type{<:Array}, T, ::Val{2}, ::Val{dims}, elems...) where dims
    typed_vhcat(T, dims, elems...)
end


vhcat(sz::Tuple{Int,Int}, xs::T...) where {T} = typed_vhcat(T, sz, xs...)
vhcat(sz::Tuple{Int,Int}, xs::Number...) = typed_vhcat(Base.promote_typeof(xs...), sz, xs...)
vhcat(sz::Tuple{Int,Int}, xs...) = typed_vhcat(Base.promote_eltypeof(xs...), sz, xs...)

function typed_vhcat(::Type{T}, sz::Tuple{Int, Int}, xs...) where T
    nr,nc = sz
    a = Matrix{T}(undef, nr, nc)
    k = 1
    for j=1:nc
        @inbounds for i=1:nr
            a[i, j] = xs[k]
            k += 1
        end
    end
    a
end

## Arrays of the special kind
@inline function create_array(A::Type{<:SubArray{T,N,P,I,L}}, S, nd::Val, d::Val, elems...) where {T,N,P,I,L}
    create_array(P, S, nd, d, elems...)
end

@inline function create_array(A::Type{<:PermutedDimsArray{T,N,perm,iperm,P}}, S, nd::Val, d::Val, elems...) where {T,N,perm,iperm,P}
    create_array(P, S, nd, d, elems...)
end


@inline function create_array(A::Type{<:Transpose{T,P}}, S, nd::Val, d::Val, elems...) where {T,P}
    create_array(P, S, nd, d, elems...)
end

@inline function create_array(A::Type{<:UpperTriangular{T,P}}, S, nd::Val, d::Val, elems...) where {T,P}
    create_array(P, S, nd, d, elems...)
end

## SArray
@inline function create_array(::Type{<:SArray}, ::Nothing, nd::Val, ::Val{dims}, elems...) where dims
    SArray{Tuple{dims...}}(elems...)
end

@inline function create_array(::Type{<:SArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    SArray{Tuple{dims...}, T}(elems...)
end

## MArray
@inline function create_array(::Type{<:MArray}, ::Nothing, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}}(elems...)
end

@inline function create_array(::Type{<:MArray}, T, nd::Val, ::Val{dims}, elems...) where dims
    MArray{Tuple{dims...}, T}(elems...)
end

## LabelledArrays
@inline function create_array(A::Type{<:SLArray}, T, nd::Val, d::Val{dims}, elems...) where {dims}
    a = create_array(SArray, T, nd, d, elems...)
    if nfields(dims) === ndims(A)
        similar_type(A, eltype(a), Size(dims))(a)
    else
        a
    end
end

@inline function create_array(A::Type{<:LArray}, T, nd::Val, d::Val{dims}, elems...) where {dims}
    data = create_array(Array, T, nd, d, elems...)
    if nfields(dims) === ndims(A)
        LArray{eltype(data),nfields(dims),typeof(data),LabelledArrays.symnames(A)}(data)
    else
        data
    end
end

## We use a separate type for Sparse Arrays to sidestep the need for
## iszero to be defined on the expression type
@matchable struct MakeSparseArray{S<:AbstractSparseArray}
    array::S
end

"""
    MakeSpaseArray(array)

An expression which creates a `SparseMatrixCSC` or a `SparseVector`.

The generated expression contains the sparsity information of `array`,

it only creates the `nzval` field at run time.
"""
MakeSparseArray

function toexpr(a::MakeSparseArray{<:SparseMatrixCSC}, st)
    sp = a.array
    :(SparseMatrixCSC($(sp.m), $(sp.n),
                      $(copy(sp.colptr)), $(copy(sp.rowval)),
                      [$(toexpr.(sp.nzval, (st,))...)]))
end

function toexpr(a::MakeSparseArray{<:SparseVector}, st)
    sp = a.array
    :(SparseVector($(sp.n),
                   $(copy(sp.nzind)),
                   [$(toexpr.(sp.nzval, (st,))...)]))
end

@matchable struct MakeTuple
    elems
end

"""
    MakeTuple(tup)

Make a Tuple from a tuple of expressions.
"""
MakeTuple

function toexpr(a::MakeTuple, st)
    :(($(toexpr.(a.elems, (st,))...),))
end

struct Multithreaded end
"""
    SpawnFetch{ParallelType}(funcs [, args], reduce)

Run every expression in `funcs` in its own task, the expression
should be a `Func` object and is passed to `Threads.Task(f)`.
If `Func` takes arguments, then the arguments must be passed in as `args`--a vector of vector of arguments to each function in `funcs`. We don't use `@spawn` in order to support RuntimeGeneratedFunctions which disallow closures, instead we interpolate these functions or closures as smaller RuntimeGeneratedFunctions.

`reduce` function is used to combine the results of executing `exprs`. A SpawnFetch expression returns the reduced result.


Use `Symbolics.MultithreadedForm` ParallelType from the Symbolics.jl package to get the RuntimeGeneratedFunction version SpawnFetch.

`ParallelType` can be used to define more parallelism types
SymbolicUtils supports `Multithreaded` type. Which spawns
threaded tasks.
"""
struct SpawnFetch{Typ}
    exprs::Vector
    args::Union{Nothing, Vector}
    combine
end

(::Type{SpawnFetch{T}})(exprs, combine) where {T} = SpawnFetch{T}(exprs, nothing, combine)

function toexpr(p::SpawnFetch{Multithreaded}, st)
    args = isnothing(p.args) ? Iterators.repeated((), length(p.exprs)) : p.args
    spawns = map(p.exprs, args) do thunk, xs
        :(Base.Threads.@spawn $(toexpr(thunk, st))($(toexpr.(xs, (st,))...)))
    end
    quote
        $(toexpr(p.combine, st))(map(fetch, ($(spawns...),))...)
    end
end

"""
    LiteralExpr(ex)

Literally `ex`, an `Expr`. `toexpr` on `LiteralExpr` recursively calls
`toexpr` on any interpolated symbolic expressions.
"""
struct LiteralExpr
    ex
end

recurse_expr(ex::Expr, st) = Expr(ex.head, recurse_expr.(ex.args, (st,))...)
recurse_expr(ex, st) = toexpr(ex, st)

function toexpr(exp::LiteralExpr, st)
    recurse_expr(exp.ex, st)
end


### Code-related utilities

### Common subexprssion evaluation

@inline newsym(::Type{T}) where T = Sym{T}(gensym("cse"))

function _cse!(mem, expr)
    istree(expr) || return expr
    op = _cse!(mem, operation(expr))
    args = map(Base.Fix1(_cse!, mem), arguments(expr))
    t = similarterm(expr, op, args)

    v, dict = mem
    update! = let v=v, t=t
        () -> begin
            var = newsym(symtype(t))
            push!(v, var ← t)
            length(v)
        end
    end
    v[get!(update!, dict, t)].lhs
end

function cse(expr)
    !istree(expr) && return expr
    assignments = Assignment[]
    final = _cse!((assignments, Dict{Any,Int}()), expr)
    Let(assignments, final)
end

function _cse(exprs::AbstractArray)
    assignments = Assignment[]
    mem = (assignments, Dict{Any,Int}())
    final = map(Base.Fix1(_cse!, mem), exprs)
    assignments, final
end

function cse(x::MakeArray)
    assigns, expr = _cse(x.elems)
    Let(assigns, MakeArray(expr, x.similarto, x.output_eltype))
end

function cse(x::SetArray)
    assigns, expr = _cse(x.elems)
    Let(assigns, SetArray(x.inbounds, x.arr, expr))
end

function cse(x::MakeSparseArray)
    sp = x.array
    assigns, expr = _cse(sp.nzval)
    if sp isa SparseMatrixCSC
        Let(assigns, MakeSparseArray(SparseMatrixCSC(sp.m, sp.n,
                                                     sp.colptr, sp.rowval, exprs)))
    else
        Let(assigns, MakeSparseArray(SparseVector(sp.n, sp.nzinds, exprs)))
    end
end

end
