
@inline alwaystrue(x) = true

# Matcher patterns with Slot and Segment

# matches one term
# syntax:  ~x
struct Slot{P}
    name::Symbol
    predicate::P
end

Slot(s) = Slot(s, alwaystrue)

Base.isequal(s1::Slot, s2::Slot) = s1.name == s2.name

Base.show(io::IO, s::Slot) = (print(io, "~"); print(io, s.name))

# matches zero or more terms
# syntax: ~~x
struct Segment{F}
    name::Symbol
    predicate::F
end

ismatch(s::Segment, t) = s.predicate(t)

Segment(s) = Segment(s, alwaystrue)

Base.show(io::IO, s::Segment) = (print(io, "~~"); print(io, s.name))

makesegment(s::Symbol, keys) = (push!(keys, s); Segment(s))

function makesegment(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a segment is ~~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Segment($(QuoteNode(name)), $(esc(s.args[2]))))
end

makeslot(s::Symbol, keys) = (push!(keys, s); Slot(s))

function makeslot(s::Expr, keys)
    if !(s.head == :(::))
        error("Syntax for specifying a slot is ~x::\$predicate, where predicate is a boolean function")
    end

    name = s.args[1]

    push!(keys, name)
    :(Slot($(QuoteNode(name)), $(esc(s.args[2]))))
end

function makepattern(expr, keys)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    # matches ~~x::predicate
                    makesegment(expr.args[2].args[2], keys)
                else
                    # matches ~x::predicate
                    makeslot(expr.args[2], keys)
                end
            else
                :(term($(map(x->makepattern(x, keys), expr.args)...); type=Any))
            end
        else
            error("Unsupported Expr of type $(expr.head) found in pattern")
        end
    else
        # treat as a literal
        return esc(expr)
    end
end

function makeconsequent(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(~)
                if expr.args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2]))))
                elseif expr.args[2] isa Expr && expr.args[2].args[1] == :(~)
                    @assert expr.args[2].args[2] isa Symbol
                    return :(getindex(__MATCHES__, $(QuoteNode(expr.args[2].args[2]))))
                end
            else
                return Expr(:call, map(makeconsequent, expr.args)...)
            end
        else
            return Expr(expr.head, map(makeconsequent, expr.args)...)
        end
    else
        # treat as a literal
        return esc(expr)
    end
end

abstract type AbstractRule end # Currently doesn't really do anything. Can be removed.

#-----------------------------
#### Regular Rewriting Rules

struct Rule{L, M, R} <: AbstractRule
    expr::Expr               # rule pattern stored for pretty printing
    lhs::L                   # the pattern
    matcher::M               # matcher(lhs)
    rhs::R                   # consequent
    depth::Int               # number of levels of expr this rule touches
end

getdepth(r::Rule) = r.depth

function rule_depth(rule, d=0, maxdepth=0)
    if rule isa Term
        maxdepth = reduce(max, (rule_depth(r, d+1, maxdepth) for r in arguments(rule)), init=1)
    elseif rule isa Slot || rule isa Segment
        maxdepth = max(d, maxdepth)
    end
    return maxdepth
end

function Base.show(io::IO, r::Rule)
    Base.print(io, r.expr)
end

const EMPTY_DICT = ImmutableDict{Symbol, Any}(:____, nothing)

function (r::Rule)(term)
    rhs = r.rhs

    try
        return r.matcher((term,), EMPTY_DICT) do bindings, n
            # n == 1 means that exactly one term of the input (term,) was matched
            n === 1 ? (@timer "RHS" rhs(bindings)) : nothing
        end
    catch err
        throw(RuleRewriteError(r, term))
    end
end

"""
    @rule LHS => RHS

Creates a `Rule` object. A rule object is callable, and  takes an expression and rewrites
it if it matches the LHS pattern to the RHS pattern, returns `nothing` otherwise.
The rule language is described below.

LHS can be any possibly nested function call expression where any of the arugments can
optionally be a Slot (`~x`) or a Segment (`~~x`) (described below).

If an expression matches LHS entirely, then it is rewritten to the pattern in the RHS
Segment (`~x`) and slot variables (`~~x`) on the RHS will substitute the result of the
matches found for these variables in the LHS.

**Slot**:

A Slot variable is written as `~x` and matches a single expression. `x` is the name of the variable. If a slot appears more than once in an LHS expression then expression matched at every such location must be equal (as shown by `isequal`).

_Example:_

Simple rule to turn any `sin` into `cos`:

```julia
julia> @syms a b c
(a, b, c)

julia> r = @rule sin(~x) => cos(~x)
sin(~x) => cos(~x)

julia> r(sin(1+a))
cos((1 + a))
```

A rule with 2 segment variables

```julia
julia> r = @rule sin(~x + ~y) => sin(~x)*cos(~y) + cos(~x)*sin(~y)
sin(~x + ~y) => sin(~x) * cos(~y) + cos(~x) * sin(~y)

julia> r(sin(a + b))
cos(a)*sin(b) + sin(a)*cos(b)
```

A rule that matches two of the same expressions:

```julia
julia> r = @rule sin(~x)^2 + cos(~x)^2 => 1
sin(~x) ^ 2 + cos(~x) ^ 2 => 1

julia> r(sin(2a)^2 + cos(2a)^2)
1

julia> r(sin(2a)^2 + cos(a)^2)
# nothing
```

**Segment**:

A Segment variable is written as `~~x` and matches zero or more expressions in the
function call.

_Example:_

This implements the distributive property of multiplication: `+(~~ys)` matches expressions
like `a + b`, `a+b+c` and so on. On the RHS `~~ys` presents as any old julia array.

```julia
julia> r = @rule ~x * +((~~ys)) => sum(map(y-> ~x * y, ~~ys));

julia> r(2 * (a+b+c))
((2 * a) + (2 * b) + (2 * c))
```

**Predicates**:

Predicates can be used on both `~x` and `~~x` by using the `~x::f` or `~~x::f`.
Here `f` can be any julia function. In the case of a slot the function gets a single
matched subexpression, in the case of segment, it gets an array of matched expressions.

The predicate should return `true` if the current match is acceptable, and `false`
otherwise.

```julia
julia> two_πs(x::Number) = abs(round(x/(2π)) - x/(2π)) < 10^-9
two_πs (generic function with 1 method)

julia> two_πs(x) = false
two_πs (generic function with 2 methods)

julia> r = @rule sin(~~x + ~y::two_πs + ~~z) => sin(+(~~x..., ~~z...))
sin(~(~x) + ~(y::two_πs) + ~(~z)) => sin(+(~(~x)..., ~(~z)...))

julia> r(sin(a+3π))

julia> r(sin(a+6π))
sin(a)

julia> r(sin(a+6π+c))
sin((a + c))
```

Predicate function gets an array of values if attached to a segment variable (`~~x`).

**Context**:

_In predicates_: Contextual predicates are functions wrapped in the `Contextual` type.
The function is called with 2 arguments: the expression and a context object
passed during a call to the Rule object (maybe done by passing a context to `simplify` or
a `RuleSet` object).

The function can use the inputs however it wants, and must return a boolean indicating
whether the predicate holds or not.

_In the consequent pattern_: Use `(@ctx)` to access the context object on the right hand side
of an expression.
"""
macro rule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    keys = Symbol[]
    lhs_term = makepattern(lhs, keys)
    unique!(keys)
    quote
        $(__source__)
        lhs_pattern = $(lhs_term)
        Rule($(QuoteNode(expr)),
             lhs_pattern,
             matcher(lhs_pattern),
             __MATCHES__ -> $(makeconsequent(rhs)),
             rule_depth($lhs_term))
    end
end

#-----------------------------
#### Associative Commutative Rules

struct ACRule{F,R} <: AbstractRule
    sets::F
    rule::R
    arity::Int
end

Rule(acr::ACRule)   = acr.rule
getdepth(r::ACRule) = getdepth(r.rule)

macro acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(permutations, $(esc(:(@rule($(expr))))), $arity)
    end
end

macro ordered_acrule(expr)
    arity = length(expr.args[2].args[2:end])
    quote
        ACRule(combinations, $(esc(:(@rule($(expr))))), $arity)
    end
end

Base.show(io::IO, acr::ACRule) = print(io, "ACRule(", acr.rule, ")")

function (acr::ACRule)(term)
    r = Rule(acr)
    if !istree(term)
        r(term)
    else
        f =  operation(term)
        # Assume that the matcher was formed by closing over a term
        if f != operation(r.lhs) # Maybe offer a fallback if m.term errors.
            return nothing
        end

        T = symtype(term)
        args = arguments(term)

        itr = acr.sets(eachindex(args), acr.arity)

        for inds in itr
            result = r(Term{T}(f, @views args[inds]))
            if !isnothing(result)
                # Assumption: inds are unique
                length(args) == length(inds) && return result
                return similarterm(term, f, [result, (args[i] for i in eachindex(args) if i ∉ inds)...])
            end
        end
    end
end

#-----------------------------
#### Numeric Rules

function expr_to_canon(expr)
    if expr isa Expr
        if expr.head === :call
            if expr.args[1] === :(-)
                if length(expr.args) == 2
                    return :((-1)*$(expr_to_canon(expr.args[2])))
                elseif !(expr.args[3] isa Number)
                    return :($(expr_to_canon(expr.args[2])) + (-1)*$(expr_to_canon(expr.args[3])))
                else
                    return :($(expr_to_canon(expr.args[2])) + $(-expr.args[3]))
                end
            elseif expr.args[1] === :(/)
                if !(expr.args[2] isa Number) || expr.args[2] != 1
                    if !(expr.args[3] isa Number) && !(expr.args[3] in [:π, :ℯ, :pi])
                        return :($(expr_to_canon(expr.args[2])) * $(expr_to_canon(expr.args[3]))^(-1))
                    else
                        return :($(eval(:(inv($(expr.args[3]))))) * $(expr_to_canon(expr.args[2])))
                    end
                else
                    # literal number
                    return :($(expr_to_canon(expr.args[3]))^(-1))
                end
            elseif expr.args[1] === :(\)
                return expr_to_canon(:($(expr.args[3]) / $(expr.args[2])))
            elseif expr.args[1] === :(//)
                if !(expr.args[3] isa Number) && !(expr.args[3] in [:π, :ℯ, :pi])
                    return expr_to_canon(:($(expr.args[2]) / $(expr.args[3])))
                else #if expr.args[3] isa Integer
                    return expr_to_canon(:($(1//eval(expr.args[3])) * $(expr.args[2])))
                end
            else
                return :($(expr.args[1])($(expr_to_canon.(expr.args[2:end])...)))
            end
        end
    else
        # treat as a literal
        return expr
    end
end

macro numrule(expr)
    @assert expr.head == :call && expr.args[1] == :(=>)
    lhs,rhs = expr.args[2], expr.args[3]
    lhs = expr_to_canon(lhs)
    expr = :($lhs => $rhs)
    quote
        $(esc(:(@rule($(expr)))))
    end
end

struct RuleRewriteError
    rule
    expr
end

getdepth(::Any) = typemax(Int)

@noinline function Base.showerror(io::IO, err::RuleRewriteError)
    msg = "Failed to apply rule $(err.rule) on expression "
    msg *= sprint(io->showraw(io, err.expr))
    print(io, msg)
end

function timerewrite(f)
    if !TIMER_OUTPUTS
        error("timerewrite must be called after enabling " *
              "TIMER_OUTPUTS in the main file of this package")
    end
    reset_timer!()
    being_timed[] = true
    x = f()
    being_timed[] = false
    print_timer()
    println()
    x
end


"""
    @timerewrite expr

If `expr` calls `simplify` or a `RuleSet` object, track the amount of time
it spent on applying each rule and pretty print the timing.

This uses [TimerOutputs.jl](https://github.com/KristofferC/TimerOutputs.jl).

## Example:

```julia

julia> expr = foldr(*, rand([a,b,c,d], 100))
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)

julia> @timerewrite simplify(expr)
 ────────────────────────────────────────────────────────────────────────────────────────────────
                                                         Time                   Allocations
                                                 ──────────────────────   ───────────────────────
                Tot / % measured:                     340ms / 15.3%           92.2MiB / 10.8%

 Section                                 ncalls     time   %tot     avg     alloc   %tot      avg
 ────────────────────────────────────────────────────────────────────────────────────────────────
 ACRule((~y) ^ ~n * ~y => (~y) ^ (~n ...    667   11.1ms  21.3%  16.7μs   2.66MiB  26.8%  4.08KiB
   RHS                                       92    277μs  0.53%  3.01μs   14.4KiB  0.14%     160B
 ACRule((~x) ^ ~n * (~x) ^ ~m => (~x)...    575   7.63ms  14.6%  13.3μs   1.83MiB  18.4%  3.26KiB
 (*)(~(~(x::!issortedₑ))) => sort_arg...    831   6.31ms  12.1%  7.59μs    738KiB  7.26%     910B
   RHS                                      164   3.03ms  5.81%  18.5μs    250KiB  2.46%  1.52KiB
   ...
   ...
 ────────────────────────────────────────────────────────────────────────────────────────────────
(a ^ 26) * (b ^ 30) * (c ^ 16) * (d ^ 28)
```
"""
macro timerewrite(expr)
    :(timerewrite(()->$(esc(expr))))
end

Base.@deprecate RuleSet(x) Postwalk(Chain(x))
