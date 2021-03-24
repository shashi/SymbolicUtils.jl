# Polynomial Normal Form

"""
    labels!(dict, t)

Find all terms that are not + and * and replace them
with a symbol, store the symbol => term mapping in `dict`.
"""
function labels! end

# Turn a Term into a multivariate polynomial
function labels!(dicts, t::Sym)
    sym2term, term2sym = dicts
    if !haskey(term2sym, t)
        sym2term[t] = t
        term2sym[t] = t
    end
    return t
end

function labels!(dicts, t, generic_recurse=true)
    if t isa Integer
        return t
    elseif istree(t) && (operation(t) == (*) || operation(t) == (+) || operation(t) == (-))
        tt = arguments(t)
        return similarterm(t, operation(t), map(x->labels!(dicts, x, generic_recurse), tt), symtype(t))
    elseif istree(t) && operation(t) == (^) && length(arguments(t)) > 1 && isnonnegint(arguments(t)[2])
        return similarterm(t, operation(t), map(x->labels!(dicts, x, generic_recurse), arguments(t)), symtype(t))
    else
        sym2term, term2sym = dicts
        if haskey(term2sym, t)
            return term2sym[t]
        end
        if istree(t)
            tt = arguments(t)
            sym = Sym{symtype(t)}(gensym(nameof(operation(t))))
            dicts2 = _dicts(dicts[2])
            if generic_recurse
                sym2term[sym] = similarterm(t, operation(t),
                                            map(x->to_mpoly(x, dicts)[1], arguments(t)),
                                            symtype(t))
            else
                sym2term[sym] = t
            end
        else
            sym = Sym{symtype(t)}(gensym("literal"))
            sym2term[sym] = t
        end

        term2sym[t] = sym

        return sym
    end
end

struct Factors
    facts::Vector
end
Base.isequal(f::Factors, q::Factors) = isequal(f.facts, q.facts)
Base.hash(f::Factors, u) = hash(f.facts, xor(u, 0xfac1fac1fac1fac1))
*(x::Factors, y::Factors) = Factors([x.facts; y.facts])
*(x::Factors, y) = Factors([x.facts; y])
*(x, y::Factors) = Factors([x; y.facts])
^(x::Factors, y) = Factors(x.facts .^ (y,))

ismpoly(x) = x isa MPoly || x isa Factors || x isa Integer
isnonnegint(x) = x isa Integer && x >= 0

_dicts(t2s=OrderedDict{Any, Sym}()) = (OrderedDict{Sym, Any}(), t2s)

let
    mpoly_preprocess = [@rule(identity(~x) => ~x)
                        @rule(zero(~x) => 0)
                        @rule(one(~x) => 1)]

    mpoly_rules = [@rule(~x::ismpoly - ~y::ismpoly => ~x + -1 * (~y))
                   @rule(-(~x) => -1 * ~x)
                   @acrule(~x::ismpoly + ~y::ismpoly => ~x + ~y)
                   @rule(+(~x) => ~x)
                   @rule(*(~x) => ~x)
                   @rule((~x::ismpoly)^(~a::isnonnegint) => (~x)^(~a))
                   @acrule(~x::ismpoly * ~y::ismpoly => ~x * ~y)]

    mpoly_factors_rules = push!(vec(mpoly_rules[1:end-1]),
                                @rule(~x::ismpoly * ~y::ismpoly => Factors([~x, ~y])))
    global const MPOLY_CLEANUP = Fixpoint(Postwalk(PassThrough(RestartedChain(mpoly_preprocess))))
    global const MPOLY_MAKER = Fixpoint(Postwalk(PassThrough(RestartedChain(mpoly_rules))))
    global const MPOLY_FACTORS = Fixpoint(Postwalk(PassThrough(RestartedChain(mpoly_factors_rules))))

    global to_mpoly
    function to_mpoly(t, dicts=_dicts())
        # term2sym is only used to assign the same
        # symbol for the same term -- in other words,
        # it does common subexpression elimination
        t = MPOLY_CLEANUP(t)
        sym2term, term2sym = dicts
        labeled = labels!((sym2term, term2sym), t)

        if isempty(sym2term)
            return MPOLY_MAKER(labeled), Dict{Sym,Any}()
        end

        ks = sort(collect(keys(sym2term)), lt=<ₑ)
        R, vars = PolynomialRing(ZZ, String.(nameof.(ks)))

        replace_with_poly = Dict{Sym,MPoly}(zip(ks, vars))
        t_poly = substitute(labeled, replace_with_poly, fold=false)
        MPOLY_MAKER(t_poly), sym2term
    end
end

function to_term(reference, x, dict)
    syms = Dict(zip(nameof.(keys(dict)), keys(dict)))
    dict = copy(dict)
    for (k, v) in dict
        dict[k] = _to_term(reference, v, dict, syms)
    end
    _to_term(reference, x, dict, syms)
end

function _to_term(reference, x::MPoly, dict, syms)

    function mul_coeffs(exps, ring)
        l = length(syms)
        ss = symbols(ring)
        monics = [e == 1 ? syms[ss[i]] : syms[ss[i]]^e for (i, e) in enumerate(exps) if !iszero(e)]
        if length(monics) == 1
            return monics[1]
        elseif length(monics) == 0
            return 1
        else
            return similarterm(reference, *, monics, symtype(reference))
        end
    end

    monoms = [mul_coeffs(exponent_vector(x, i), x.parent) for i in 1:x.length]
    if length(monoms) == 0
        return 0
    elseif length(monoms) == 1
        t = !isone(x.coeffs[1]) ?  monoms[1] * Int(x.coeffs[1]) : monoms[1]
    else
        t = similarterm(reference,
                        +,
                        map((x,y)->isone(y) ? x : Int(y)*x,
                            monoms, x.coeffs[1:length(monoms)]),
                        symtype(reference))
    end

    substitute(t, dict, fold=false)
end

function _to_term(reference, x, dict, vars)
    if istree(x)
        t=similarterm(x, operation(x), _to_term.((reference,), arguments(x), (dict,), (vars,)), symtype(x))
    else
        if haskey(dict, x)
            return dict[x]
        else
            return x
        end
    end
end

<ₑ(a::MPoly, b::MPoly) = false

function polynormalize(x)
    to_term(x, to_mpoly(x)...)
end

struct Div{T}
    num::Vector # factors
    den::Vector # factors
    labels::Tuple # dicts
end
# (x + y^2) -> [(x + y^2)]
# (x + y)*(x + z) -> [(x + y), (x + z)]
# (x + y)*(sin(x + z)) -> [(x + y), gensym]
# (x + y)*(2x + 1//2z) -> [(x + y), (2x + 1//2z)]
# (x + y)*(2.0x + 1.23z) -> [(x + y), (2x + gensym)] (using isinteger)
# plus labels
function /(a::Union{SN,Number}, b::SN)
    ds = _dicts()
    a = MPOLY_CLEANUP(a)
    b = MPOLY_CLEANUP(b)

    labeled_a = labels!(ds, a)
    labeled_b = labels!(ds, b)

    sym2term, term2sym = ds

    ks = sort(collect(keys(sym2term)), lt=<ₑ)
    R, vars = PolynomialRing(ZZ, String.(nameof.(ks)))

    replace_with_poly = Dict{Sym,MPoly}(zip(ks, vars))
    a_poly = substitute(labeled_a, replace_with_poly, fold=false)
    b_poly = substitute(labeled_b, replace_with_poly, fold=false)

    a_poly = MPOLY_FACTORS(a_poly)
    b_poly = MPOLY_FACTORS(b_poly)
    afacts, bfacts = rm_gcd!(a_poly, b_poly)
    Div{Number}(afacts, bfacts, ds)
end

function rm_gcd!(f::Factors, g::Factors)
    gg = g.facts
    ff = f.facts
    for i in 1:length(gg)
        for j in 1:length(ff)
            gc = gcd(gg[i], ff[j])
            if !isone(gc)
                gg[i] = divexact(gg[i], gc)
                ff[j] = divexact(ff[j], gc)
            end
        end
    end
    filter!(!isone, ff), filter!(!isone, gg)
end
rm_gcd!(f::Factors, g) = rm_gcd!(f, Factors([g]))
rm_gcd!(f, g::Factors) = rm_gcd!(Factors([f]), g)
rm_gcd!(f, g) = rm_gcd!(Factors([f]), Factors([g]))

\(a::SN, b::Union{Number, SN}) = b / a

\(a::Number, b::SN) = b / a

/(a::SN, b::Number) = inv(b) * a
