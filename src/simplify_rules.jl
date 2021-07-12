using .Rewriters

let
    PLUS_RULES = [
        @rule(~x::isnotflat(+) => flatten_term(+, ~x))
        @rule(~x::needs_sorting(+) => sort_args(+, ~x))
        @ordered_acrule(~a::is_literal_number + ~b::is_literal_number => ~a + ~b)

        @acrule(*(~~x) + *(~β, ~~x) => *(1 + ~β, (~~x)...))
        @acrule(*(~α, ~~x) + *(~β, ~~x) => *(~α + ~β, (~~x)...))
        @acrule(*(~~x, ~α) + *(~~x, ~β) => *(~α + ~β, (~~x)...))

        @acrule(~x + *(~β, ~x) => *(1 + ~β, ~x))
        @acrule(*(~α::is_literal_number, ~x) + ~x => *(~α + 1, ~x))
        @rule(+(~~x::hasrepeats) => +(merge_repeats(*, ~~x)...))

        @ordered_acrule((~z::_iszero + ~x) => ~x)
        @rule(+(~x) => ~x)
    ]

    TIMES_RULES = [
        @rule(~x::isnotflat(*) => flatten_term(*, ~x))
        @rule(~x::needs_sorting(*) => sort_args(*, ~x))

        @ordered_acrule(~a::is_literal_number * ~b::is_literal_number => ~a * ~b)
        @rule(*(~~x::hasrepeats) => *(merge_repeats(^, ~~x)...))

        @acrule((~y)^(~n) * ~y => (~y)^(~n+1))
        @ordered_acrule((~x)^(~n) * (~x)^(~m) => (~x)^(~n + ~m))

        @ordered_acrule((~z::_isone  * ~x) => ~x)
        @ordered_acrule((~z::_iszero *  ~x) => ~z)
        @rule(*(~x) => ~x)
    ]


    POW_RULES = [
        @rule(^(*(~~x), ~y::_isinteger) => *(map(a->pow(a, ~y), ~~x)...))
        @rule((((~x)^(~p::_isinteger))^(~q::_isinteger)) => (~x)^((~p)*(~q)))
        @rule(^(~x, ~z::_iszero) => 1)
        @rule(^(~x, ~z::_isone) => ~x)
        @rule(inv(~x) => ~x ^ -1)
    ]

    ASSORTED_RULES = [
        @rule(identity(~x) => ~x)
        @rule(-(~x) => -1*~x)
        @rule(-(~x, ~y) => ~x + -1(~y))
        @rule(~x::_isone \ ~y => ~y)
        @rule(~x \ ~y => ~y / (~x))
        @rule(~x / ~y => ~x * pow(~y, -1))
        @rule(one(~x) => one(symtype(~x)))
        @rule(zero(~x) => zero(symtype(~x)))
        @rule(conj(~x::_isreal) => ~x)
        @rule(real(~x::_isreal) => ~x)
        @rule(imag(~x::_isreal) => zero(symtype(~x)))
        @rule(ifelse(~x::is_literal_number, ~y, ~z) => ~x ? ~y : ~z)
    ]

    TRIG_RULES = [
        @acrule(sin(~x)^2 + cos(~x)^2 => one(~x))
        @acrule(sin(~x)^2 + -1        => cos(~x)^2)
        @acrule(cos(~x)^2 + -1        => sin(~x)^2)

        @acrule(tan(~x)^2 + -1*sec(~x)^2 => one(~x))
        @acrule(tan(~x)^2 +  1 => sec(~x)^2)
        @acrule(sec(~x)^2 + -1 => tan(~x)^2)

        @acrule(cot(~x)^2 + -1*csc(~x)^2 => one(~x))
        @acrule(cot(~x)^2 +  1 => csc(~x)^2)
        @acrule(csc(~x)^2 + -1 => cot(~x)^2)

        # double-angle rules
        @acrule(cos(~x)^2 + -1*sin(~x)^2   => cos(2 * ~x))
        @acrule(2*sin(~x)*cos(~x)        => sin(2 * ~x))
        @acrule(cosh(~x)^2 + sinh(~x)^2 => cosh(2 * ~x))
        @acrule(2*sinh(~x)*cosh(~x)      => sinh(2 * ~x))

        # addition/subtraction formulas
        @acrule(sin(~x)cos(~y) + cos(~x)sin(~y) => sin(~x + ~y))
        @acrule(sin(~x)cos(~y) + -1*cos(~x)*sin(~y) => sin(~x - ~y))
        @acrule(cos(~x)cos(~y) + sin(~x)sin(~y) => cos(~x - ~y))
        @acrule(cos(~x)cos(~y) + -1*sin(~x)*sin(~y) => cos(~x + ~y))
        
        @acrule(sinh(~x)cosh(~y) + cosh(~x)sinh(~y) => sinh(~x + ~y))
        @acrule(cosh(~x)cosh(~y) + sinh(~x)sinh(~y) => cosh(~x + ~y))
        @acrule(sinh(~x)cosh(~y) + -1*cosh(~x)*sinh(~y) => sinh(~x - ~y))
        @acrule(cosh(~x)cosh(~y) + -1*sinh(~x)*sinh(~y) => cosh(~x - ~y))
        ]

    BOOLEAN_RULES = [
        @rule((true | (~x)) => true)
        @rule(((~x) | true) => true)
        @rule((false | (~x)) => ~x)
        @rule(((~x) | false) => ~x)
        @rule((true & (~x)) => ~x)
        @rule(((~x) & true) => ~x)
        @rule((false & (~x)) => false)
        @rule(((~x) & false) => false)

        @rule(!(~x) & ~x => false)
        @rule(~x & !(~x) => false)
        @rule(!(~x) | ~x => true)
        @rule(~x | !(~x) => true)
        @rule(xor(~x, !(~x)) => true)
        @rule(xor(~x, ~x) => false)

        @rule(~x == ~x => true)
        @rule(~x != ~x => false)
        @rule(~x < ~x => false)
        @rule(~x > ~x => false)

        # simplify terms with no symbolic arguments
        # e.g. this simplifies term(isodd, 3, type=Bool)
        # or term(!, false)
        @rule((~f)(~x::is_literal_number) => (~f)(~x))
        # and this simplifies any binary comparison operator
        @rule((~f)(~x::is_literal_number, ~y::is_literal_number) => (~f)(~x, ~y))
    ]

    function number_simplifier()
        rule_tree = [If(istree, Chain(ASSORTED_RULES)),
                     If(is_operation(+),
                        Chain(PLUS_RULES)),
                     If(is_operation(*),
                        Chain(TIMES_RULES)),
                     If(is_operation(^),
                        Chain(POW_RULES))] |> RestartedChain

        rule_tree
    end

    trig_simplifier(;kw...) = Chain(TRIG_RULES)

    bool_simplifier() = Chain(BOOLEAN_RULES)

    global default_simplifier
    global serial_simplifier
    global threaded_simplifier
    global serial_simplifier
    global serial_expand_simplifier

    function default_simplifier(; kw...)
        IfElse(has_trig,
               Postwalk(IfElse(x->symtype(x) <: Number,
                               Chain((number_simplifier(),
                                      trig_simplifier())),
                               If(x->symtype(x) <: Bool,
                                  bool_simplifier()))
                        ; kw...),
               Postwalk(Chain((If(x->symtype(x) <: Number,
                                  number_simplifier()),
                               If(x->symtype(x) <: Bool,
                                  bool_simplifier())))
                        ; kw...))
    end

    # reduce overhead of simplify by defining these as constant
    serial_simplifier = If(istree, Fixpoint(default_simplifier()))

    threaded_simplifier(cutoff) = Fixpoint(default_simplifier(threaded=true,
                                                              thread_cutoff=cutoff))

    serial_expand_simplifier = If(istree,
                                  Fixpoint(Chain((expand,
                                                  Fixpoint(default_simplifier())))))

end
