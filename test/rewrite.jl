@syms a b c

@testset "Equality" begin
    @eqtest a == a
    @eqtest a != b
    @eqtest a*b == a*b
    @eqtest a*b != a
    @eqtest a != a*b
end

@testset "Literal Matcher" begin
    r = @rule 1 => 4
    @test r(1) === 4
    @test r(1.0) === 4
    @test r(2) === nothing
end

@testset "Slot matcher" begin
    @test @rule(~x => true)("?") === true
    @test @rule( ~x => ~x)(2) === 2
end

@testset "Number matcher" begin
    @test @numrule(-~x => ~x)(-a) === a
    @test @numrule(~x-~y => ~x)(a-b) === a
    @test @numrule(1/~x => ~x)(1/a) === a
    @test @numrule(1/~x => ~x)(a\1) === a
    @test @numrule(~x\1 => ~x)(1/a) === a
    @test @numrule(~x\1 => ~x)(a\1) === a
    @test @numrule(~x//2 => ~x)(a//2) === a
    # there is a difference in representations between numeric // and
    # symbolic
    @test @numrule(~x//~y => ~x)(a//b) === a
end

@testset "Term matcher" begin
    @test @rule(sin(~x) => ~x)(sin(a)) === a
    @eqtest @rule(sin(~x) => ~x)(sin(a^2)) == a^2
    @test @rule(sin(~x) => ~x)(sin(a)^2) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(a^2)) === nothing
    @test @rule(sin(sin(~x)) => ~x)(sin(sin(a))) === a
    @test @rule(sin(~x)^2 => ~x)(sin(a)^2) === a
end

@testset "Equality matching" begin
    @test @rule((~x)^(~x) => ~x)(a^a) === a
    @test @rule((~x)^(~x) => ~x)(b^a) === nothing
    @test @rule((~x)^(~x) => ~x)(a+a) === nothing
    @eqtest @rule((~x)^(~x) => ~x)(sin(a)^sin(a)) == sin(a)
    @eqtest @rule((~x*~y + ~x*~z)  => ~x * (~y+~z))(a*b + a*c) == a*(b+c)

    @eqtest @rule(+(~~x) => ~~x)(a + b) == [a,b]
    @eqtest @rule(+(~~x) => ~~x)(term(+, a, b, c)) == [a,b,c]
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y))(term(+,9,8,9,type=Any)) == ([9,],8)
    @eqtest @rule(+(~~x,~y, ~~x) => (~~x, ~y, ~~x))(term(+,9,8,9,9,8,type=Any)) == ([9,8], 9, [9,8])
    @eqtest @rule(+(~~x,~y,~~x) => (~~x, ~y, ~~x))(term(+,6,type=Any)) == ([], 6, [])
end
