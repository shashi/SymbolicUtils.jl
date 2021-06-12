include("fuzzlib.jl")

using Random: seed!

seed!(6174)
# expand fuzz
@time for i=1:500
    fuzz_test(5, num_spec, SymbolicUtils.expand; min_depth=3)
end
# num fuzz
@time for i=1:1500
    fuzz_test(5, num_spec)
end
# bool fuzz
@time for i=1:500
    seed!(i)
    fuzz_test(5, bool_spec)
end
# fuzz addmulpow
@time for i=1:100
    fuzz_addmulpow(1)
end
@time for i=1:50
    fuzz_addmulpow(2)
end
@time for i=1:25
    fuzz_addmulpow(3)
end
@time for i=1:12
    fuzz_addmulpow(4)
end
