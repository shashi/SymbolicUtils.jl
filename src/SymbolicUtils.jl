module SymbolicUtils

export @syms, term, showraw, hasmetadata, getmetadata, setmetadata

# Sym, Term,
# Add, Mul and Pow
using DataStructures
using Setfield
import Setfield: PropertyLens
import Base: +, -, *, /, //, \, ^, ImmutableDict
using ConstructionBase
include("types.jl")

# Methods on symbolic objects
using SpecialFunctions, NaNMath
import IfElse: ifelse  # need to not bring IfElse name in or it will clash with Rewriters.IfElse
include("methods.jl")

# LinkedList, simplification utilities
include("utils.jl")

export Rewriters

# A library for composing together expr -> expr functions
include("rewriters.jl")

using .Rewriters

using Combinatorics: permutations, combinations
export @rule, @acrule, RuleSet

# Rule type and @rule macro
include("rule.jl")

# Matching a Rule
include("matchers.jl")

# Convert to an efficient multi-variate polynomial representation
import MultivariatePolynomials
const MP = MultivariatePolynomials
import DynamicPolynomials
export expand
include("abstractalgebra.jl")

# Term ordering
include("ordering.jl")

# Default rules for expression simplification
include("simplify_rules.jl")

# API = simplify + substitute
export simplify, substitute
include("api.jl")

include("code.jl")

# ADjoints
include("adjoints.jl")

# TermInterface.jl 
include("terminterface.jl")

end # module
