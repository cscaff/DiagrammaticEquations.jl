using Test
using Catlab
using DiagrammaticEquations

# Import Decapodes AST Nodes
using DiagrammaticEquations: Lit, AppCirc1, App1, App2, Plus, Mult, Tan, Eq
# TODO: Var conflicts with current Catlab main branch. Will be fixed in next PR. Manually using var as of now.

# Import PEG Rules
using DiagrammaticEquations: DecapodeExpr, SingleLineComment, MultiLineComment, Line, Statement, 
  Judgement, TypeName, Equation, SummationOperation, PrecMinusOperation, PrecDivOperation, MultOperation,
  PrecPowerOperation, Term, Grouping, Derivative, Compose, Call, CallName, UnaryOperator, Args, List, 
  CallList, Atom, Ident, Digit, PrecMinusOp, PrecDivOp, PrecPowerOp, OpSuffixes

# Unit Tests
#############

@testset "Overall Decapode Expression" begin
  @test DecapodeExpr("a::b\nc == d\ndt(X) == Y\n")[1] == DecaExpr(
    [Judgement(:a, :b, :I)],
    [Eq(DiagrammaticEquations.decapodes.Var(:c), DiagrammaticEquations.decapodes.Var(:d)),
      Eq(Tan(DiagrammaticEquations.decapodes.Var(:X)), DiagrammaticEquations.decapodes.Var(:Y))]
  )
  @test DecapodeExpr(" \n")[1] == DecaExpr([],[])
  @test DecapodeExpr("a::b\n")[1] == DecaExpr([Judgement(:a, :b, :I)],[])
  @test DecapodeExpr("a::b\nx::y\nz::l\na == b\n")[1] == DecaExpr(
    [Judgement(:a, :b, :I), Judgement(:x, :y, :I), Judgement(:z, :l, :I)],
    [Eq(DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b))]
  )
end

@testset "Comments" begin
  @test DecapodeExpr("a::b\n# This is a comment\n")[1] == DecaExpr([Judgement(:a, :b, :I)], [])
  @test DecapodeExpr("a::b\n#a::b\n")[1] == DecaExpr([Judgement(:a, :b, :I)], [])
  @test DecapodeExpr("# This is a comment\na::b\n")[1] == DecaExpr([Judgement(:a, :b, :I)], [])
  @test DecapodeExpr("a::b\n# This is comment\nc == d\n")[1] == DecaExpr(
    [Judgement(:a, :b, :I)], 
    [Eq(DiagrammaticEquations.decapodes.Var(:c), DiagrammaticEquations.decapodes.Var(:d))]
  )
  @test DecapodeExpr("#= This is a multi-line comment\nspanning multiple lines\n=# a::b\n")[1] == DecaExpr(
    [DiagrammaticEquations.decapodes.Judgement(:a, :b, :I)], []
  )
  @test DecapodeExpr("a::b\n#= Multi-line comment\nspanning lines\n=#\nc == d\n")[1] == DecaExpr(
    [Judgement(:a, :b, :I)], [Eq(DiagrammaticEquations.decapodes.Var(:c), DiagrammaticEquations.decapodes.Var(:d))]
  )
end

@testset "Lines" begin
  @test Line("a::b\n")[1] == Judgement(:a, :b, :I)
  @test Line("alpha::beta\n")[1] == Judgement(:alpha, :beta, :I)
  @test Line("x::y\n")[1] == Judgement(:x, :y, :I)
  @test Line("a == b\n")[1] == Eq(
  DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b)
  )
  @test Line("Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)\n")[1] == Eq(
  DiagrammaticEquations.decapodes.Var(Symbol("Ċ")), AppCirc1([:⋆₀⁻¹, :dual_d₁, :⋆₁], DiagrammaticEquations.decapodes.Var(Symbol("ϕ")))
  )
end

@testset "Statements" begin
  @test DiagrammaticEquations.Statement("a::b")[1] == Judgement(:a, :b, :I)
  @test DiagrammaticEquations.Statement("a == b")[1] == Eq(
  DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b)
  )
end

@testset "Judgements" begin
  @test Judgement("alpha::beta")[1] == Judgement(:alpha, :beta, :I)
  @test Judgement("a::Form{X}")[1] == Judgement(:a, :Form, :X)
  @test Judgement("(a, b, c)::d")[1] == [Judgement(:a, :d, :I), Judgement(:b, :d, :I), Judgement(:c, :d, :I)]
  @test Judgement("(a, b, c)::Form{X}")[1] == [Judgement(:a, :Form, :X), Judgement(:b, :Form, :X), Judgement(:c, :Form, :X)]
end

@testset "Type Naming" begin
  @test TypeName("Form0")[1] == :Form0
  @test TypeName("Form0{X}")[1] == [:Form0, :X]
|end

@testset "Equation" begin
  @test Equation("a == b")[1] == Eq(
    DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b)
  )
  @test Equation("a 
  ==
   b")[1] == Eq(
  DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b)
  )
  @test Equation("dt( X ) == Y")[1] == Eq(
    Tan(DiagrammaticEquations.decapodes.Var(:X)), DiagrammaticEquations.decapodes.Var(:Y)
  )
  @test Equation("f(n+1, N+2) * ∂ₜ(X) == ∘(a, b)(c)")[1] == Eq(
    App2(:*, App2(:f,
      Plus([DiagrammaticEquations.decapodes.Var(Symbol("n")), Lit(Symbol("1"))]),
      Plus([DiagrammaticEquations.decapodes.Var(Symbol("N")), Lit(Symbol("2"))])),
    Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))),
    AppCirc1([:a, :b], DiagrammaticEquations.decapodes.Var(:c))
  )
  @test Equation("Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)")[1] == Eq(
    DiagrammaticEquations.decapodes.Var(Symbol("Ċ")),
    AppCirc1([:⋆₀⁻¹, :dual_d₁, :⋆₁], DiagrammaticEquations.decapodes.Var(Symbol("ϕ")))
  )
end

@testset "Summation Operation" begin
  @test SummationOperation("a + b")[1] == Plus(
    [DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b"))]
  )
  @test SummationOperation("a + b + c")[1] == Plus(
    [DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")), DiagrammaticEquations.decapodes.Var(Symbol("c"))]
  )
  @test SummationOperation("dt(X) + ∂ₜ(X)")[1] == Plus(
    [Tan(DiagrammaticEquations.decapodes.Var(Symbol("X"))), Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))]
  )
  @test SummationOperation("a * b + c")[1] == Plus(
    [App2(:*, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b"))), DiagrammaticEquations.decapodes.Var(Symbol("c"))]
  )
  @test SummationOperation("3 * (5 + 2)")[1] == App2(:*,
    Lit(Symbol("3")), Plus([Lit(Symbol("5")), Lit(Symbol("2"))])
  )
  @test SummationOperation("3 * 5 + 2")[1] == Plus(
    [App2(:*, Lit(Symbol("3")), Lit(Symbol("5"))),Lit(Symbol("2"))]
  )
  @test SummationOperation("10 / 2 + 3")[1] == Plus(
    [App2(:/, Lit(Symbol("10")), Lit(Symbol("2"))), Lit(Symbol("3"))]
  ) 
  @test SummationOperation("3 - 2 + 1")[1] == Plus(
    [App2(:-, Lit(Symbol("3")), Lit(Symbol("2"))), Lit(Symbol("1"))]
  )
end

@testset "Subtraction Precedence Operations" begin
  @test PrecMinusOperation("3 - 2")[1] == App2(:-, Lit(Symbol("3")), Lit(Symbol("2")))
  @test PrecMinusOperation("3 - 2 - 1")[1] ==  App2(:-, App2(:-, Lit(Symbol("3")), Lit(Symbol("2"))), Lit(Symbol("1")))
  @test PrecMinusOperation("3 .- 2")[1] == App2(:.-, Lit(Symbol("3")), Lit(Symbol("2")))
  @test PrecMinusOperation("3 ⊕₀₁ 4")[1] == App2(:⊕₀₁, Lit(Symbol("3")), Lit(Symbol("4")))
  @test PrecMinusOperation("-3 - 4")[1] == App2(:-, Lit(Symbol("-3")), Lit(Symbol("4")))
  @test PrecMinusOperation("3 - -4")[1] == App2(:-, Lit(Symbol("3")), Lit(Symbol("-4")))
end

@testset "Division Precedence Operations" begin
  @test PrecDivOperation("10/2")[1] == App2(:/, Lit(Symbol("10")), Lit(Symbol("2")))
  @test PrecDivOperation("10 / 2")[1] == App2(:/, Lit(Symbol("10")), Lit(Symbol("2")))
  @test PrecDivOperation("10 ∧ 2")[1] == App2(:∧, Lit(Symbol("10")), Lit(Symbol("2")))
  @test PrecDivOperation("C ∧₀₁ V")[1] == App2(:∧₀₁, DiagrammaticEquations.decapodes.Var(Symbol("C")), DiagrammaticEquations.decapodes.Var(Symbol("V")))
  @test PrecDivOperation("A .* B")[1] == App2(:.*, DiagrammaticEquations.decapodes.Var(Symbol("A")), DiagrammaticEquations.decapodes.Var(Symbol("B")))
end

@testset "Multiplication Operations" begin
  @test MultOperation("a * b")[1] == App2(:*, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test MultOperation("(a)b")[1] == App2(:*, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test MultOperation("3(a)b")[1] == Mult(
    [Lit(Symbol("3")), DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b"))]
  )
  @test MultOperation("(a) * b")[1] == App2(:*, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test MultOperation("a * 
  b")[1] == App2(:*, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test MultOperation("a * b * c")[1] == Mult(
    [DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")), DiagrammaticEquations.decapodes.Var(Symbol("c"))]
  )
  @test MultOperation("2*d₀(C)")[1] == App2(:*, Lit(Symbol("2")), App1(:d₀, DiagrammaticEquations.decapodes.Var(Symbol("C"))))
end

@testset "Power Precedence Operations" begin
  @test PrecPowerOperation("a^b")[1] == App2(:^, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test PrecPowerOperation("0.5^b")[1] == App2(:^, Lit(Symbol("0.5")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
end

@testset "Terms" begin
  @test Term("∂ₜ(X)")[1] == Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))
  @test Term("a")[1] == DiagrammaticEquations.decapodes.Var(Symbol("a"))
  @test Term("12")[1] == Lit(Symbol("12"))
  @test Term("∘(a, b)(c)")[1] == AppCirc1([:a, :b], DiagrammaticEquations.decapodes.Var(:c))
  @test Term("a(b)")[1] == App1(:a, DiagrammaticEquations.decapodes.Var(Symbol("b")))
end

@testset "Grouping" begin
  @test Grouping("(a)")[1] == DiagrammaticEquations.decapodes.Var(Symbol("a"))
  @test Grouping("(a + b)")[1] == Plus(
    [DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b"))]
  )
end

@testset "Derivatives" begin
   @test Derivative("dt( X )")[1] == Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))
   @test Derivative("∂ₜ(X)")[1] == Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))
end

@testset "Compose" begin
  @test Compose("∘(a, b)(c)")[1] == AppCirc1([:a, :b], DiagrammaticEquations.decapodes.Var(:c))
  @test Compose("∘(a, b, c)(d)")[1] == AppCirc1([:a, :b, :c], DiagrammaticEquations.decapodes.Var(:d))
  @test Compose("∘(a)(∂ₜ(X))")[1] == AppCirc1([:a], Tan(DiagrammaticEquations.decapodes.Var(Symbol("X"))))
  @test Compose("∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)")[1] == AppCirc1([:⋆₀⁻¹, :dual_d₁, :⋆₁], DiagrammaticEquations.decapodes.Var(:ϕ))
  @test Compose("(⋆ ∘ ⋆)(C ∧ dX)")[1] == AppCirc1(
    [:⋆, :⋆], App2(:∧, DiagrammaticEquations.decapodes.Var(Symbol("C")), DiagrammaticEquations.decapodes.Var(Symbol("dX")))
  )
end

@testset "Function Call" begin
  @test Call("a(b)")[1] == App1(:a, DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test Call("a(b, c)")[1] == App2(:a, DiagrammaticEquations.decapodes.Var(Symbol("b")), DiagrammaticEquations.decapodes.Var(Symbol("c")))
  @test Call("f(n + 1)")[1] == App1(:f, Plus(
    [DiagrammaticEquations.decapodes.Var(Symbol("n")), Lit(Symbol("1"))]
  ))
  @test Call("f(n+1, N+2)")[1] == App2(:f,
    Plus([DiagrammaticEquations.decapodes.Var(Symbol("n")), Lit(Symbol("1"))]),
    Plus([DiagrammaticEquations.decapodes.Var(Symbol("N")), Lit(Symbol("2"))])
  )
  @test Call("⊕(a, b)")[1] == App2(:⊕, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test Call("⊕(a)")[1] == App1(:⊕, DiagrammaticEquations.decapodes.Var(Symbol("a")))
  @test Call("HI(a, b)")[1] == App2(:HI, DiagrammaticEquations.decapodes.Var(Symbol("a")), DiagrammaticEquations.decapodes.Var(Symbol("b")))
  @test Call("d(Ψ)")[1] == App1(:d, DiagrammaticEquations.decapodes.Var(Symbol("Ψ")))
  @test Call("(d)(Ψ)")[1] == App1(:d, DiagrammaticEquations.decapodes.Var(Symbol("Ψ")))
end

@testset "Function Call Names" begin
  # Identifier Case
  @test CallName("f")[1] == :f
  # Unary Case
  @test CallName("⊕")[1] == "⊕"
end

@testset "Unary Operators" begin
  @test UnaryOperator("-")[1] == "-"
  @test UnaryOperator("⊕")[1] == "⊕"
  @test UnaryOperator("⊽")[1] == "⊽"
end

@testset "Function Arguments" begin
  @test Args("a")[1] == [DiagrammaticEquations.decapodes.Var(:a)]
  @test Args("a, b")[1] == [DiagrammaticEquations.decapodes.Var(:a), DiagrammaticEquations.decapodes.Var(:b)]
  @test Args("∂ₜ(X)")[1] == [Tan(DiagrammaticEquations.decapodes.Var(Symbol("X")))]
  @test Args("∂ₜ(X), dt(Y)")[1] == [Tan(DiagrammaticEquations.decapodes.Var(Symbol("X"))), Tan(DiagrammaticEquations.decapodes.Var(Symbol("Y")))]
  @test Args("n + 1, n + 2")[1] == [
    Plus([DiagrammaticEquations.decapodes.Var(Symbol("n")), Lit(Symbol("1"))]),
    Plus([DiagrammaticEquations.decapodes.Var(Symbol("n")), Lit(Symbol("2"))])
  ]
end

@testset "List" begin
  @test List("a, b")[1] == [:a, :b]
  @test List("a, b, c")[1] == [:a, :b, :c]
end

@testset "Call List" begin
  @test CallList("a, b")[1] == [:a, :b]
  @test CallList("⊕, ⊽, A")[1] == [:⊕, :⊽, :A]
end

@testset "Atoms" begin
  @test Atom("a")[1] == DiagrammaticEquations.decapodes.Var(Symbol("a"))
  @test Atom("23")[1] == Lit(Symbol("23"))
  @test Atom("-2")[1] == Lit(Symbol("-2"))
  @test Atom("32.23")[1] == Lit(Symbol("32.23"))
  @test Atom("1.65e7")[1] == Lit(Symbol("1.65e7"))
end

@testset "Identifiers" begin
  @test Ident("abc")[1] == :abc
  @test Ident("Ċ")[1] == Symbol("Ċ")
  @test Ident("meep")[1] == :meep
  @test Ident("a")[1] == :a
end

@testset "Digits" begin
  @test Digit("1")[1] == Lit(Symbol("1"))
  @test Digit("-2")[1] == Lit(Symbol("-2"))
  @test Digit("1231232")[1] == Lit(Symbol("1231232"))
end

@testset "Subtraction Precedence Operator" begin
  @test PrecMinusOp("-")[1] == "-"
  @test PrecMinusOp("⊕")[1] == "⊕"
  @test PrecMinusOp("⊕²³")[1] == "⊕²³"
  @test PrecMinusOp("⨨")[1] == "⨨"
end

@testset "Division Precedence Operator" begin
  @test PrecDivOp("/")[1] == "/"
  @test PrecDivOp("∧")[1] == "∧"
  @test PrecDivOp(".*")[1] == ".*"
  @test PrecDivOp("×₆₇")[1] == "×₆₇"
  @test PrecDivOp("⋉")[1] == "⋉"
end

@testset "Power Precedence Operator" begin
  @test PrecPowerOp("^")[1] == "^"
  @test PrecPowerOp("↑")[1] == "↑"
  @test PrecPowerOp("⤋ʷ")[1] == "⤋ʷ"
end

@testset "Operator Suffixes" begin
  @test OpSuffixes("₁₂₃₄₅")[1] == "₁₂₃₄₅" 
end

# Exception Handling Tests
##########################

# Taken from "PEG.jl/blob/master/test/misc.jl": Returns byte where parsing fails.
function parse_fails_at(rule, input)
  try
    parse_whole(rule, input)
    "parse succeeded!"
  catch err
    isa(err, Meta.ParseError) || rethrow()
    m = match(r"^On line \d+, at column \d+ \(byte (\d+)\):", err.msg)
    m == nothing && rethrow()
    parse(Int, m.captures[1])
  end
end

@testset "Exception Handling" begin
  # Comparing byte # where parsing error occured.
  # Tests random variety of different parsing exceptions.

  # Test List Exceptions - Missing comma
  test_input = "meow bark woof"
  @test parse_fails_at(List, test_input) == 6

  # Test List Exceptions - Missing comma 2
  test_input = "meow bark, woof"
  @test parse_fails_at(List, test_input) == 6

  # Test Argument Exceptions - Extra Parameter
  test_input = "ident, ident ident"
  @test parse_fails_at(Args, test_input) == 14

  # Test Argument Exceptions - Missing Comma
  test_input = "ident ident"
  @test parse_fails_at(Args, test_input) == 7

  # Test Call Exceptions - Missing Closing Parenthesis
  test_input = "ident(ident"
  @test parse_fails_at(Call, test_input) == 12

  # Test Call Exceptions - Missing Opening Parenthesis
  test_input = "ident ident)"
  @test parse_fails_at(Call, test_input) == 6

  # Test Call Exceptions - Missing Parameters
  test_input = "ident()"
  @test parse_fails_at(Call, test_input) == 7

  # Test Composure Exceptions - Missing Second Argument
  test_input = "∘(ident)"
  @test parse_fails_at(Compose, test_input) == 11

  # Test Composure Exceptions - Missing Parenthesis
  test_input = "∘(ident)ident"
  @test parse_fails_at(Compose, test_input) == 11

  # Test Composure Exceptions - Missing Parenthesis 2
  test_input = "∘ident(ident)"
  @test parse_fails_at(Compose, test_input) == 4

  # Test Derivative Exceptions - Missing Derivative Symbol
  test_input = "ident(X)"
  @test parse_fails_at(Derivative, test_input) == 1

  # Test Derivative Exceptions - Missing Parenthesis
  test_input = "∂ₜident"
  @test parse_fails_at(Derivative, test_input) == 7

  # Test Derivative Exceptions - Missing Parenthesis 2
  test_input = "∂ₜ(X"
  @test parse_fails_at(Derivative, test_input) == 9

  # Test Grouping Exceptions - Missing Parenthesis
  test_input = "(ident"
  @test parse_fails_at(Grouping, test_input) == 7

  # Test Multiplication Exceptions - Missing Second Argument
  test_input = "ident *"
  @test parse_fails_at(MultOperation, test_input) == 8

  # Test Multiplication Exceptions - Missing Operator
  test_input = "2 3"
  @test parse_fails_at(MultOperation, test_input) == 3

  # Test Plus Exceptions - Missing Argument
  test_input = " + 3"
  @test parse_fails_at(SummationOperation, test_input) == 1

  # Test Equation Exceptions - Missing Equation Symbol
  test_input = "A B"
  @test parse_fails_at(Statement, test_input) == 3

  # Test Equation Exceptions - Missing RHS
  test_input = "A == "
  @test parse_fails_at(Statement, test_input) == 6

  # Test Equation Exceptions - Too many equations
  test_input = "A == B == C"
  @test parse_fails_at(Statement, test_input) == 8

  # Test TypeName Exceptions - Missing Bracket Argument
  test_input = "Form0{}"
  @test parse_fails_at(TypeName, test_input) == 7

  # Test TypeName Exceptions - Missing Bracket
  # Interestingly fails at the identifier before the }.
  # Seems to be a handling difference with the PEG. 
  test_input = "Form0{X "
  @test parse_fails_at(TypeName, test_input) == 7

  # Test Judgement Exceptions - Missing Type
  test_input = "ident::"
  @test parse_fails_at(Statement, test_input) == 8

  # Test Judgement Exceptions - Missing Var
  test_input = "::ident"
  @test parse_fails_at(Statement, test_input) == 1
end

# END-END Tests
##################

(≃) = is_isomorphic

@testset "End to End" begin
  parsed_result = decapode"
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  ∘(k, d₀)(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ"

  DiffusionExprBody1 = quote
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  ∘(k, d₀)(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ
  end
  ddp1 = SummationDecapode(parse_decapode(DiffusionExprBody1))
  
  @test parsed_result ≃ ddp1
  
  # Support parsing literals.
  parsed_result = decapode"
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  2*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ"

  DiffusionExprBody2 =  quote
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  2*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ
  end

  ddp2 = SummationDecapode(parse_decapode(DiffusionExprBody2))

  @test parsed_result ≃ ddp2
  
  # Multiply without explicitly giving parentheses.
  parsed_result = decapode"
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  4*2*3*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ"


  DiffusionExprBody3 =  quote
  (C, Ċ)::Form0
  ϕ::Form1
  ϕ ==  4*2*3*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ
  end

  ddp3 = SummationDecapode(parse_decapode(DiffusionExprBody3))

  @test parsed_result ≃ ddp3

  # Variables need not be declared before use.
  parsed_result = decapode"
  Ċ::Form0
  ϕ ==  4*2*3*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ"

  DiffusionExprBody4 =  quote
  Ċ::Form0
  ϕ ==  4*2*3*d₀(C)
  Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  ∂ₜ(C) == Ċ
  end
  
  ddp4 = SummationDecapode(parse_decapode(DiffusionExprBody4))
  
  @test parsed_result ≃ ddp4

  parsed_result = decapode"
    ϕ ==  2*d₀(C)
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    ∂ₜ(C) == Ċ"
  
  DiffusionExprBody5 =  quote
    ϕ ==  2*d₀(C)
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    ∂ₜ(C) == Ċ
  end

  ddp5 = SummationDecapode(parse_decapode(DiffusionExprBody5))

  @test parsed_result ≃ ddp5

  # TVars can be parsed on either side of an equation.
  parsed_result = decapode"
    ϕ ==  2*d₀(C)
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    Ċ == ∂ₜ(C)"

  DiffusionExprBody6 =  quote
    ϕ ==  2*d₀(C)
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    Ċ == ∂ₜ(C)
  end

  ddp6 = SummationDecapode(parse_decapode(DiffusionExprBody6))

  @test parsed_result ≃ ddp6

  parsed_result = decapode"
    ϕ ==  2*d₀(C)
    ∂ₜ(C) == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)"

  DiffusionExprBody7 =  quote
    ϕ ==  2*d₀(C)
    ∂ₜ(C) == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
  end

  ddp7 = SummationDecapode(parse_decapode(DiffusionExprBody7))

  @test parsed_result ≃ ddp7

  # Vars can only be of certain types.
  @test_throws ErrorException parsed_result = decapode"
    (C)::Foo
    ϕ ==  2*d₀(C)
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    Ċ == ∂ₜ(C)"
  
  # Just noting that the first decapode is denotes a X as an op1
  # while the second is a multiplication between X and F
  parsed_result_1 = decapode"
    (A, B, X)::Form0{X}
    A == X(F)"

    ParseTest2_1 = quote
      (A, B, X)::Form0{X}
      A == X(F)
    end
    pt2_1 = SummationDecapode(parse_decapode(ParseTest2_1))

    @test parsed_result_1 ≃ pt2_1

    parsed_result_2 = decapode"
       (A, B, X)::Form0{X}
       A == (X)F"

     ParseTest2_2 = quote
       (A, B, X)::Form0{X}
       A == (X)F
     end

     pt2_2 = SummationDecapode(parse_decapode(ParseTest2_2))

     @test parsed_result_2 ≃ pt2_2 

     @test parsed_result_1 != parsed_result_2
  
    # Chained Tvars test
    # TODO: Do we want explict support for higher order Tvars?
    parsed_result = decapode"
      D == ∂ₜ(C)
      E == ∂ₜ(D)"

    ParseTest3 = quote
      D == ∂ₜ(C)
      E == ∂ₜ(D)
    end

    pt3 = SummationDecapode(parse_decapode(ParseTest3))

    @test parsed_result ≃ pt3

    # Do not rename TVars if they are given a name.
    parsed_result = decapode"
      X::Form0{Point}
      V::Form0{Point}
  
      k::Constant{Point}
  
      ∂ₜ(X) == V
      ∂ₜ(V) == -1*k*(X)"

    pt5 = SummationDecapode(parse_decapode(quote
      X::Form0{Point}
      V::Form0{Point}
  
      k::Constant{Point}
  
      ∂ₜ(X) == V
      ∂ₜ(V) == -1*k*(X)
    end))

    @test parsed_result ≃ pt5

    # Recursive Expr
    parse_result = decapode"
      x::Form0{X}
      y::Form0{X}
      z::Form0{X}
  
      ∂ₜ(z) == f1(x) + ∘(g, h)(y)
      y == F(f2(x), ρ(x,z))"

    Recursion = quote
      x::Form0{X}
      y::Form0{X}
      z::Form0{X}
  
      ∂ₜ(z) == f1(x) + ∘(g, h)(y)
      y == F(f2(x), ρ(x,z))
    end
  
    rdp = SummationDecapode(parse_decapode(Recursion))

    @test parse_result ≃ rdp

    # Diffusion Diagram
    parse_result = decapode"
      (C, Ċ)::Form0{X}
      ϕ::Form1{X}

      # Fick's first law
      ϕ ==  ∘(k, d₀)(C)
      # Diffusion equation
      Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
      ∂ₜ(C) == Ċ"

    DiffusionExprBody =  quote
      (C, Ċ)::Form0{X}
      ϕ::Form1{X}

      # Fick's first law
      ϕ ==  ∘(k, d₀)(C)
      # Diffusion equation
      Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
      ∂ₜ(C) == Ċ
  end

  ddp = SummationDecapode(parse_decapode(DiffusionExprBody))

  @test parse_result ≃ ddp

  # Advection Diagram
  parse_result = decapode"
    C::Form0{X}
    (V, ϕ)::Form1{X}

    ϕ == ∧₀₁(C,V)"

  Advection = quote
    C::Form0{X}
    (V, ϕ)::Form1{X}

    ϕ == ∧₀₁(C,V)
  end

  advdp = SummationDecapode(parse_decapode(Advection))

  @test parse_result ≃ advdp

  # Superposition Diagram
  parse_result = decapode"
    (C, Ċ)::Form0{X}
    (ϕ, ϕ₁, ϕ₂)::Form1{X}

    ϕ == ϕ₁ + ϕ₂
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    ∂ₜ(C) == Ċ"

  Superposition = quote
    (C, Ċ)::Form0{X}
    (ϕ, ϕ₁, ϕ₂)::Form1{X}

    ϕ == ϕ₁ + ϕ₂
    Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ)
    ∂ₜ(C) == Ċ
  end

  supdp = SummationDecapode(parse_decapode(Superposition))

  @test parse_result ≃ supdp

  # Mixed Semicolon support test
  parse_result_semi = decapode"
    (C, Ċ)::Form0{X}; (ϕ, ϕ₁, ϕ₂)::Form1{X};

    ϕ == ϕ₁ + ϕ₂; Ċ == ∘(⋆₀⁻¹, dual_d₁, ⋆₁)(ϕ);
    ∂ₜ(C) == Ċ"

  @test parse_result_semi ≃ supdp

  # Heat Transfer Model 
  # TODO: '(⋆)' Parenthesis around call name not supported
  parse_result = decapode" 
    (HT, Tₛ)::Form0
    (D, cosϕᵖ, cosϕᵈ)::Constant
    
    HT == (D ./ cosϕᵖ) .* ⋆(d(cosϕᵈ .* ⋆(d(Tₛ))))"

  HeatTransfer = quote
    (HT, Tₛ)::Form0
    (D, cosϕᵖ, cosϕᵈ)::Constant
    
    HT == (D ./ cosϕᵖ) .* (⋆)(d(cosϕᵈ .* (⋆)(d(Tₛ))))
  end

  htts = SummationDecapode(parse_decapode(HeatTransfer))

  @test parse_result ≃ htts


  # Outgoing Longwave Radiation Model
  parse_result = decapode"
    (Tₛ, OLR)::Form0
    (A, B)::Constant
    
    OLR == A .+ B .* Tₛ"

  OutgoingLongRadiation = quote
    (Tₛ, OLR)::Form0
    (A, B)::Constant
    
    OLR == A .+ B .* Tₛ
  end

  olr = SummationDecapode(parse_decapode(OutgoingLongRadiation))

  @test parse_result ≃ olr

  # Absorbed Shortwave Radiation Model
  parse_result = decapode"
    (Q, ASR)::Form0
    α::Constant
    
    ASR == (1 .- α) .* Q"

  AbsorbedShortRadiation = quote
    (Q, ASR)::Form0
    α::Constant
    
    ASR == (1 .- α) .* Q
  end

  asr = SummationDecapode(parse_decapode(AbsorbedShortRadiation))

  @test parse_result ≃ asr

  #Advection Model
  parse_result = decapode"
    C::Form0
    (ϕ, V)::Form1
              
    ϕ == C ∧₀₁ V"

  Advection = quote
    C::Form0
    (ϕ, V)::Form1
              
    ϕ == C ∧₀₁ V
  end

  adv = SummationDecapode(parse_decapode(Advection))

  @test parse_result ≃ adv

  # Ficks Law Model
  parse_result = decapode"
    C::Form0
    ϕ::Form1
              
    ϕ == k(d₀(C))"

  FicksLaw = quote
    C::Form0
    ϕ::Form1
              
    ϕ == k(d₀(C))
  end

  ficks = SummationDecapode(parse_decapode(FicksLaw))

  @test parse_result ≃ ficks

  # IceBlockingWater Model
  parse_result = decapode"
    h::Form0
    (𝐮, w)::DualForm1
              
    w == (1 - σ(h)) ∧ᵖᵈ₀₁ 𝐮"

  IceBlockingWater = quote
    h::Form0
    (𝐮, w)::DualForm1
              
    w == (1 - σ(h)) ∧ᵖᵈ₀₁ 𝐮
  end

  ibw = SummationDecapode(parse_decapode(IceBlockingWater))

  @test parse_result ≃ ibw

  # Jordan-Kinderlehrer-Otto Model
  parse_result = decapode"
    (ρ, Ψ)::Form0
    β⁻¹::Constant
              
    ∂ₜ(ρ) == ∘(⋆, d, ⋆)(d(Ψ) ∧ ρ) + β⁻¹ * Δ(ρ)"

  JKO = quote
    (ρ, Ψ)::Form0
    β⁻¹::Constant

    ∂ₜ(ρ) == (∘(⋆, d, ⋆))(d(Ψ) ∧ ρ) + β⁻¹ * Δ(ρ)
  end

  jko = SummationDecapode(parse_decapode(JKO))

  @test parse_result ≃ jko
    
  # Lie Model
  parse_result = decapode"
    C::Form0
    V::Form1
    dX::Form1
              
    V == (⋆ ∘ ⋆)(C ∧ dX)"

  Lie = quote
    C::Form0
    V::Form1
    dX::Form1
              
    V == ((⋆) ∘ (⋆))(C ∧ dX)
  end

  lie = SummationDecapode(parse_decapode(Lie))

  @test parse_result ≃ lie

  # Mohamed Eq. 10, N2
  parse_result = decapode"
    (𝐮, w)::DualForm1
    (P, 𝑝ᵈ)::DualForm0
    μ::Constant
              
    𝑝ᵈ == P + 0.5 * ι₁₁(w, w)
              
    ∂ₜ(𝐮) == μ * ∘(d, ⋆, d, ⋆)(w) + -1 * ⋆₁⁻¹(w ∧ᵈᵖ₁₀ ⋆(d(w))) + d(𝑝ᵈ)"

  Mohamed = quote
    (𝐮, w)::DualForm1
    (P, 𝑝ᵈ)::DualForm0
    μ::Constant

    𝑝ᵈ == P + 0.5 * ι₁₁(w, w)

    ∂ₜ(𝐮) == μ * (∘(d, ⋆, d, ⋆))(w) + -1 * (⋆₁⁻¹)(w ∧ᵈᵖ₁₀ (⋆)(d(w))) + d(𝑝ᵈ)
  end

  mohamed = SummationDecapode(parse_decapode(Mohamed))

  @test parse_result ≃ mohamed

  # Momentum Model
  parse_result = decapode"
    (f, b)::Form0
    (v, V, g, Fᵥ, uˢ, v_up)::Form1
    τ::Form2
    U::Parameter
              
    uˢ̇ == ∂ₜ(uˢ)
              
    v_up == (((((((-1 * L(v, v) - L(V, v)) - L(v, V)) - f ∧ v) - ∘(⋆, d, ⋆)(uˢ) ∧ v) - d(p)) + b ∧ g) - ∘(⋆, d, ⋆)(τ)) + uˢ̇ + Fᵥ
              
    uˢ̇ == force(U)"

  Momentum = quote
    (f, b)::Form0
    (v, V, g, Fᵥ, uˢ, v_up)::Form1
    τ::Form2
    U::Parameter

    uˢ̇ == ∂ₜ(uˢ)

    v_up == (((((((-1 * L(v, v) - L(V, v)) - L(v, V)) - f ∧ v) - (∘(⋆, d, ⋆))(uˢ) ∧ v) - d(p)) + b ∧ g) - (∘(⋆, d, ⋆))(τ)) + uˢ̇ + Fᵥ

    uˢ̇ == force(U)
  end

  mom = SummationDecapode(parse_decapode(Momentum))

  @test parse_result ≃ mom

  # Navier-Stokes Model
  parse_result = decapode"
    (V, V̇, G)::Form1{X}
    (ρ, ṗ, p)::Form0{X}
              
    V̇ == neg₁(L₁′(V, V)) + div₁(kᵥ(Δ₁(V) + third(d₀(δ₁(V)))), avg₀₁(ρ)) + d₀(half(i₁′(V, V))) + neg₁(div₁(d₀(p), avg₀₁(ρ))) + G
    ∂ₜ(V) == V̇
              
    ṗ == neg₀(⋆₀⁻¹(L₀(V, ⋆₀(p))))
    ∂ₜ(p) == ṗ"

  NavierStokes = quote
    (V, V̇, G)::Form1{X}
    (ρ, ṗ, p)::Form0{X}

    V̇ == neg₁(L₁′(V, V)) + div₁(kᵥ(Δ₁(V) + third(d₀(δ₁(V)))), avg₀₁(ρ)) + d₀(half(i₁′(V, V))) + neg₁(div₁(d₀(p), avg₀₁(ρ))) + G
    ∂ₜ(V) == V̇

    ṗ == neg₀((⋆₀⁻¹)(L₀(V, (⋆₀)(p))))
    ∂ₜ(p) == ṗ
  end

  navier = SummationDecapode(parse_decapode(NavierStokes))

  @test parse_result ≃ navier

  # Oscillator Model
  parse_result = decapode"
    X::Form0
    V::Form0
    k::Constant
    
    ∂ₜ(X) == V
    ∂ₜ(V) == -k * X"

  Oscillator = quote
    X::Form0
    V::Form0
    k::Constant
    
    ∂ₜ(X) == V
    ∂ₜ(V) == -k * X
  end

  osc = SummationDecapode(parse_decapode(Oscillator))

  @test parse_result ≃ osc

  # Poiseuille Model
  parse_result = decapode"
    P::Form0
    q::Form1
    (R, μ̃)::Constant
              
    Δq == Δ(q)
    ∇P == d(P)
              
    ∂ₜ(q) == q̇
    
    q̇ == μ̃ * ∂q(Δq) + ∇P + R * q"

  Poiseuille = quote
    P::Form0
    q::Form1
    (R, μ̃)::Constant

    Δq == Δ(q)
    ∇P == d(P)

    ∂ₜ(q) == q̇
    
    q̇ == μ̃ * ∂q(Δq) + ∇P + R * q
  end

  pois = SummationDecapode(parse_decapode(Poiseuille))

  @test parse_result ≃ pois

  # Poiseuille Density Model
  parse_result = decapode"
    q::Form1
    (P, ρ)::Form0
    (k, R, μ̃)::Constant
              
    ∂ₜ(q) == q̇
    ∇P == d(P)
              
    q̇ == (μ̃ * ∂q(Δ(q)) - ∇P) + R * q
    P == k * ρ
              
    ∂ₜ(ρ) == ρ̇
              
    ρ_up == ∘(⋆, d, ⋆)(-1 * (ρ ∧₀₁ q))
              
    ρ̇ == ∂ρ(ρ_up)"

  PoiseuilleDensity = quote
    q::Form1
    (P, ρ)::Form0
    (k, R, μ̃)::Constant

    ∂ₜ(q) == q̇
    ∇P == d(P)

    q̇ == (μ̃ * ∂q(Δ(q)) - ∇P) + R * q
    P == k * ρ

    ∂ₜ(ρ) == ρ̇

    ρ_up == (∘(⋆, d, ⋆))(-1 * (ρ ∧₀₁ q))

    ρ̇ == ∂ρ(ρ_up)
  end

  poisden = SummationDecapode(parse_decapode(PoiseuilleDensity))

  @test parse_result ≃ poisden
  
  # Schroedinger Model
  parse_result = decapode"
    (i, h, m)::Constant
    V::Parameter
    Ψ::Form0
              
    ∂ₜ(Ψ) == (((-1 * h ^ 2) / (2*m)) * Δ(Ψ) + V * Ψ) / (i * h)"

  Schroedinger = quote
    (i, h, m)::Constant
    V::Parameter
    Ψ::Form0

    ∂ₜ(Ψ) == (((-1 * h ^ 2) / (2m)) * Δ(Ψ) + V * Ψ) / (i * h)
  end

  schroed = SummationDecapode(parse_decapode(Schroedinger))

  @test parse_result ≃ schroed

  # Superposition Model
  parse_result = decapode"
    (C, Ċ)::Form0
    (ϕ, ϕ₁, ϕ₂)::Form1

    ϕ == ϕ₁ + ϕ₂
    Ċ == ⋆₀⁻¹(dual_d₁(⋆₁(ϕ)))
    ∂ₜ(C) == Ċ"

  Superposition = quote
    (C, Ċ)::Form0
    (ϕ, ϕ₁, ϕ₂)::Form1

    ϕ == ϕ₁ + ϕ₂
    Ċ == (⋆₀⁻¹)(dual_d₁((⋆₁)(ϕ)))
    ∂ₜ(C) == Ċ
  end

  sup = SummationDecapode(parse_decapode(Superposition))

  @test parse_result ≃ sup

  # Gray-Scott Model
  parse_result = decapode"
    (U, V)::Form0
    UV2::Form0
    (U̇, V̇)::Form0
    (f, k, rᵤ, rᵥ)::Constant
              
    UV2 == U .* (V .* V)
    U̇ == (rᵤ * Δ(U) - UV2) + f * (1 .- U)
    V̇ == (rᵥ * Δ(V) + UV2) - (f + k) .* V
              
    ∂ₜ(U) == U̇
    ∂ₜ(V) == V̇"

  GrayScott = quote
    (U, V)::Form0
    UV2::Form0
    (U̇, V̇)::Form0
    (f, k, rᵤ, rᵥ)::Constant

    UV2 == U .* (V .* V)
    U̇ == (rᵤ * Δ(U) - UV2) + f * (1 .- U)
    V̇ == (rᵥ * Δ(V) + UV2) - (f + k) .* V

    ∂ₜ(U) == U̇
    ∂ₜ(V) == V̇
  end

  gs = SummationDecapode(parse_decapode(GrayScott))

  @test parse_result ≃ gs

  # Brusselator Model
  parse_result = decapode"
    (U, V)::Form0
    U2V::Form0
    (U̇, V̇)::Form0
    α::Constant
    F::Parameter
              
    U2V == (U .* U) .* V
    U̇ == ((1 + U2V) - 4.4*U) + α * Δ(U) + F
    V̇ == (3.4*U - U2V) + α * Δ(V)
              
    ∂ₜ(U) == U̇
    ∂ₜ(V) == V̇"

  Brusselator = quote
    (U, V)::Form0
    U2V::Form0
    (U̇, V̇)::Form0
    α::Constant
    F::Parameter

    U2V == (U .* U) .* V
    U̇ == ((1 + U2V) - 4.4U) + α * Δ(U) + F
    V̇ == (3.4U - U2V) + α * Δ(V)

    ∂ₜ(U) == U̇
    ∂ₜ(V) == V̇
  end

  brussel = SummationDecapode(parse_decapode(Brusselator))

  @test parse_result ≃ brussel

  # Kealy Model
  parse_result = decapode"
    (n, w)::DualForm0
    dX::Form1
    (a, ν)::Constant
              
    ∂ₜ(w) == ((a - w) - w * n ^ 2) + ν * Δ(w)"

  Kealy = quote
    (n, w)::DualForm0
    dX::Form1
    (a, ν)::Constant

    ∂ₜ(w) == ((a - w) - w * n ^ 2) + ν * Δ(w)
  end

  kealy = SummationDecapode(parse_decapode(Kealy))

  @test parse_result ≃ kealy

  # Klausmeier (Eq. 2a) Model
  parse_result = decapode"
    (n, w)::DualForm0
    dX::Form1
    (a, ν)::Constant
              
    ∂ₜ(w) == ((a - w) - w * n ^ 2) + ν * ℒ(dX, w)"

  Klausmeier = quote
    (n, w)::DualForm0
    dX::Form1
    (a, ν)::Constant

    ∂ₜ(w) == ((a - w) - w * n ^ 2) + ν * ℒ(dX, w)
  end

  klaus = SummationDecapode(parse_decapode(Klausmeier))

  @test parse_result ≃ klaus

  # Klausmeier (Eq. 2b) Model
  parse_result = decapode"
    (n, w)::DualForm0
    m::Constant
              
    ∂ₜ(n) == (w * n ^ 2 - m * n) + Δ(n)"

  Klausmeier2 = quote
    (n, w)::DualForm0
    m::Constant

    ∂ₜ(n) == (w * n ^ 2 - m * n) + Δ(n)
  end

  klaus2 = SummationDecapode(parse_decapode(Klausmeier2))

  @test parse_result ≃ klaus2

  # Lejeune Model
  parse_result = decapode"
    ρ::Form0
    (μ, Λ, L)::Constant
              
    ∂ₜ(ρ) == (ρ * (((1 - μ) + (Λ - 1) * ρ) - ρ * ρ) + 0.5 * (L * L - ρ) * Δ(ρ)) - 0.125 * ρ * Δ(ρ) * Δ(ρ)"

  Lejeune = quote
    ρ::Form0
    (μ, Λ, L)::Constant

    ∂ₜ(ρ) == (ρ * (((1 - μ) + (Λ - 1) * ρ) - ρ * ρ) + 0.5 * (L * L - ρ) * Δ(ρ)) - 0.125 * ρ * Δ(ρ) * Δ(ρ)
  end

  lejeune = SummationDecapode(parse_decapode(Lejeune))

  @test parse_result ≃ lejeune

  # Turing Continuous Ring Model
  parse_result = decapode"
    (X, Y)::Form0
    (μ, ν, a, b, c, d)::Constant
              
    ∂ₜ(X) == a * X + b * Y + μ * Δ(X)
    ∂ₜ(Y) == c * X + d * Y + ν * Δ(X)"

  TuringContinuousRing = quote
    (X, Y)::Form0
    (μ, ν, a, b, c, d)::Constant

    ∂ₜ(X) == a * X + b * Y + μ * Δ(X)
    ∂ₜ(Y) == c * X + d * Y + ν * Δ(X)
  end

  turing = SummationDecapode(parse_decapode(TuringContinuousRing))

  @test parse_result ≃ turing

  # Boundary Conditions Model
  parse_result = decapode"
    (S, T)::Form0
    (Ṡ, T_up)::Form0
    v::Form1
    v_up::Form1
              
    Ṫ == ∂ₜ(T)
    Ṡ == ∂ₜ(S)
    v̇ == ∂ₜ(v)
    
    Ṫ == ∂_spatial(T_up)
    v̇ == ∂_noslip(v_up)"

  BoundaryConditions = quote
    (S, T)::Form0
    (Ṡ, T_up)::Form0
    v::Form1
    v_up::Form1

    Ṫ == ∂ₜ(T)
    Ṡ == ∂ₜ(S)
    v̇ == ∂ₜ(v)
    
    Ṫ == ∂_spatial(T_up)
    v̇ == ∂_noslip(v_up)
  end

  bc = SummationDecapode(parse_decapode(BoundaryConditions))

  @test parse_result ≃ bc

  # Energy Balance Model
  parse_result = decapode"
    (Tₛ, ASR, OLR, HT)::Form0
    C::Constant
              
    Tₛ̇ == ∂ₜ(Tₛ)
              
    Tₛ̇ == ((ASR - OLR) + HT) ./ C"

  EnergyBalance = quote
    (Tₛ, ASR, OLR, HT)::Form0
    C::Constant

    Tₛ̇ == ∂ₜ(Tₛ)

    Tₛ̇ == ((ASR - OLR) + HT) ./ C
  end

  eb = SummationDecapode(parse_decapode(EnergyBalance))

  @test parse_result ≃ eb

  # Equation of State Model
  parse_result = decapode"
    (b, T, S)::Form0
    (g, α, β)::Constant
              
    b == g * (α * T - β * S)"

  EquationOfState = quote
    (b, T, S)::Form0
    (g, α, β)::Constant

    b == g * (α * T - β * S)
  end

  eos = SummationDecapode(parse_decapode(EquationOfState))

  @test parse_result ≃ eos

  # Glens Law
  parse_result = decapode"
    Γ::Form1
    (A, ρ, g, n)::Constant
              
    Γ == (2 / (n + 2)) * A * (ρ * g) ^ n"

  GlensLaw = quote
    Γ::Form1
    (A, ρ, g, n)::Constant

    Γ == (2 / (n + 2)) * A * (ρ * g) ^ n
  end

  glens = SummationDecapode(parse_decapode(GlensLaw))

  @test parse_result ≃ glens

  # Halfar (Eq. 2) Model
  parse_result = decapode"
    h::Form0
    Γ::Form1
    n::Constant
              
    ∂ₜ(h) == ∘(⋆, d, ⋆)(((Γ * d(h)) ∧ mag(♯(d(h))) ^ (n - 1)) ∧ h ^ (n + 2))"

  Halfar = quote
    h::Form0
    Γ::Form1
    n::Constant

    ∂ₜ(h) == (∘(⋆, d, ⋆))(((Γ * d(h)) ∧ mag(♯(d(h))) ^ (n - 1)) ∧ h ^ (n + 2))
  end

  halfar = SummationDecapode(parse_decapode(Halfar))

  @test parse_result ≃ halfar

  # Insolation Model
  # TODO: Implicit Multiplication not supported '450cosϕᵖ' vs '450*cosϕᵖ' 
  parse_result = decapode"
    Q::Form0
    cosϕᵖ::Constant
              
    Q == 450*cosϕᵖ"

  Insolation = quote
    Q::Form0
    cosϕᵖ::Constant

    Q == 450cosϕᵖ
  end

  ins = SummationDecapode(parse_decapode(Insolation))

  @test parse_result ≃ ins

  # Tracer Model
  parse_result = decapode"
    (c, C, F, c_up)::Form0
    (v, V, q)::Form1
              
    c_up == (((-1 * ⋆(L(v, ⋆(c))) - ⋆(L(V, ⋆(c)))) - ⋆(L(v, ⋆(C)))) - ∘(⋆, d, ⋆)(q)) + F"

  Tracer = quote
    (c, C, F, c_up)::Form0
    (v, V, q)::Form1

    c_up == (((-1 * (⋆)(L(v, (⋆)(c))) - (⋆)(L(V, (⋆)(c)))) - (⋆)(L(v, (⋆)(C)))) - (∘(⋆, d, ⋆))(q)) + F
  end

  trac = SummationDecapode(parse_decapode(Tracer))

  @test parse_result ≃ trac

  # Warming Model
  parse_result = decapode"
    Tₛ::Form0
    A::Form1
              
    A == avg₀₁(5.8282 * 10 ^ (-0.236*Tₛ) * 1.65e7)"

  Warming = quote
    Tₛ::Form0
    A::Form1

    A == avg₀₁(5.8282 * 10 ^ (-0.236Tₛ) * 1.65e7)
  end

  warm = SummationDecapode(parse_decapode(Warming))

  @test parse_result ≃ warm

end