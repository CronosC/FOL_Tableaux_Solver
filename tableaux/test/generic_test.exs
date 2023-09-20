defmodule GenericTests do
  use ExUnit.Case, async: true
  doctest Tableaux
  doctest Logic
  doctest Parser
  doctest PrePro
  doctest Helper

  '''
  test "greets the world" do
    assert Tableaux.hello() == :world
  end
  '''
  test "rename_quantified" do
    a = {:exqu, [:X], {:f, [:X, :Y]}}
    b = {:or, [:Y, :X, {:allqu, [:Y], {:exqu, [:X], {:f, [:X, :Y]}}}]}
    assert PrePro.preprocess_quantifiers(a) == {:exqu, [:QVar_X], {:f, [:QVar_X, :Y]}}
    assert PrePro.preprocess_quantifiers(b) == {:or, [:Y, :X, {:allqu, [:QVar_Y], {:exqu, [:QVar_X], {:f, [:QVar_X, :QVar_Y]}}}]}
  end

  test "checks" do
    vs = [:A, :B, :C]
    cs = [:a, :b, :c]
    ps = [{:f, [:A]}, {:g, [:A, :a, :B, :b]}, {:h, [:A, :a, {:f, [:a, :A]}]}]
    not_ps = [{:or, [:A, :B]}, {:f, [{:or, [:a, :B]}]}, {:not, {:f, [:a, :B, :c]}}]
    atomic = [{:not, {:f, [:a, :B, :c]}}, :a, {:f, [:a, :B]}]
    assert Logic.variable?(vs)
    assert Logic.constant?(cs)
    assert Logic.predicate?(ps)
    assert not Enum.any?(Enum.map(not_ps ++ vs ++ cs, fn x -> Logic.predicate?(x) end))
    assert Enum.all?(Enum.map(atomic ++ ps ++ vs ++ cs, fn x -> Logic.atomic?(x) end))
  end

  test "substitution" do
    a = {:f, [:A, :B, :C, :A, :a, :b]}
    b = {:g, [:A, {:h, [:B]}]}
    theta1 = %{:A => :a, :B => {:f, [:b]}}
    theta2 = %{:A => :a, :B => :a}
    assert Logic.substitute(a, theta1) == {:f, [:a, {:f, [:b]}, :C, :a, :a, :b]}
    assert Logic.substitute(a, theta2) == {:f, [:a, :a, :C, :a, :a, :b]}
    assert Logic.substitute(b, theta1) == {:g, [:a, {:h, [{:f, [:b]}]}]}
    assert Logic.substitute(b, theta2) == {:g, [:a, {:h, [:a]}]}
  end

  test "skolemization" do
    a = {:exqu, [:X], {:f, [:X, :Y]}}
    a_sk = {:f, [:sk_const_X, :Y]}
    b = {:allqu, [:Y], {:exqu, [:X], {:f, [:X, :Y]}}}
    b_sk = {:allqu, [:Y], {:f, [{:sk_func_X, [:Y]}, :Y]}}
    assert Logic.skolemization(a) == a_sk
    assert Logic.skolemization(b) == b_sk
  end

  test "unification" do
    a = [{:f, [:X, :c]}]
    b = [{:f, [:d, :Y]}]
    c = [{:g, [:X, :c]}]
    d = [:X]
    e = [{:f, [:X]}]
    assert Logic.substitute(a, Logic.unify(a, b)) == Logic.substitute(b, Logic.unify(a, b))
    assert Logic.substitute(d, Logic.unify(d, b)) == Logic.substitute(b, Logic.unify(d, b))
    assert(:error_unification_not_possible == Logic.unify(a, c))
    assert(:error_unification_not_possible == Logic.unify(c, d))
    assert(:error_unification_not_possible == Logic.unify(d, e))
  end

  test "wff_tests" do
    assert Logic.wff?(Logic.expr_sat())
    assert Logic.wff?(Logic.expr_quant())
  end


  #test "parsing_changed_test" do
  #  assert Parser.parse_KR() == {:and,[e: [:exist],or: [equalish: [:X5, {:u0r4, [:X1]}],not: {:or, [e: [:X1], not: {:r, [:X1, :X5]}]}],or: [r: [:X1, {:u0r4, [:X1]}], not: {:e, [:X1]}],not: {:or, [e: [:X1], not: {:equalish, [u0r3: [:X1], u0r2: [:X1]]}]},or: [r: [:X1, {:u0r2, [:X1]}], not: {:e, [:X1]}],or: [r: [:X1, {:u0r3, [:X1]}], not: {:e, [:X1]}],or: [e: [:X1],or: [equalish: [:X3, :X2],not: {:or,[r: [:X1, :X3],not: {:or,[r: [:X1, :X2],not: {:or,[r: [:X1, :X4], not: {:equalish, [{:u0r1, [:X4, :X1]}, :X4]}]}]}]}]],or: [e: [:X1],or: [equalish: [:X3, :X2],or: [r: [:X1, {:u0r1, [:X4, :X1]}],not: {:or,[r: [:X1, :X3], not: {:or, [r: [:X1, :X2], not: {:r, [:X1, :X4]}]}]}]]]]}
  #end


  test "prop_logic_test" do
    assert Tableaux.proof(Logic.expr_sat) == :true
    assert Tableaux.proof(Logic.expr_unsat) == :false
  end

  test "fo_logic_test" do
    assert Tableaux.proof(Logic.expr_quant_sat, :false, 2500) == :true
    assert Tableaux.proof(Logic.expr_quant_unsat, :false, 2500) == :false
  end

  test "small_parse_test_sat" do
    assert Enum.all?(Helper.test_all("cnf_sat_subset"))
  end

  test "small_parse_test_unsat" do
    assert not Enum.any?(Helper.test_all("cnf_unsat_subset"))
  end


  #test "master_parse_test_sat" do
  #  assert Enum.all?(Helper.test_all("cnf_sat"))
  #end

  #test "master_parse_test_unsat" do
  #  assert not Enum.any?(Helper.test_all("cnf_unsat"))
  #end
end
