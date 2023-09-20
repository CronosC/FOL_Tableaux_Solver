defmodule Logic do

  #############################################
  ######## TEST DEFINITIONS ###################
  #############################################

  def expr_quant() do
    {:not, {:exqu, [:A], {:allqu, [:B], {:exqu, [:C, :D], {:or, [:A, {:f, [:A, :B, :C, :D]}]}}}}}
  end

  def expr_quant_sat() do
    {:and, [{:allqu, [:X], {:f, [:X]}}, {:exqu, [:Y], {:g, [:X, :Y]}}, {:or, [{:not, {:f, [:x]}}, {:h, [:X, :Y, :X]}]} ]}
  end

  def expr_quant_unsat() do
    {:and, [{:allqu, [:X], {:f, [:X]}}, {:g, [:X, :Y]}, {:or, [{:not, {:g, [:y]}}, {:h, [:X, :Y, :X]}]}, {:exqu, [:Z], {:not, {:f, [:Z]}}}]}
  end

  @spec expr_unsat :: {:and, [:A | {:not, :D} | {:or, [...]}, ...]}
  def expr_unsat() do
    {:and, [:A, {:or, [:C, :D]}, {:or, [{:not, :A}, :D]}, {:not, :D}]}
  end

  def expr_sat() do
    {:not, expr_unsat()}
  end

  #############################################
  ######## CHECKS #############################
  #############################################

  # checks syntactic correctness of an expression
  def wff?(expression) do
    case expression do
      x -> if atomic?(x) do :true else
        case x do
          {:allqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:exqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:not, x} -> wff?(x)
          {:and, ops} -> if length(ops) >= 1 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:or, ops} -> if length(ops) >= 1 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nand, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nor, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:rimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:limp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nrimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nlimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {f, x} -> if not operator?(f) and not atomic?({f, x}) do :false else
            IO.puts("Forgotten case in wff?!")
            IO.inspect({f, x})
            :error_missing_case
          end
          x -> IO.puts("Forgotten case in wff?!")
               IO.inspect(x)
               :error_missing_case
        end
      end
    end
  end

  # checks if something is in our approved operator list.
  def operator?(f) do
      f in [:not, :and, :or]
  end

  # checks if something is a variable
  def variable?(expression) do
    case expression do
      x when is_list(x) -> Enum.all?(Enum.map(x, fn y -> variable?(y) end))
      x when is_atom(x) ->
        <<first::binary-size(1)>> <> _ = Atom.to_string(expression) # pattern matches s.t. first is the first char in expression
        first =~ ~r/^\p{Lu}$/u  # regex that checks for uppercase
      _ -> :false
    end
  end

  # checks if something is a constant
  def constant?(expression) do
    case expression do
      x when is_list(x) -> Enum.all?(Enum.map(x, fn y -> constant?(y) end))
      x when is_atom(x) -> not variable?(x)
      _ -> :false
    end
  end

  # checks if something is a predicate
  def predicate?(expression) do
    case expression do
      x when is_list(x) -> Enum.all?(Enum.map(x, fn y -> predicate?(y) end))
      {f, x} -> not operator?(f) and Enum.all?(Enum.map(x, &atomic?/1))
      _ -> :false
    end
  end

  # checks if some expression is atomic. Includes predicates.
  def atomic?(expression) do
    case expression do
      x when is_list(x) -> Enum.all?(Enum.map(x, &atomic?/1))
      {:not, x} -> atomic?(x)
      {_, _, _} -> :false  # must be quantor
      {f, x} -> (not operator?(f)) and atomic?(x)
      x when is_atom(x) -> not operator?(x)
    end
  end

  #############################################
  ######## INFER SIGNATURE ####################
  #############################################

  def get_Signature(expressions) do
    %{:Relations => get_Relations(expressions), :Functions => get_Functions(expressions), :Constants => get_Constants(expressions), :Variables => get_Variables(expressions)}
  end

  defp get_Relations(expressions) do
    case expressions do
      [] -> []
      x when is_list(x) ->
        Enum.concat(Enum.map(x, fn y -> get_Relations(y) end))
      {f, x} -> if operator?(f) do get_Relations(x) else [{f, length(x)}] ++ get_Relations(x) end
      {_q, _v, x} ->
        get_Relations(x)
      x -> if atomic?(x) do []
        else
          IO.puts("Forgotten case in get_Relations!")
          IO.inspect(x)
          :error_missing_case
      end
    end
  end

  defp get_Functions(_expressions) do
    []
  end

  defp get_Constants(expressions) do
    case expressions do
      x when is_list(x) -> Enum.reduce(Enum.map(x, fn x -> get_Constants(x) end), fn x, y -> x ++ y end)
      {_f, x} -> get_Constants(x)
      {_q, _v, x} -> get_Constants(x)
      x -> if constant?(x) do [x] else
        if variable?(x) do [] else
          IO.puts("Forgotten case in get_Constants!")
          IO.inspect(x)
          :error_missing_case
        end
      end
    end
  end

  defp get_Variables(expressions) do
    case expressions do
      x when is_list(x) -> Enum.reduce(Enum.map(x, fn x -> get_Variables(x) end), fn x, y -> x ++ y end)
      {_f, x} -> get_Variables(x)
      {_q, _v, x} -> get_Variables(x)
      x -> if variable?(x) do [x] else
        if constant?(x) do [] else
          IO.puts("Forgotten case in get_Variables!")
          IO.inspect(x)
          :error_missing_case
        end
      end
    end
  end

  #############################################
  ######## TRANSFORMATIONS ####################
  #############################################

  # negates an expression
  def negate(expressions) do
    case expressions do
      x when is_list(x) -> Enum.map(x, &negate/1)
      :true -> :false
      :false -> :true
      {:not, x} -> x
      x -> {:not, x}
    end
  end

  # theta is a substitution map, the method looks for occurences of keys of theta in formula and replaces them with the assosiacted values
  def substitute(formula, theta) do
    case formula do
      x when is_list(x) -> Enum.map(x, fn x -> substitute(x, theta) end)
      {q, v, x} -> {q, v, substitute(x, theta)}
      {f, x} -> {f, substitute(x, theta)}
      x when is_map_key(theta, x) -> theta[x]
      x -> x
    end
  end


  # transforms a formula into negation normal form
  def nnf(expression) do
    case expression do
      x when is_list(x) -> Enum.map(x, fn x -> nnf(x) end)
      {:not, {:not, x}} -> nnf(negate(x))
      {:not, {:and, x}} -> {:or, nnf(negate(x))}
      {:not, {:or, x}} -> {:and, nnf(negate(x))}
      {:not, {:allqu, v, x}} -> {:exqu, v, nnf(negate(x))}
      {:not, {:exqu, v, x}} -> {:allqu, v, nnf(negate(x))}
      {f, x} -> {f, nnf(x)}
      {q, v, x} -> {q, v, nnf(x)}
      x -> if atomic?(x) do x else
        IO.puts("Forgotten case in nnf!")
        IO.inspect(x)
        :error_missing_case
      end
    end
  end

  # applies skolemization to a formula and returns the result
  def skolemization(expression, scope\\[]) do
    case expression do
      x when is_list(x) -> Enum.map(x, fn x -> skolemization(x, scope) end)
      {:exqu, v , x} ->
        theta = get_skolem_substitution(v, scope)
        skolemization(substitute(x, theta))
      {:allqu, v, x} -> {:allqu, v, skolemization(x, scope ++ v)}
      {f, x} -> {f, skolemization(x, scope)}
      x -> if atomic?(x) do x else
        IO.puts("Forgotten case in skolemization!")
        IO.inspect(x)
        :error_missing_case
      end
    end
  end

  # given a set of variables and a scope constructs a fitting substitution for these variables according to skolemization
  def get_skolem_substitution(variables, scope) do
    case variables do
      [] -> %{}
      [v | vs] ->
        case scope do
          [] -> Map.merge(%{v => String.to_atom("sk_const_" <> Atom.to_string(v))}, get_skolem_substitution(vs, scope))
          x when is_list(x) -> Map.merge(%{v => {String.to_atom("sk_func_" <> Atom.to_string(v)), x}}, get_skolem_substitution(vs, scope))
          x ->
            IO.puts("Forgotten case in get_skolem_substitution!")
            IO.inspect(x)
            :error_missing_case
        end
    end
  end

  # finds a most general unifier for two expressions, if one exists
  def unify(expressions1, expressions2) do
    if Enum.all?(Enum.map(expressions1 ++ expressions2, fn x -> atomic?(x) end)) and length(expressions1) == length(expressions2) do
      unify_MM(expressions1, expressions2)
    else
      :error_unification_not_possible
  end

  end

  # unification helper method that implements unification according to Martelli/Montanari
  defp unify_MM(expressions1, expressions2) do
    case {expressions1, expressions2} do
      {[], []} -> %{}
      {[x | x1s], [x | x2s]} -> unify_MM(x1s, x2s)
      {[{f, x1} | x1s], [{f, x2} | x2s]} ->
        if length(x1) == length(x2) do
          unify_MM(x1 ++ x1s, x2 ++ x2s)    # unify([f(a, C)], [f(X, Y)]) == unify([a, C], [X, Y])
        else
          :error_unification_not_possible
        end
      {[{_f, _} | _], [[{_g, _} | _]]} -> :error_unification_not_possible
      {[ x1 | x1s], [ x2 | x2s]} -> if variable?(x1) or variable?(x2) do
        if variable?(x1) do
          if not occurs_free(x1, x2) do
            Map.merge(%{x1 => x2}, unify_MM(substitute(x1s, %{x1 => x2}), substitute(x2s, %{x1 => x2})))
          else
            :error_unification_not_possible
          end
        else
          if not occurs_free(x2, x1) do
            Map.merge(%{x2 => x1}, unify_MM(substitute(x1s, %{x2 => x1}), substitute(x2s, %{x2 => x1})))
          else
            :error_unification_not_possible
          end
        end
        else
            :error_unification_not_possible
        end
        x ->
          IO.puts("Forgotten case in unify_MM!")
          IO.inspect(x)
          :error_missing_case
    end
  end

  defp occurs_free(x, t) do
    case t do
      y when is_list(y) -> Enum.any?(Enum.map(y, fn t_i -> occurs_free(x, t_i) end))
      {_, y} -> occurs_free(x, y)
      ^x -> :true
      _y -> :false
    end
  end

end
