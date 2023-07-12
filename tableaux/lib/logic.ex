defmodule Logic do

  def expr_q() do
    {:not, {:exqu, [:A], {:allqu, [:B], {:exqu, [:C, :D], {:or, [:A, {:f, [:A, :B, :C, :D]}]}}}}}
  end

  def expr_unsat() do
    {:and, [:A, {:or, [:C, :D]}, {:or, [{:not, :A}, :D]}, {:not, :D}]}
  end

  def expr_sat() do
    {:not, expr_unsat()}
  end


  # checks syntactic correctness of an expression
  def wff?(expression) do
    case expression do
      x -> if atomic?(x) do :true else
        case x do
          {:allqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:exqu, v, x} -> if Enum.all?(Enum.map(v, &atomic?/1)) do wff?(x) else :false end
          {:not, x} -> wff?(x)
          {:and, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          {:or, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nand, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nor, ops} -> if length(ops) >= 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:rimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:limp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nrimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          #{:nlimp, ops} -> if length(ops) == 2 do Enum.all?(Enum.map(ops, &wff?/1)) else :false end
          x -> IO.puts("Forgotten case in wff?!")
               IO.inspect(x)
               :false
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
      x when is_atom(x) ->
        <<first::utf8>> <> _ = Atom.to_string(expression) # pattern matches s.t. first is the first char in expression
        first =~ ~r/^\p{Lu}$/u  # regex that checks for uppercase
      _ -> :false
    end
  end

  # checks if something is a constant
  def constant?(expression) do
    case expression do
      x when is_atom(x) -> not variable?(x)
      _ -> :false
    end
  end

  # checks if something is a predicate
  def predicate?(expression) do
    case expression do
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
      {f, x} when is_list(x) -> (not operator?(f)) and atomic?(x)
      {f, x} -> (not operator?(f)) and atomic?(x)
      x when is_atom(x) -> not operator?(x)
    end
  end

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

  #############################################
  ######## TRANSFORMATIONS ####################
  #############################################

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
        :false
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
        :false
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
            :false
        end
    end
  end

end
